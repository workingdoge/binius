// Copyright 2025 Working Doge LLC
//! Prove the T-account group axioms (associativity, identity, inverse, commutativity) purely in
//! circuit form – all (debit, credit) pairs stay private, the verifier learns only the digest.
//!
//! Run with:
//! ```bash
//! cargo run -p binius-examples --example t_account_group
//! ```

use anyhow::{Result, anyhow};
use binius_core::{verify::verify_constraints, word::Word};
use binius_examples::setup_sha256;
use binius_frontend::{CircuitBuilder, Wire, t_account::host_commitment};
use binius_verifier::{
	config::StdChallenger,
	transcript::{ProverTranscript, VerifierTranscript},
};

const COMMIT_SEED: u64 = 0x6A09_E667_F3BC_C908;
const MIX_CONSTS: [u64; 4] = [
	0xBB67_AE85_84CA_A73B,
	0x3C6E_F372_FE94_F82B,
	0xA54F_F53A_5F1D_36F1,
	0x510E_527F_ADE6_82D1,
];
const ROTL_CONSTS: [u32; 4] = [13, 27, 43, 59];

#[derive(Clone, Copy)]
struct TAccountWires {
	debit: Wire,
	credit: Wire,
}

#[derive(Clone, Copy, Debug)]
struct HostAccount {
	debit: u64,
	credit: u64,
}

impl HostAccount {
	fn new(debit: u64, credit: u64) -> Self {
		let common = debit.min(credit);
		Self {
			debit: debit - common,
			credit: credit - common,
		}
	}

	fn from_i64(balance: i64) -> Self {
		if balance >= 0 {
			Self::new(balance as u64, 0)
		} else {
			Self::new(0, balance.unsigned_abs() as u64)
		}
	}
}

fn add_accounts(
	builder: &CircuitBuilder,
	zero: Wire,
	lhs: &TAccountWires,
	rhs: &TAccountWires,
) -> TAccountWires {
	let (debit_sum, _debit_carry) = builder.iadd_cin_cout(lhs.debit, rhs.debit, zero);
	let (credit_sum, _credit_carry) = builder.iadd_cin_cout(lhs.credit, rhs.credit, zero);

	let lt = builder.icmp_ult(debit_sum, credit_sum);
	let common = builder.select(lt, debit_sum, credit_sum);

	let (canon_debit, _borrow_debit) = builder.isub_bin_bout(debit_sum, common, zero);
	let (canon_credit, _borrow_credit) = builder.isub_bin_bout(credit_sum, common, zero);

	TAccountWires {
		debit: canon_debit,
		credit: canon_credit,
	}
}

fn commit_wires(builder: &CircuitBuilder, zero: Wire, values: &[Wire]) -> Wire {
	let mut acc = builder.add_constant_64(COMMIT_SEED);

	for (idx, &value) in values.iter().enumerate() {
		let rot = builder.rotl(acc, ROTL_CONSTS[idx % ROTL_CONSTS.len()]);
		let mix = builder.add_constant_64(MIX_CONSTS[idx % MIX_CONSTS.len()]);
		let mixed = builder.bxor(rot, mix);
		let (sum, _carry) = builder.iadd_cin_cout(mixed, value, zero);
		acc = sum;
	}

	let digest = builder.add_inout();
	builder.assert_eq("t_account_commitment", acc, digest);
	digest
}

fn main() -> Result<()> {
	let builder = CircuitBuilder::new();

	let zero = builder.add_constant_64(0);

	let account_a = TAccountWires {
		debit: builder.add_witness(),
		credit: builder.add_witness(),
	};
	let account_b = TAccountWires {
		debit: builder.add_witness(),
		credit: builder.add_witness(),
	};
	let account_c = TAccountWires {
		debit: builder.add_witness(),
		credit: builder.add_witness(),
	};

	let sum_ab = add_accounts(&builder, zero, &account_a, &account_b);
	let sum_bc = add_accounts(&builder, zero, &account_b, &account_c);
	let assoc_left = add_accounts(&builder, zero, &sum_ab, &account_c);
	let assoc_right = add_accounts(&builder, zero, &account_a, &sum_bc);
	builder.assert_eq("assoc_debit", assoc_left.debit, assoc_right.debit);
	builder.assert_eq("assoc_credit", assoc_left.credit, assoc_right.credit);

	let identity = TAccountWires {
		debit: zero,
		credit: zero,
	};
	let left_identity = add_accounts(&builder, zero, &account_a, &identity);
	builder.assert_eq("left_identity_debit", left_identity.debit, account_a.debit);
	builder.assert_eq("left_identity_credit", left_identity.credit, account_a.credit);

	let right_identity = add_accounts(&builder, zero, &identity, &account_a);
	builder.assert_eq("right_identity_debit", right_identity.debit, account_a.debit);
	builder.assert_eq("right_identity_credit", right_identity.credit, account_a.credit);

	let inverse_a = TAccountWires {
		debit: account_a.credit,
		credit: account_a.debit,
	};
	let a_plus_inv = add_accounts(&builder, zero, &account_a, &inverse_a);
	builder.assert_eq("inverse_debit", a_plus_inv.debit, zero);
	builder.assert_eq("inverse_credit", a_plus_inv.credit, zero);

	let inv_plus_a = add_accounts(&builder, zero, &inverse_a, &account_a);
	builder.assert_eq("inverse_debit_comm", inv_plus_a.debit, zero);
	builder.assert_eq("inverse_credit_comm", inv_plus_a.credit, zero);

	let comm_sum = sum_ab;
	let comm_rev_sum = add_accounts(&builder, zero, &account_b, &account_a);
	builder.assert_eq("comm_debit", comm_sum.debit, comm_rev_sum.debit);
	builder.assert_eq("comm_credit", comm_sum.credit, comm_rev_sum.credit);

	let flatten_accounts = [
		account_a.debit,
		account_a.credit,
		account_b.debit,
		account_b.credit,
		account_c.debit,
		account_c.credit,
	];
	let commitment_wire = commit_wires(&builder, zero, &flatten_accounts);

	let circuit = builder.build();
	let cs = circuit.constraint_system();

	let mut witness = circuit.new_witness_filler();

	let host_a = HostAccount::from_i64(1_000);
	let host_b = HostAccount::from_i64(-370);
	let host_c = HostAccount::from_i64(300);

	witness[account_a.debit] = Word(host_a.debit);
	witness[account_a.credit] = Word(host_a.credit);
	witness[account_b.debit] = Word(host_b.debit);
	witness[account_b.credit] = Word(host_b.credit);
	witness[account_c.debit] = Word(host_c.debit);
	witness[account_c.credit] = Word(host_c.credit);

	let host_commit_values = [
		host_a.debit,
		host_a.credit,
		host_b.debit,
		host_b.credit,
		host_c.debit,
		host_c.credit,
	];
	let commitment = host_commitment(&host_commit_values);
	witness[commitment_wire] = Word(commitment);

	circuit.populate_wire_witness(&mut witness)?;
	let witness_vec = witness.into_value_vec();

	verify_constraints(cs, &witness_vec)
		.map_err(|err| anyhow!("Local constraint verification failed: {err}"))?;

	let log_inv_rate = 2usize;
	let (verifier, prover) = setup_sha256(cs.clone(), log_inv_rate, None)?;
	let challenger = StdChallenger::default();

	let public_words = witness_vec.public().to_vec();
	let mut prover_transcript = ProverTranscript::new(challenger.clone());
	prover.prove(witness_vec.clone(), &mut prover_transcript)?;
	let proof = prover_transcript.finalize();

	let mut verifier_transcript = VerifierTranscript::new(challenger, proof);
	verifier.verify(&public_words, &mut verifier_transcript)?;
	verifier_transcript.finalize()?;

	let digest_value = witness_vec[circuit.witness_index(commitment_wire)].0;
	println!("✓ T-account group proof generated and verified.");
	println!("Ledger commitment digest: {digest_value:#018X}");

	Ok(())
}
