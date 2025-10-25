// Copyright 2025 Working Doge LLC
use anyhow::{Result, anyhow};
use binius_core::verify::verify_constraints;
use binius_examples::setup_sha256;
use binius_frontend::{
	CircuitBuilder,
	t_account::{
		LedgerPi, LedgerShape, LedgerSigma, accumulate_transactions, build_ledger_squash_circuit,
		host_commitment, populate_squash_witness,
	},
};
use binius_verifier::{
	config::StdChallenger,
	transcript::{ProverTranscript, VerifierTranscript},
};

const ACCS: usize = 4;
const DIMS: usize = 2;

const USD: usize = 0;
const WDG: usize = 1;

const CASH: usize = 0;
const EQUITY: usize = 1;
const WH_A: usize = 2;
const WH_B: usize = 3;

fn build_transactions(shape: LedgerShape) -> Vec<LedgerPi> {
	let mut txs = Vec::new();

	let mut tx0 = LedgerPi::new(shape);
	tx0.post_debit(CASH, USD, 0, 1_000);
	tx0.post_credit(EQUITY, USD, 0, 1_000);
	txs.push(tx0);

	let mut tx1 = LedgerPi::new(shape);
	tx1.post_debit(WH_B, WDG, 0, 120);
	tx1.post_credit(WH_A, WDG, 0, 120);
	txs.push(tx1);

	let mut tx2 = LedgerPi::new(shape);
	tx2.post_debit(EQUITY, USD, 0, 200);
	tx2.post_credit(CASH, USD, 0, 200);
	txs.push(tx2);

	txs
}

fn main() -> Result<()> {
	let shape = LedgerShape::new(ACCS, DIMS, 1);
	let transactions = build_transactions(shape);
	let initial_sigma = LedgerSigma::zero(shape);
	let final_sigma = accumulate_transactions(&initial_sigma, &transactions);

	let builder = CircuitBuilder::new();
	let squash_wires = build_ledger_squash_circuit(&builder, shape, transactions.len());
	let circuit = builder.build();
	let cs = circuit.constraint_system();

	let mut witness = circuit.new_witness_filler();
	populate_squash_witness(
		&mut witness,
		&squash_wires,
		&initial_sigma,
		&transactions,
		&final_sigma,
	);

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

	let initial_commit = host_commitment(&initial_sigma.flatten_twos_complement());
	let final_commit = host_commitment(&final_sigma.flatten_twos_complement());
	println!("✓ Ledger state squash proof generated and verified.");
	println!("Initial ledger commitment: {initial_commit:#018X}");
	println!("Final ledger commitment:   {final_commit:#018X}");

	Ok(())
}
//! Balance-sheet style state squash: fold a sequence of transaction commitments into a final
//! ledger commitment while keeping individual postings private.
//!
//! Run with:
//! ```bash
//! cargo run -p binius-examples --example ledger_state_squash
//! ```
