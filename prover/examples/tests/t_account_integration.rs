// Copyright 2025 Working Doge LLC
use anyhow::Result;
use binius_examples::setup_sha256;
use binius_frontend::{
	t_account::{
		accumulate_transactions, build_ledger_circuit, build_ledger_squash_circuit, populate_squash_witness,
		populate_witness, LedgerPi, LedgerShape, LedgerSigma,
	},
	CircuitBuilder,
};
use binius_verifier::{
	config::StdChallenger,
	transcript::{ProverTranscript, VerifierTranscript},
};
use proptest::{collection::vec, prelude::*};

fn prove_and_verify(shape: LedgerShape, pi: &LedgerPi, sigma: &LedgerSigma) -> Result<()> {
	let builder = CircuitBuilder::new();
	let wires = build_ledger_circuit(&builder, shape);
	let circuit = builder.build();
	let cs = circuit.constraint_system().clone();

	let mut witness = circuit.new_witness_filler();
	populate_witness(&mut witness, &wires, pi, sigma);
	circuit.populate_wire_witness(&mut witness)?;
	let witness_vec = witness.into_value_vec();

	let (verifier, prover) = setup_sha256(cs.clone(), 2, None)?;
	let challenger = StdChallenger::default();
	let mut prover_transcript = ProverTranscript::new(challenger.clone());
	prover.prove(witness_vec.clone(), &mut prover_transcript)?;
	let proof = prover_transcript.finalize();
	let mut verifier_transcript = VerifierTranscript::new(challenger, proof);
	verifier.verify(witness_vec.public(), &mut verifier_transcript)?;
	verifier_transcript.finalize()?;
	Ok(())
}

fn prove_and_verify_squash(shape: LedgerShape, txs: &[LedgerPi]) -> Result<()> {
	let initial_sigma = LedgerSigma::zero(shape);
	let final_sigma = accumulate_transactions(&initial_sigma, txs);
	let builder = CircuitBuilder::new();
	let wires = build_ledger_squash_circuit(&builder, shape, txs.len());
	let circuit = builder.build();
	let cs = circuit.constraint_system().clone();

	let mut witness = circuit.new_witness_filler();
	populate_squash_witness(&mut witness, &wires, &initial_sigma, txs, &final_sigma);
	circuit.populate_wire_witness(&mut witness)?;
	let witness_vec = witness.into_value_vec();

	let (verifier, prover) = setup_sha256(cs.clone(), 2, None)?;
	let challenger = StdChallenger::default();
	let mut prover_transcript = ProverTranscript::new(challenger.clone());
	prover.prove(witness_vec.clone(), &mut prover_transcript)?;
	let proof = prover_transcript.finalize();
	let mut verifier_transcript = VerifierTranscript::new(challenger, proof);
	verifier.verify(witness_vec.public(), &mut verifier_transcript)?;
	verifier_transcript.finalize()?;
	Ok(())
}

#[test]
fn proves_single_t_account_instance() {
	let shape = LedgerShape::new(2, 1, 1);
	let mut pi = LedgerPi::new(shape);
	pi.post_debit(0, 0, 0, 10);
	pi.post_credit(1, 0, 0, 10);
	let sigma = pi.to_sigma();
	prove_and_verify(shape, &pi, &sigma).unwrap();
}

#[test]
fn proves_state_squash() {
	let shape = LedgerShape::new(2, 1, 1);
	let mut tx0 = LedgerPi::new(shape);
	tx0.post_debit(0, 0, 0, 7);
	tx0.post_credit(1, 0, 0, 7);
	let mut tx1 = LedgerPi::new(shape);
	tx1.post_debit(1, 0, 0, 3);
	tx1.post_credit(0, 0, 0, 3);
	let txs = vec![tx0, tx1];
	prove_and_verify_squash(shape, &txs).unwrap();
}

const PROP_ACCS: usize = 2;
const PROP_DIMS: usize = 1;
const PROP_TXS: usize = 1;

fn tx_strategy() -> impl Strategy<Value = Vec<LedgerPi>> {
	let entry = vec(0u64..128, PROP_DIMS);
	let base = vec(entry, PROP_ACCS);
	(1usize..=3).prop_flat_map(move |len| {
		vec(base.clone(), len).prop_map(move |samples| {
			let shape = LedgerShape::new(PROP_ACCS, PROP_DIMS, PROP_TXS);
			samples
				.into_iter()
				.map(|matrix| {
					let mut pi = LedgerPi::new(shape);
					for a in 0..PROP_ACCS {
						for d in 0..PROP_DIMS {
							let amt = matrix[a][d];
							pi.post_debit(a, d, 0, amt);
							let other = (a + 1) % PROP_ACCS;
							pi.post_credit(other, d, 0, amt);
						}
					}
					pi
				})
				.collect::<Vec<_>>()
		})
	})
}

proptest! {
	#[test]
	fn proves_random_transactions(txs in tx_strategy()) {
		let shape = LedgerShape::new(PROP_ACCS, PROP_DIMS, PROP_TXS);
		for pi in &txs {
			let sigma = pi.to_sigma();
			prove_and_verify(shape, pi, &sigma).unwrap();
		}
		prove_and_verify_squash(shape, &txs).unwrap();
	}
}
