// Copyright 2025 Working Doge LLC
//! Vector Accounting (Ellerman / Pacioli group) demo over Binius64
//!
//! This example builds a small circuit that encodes the core *trial-balance* invariant
//! of Ellerman-style vector double-entry bookkeeping:
//!
//! For each commodity dimension `j` and each transaction `t`, the sum of *debits*
//! across all accounts equals the sum of *credits* across all accounts.
//!
//! We model accounts using T-accounts [d // c] over non‑negative 64-bit integers per
//! commodity dimension. The final per-account balances are (d − c) in Z for each
//! dimension; we expose these balances as public outputs.
//!
//! References:
//! - D. Ellerman, "The Math of Double-Entry Bookkeeping: Part II (vectors)". https://www.ellerman.org/the-math-of-double-entry-bookkeeping-part-ii-vectors/
//! - D. Ellerman, "On Double-Entry Bookkeeping: The Mathematical Treatment". https://arxiv.org/abs/1407.1898
//! - Binius64 documentation, "Building". https://www.binius.xyz/building/
//!
//! How to run (from repo root):
//! ```bash
//! cargo run -p binius-examples --example vector_accounting_pacioli
//! ```
use anyhow::{Result, anyhow};
use binius_core::verify::verify_constraints;
use binius_examples::setup_sha256;
use binius_frontend::{
	CircuitBuilder,
	t_account::{LedgerPi, LedgerShape, build_ledger_circuit, host_commitment, populate_witness},
};
use binius_verifier::{
	config::StdChallenger,
	transcript::{ProverTranscript, VerifierTranscript},
};

const ACCS: usize = 4;
const DIMS: usize = 2;
const TXS: usize = 3;

const USD: usize = 0;
const WDG: usize = 1;

const CASH: usize = 0; // USD
const EQUITY: usize = 1; // USD
const WH_A: usize = 2; // Widgets
const WH_B: usize = 3; // Widgets

fn main() -> Result<()> {
	// --------------------------
	// 1) Build the circuit
	// --------------------------
	let builder = CircuitBuilder::new();
	let shape = LedgerShape::new(ACCS, DIMS, TXS);
	let ledger_wires = build_ledger_circuit(&builder, shape);

	let circuit = builder.build();
	let cs = circuit.constraint_system();

	// --------------------------
	// 2) Prepare an instance
	// --------------------------
	// Example ledger with 4 accounts and 2 commodity dimensions:
	// - t0 (USD): debit Cash 1000, credit Equity 1000
	// - t1 (Widgets): debit WH_B 120, credit WH_A 120
	// - t2 (USD): debit Equity 200, credit Cash 200
	let mut pi = LedgerPi::new(shape);

	// t0: owner invests $1000
	pi.post_debit(CASH, USD, 0, 1000);
	pi.post_credit(EQUITY, USD, 0, 1000);

	// t1: move 120 widgets from A to B
	pi.post_debit(WH_B, WDG, 1, 120);
	pi.post_credit(WH_A, WDG, 1, 120);

	// t2: $200 distribution to owner (debit Equity, credit Cash)
	pi.post_debit(EQUITY, USD, 2, 200);
	pi.post_credit(CASH, USD, 2, 200);

	let sigma = pi.to_sigma();

	// --------------------------
	// 3) Populate the witness
	// --------------------------
	let mut witness = circuit.new_witness_filler();
	populate_witness(&mut witness, &ledger_wires, &pi, &sigma);

	// Let the circuit compute internal wires and check basic consistency.
	circuit.populate_wire_witness(&mut witness)?;
	let witness_vec = witness.into_value_vec();

	// Local (non-cryptographic) check that constraints are satisfied
	verify_constraints(cs, &witness_vec)
		.map_err(|err| anyhow!("Local constraint verification failed: {err}"))?;
	println!("✓ trial-balance constraints satisfied and balances match.");

	// --------------------------
	// 4) Produce and verify a Binius proof
	// --------------------------
	// small FRI expansion factor (log_inv_rate) for demo
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

	println!("✓ Binius proof generated and verified.");
	let commitment_value = host_commitment(&sigma.flatten_twos_complement());
	println!("Ledger commitment digest: {commitment_value:#018X}");

	Ok(())
}
