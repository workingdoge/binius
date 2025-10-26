// Copyright 2025 Working Doge LLC
use binius_core::verify::verify_constraints;
use binius_frontend::{
	CircuitBuilder,
	t_account::{
		LedgerPi, LedgerShape, LedgerSigma, accumulate_transactions, build_ledger_circuit,
		build_ledger_squash_circuit, host_commitment, populate_squash_witness, populate_witness,
	},
};
use proptest::{collection::vec, prelude::*};

fn example_shape() -> LedgerShape {
	LedgerShape::new(2, 1, 3)
}

fn simple_transactions(shape: LedgerShape) -> Vec<LedgerPi> {
	let mut tx0 = LedgerPi::new(LedgerShape::new(shape.accounts, shape.dimensions, 1));
	tx0.post_debit(0, 0, 0, 10);
	tx0.post_credit(1, 0, 0, 10);

	let mut tx1 = LedgerPi::new(LedgerShape::new(shape.accounts, shape.dimensions, 1));
	tx1.post_debit(1, 0, 0, 4);
	tx1.post_credit(0, 0, 0, 4);

	vec![tx0, tx1]
}

#[test]
fn pi_to_sigma_matches_expected_balances() {
	let shape = example_shape();
	let mut pi = LedgerPi::new(shape);
	pi.post_debit(0, 0, 0, 15);
	pi.post_credit(0, 0, 1, 3);
	pi.post_credit(1, 0, 2, 12);

	let sigma = pi.to_sigma();
	assert_eq!(sigma.shape.accounts, 2);
	assert_eq!(sigma.shape.dimensions, 1);
	assert_eq!(sigma.balances[0][0], 12);
	assert_eq!(sigma.balances[1][0], -12);
}

const PROP_ACCS: usize = 2;
const PROP_DIMS: usize = 2;
const PROP_TXS: usize = 3;

fn ledger_inputs_strategy() -> impl Strategy<Value = (Vec<Vec<Vec<u64>>>, Vec<Vec<Vec<u64>>>)> {
	let contrib_a = vec(vec(0u64..128, PROP_TXS), PROP_DIMS);
	let contrib_b = vec(vec(0u64..128, PROP_TXS), PROP_DIMS);
	(contrib_a, contrib_b).prop_map(|(a_vals, b_vals)| {
		let mut debits = vec![vec![vec![0; PROP_TXS]; PROP_DIMS]; PROP_ACCS];
		let mut credits = vec![vec![vec![0; PROP_TXS]; PROP_DIMS]; PROP_ACCS];
		for j in 0..PROP_DIMS {
			for t in 0..PROP_TXS {
				let amt_a = a_vals[j][t];
				let amt_b = b_vals[j][t];
				debits[0][j][t] = amt_a;
				credits[1][j][t] = amt_a;
				debits[1][j][t] = amt_b;
				credits[0][j][t] = amt_b;
			}
		}
		(debits, credits)
	})
}

fn to_pi(shape: LedgerShape, debits: &[Vec<Vec<u64>>], credits: &[Vec<Vec<u64>>]) -> LedgerPi {
	let mut pi = LedgerPi::new(shape);
	for a in 0..shape.accounts {
		for j in 0..shape.dimensions {
			for t in 0..shape.transactions {
				pi.post_debit(a, j, t, debits[a][j][t]);
				pi.post_credit(a, j, t, credits[a][j][t]);
			}
		}
	}
	pi
}

fn manual_sigma(debits: &[Vec<Vec<u64>>], credits: &[Vec<Vec<u64>>]) -> Vec<Vec<i128>> {
	let mut balances = vec![vec![0i128; PROP_DIMS]; PROP_ACCS];
	for a in 0..PROP_ACCS {
		for j in 0..PROP_DIMS {
			let sd: i128 = debits[a][j].iter().map(|&v| v as i128).sum();
			let sc: i128 = credits[a][j].iter().map(|&v| v as i128).sum();
			balances[a][j] = sd - sc;
		}
	}
	balances
}

proptest! {
	#[test]
	fn pi_to_sigma_matches_manual_calculation((debits, credits) in ledger_inputs_strategy()) {
		let shape = LedgerShape::new(PROP_ACCS, PROP_DIMS, PROP_TXS);
		let pi = to_pi(shape, &debits, &credits);
		let sigma = pi.to_sigma();
		let manual = manual_sigma(&debits, &credits);
		prop_assert_eq!(sigma.balances, manual);
	}

	#[test]
	fn commitment_matches_circuit_output((debits, credits) in ledger_inputs_strategy()) {
		let shape = LedgerShape::new(PROP_ACCS, PROP_DIMS, PROP_TXS);
		let pi = to_pi(shape, &debits, &credits);
		let sigma = pi.to_sigma();

		let builder = CircuitBuilder::new();
		let wires = build_ledger_circuit(&builder, shape);
		let circuit = builder.build();
		let mut witness = circuit.new_witness_filler();
		populate_witness(&mut witness, &wires, &pi, &sigma);
		circuit.populate_wire_witness(&mut witness).unwrap();
		let witness_vec = witness.into_value_vec();
		verify_constraints(circuit.constraint_system(), &witness_vec).unwrap();

		let expected = host_commitment(&sigma.flatten_twos_complement());
		let commit_index = circuit.witness_index(wires.commitment);
		prop_assert_eq!(expected, witness_vec[commit_index].0);
	}
}

#[test]
fn accumulate_transactions_sums_deltas() {
	let shape = example_shape();
	let initial = LedgerSigma::zero(shape);
	let transactions = simple_transactions(shape);

	let final_sigma = accumulate_transactions(&initial, &transactions);
	assert_eq!(final_sigma.balances[0][0], 6);
	assert_eq!(final_sigma.balances[1][0], -6);
}

#[test]
fn ledger_commitment_circuit_satisfies_constraints() {
	let shape = example_shape();
	let mut pi = LedgerPi::new(shape);
	pi.post_debit(0, 0, 0, 8);
	pi.post_credit(1, 0, 0, 8);
	pi.post_debit(1, 0, 1, 5);
	pi.post_credit(0, 0, 1, 5);
	pi.post_debit(1, 0, 2, 3);
	pi.post_credit(0, 0, 2, 3);
	let sigma = pi.to_sigma();

	let builder = CircuitBuilder::new();
	let wires = build_ledger_circuit(&builder, shape);
	let circuit = builder.build();
	let cs = circuit.constraint_system();

	let mut witness = circuit.new_witness_filler();
	populate_witness(&mut witness, &wires, &pi, &sigma);
	circuit.populate_wire_witness(&mut witness).unwrap();

	let witness_vec = witness.into_value_vec();
	verify_constraints(cs, &witness_vec).unwrap();

	let host_commit = host_commitment(&sigma.flatten_twos_complement());
	let commit_index = circuit.witness_index(wires.commitment);
	assert_eq!(host_commit, witness_vec[commit_index].0);
}

#[test]
fn ledger_squash_circuit_tracks_state_transition() {
	let shape = LedgerShape::new(2, 1, 1);
	let txs = simple_transactions(shape);
	let initial_sigma = LedgerSigma::zero(shape);
	let final_sigma = accumulate_transactions(&initial_sigma, &txs);

	let builder = CircuitBuilder::new();
	let wires = build_ledger_squash_circuit(&builder, shape, txs.len());
	let circuit = builder.build();
	let cs = circuit.constraint_system();

	let mut witness = circuit.new_witness_filler();
	populate_squash_witness(&mut witness, &wires, &initial_sigma, &txs, &final_sigma);
	circuit.populate_wire_witness(&mut witness).unwrap();

	let witness_vec = witness.into_value_vec();
	verify_constraints(cs, &witness_vec).unwrap();

	let init_commit = host_commitment(&initial_sigma.flatten_twos_complement());
	let final_commit = host_commitment(&final_sigma.flatten_twos_complement());
	let init_index = circuit.witness_index(wires.initial_commitment);
	let final_index = circuit.witness_index(wires.final_commitment);
	assert_eq!(init_commit, witness_vec[init_index].0);
	assert_eq!(final_commit, witness_vec[final_index].0);
}
