// Copyright 2025 Working Doge LLC
//! T-account sigma/π abstractions and reusable circuit gadgets.
//!
//! This module provides a clean separation between:
//! - **Σ-objects** (`LedgerSigma`): canonical T-account balances in ℤ
//! - **Π-objects** (`LedgerPi`): sequences of debit/credit postings
//! - **Circuit helpers** that enforce double-entry invariants, derive balances, and publish
//!   sponge commitments to the T-account state
//!
//! The API mirrors the construction used in the `vector_accounting_pacioli` and
//! `ledger_state_squash` examples: aggregate postings into a `LedgerPi`, collapse to
//! `LedgerSigma`, and call [`build_ledger_circuit`] to obtain the wires. Witness population is
//! fully deterministic—fill the Π/Σ structures and the gadget handles the rest.
//!
//! ```ignore
//! use anyhow::Result;
//! use binius_core::verify::verify_constraints;
//! use binius_frontend::{
//!     t_account::{LedgerPi, LedgerShape, build_ledger_circuit, populate_witness},
//!     CircuitBuilder,
//! };
//!
//! fn prove_trial_balance() -> Result<()> {
//!     let shape = LedgerShape::new(2, 1, 1);
//!     let mut pi = LedgerPi::new(shape);
//!     pi.post_debit(0, 0, 0, 10);
//!     pi.post_credit(1, 0, 0, 10);
//!     let sigma = pi.to_sigma();
//!
//!     let builder = CircuitBuilder::new();
//!     let wires = build_ledger_circuit(&builder, shape);
//!     let circuit = builder.build();
//!     let cs = circuit.constraint_system();
//!     let mut witness = circuit.new_witness_filler();
//!     populate_witness(&mut witness, &wires, &pi, &sigma);
//!     circuit.populate_wire_witness(&mut witness)?;
//!     verify_constraints(cs, &witness.into_value_vec())?;
//!     Ok(())
//! }
//! ```

use binius_core::word::Word;

use crate::{compiler::circuit::WitnessFiller, CircuitBuilder, Wire};

/// Shape of a T-account ledger instance: number of accounts, commodity dimensions, and transactions.
#[derive(Clone, Copy, Debug)]
pub struct LedgerShape {
	/// Number of distinct accounts.
	pub accounts: usize,
	/// Number of commodity dimensions.
	pub dimensions: usize,
	/// Number of transactions per `LedgerPi`.
	pub transactions: usize,
}

impl LedgerShape {
	/// Construct a new shape.
	#[inline]
	pub const fn new(accounts: usize, dimensions: usize, transactions: usize) -> Self {
		Self {
			accounts,
			dimensions,
			transactions,
		}
	}
}

/// Sigma-type: canonical T-account balances in ℤ for each account × dimension.
#[derive(Clone, Debug)]
pub struct LedgerSigma {
	/// Shape associated with this sigma object.
	pub shape: LedgerShape,
	/// `balances[account][dimension] = debit_sum - credit_sum` (signed).
	pub balances: Vec<Vec<i128>>,
}

impl LedgerSigma {
	/// Sigma object with all balances equal to zero.
	pub fn zero(shape: LedgerShape) -> Self {
		let balances = vec![vec![0i128; shape.dimensions]; shape.accounts];
		Self { shape, balances }
	}

	/// Flatten balances into two's complement `u64` encoding (row-major).
	pub fn flatten_twos_complement(&self) -> Vec<u64> {
		self.balances
			.iter()
			.flat_map(|dims| dims.iter().map(|&z| encode_balance(z)))
			.collect()
	}

	/// Add another sigma object in-place.
	pub fn add_assign(&mut self, other: &LedgerSigma) {
		assert_eq!(self.shape.accounts, other.shape.accounts);
		assert_eq!(self.shape.dimensions, other.shape.dimensions);
		for (lhs_row, rhs_row) in self.balances.iter_mut().zip(&other.balances) {
			for (lhs, rhs) in lhs_row.iter_mut().zip(rhs_row) {
				*lhs += rhs;
			}
		}
	}

	/// Return a new sigma that is the sum of `self` and `other`.
	pub fn added(&self, other: &LedgerSigma) -> LedgerSigma {
		let mut out = self.clone();
		out.add_assign(other);
		out
	}
}

/// Pi-type: postings (debit/credit amounts) for each account × dimension × transaction.
#[derive(Clone, Debug)]
pub struct LedgerPi {
	/// Debit postings.
	pub debits: Vec<Vec<Vec<u64>>>,
	/// Credit postings.
	pub credits: Vec<Vec<Vec<u64>>>,
	shape: LedgerShape,
}

impl LedgerPi {
	/// Create a new Π object initialised to zero.
	pub fn new(shape: LedgerShape) -> Self {
		let LedgerShape {
			accounts,
			dimensions,
			transactions,
		} = shape;
		let debits = vec![vec![vec![0; transactions]; dimensions]; accounts];
		let credits = vec![vec![vec![0; transactions]; dimensions]; accounts];
		Self {
			debits,
			credits,
			shape,
		}
	}

	/// Post a debit entry.
	pub fn post_debit(&mut self, account: usize, dimension: usize, tx: usize, amount: u64) {
		self.debits[account][dimension][tx] = amount;
	}

	/// Post a credit entry.
	pub fn post_credit(&mut self, account: usize, dimension: usize, tx: usize, amount: u64) {
		self.credits[account][dimension][tx] = amount;
	}

	/// Return the shape of this Π object.
	pub fn shape(&self) -> LedgerShape {
		self.shape
	}

	/// Left adjoint: collapse postings into canonical balances.
	pub fn to_sigma(&self) -> LedgerSigma {
		let mut balances = vec![vec![0i128; self.shape.dimensions]; self.shape.accounts];
		for a in 0..self.shape.accounts {
			for j in 0..self.shape.dimensions {
				let sd: u128 = (0..self.shape.transactions)
					.map(|t| self.debits[a][j][t] as u128)
					.sum();
				let sc: u128 = (0..self.shape.transactions)
					.map(|t| self.credits[a][j][t] as u128)
					.sum();
				balances[a][j] = sd as i128 - sc as i128;
			}
		}
		LedgerSigma { shape: self.shape, balances }
	}
}

/// Fold a sequence of transaction Π-objects into a Σ state.
pub fn accumulate_transactions(initial: &LedgerSigma, transactions: &[LedgerPi]) -> LedgerSigma {
	let mut acc = initial.clone();
	for tx in transactions {
		let delta = tx.to_sigma();
		acc.add_assign(&delta);
	}
	acc
}

/// Circuit wires for a single T-account commitment gadget.
pub struct LedgerWires {
	/// Debit postings: `[account][dimension][transaction]`.
	pub debit: Vec<Vec<Vec<Wire>>>,
	/// Credit postings: `[account][dimension][transaction]`.
	pub credit: Vec<Vec<Vec<Wire>>>,
	/// Canonical balances: `[account][dimension]`.
	pub balance: Vec<Vec<Wire>>,
	/// Commitment to balances.
	pub commitment: Wire,
}

/// Wires for the state squash gadget.
pub struct LedgerSquashWires {
	/// Initial balances.
	pub initial_balance: Vec<Vec<Wire>>,
	/// Final balances.
	pub final_balance: Vec<Vec<Wire>>,
	/// Debit postings per transaction.
	pub tx_debit: Vec<Vec<Vec<Wire>>>,
	/// Credit postings per transaction.
	pub tx_credit: Vec<Vec<Vec<Wire>>>,
	/// Commitment to the initial balances.
	pub initial_commitment: Wire,
	/// Commitment to the final balances.
	pub final_commitment: Wire,
	/// Commitments to each transaction delta.
	pub tx_commitments: Vec<Wire>,
}

fn flatten_matrix(matrix: &[Vec<Wire>]) -> Vec<Wire> {
	matrix.iter().flat_map(|row| row.iter().copied()).collect()
}

fn sum_many64(builder: &CircuitBuilder, mut wires: Vec<Wire>) -> (Wire, Wire) {
	let zero = builder.add_constant_64(0);
	let mut sum = zero;
	let mut carry = zero;
	for w in wires.drain(..) {
		let (s, c) = builder.iadd_cin_cout(sum, w, carry);
		sum = s;
		carry = c;
	}
	(sum, carry)
}

fn sub64(builder: &CircuitBuilder, a: Wire, b: Wire) -> Wire {
	let all_one = builder.add_constant_64(u64::MAX);
	let cin_one = builder.add_constant_64(1u64 << 63);
	let b_inv = builder.bxor(b, all_one);
	let (sum, _cout) = builder.iadd_cin_cout(a, b_inv, cin_one);
	sum
}

fn encode_balance(z: i128) -> u64 {
	if z >= 0 {
		z as u64
	} else {
		(!0u64).wrapping_add((z + 1) as u64)
	}
}

const COMMIT_SEED: u64 = 0x6A09_E667_F3BC_C908;
const MIX_CONSTS: [u64; 4] = [
	0xBB67_AE85_84CA_A73B,
	0x3C6E_F372_FE94_F82B,
	0xA54F_F53A_5F1D_36F1,
	0x510E_527F_ADE6_82D1,
];
const ROTL_CONSTS: [u32; 4] = [13, 27, 43, 59];

fn commit_wires(builder: &CircuitBuilder, balances: &[Wire]) -> Wire {
	let mut acc = builder.add_constant_64(COMMIT_SEED);
	let zero = builder.add_constant_64(0);
	for (idx, &balance) in balances.iter().enumerate() {
		let rot = builder.rotl(acc, ROTL_CONSTS[idx % ROTL_CONSTS.len()]);
		let mix_const = builder.add_constant_64(MIX_CONSTS[idx % MIX_CONSTS.len()]);
		let mixed = builder.bxor(rot, mix_const);
		let (sum, _carry) = builder.iadd_cin_cout(mixed, balance, zero);
		acc = sum;
	}
	let digest = builder.add_inout();
	builder.assert_eq("ledger_commitment", acc, digest);
	digest
}

/// Host-side commitment helper mirroring the circuit gadget.
pub fn host_commitment(words: &[u64]) -> u64 {
	let mut acc = COMMIT_SEED;
	for (idx, value) in words.iter().copied().enumerate() {
		let rot = acc.rotate_left(ROTL_CONSTS[idx % ROTL_CONSTS.len()]);
		let mix = rot ^ MIX_CONSTS[idx % MIX_CONSTS.len()];
		acc = mix.wrapping_add(value);
	}
	acc
}

/// Build the T-account commitment circuit for a batch of postings.
pub fn build_ledger_circuit(builder: &CircuitBuilder, shape: LedgerShape) -> LedgerWires {
	let LedgerShape {
		accounts,
		dimensions,
		transactions,
	} = shape;

	let debit: Vec<Vec<Vec<Wire>>> = (0..accounts)
		.map(|_| {
			(0..dimensions)
				.map(|_| (0..transactions).map(|_| builder.add_witness()).collect())
				.collect()
		})
		.collect();
	let credit: Vec<Vec<Vec<Wire>>> = (0..accounts)
		.map(|_| {
			(0..dimensions)
				.map(|_| (0..transactions).map(|_| builder.add_witness()).collect())
				.collect()
		})
		.collect();

	let balance: Vec<Vec<Wire>> = (0..accounts)
		.map(|_| (0..dimensions).map(|_| builder.add_witness()).collect())
		.collect();

	for t in 0..transactions {
		for j in 0..dimensions {
			let (sum_d, carry_d) =
				sum_many64(builder, (0..accounts).map(|a| debit[a][j][t]).collect());
			let (sum_c, carry_c) =
				sum_many64(builder, (0..accounts).map(|a| credit[a][j][t]).collect());
			builder.assert_eq(format!("tx{t}_dim{j}_sum"), sum_d, sum_c);
			builder.assert_eq(format!("tx{t}_dim{j}_carry"), carry_d, carry_c);
		}
	}

	for a in 0..accounts {
		for j in 0..dimensions {
			let (sum_d, _cd) =
				sum_many64(builder, (0..transactions).map(|t| debit[a][j][t]).collect());
			let (sum_c, _cc) =
				sum_many64(builder, (0..transactions).map(|t| credit[a][j][t]).collect());
			let diff = sub64(builder, sum_d, sum_c);
			builder.assert_eq(format!("balance_a{a}_dim{j}"), diff, balance[a][j]);
		}
	}

	let commitment = commit_wires(builder, &flatten_matrix(&balance));

	LedgerWires {
		debit,
		credit,
		balance,
		commitment,
	}
}

/// Populate witness values for the T-account commitment gadget.
pub fn populate_witness(
	witness: &mut WitnessFiller<'_>,
	wires: &LedgerWires,
	pi: &LedgerPi,
	sigma: &LedgerSigma,
) {
	assert_eq!(pi.shape.accounts, wires.debit.len());
	assert_eq!(pi.shape.dimensions, wires.debit[0].len());

	for (a, account) in wires.debit.iter().enumerate() {
		for (j, dim) in account.iter().enumerate() {
			for (t, &wire) in dim.iter().enumerate() {
				witness[wire] = Word(pi.debits[a][j][t]);
			}
		}
	}
	for (a, account) in wires.credit.iter().enumerate() {
		for (j, dim) in account.iter().enumerate() {
			for (t, &wire) in dim.iter().enumerate() {
				witness[wire] = Word(pi.credits[a][j][t]);
			}
		}
	}
	for (a, account) in wires.balance.iter().enumerate() {
		for (j, &wire) in account.iter().enumerate() {
			let encoded = encode_balance(sigma.balances[a][j]);
			witness[wire] = Word(encoded);
		}
	}
	let commitment_words = sigma.flatten_twos_complement();
	witness[wires.commitment] = Word(host_commitment(&commitment_words));
}

/// Build the T-account state squash circuit for a fixed number of transactions.
///
/// Each transaction is expected to be represented by a `LedgerPi` with `transactions == 1`.
pub fn build_ledger_squash_circuit(
	builder: &CircuitBuilder,
	shape: LedgerShape,
	n_transactions: usize,
) -> LedgerSquashWires {
	let LedgerShape {
		accounts,
		dimensions,
		..
	} = shape;

	let zero = builder.add_constant_64(0);

	let initial_balance: Vec<Vec<Wire>> = (0..accounts)
		.map(|_| (0..dimensions).map(|_| builder.add_witness()).collect())
		.collect();
	let initial_commitment = commit_wires(builder, &flatten_matrix(&initial_balance));

	let final_balance: Vec<Vec<Wire>> = (0..accounts)
		.map(|_| (0..dimensions).map(|_| builder.add_witness()).collect())
		.collect();

	let mut tx_debit = Vec::with_capacity(n_transactions);
	let mut tx_credit = Vec::with_capacity(n_transactions);
	let mut tx_commitments = Vec::with_capacity(n_transactions);

	let mut state = initial_balance.clone();

	for t in 0..n_transactions {
		let debit_t: Vec<Vec<Wire>> = (0..accounts)
			.map(|_| (0..dimensions).map(|_| builder.add_witness()).collect())
			.collect();
		let credit_t: Vec<Vec<Wire>> = (0..accounts)
			.map(|_| (0..dimensions).map(|_| builder.add_witness()).collect())
			.collect();

		for j in 0..dimensions {
			let (sum_d, carry_d) =
				sum_many64(builder, (0..accounts).map(|a| debit_t[a][j]).collect());
			let (sum_c, carry_c) =
				sum_many64(builder, (0..accounts).map(|a| credit_t[a][j]).collect());
			builder.assert_eq(
				format!("squash_tx{t}_dim{j}_sum"),
				sum_d,
				sum_c,
			);
			builder.assert_eq(
				format!("squash_tx{t}_dim{j}_carry"),
				carry_d,
				carry_c,
			);
		}

		let mut diff_flat = Vec::with_capacity(accounts * dimensions);
		for a in 0..accounts {
			for j in 0..dimensions {
				let diff = sub64(builder, debit_t[a][j], credit_t[a][j]);
				diff_flat.push(diff);
				let (updated, _carry) = builder.iadd_cin_cout(state[a][j], diff, zero);
				state[a][j] = updated;
			}
		}
		let tx_commit = commit_wires(builder, &diff_flat);
		tx_commitments.push(tx_commit);
		tx_debit.push(debit_t);
		tx_credit.push(credit_t);
	}

	for a in 0..accounts {
		for j in 0..dimensions {
			builder.assert_eq(
				format!("squash_final_a{a}_dim{j}"),
				state[a][j],
				final_balance[a][j],
			);
		}
	}
	let final_commitment = commit_wires(builder, &flatten_matrix(&final_balance));

	LedgerSquashWires {
		initial_balance,
		final_balance,
		tx_debit,
		tx_credit,
		initial_commitment,
		final_commitment,
		tx_commitments,
	}
}

/// Populate witness values for the state squash gadget.
///
/// Each `transactions[i]` must have `transactions == 1` in its shape.
pub fn populate_squash_witness(
	witness: &mut WitnessFiller<'_>,
	wires: &LedgerSquashWires,
	initial_sigma: &LedgerSigma,
	transactions: &[LedgerPi],
	final_sigma: &LedgerSigma,
) {
	assert_eq!(transactions.len(), wires.tx_debit.len());

	for (a, row) in wires.initial_balance.iter().enumerate() {
		for (j, &wire) in row.iter().enumerate() {
			let encoded = encode_balance(initial_sigma.balances[a][j]);
			witness[wire] = Word(encoded);
		}
	}

	for (tx_idx, (debit_wires, credit_wires)) in
		wires.tx_debit.iter().zip(&wires.tx_credit).enumerate()
	{
		let pi = &transactions[tx_idx];
		assert_eq!(
			pi.shape.transactions, 1,
			"squash gadget expects transactions with a single posting column"
		);
		for (a, account) in debit_wires.iter().enumerate() {
			for (j, &wire) in account.iter().enumerate() {
				witness[wire] = Word(pi.debits[a][j][0]);
			}
		}
		for (a, account) in credit_wires.iter().enumerate() {
			for (j, &wire) in account.iter().enumerate() {
				witness[wire] = Word(pi.credits[a][j][0]);
			}
		}
	}

	for (a, row) in wires.final_balance.iter().enumerate() {
		for (j, &wire) in row.iter().enumerate() {
			let encoded = encode_balance(final_sigma.balances[a][j]);
			witness[wire] = Word(encoded);
		}
	}

	let init_commit = host_commitment(&initial_sigma.flatten_twos_complement());
	witness[wires.initial_commitment] = Word(init_commit);

	for (wire, pi) in wires.tx_commitments.iter().zip(transactions) {
		let delta_sigma = pi.to_sigma();
		let commit = host_commitment(&delta_sigma.flatten_twos_complement());
		witness[*wire] = Word(commit);
	}

	let final_commit = host_commitment(&final_sigma.flatten_twos_complement());
	witness[wires.final_commitment] = Word(final_commit);
}
