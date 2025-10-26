//! Combined T-account showcase: group axioms plus ledger state squash in a single run.
use std::cell::Cell;

use anyhow::{Result, bail};
use binius_core::word::Word;
use binius_examples::{CompressionType, ExampleCircuit, prove_example};
use binius_frontend::{
	CircuitBuilder, Wire, WitnessFiller,
	t_account::{
		LedgerPi, LedgerShape, LedgerSigma, LedgerSquashWires, accumulate_transactions,
		build_ledger_squash_circuit, commit_wires, host_commitment, populate_squash_witness,
	},
};
use clap::{ArgGroup, Args, Parser};

#[derive(Parser, Debug)]
#[command(
	name = "t_account_showcase",
	about = "End-to-end T-account demo: group axioms and ledger state squash",
	group(
		ArgGroup::new("selection")
			.args(["skip_group", "skip_ledger"])
			.multiple(true)
	)
)]
struct ShowcaseArgs {
	/// Log of the inverse rate for the proof system.
	#[arg(long = "log-inv-rate", default_value_t = 1, value_parser = clap::value_parser!(u32).range(1..))]
	log_inv_rate: u32,

	/// Compression function to use for Merkle trees.
	#[arg(long, value_enum, default_value_t = CompressionType::Sha256)]
	compression: CompressionType,

	/// Disable the T-account group proof.
	#[arg(long)]
	skip_group: bool,

	/// Disable the ledger state squash proof.
	#[arg(long)]
	skip_ledger: bool,

	#[command(flatten)]
	group: GroupInstance,

	#[command(flatten)]
	ledger: LedgerInstance,
}

#[derive(Args, Debug, Clone, Default)]
struct GroupParams {}

#[derive(Args, Debug, Clone)]
struct GroupInstance {
	#[arg(long = "group-a", default_value_t = 1_000)]
	account_a_balance: i64,
	#[arg(long = "group-b", default_value_t = -370)]
	account_b_balance: i64,
	#[arg(long = "group-c", default_value_t = 300)]
	account_c_balance: i64,
}

#[derive(Args, Debug, Clone, Default)]
struct LedgerParams {}

#[derive(Args, Debug, Clone)]
struct LedgerInstance {
	#[arg(long = "ledger-invest-usd", default_value_t = 1_000)]
	invest_usd: u64,
	#[arg(long = "ledger-move-widgets", default_value_t = 120)]
	move_widgets: u64,
	#[arg(long = "ledger-distribution-usd", default_value_t = 200)]
	distribution_usd: u64,
}

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

struct TAccountGroupExample {
	account_a: TAccountWires,
	account_b: TAccountWires,
	account_c: TAccountWires,
	commitment_wire: Wire,
	commitment_value: Cell<Option<u64>>,
}

impl ExampleCircuit for TAccountGroupExample {
	type Params = GroupParams;
	type Instance = GroupInstance;

	fn build(_params: GroupParams, builder: &mut CircuitBuilder) -> Result<Self> {
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

		let sum_ab = add_accounts(builder, zero, &account_a, &account_b);
		let sum_bc = add_accounts(builder, zero, &account_b, &account_c);
		let assoc_left = add_accounts(builder, zero, &sum_ab, &account_c);
		let assoc_right = add_accounts(builder, zero, &account_a, &sum_bc);
		builder.assert_eq("assoc_debit", assoc_left.debit, assoc_right.debit);
		builder.assert_eq("assoc_credit", assoc_left.credit, assoc_right.credit);

		let identity = TAccountWires {
			debit: zero,
			credit: zero,
		};
		let left_identity = add_accounts(builder, zero, &account_a, &identity);
		builder.assert_eq("left_identity_debit", left_identity.debit, account_a.debit);
		builder.assert_eq("left_identity_credit", left_identity.credit, account_a.credit);

		let right_identity = add_accounts(builder, zero, &identity, &account_a);
		builder.assert_eq("right_identity_debit", right_identity.debit, account_a.debit);
		builder.assert_eq("right_identity_credit", right_identity.credit, account_a.credit);

		let inverse_a = TAccountWires {
			debit: account_a.credit,
			credit: account_a.debit,
		};
		let a_plus_inv = add_accounts(builder, zero, &account_a, &inverse_a);
		builder.assert_eq("inverse_debit", a_plus_inv.debit, zero);
		builder.assert_eq("inverse_credit", a_plus_inv.credit, zero);

		let inv_plus_a = add_accounts(builder, zero, &inverse_a, &account_a);
		builder.assert_eq("inverse_debit_comm", inv_plus_a.debit, zero);
		builder.assert_eq("inverse_credit_comm", inv_plus_a.credit, zero);

		let comm_sum = sum_ab;
		let comm_rev_sum = add_accounts(builder, zero, &account_b, &account_a);
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
		let commitment_wire = commit_wires(builder, &flatten_accounts, "t_account_commitment");

		Ok(Self {
			account_a,
			account_b,
			account_c,
			commitment_wire,
			commitment_value: Cell::new(None),
		})
	}

	fn populate_witness(&self, instance: GroupInstance, witness: &mut WitnessFiller) -> Result<()> {
		let host_a = HostAccount::from_i64(instance.account_a_balance);
		let host_b = HostAccount::from_i64(instance.account_b_balance);
		let host_c = HostAccount::from_i64(instance.account_c_balance);

		witness[self.account_a.debit] = Word(host_a.debit);
		witness[self.account_a.credit] = Word(host_a.credit);
		witness[self.account_b.debit] = Word(host_b.debit);
		witness[self.account_b.credit] = Word(host_b.credit);
		witness[self.account_c.debit] = Word(host_c.debit);
		witness[self.account_c.credit] = Word(host_c.credit);

		let host_commit_values = [
			host_a.debit,
			host_a.credit,
			host_b.debit,
			host_b.credit,
			host_c.debit,
			host_c.credit,
		];
		let commitment = host_commitment(&host_commit_values);
		witness[self.commitment_wire] = Word(commitment);
		self.commitment_value.set(Some(commitment));

		Ok(())
	}

	fn on_prove_success(&self) -> Result<()> {
		println!("✓ T-account group proof generated and verified.");
		if let Some(digest) = self.commitment_value.get() {
			println!("Ledger commitment digest: {digest:#018X}");
		}
		Ok(())
	}
}

const ACCS: usize = 4;
const DIMS: usize = 2;
const TX_COLUMNS_PER_PI: usize = 1;
const TX_COUNT: usize = 3;

const USD: usize = 0;
const WDG: usize = 1;

const CASH: usize = 0;
const EQUITY: usize = 1;
const WH_A: usize = 2;
const WH_B: usize = 3;

struct LedgerStateSquashExample {
	shape: LedgerShape,
	wires: LedgerSquashWires,
	summary: Cell<Option<(u64, u64)>>,
}

impl LedgerStateSquashExample {
	fn build_transactions(shape: LedgerShape, instance: &LedgerInstance) -> Vec<LedgerPi> {
		let mut txs = Vec::with_capacity(TX_COUNT);

		let mut tx0 = LedgerPi::new(shape);
		tx0.post_debit(CASH, USD, 0, instance.invest_usd);
		tx0.post_credit(EQUITY, USD, 0, instance.invest_usd);
		txs.push(tx0);

		let mut tx1 = LedgerPi::new(shape);
		tx1.post_debit(WH_B, WDG, 0, instance.move_widgets);
		tx1.post_credit(WH_A, WDG, 0, instance.move_widgets);
		txs.push(tx1);

		let mut tx2 = LedgerPi::new(shape);
		tx2.post_debit(EQUITY, USD, 0, instance.distribution_usd);
		tx2.post_credit(CASH, USD, 0, instance.distribution_usd);
		txs.push(tx2);

		txs
	}
}

impl ExampleCircuit for LedgerStateSquashExample {
	type Params = LedgerParams;
	type Instance = LedgerInstance;

	fn build(_params: LedgerParams, builder: &mut CircuitBuilder) -> Result<Self> {
		let shape = LedgerShape::new(ACCS, DIMS, TX_COLUMNS_PER_PI);
		let wires = build_ledger_squash_circuit(builder, shape, TX_COUNT);
		Ok(Self {
			shape,
			wires,
			summary: Cell::new(None),
		})
	}

	fn populate_witness(
		&self,
		instance: LedgerInstance,
		witness: &mut WitnessFiller,
	) -> Result<()> {
		let transactions = Self::build_transactions(self.shape, &instance);
		let initial_sigma = LedgerSigma::zero(self.shape);
		let final_sigma = accumulate_transactions(&initial_sigma, &transactions);

		populate_squash_witness(witness, &self.wires, &initial_sigma, &transactions, &final_sigma);

		let initial_commit = host_commitment(&initial_sigma.flatten_twos_complement());
		let final_commit = host_commitment(&final_sigma.flatten_twos_complement());
		self.summary.set(Some((initial_commit, final_commit)));

		Ok(())
	}

	fn on_prove_success(&self) -> Result<()> {
		println!("✓ Ledger state squash proof generated and verified.");
		if let Some((initial_commit, final_commit)) = self.summary.get() {
			println!("Initial ledger commitment: {initial_commit:#018X}");
			println!("Final ledger commitment:   {final_commit:#018X}");
		}
		Ok(())
	}
}
fn main() -> Result<()> {
	let args = ShowcaseArgs::parse();
	if args.skip_group && args.skip_ledger {
		bail!("both demos disabled; enable at least one of --skip-group / --skip-ledger");
	}

	let log_inv_rate = args.log_inv_rate as usize;
	let compression = args.compression.clone();

	if !args.skip_group {
		println!("=== Proving T-account group axioms ===");
		let group_params = GroupParams::default();
		let group_instance = args.group.clone();
		prove_example::<TAccountGroupExample>(
			group_params,
			group_instance,
			log_inv_rate,
			compression.clone(),
		)?;
	}

	if !args.skip_ledger {
		println!("\n=== Proving ledger state squash ===");
		let ledger_params = LedgerParams::default();
		let ledger_instance = args.ledger.clone();
		prove_example::<LedgerStateSquashExample>(
			ledger_params,
			ledger_instance,
			log_inv_rate,
			args.compression,
		)?;
	}

	Ok(())
}
