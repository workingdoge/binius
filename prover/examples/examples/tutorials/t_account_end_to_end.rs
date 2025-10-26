// Copyright 2025 Irreducible Inc.
//! T-account end-to-end walkthrough: build circuits, populate witnesses, verify constraints,
//! generate proofs, and check them – all in one file.

use anyhow::{Result, anyhow};
use binius_core::{verify::verify_constraints, word::Word};
use binius_examples::setup_sha256;
use binius_frontend::{
	CircuitBuilder, Wire,
	t_account::{
		LedgerPi, LedgerShape, LedgerSigma, build_ledger_squash_circuit, commit_wires,
		host_commitment, populate_squash_witness,
	},
};
use binius_verifier::{
	config::StdChallenger,
	transcript::{ProverTranscript, VerifierTranscript},
};

const LOG_INV_RATE: usize = 1;

fn main() -> Result<()> {
	let group_digest = run_group_demo()?;
	println!("✓ group axioms satisfied with commitment {group_digest:#018X}\n");

	let (initial_commit, final_commit) = run_ledger_demo()?;
	println!("✓ ledger state squash succeeded");
	println!("  initial commitment: {initial_commit:#018X}");
	println!("  final commitment:   {final_commit:#018X}");

	Ok(())
}

#[derive(Clone, Copy)]
struct TAccountWires {
	debit: Wire,
	credit: Wire,
}

#[derive(Clone, Copy)]
struct GroupWires {
	account_a: TAccountWires,
	account_b: TAccountWires,
	account_c: TAccountWires,
	commitment: Wire,
}

#[derive(Clone, Copy)]
struct HostAccount {
	debit: u64,
	credit: u64,
}

impl HostAccount {
	fn from_i64(balance: i64) -> Self {
		if balance >= 0 {
			Self {
				debit: balance as u64,
				credit: 0,
			}
		} else {
			Self {
				debit: 0,
				credit: balance.unsigned_abs() as u64,
			}
		}
	}

	fn balance(&self) -> i128 {
		self.debit as i128 - self.credit as i128
	}
}

#[derive(Clone, Copy)]
struct AccountInfo {
	category: &'static str,
	label: &'static str,
}

fn print_balance_table(
	account_infos: &[AccountInfo],
	dimension_names: &[&str],
	balances: &[Vec<i128>],
) {
	const ACCOUNT_COL_WIDTH: usize = 24;
	const VALUE_COL_WIDTH: usize = 16;
	const CATEGORY_ORDER: [&str; 5] = ["Assets", "Liabilities", "Equity", "Revenue", "Expenses"];

	fn print_category(
		category: &str,
		indices: &[usize],
		infos: &[AccountInfo],
		dimension_names: &[&str],
		balances: &[Vec<i128>],
		grand: &mut [i128],
	) {
		let indent = "  ";
		let dims = dimension_names.len();
		let border = || {
			let mut line = format!("{indent}+{}", "-".repeat(ACCOUNT_COL_WIDTH + 1));
			for _ in 0..dims {
				line.push_str(&format!("+{}", "-".repeat(VALUE_COL_WIDTH + 1)));
			}
			line.push('+');
			line
		};

		println!("{category}:");
		let border_line = border();
		println!("{border_line}");
		print!("{indent}| {:^width$} |", "Account", width = ACCOUNT_COL_WIDTH - 1);
		for &dim in dimension_names {
			print!(" {:^width$} |", dim, width = VALUE_COL_WIDTH - 1);
		}
		println!("\n{border_line}");

		let mut category_totals = vec![0i128; dims];
		for &idx in indices {
			print!("{indent}| {:<width$} |", infos[idx].label, width = ACCOUNT_COL_WIDTH - 1);
			for (dim_idx, _) in dimension_names.iter().enumerate() {
				let value = balances[idx][dim_idx];
				category_totals[dim_idx] += value;
				grand[dim_idx] += value;
				print!(" {:>+width$} |", value, width = VALUE_COL_WIDTH - 1);
			}
			println!();
		}
		println!("{border_line}");
		print!("{indent}| {:<width$} |", "Subtotal", width = ACCOUNT_COL_WIDTH - 1);
		for total in &category_totals {
			print!(" {:>+width$} |", total, width = VALUE_COL_WIDTH - 1);
		}
		println!("\n{border_line}\n");
	}

	let mut grand_totals = vec![0i128; dimension_names.len()];
	for &category in &CATEGORY_ORDER {
		let indices: Vec<usize> = account_infos
			.iter()
			.enumerate()
			.filter(|(_, info)| info.category == category)
			.map(|(idx, _)| idx)
			.collect();
		if indices.is_empty() {
			continue;
		}
		print_category(
			category,
			&indices,
			account_infos,
			dimension_names,
			balances,
			&mut grand_totals,
		);
	}
	print!("Overall totals:");
	for (dim, total) in dimension_names.iter().zip(grand_totals.iter()) {
		print!(" {dim} = {:+}", total);
	}
	println!("\n");
}

fn print_postings_table(
	title: &str,
	pi: &LedgerPi,
	account_infos: &[AccountInfo],
	dimension_names: &[&str],
) {
	let account_width = 16;
	let dim_width = 10;
	let amount_width = 12;
	println!("{title}");
	println!(
		"+{}+{}+{}+{}+",
		"-".repeat(account_width + 1),
		"-".repeat(dim_width + 1),
		"-".repeat(amount_width + 1),
		"-".repeat(amount_width + 1)
	);
	println!(
		"| {:^width$} | {:^dim_width$} | {:^amt_width$} | {:^amt_width$} |",
		"Account",
		"Commodity",
		"Debit",
		"Credit",
		width = account_width - 1,
		dim_width = dim_width - 1,
		amt_width = amount_width - 1
	);
	println!(
		"+{}+{}+{}+{}+",
		"-".repeat(account_width + 1),
		"-".repeat(dim_width + 1),
		"-".repeat(amount_width + 1),
		"-".repeat(amount_width + 1)
	);

	for (account_idx, info) in account_infos.iter().enumerate() {
		for (dim_idx, &commodity) in dimension_names.iter().enumerate() {
			let debit = pi.debits[account_idx][dim_idx][0];
			let credit = pi.credits[account_idx][dim_idx][0];
			if debit == 0 && credit == 0 {
				continue;
			}
			let debit_str = if debit == 0 {
				String::new()
			} else {
				debit.to_string()
			};
			let credit_str = if credit == 0 {
				String::new()
			} else {
				credit.to_string()
			};
			println!(
				"| {:<width$} | {:<dim_width$} | {:>amt_width$} | {:>amt_width$} |",
				info.label,
				commodity,
				debit_str,
				credit_str,
				width = account_width - 1,
				dim_width = dim_width - 1,
				amt_width = amount_width - 1
			);
		}
	}
	println!(
		"+{}+{}+{}+{}+",
		"-".repeat(account_width + 1),
		"-".repeat(dim_width + 1),
		"-".repeat(amount_width + 1),
		"-".repeat(amount_width + 1)
	);
}

fn assert_transaction_balanced(pi: &LedgerPi, label: &str) {
	let shape = pi.shape();
	for dim in 0..shape.dimensions {
		let mut sum: i128 = 0;
		for acc in 0..shape.accounts {
			sum += pi.debits[acc][dim][0] as i128;
			sum -= pi.credits[acc][dim][0] as i128;
		}
		assert_eq!(sum, 0, "{label}: imbalance detected in dimension {dim}");
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

fn build_group_circuit(builder: &mut CircuitBuilder) -> GroupWires {
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
	let right_identity = add_accounts(builder, zero, &identity, &account_a);
	builder.assert_eq("left_identity_debit", left_identity.debit, account_a.debit);
	builder.assert_eq("left_identity_credit", left_identity.credit, account_a.credit);
	builder.assert_eq("right_identity_debit", right_identity.debit, account_a.debit);
	builder.assert_eq("right_identity_credit", right_identity.credit, account_a.credit);

	let inverse_a = TAccountWires {
		debit: account_a.credit,
		credit: account_a.debit,
	};
	let a_plus_inv = add_accounts(builder, zero, &account_a, &inverse_a);
	let inv_plus_a = add_accounts(builder, zero, &inverse_a, &account_a);
	builder.assert_eq("inverse_debit", a_plus_inv.debit, zero);
	builder.assert_eq("inverse_credit", a_plus_inv.credit, zero);
	builder.assert_eq("inverse_comm_debit", inv_plus_a.debit, zero);
	builder.assert_eq("inverse_comm_credit", inv_plus_a.credit, zero);

	let comm_sum = sum_ab;
	let comm_rev_sum = add_accounts(builder, zero, &account_b, &account_a);
	builder.assert_eq("comm_debit", comm_sum.debit, comm_rev_sum.debit);
	builder.assert_eq("comm_credit", comm_sum.credit, comm_rev_sum.credit);

	let flatten = [
		account_a.debit,
		account_a.credit,
		account_b.debit,
		account_b.credit,
		account_c.debit,
		account_c.credit,
	];
	let commitment = commit_wires(builder, &flatten, "t_account_commitment");

	GroupWires {
		account_a,
		account_b,
		account_c,
		commitment,
	}
}

fn run_group_demo() -> Result<u64> {
	let mut builder = CircuitBuilder::new();
	let wires = build_group_circuit(&mut builder);
	let circuit = builder.build();
	let cs = circuit.constraint_system().clone();

	let mut witness = circuit.new_witness_filler();

	let host_a = HostAccount::from_i64(1_000);
	let host_b = HostAccount::from_i64(-370);
	let host_c = HostAccount::from_i64(300);

	witness[wires.account_a.debit] = Word(host_a.debit);
	witness[wires.account_a.credit] = Word(host_a.credit);
	witness[wires.account_b.debit] = Word(host_b.debit);
	witness[wires.account_b.credit] = Word(host_b.credit);
	witness[wires.account_c.debit] = Word(host_c.debit);
	witness[wires.account_c.credit] = Word(host_c.credit);

	let host_commit = host_commitment(&[
		host_a.debit,
		host_a.credit,
		host_b.debit,
		host_b.credit,
		host_c.debit,
		host_c.credit,
	]);
	witness[wires.commitment] = Word(host_commit);

	circuit.populate_wire_witness(&mut witness)?;
	let witness_vec = witness.into_value_vec();
	verify_constraints(&cs, &witness_vec)
		.map_err(|err| anyhow!("group constraints violated: {err}"))?;
	println!("✓ T-account group constraints satisfied");
	println!(
		"  balances: A = {:+}, B = {:+}, C = {:+}",
		host_a.balance(),
		host_b.balance(),
		host_c.balance()
	);

	let (verifier, prover) = setup_sha256(cs, LOG_INV_RATE, None)?;
	let challenger = StdChallenger::default();
	let mut prover_transcript = ProverTranscript::new(challenger.clone());
	prover.prove(witness_vec.clone(), &mut prover_transcript)?;
	let proof = prover_transcript.finalize();

	let mut verifier_transcript = VerifierTranscript::new(challenger, proof);
	verifier.verify(witness_vec.public(), &mut verifier_transcript)?;
	verifier_transcript.finalize()?;
	println!("✓ T-account group proof verified");

	Ok(host_commit)
}

fn run_ledger_demo() -> Result<(u64, u64)> {
	const ACCS: usize = 10;
	const DIMS: usize = 3;
	const TXS: usize = 6;

	const USD: usize = 0;
	const RARE: usize = 1;
	const WIDGET: usize = 2;

	const CASH: usize = 0;
	const EQUIPMENT: usize = 1;
	const INVENTORY_RAW: usize = 2;
	const INVENTORY_FINISHED: usize = 3;
	const REVENUE: usize = 4;
	const COGS: usize = 5;
	const EQUITY: usize = 6;
	const VENDOR: usize = 7;
	const PRODUCTION: usize = 8;
	const CUSTOMER: usize = 9;

	let builder = CircuitBuilder::new();
	let shape = LedgerShape::new(ACCS, DIMS, 1);
	let wires = build_ledger_squash_circuit(&builder, shape, TXS);
	let circuit = builder.build();
	let cs = circuit.constraint_system().clone();

	let mut txs = Vec::new();

	let mut tx0 = LedgerPi::new(shape);
	tx0.post_debit(CASH, USD, 0, 1_000);
	tx0.post_credit(EQUITY, USD, 0, 1_000);
	txs.push(tx0);

	let mut tx1 = LedgerPi::new(shape);
	tx1.post_debit(EQUIPMENT, USD, 0, 500);
	tx1.post_credit(CASH, USD, 0, 500);
	txs.push(tx1);

	let mut tx2 = LedgerPi::new(shape);
	tx2.post_debit(INVENTORY_RAW, USD, 0, 200);
	tx2.post_debit(INVENTORY_RAW, RARE, 0, 5);
	tx2.post_credit(CASH, USD, 0, 200);
	tx2.post_credit(VENDOR, RARE, 0, 5);
	txs.push(tx2);

	let mut tx3 = LedgerPi::new(shape);
	tx3.post_debit(INVENTORY_FINISHED, USD, 0, 200);
	tx3.post_debit(INVENTORY_FINISHED, WIDGET, 0, 1);
	tx3.post_credit(INVENTORY_RAW, USD, 0, 200);
	tx3.post_credit(INVENTORY_RAW, RARE, 0, 2);
	tx3.post_debit(PRODUCTION, RARE, 0, 2);
	tx3.post_credit(PRODUCTION, WIDGET, 0, 1);
	txs.push(tx3);

	let mut tx4 = LedgerPi::new(shape);
	tx4.post_debit(CASH, USD, 0, 350);
	tx4.post_credit(REVENUE, USD, 0, 350);
	txs.push(tx4);

	let mut tx5 = LedgerPi::new(shape);
	tx5.post_debit(COGS, USD, 0, 200);
	tx5.post_debit(CUSTOMER, WIDGET, 0, 1);
	tx5.post_credit(INVENTORY_FINISHED, USD, 0, 200);
	tx5.post_credit(INVENTORY_FINISHED, WIDGET, 0, 1);
	txs.push(tx5);

	let initial_sigma = LedgerSigma::zero(shape);
	const ACCOUNT_INFOS: [AccountInfo; ACCS] = [
		AccountInfo {
			category: "Assets",
			label: "Cash",
		},
		AccountInfo {
			category: "Assets",
			label: "Equipment",
		},
		AccountInfo {
			category: "Assets",
			label: "Inventory (Raw)",
		},
		AccountInfo {
			category: "Assets",
			label: "Inventory (Finished)",
		},
		AccountInfo {
			category: "Revenue",
			label: "Revenue",
		},
		AccountInfo {
			category: "Expenses",
			label: "COGS",
		},
		AccountInfo {
			category: "Equity",
			label: "Equity",
		},
		AccountInfo {
			category: "Liabilities",
			label: "Vendor",
		},
		AccountInfo {
			category: "Assets",
			label: "Production",
		},
		AccountInfo {
			category: "Liabilities",
			label: "Customer",
		},
	];
	const DIMENSION_NAMES: [&str; DIMS] = ["USD", "Rare Earth (kg)", "Widgets"];
	println!("Initial balances:");
	print_balance_table(&ACCOUNT_INFOS, &DIMENSION_NAMES, &initial_sigma.balances);
	println!();

	let tx_descriptions = [
		"Owner invests 1,000 USD (debit Cash, credit Equity)",
		"Buy CNC machine for 500 USD (debit Equipment, credit Cash)",
		"Purchase 5 kg rare earth inputs for 200 USD (debit Inventory Raw, credit Cash & Vendor)",
		"Manufacture one widget (debit Inventory Finished, credit Inventory Raw & Production)",
		"Sell finished widget for 350 USD cash (debit Cash, credit Revenue)",
		"Recognize cost of goods sold 200 USD (debit COGS & Customer, credit Inventory Finished)",
	];
	let mut running_sigma = initial_sigma.clone();
	for (idx, tx) in txs.iter().enumerate() {
		let title = format!("Transaction {}: {}", idx + 1, tx_descriptions[idx]);
		assert_transaction_balanced(tx, &title);
		print_postings_table(&title, tx, &ACCOUNT_INFOS, &DIMENSION_NAMES);
		running_sigma.add_assign(&tx.to_sigma());
		println!("  Balances after transaction {}:", idx + 1);
		print_balance_table(&ACCOUNT_INFOS, &DIMENSION_NAMES, &running_sigma.balances);
		println!();
	}
	let final_sigma = running_sigma.clone();

	let mut witness = circuit.new_witness_filler();
	populate_squash_witness(&mut witness, &wires, &initial_sigma, &txs, &final_sigma);

	circuit.populate_wire_witness(&mut witness)?;
	let witness_vec = witness.into_value_vec();
	verify_constraints(&cs, &witness_vec)
		.map_err(|err| anyhow!("ledger constraints violated: {err}"))?;
	println!("✓ ledger squash constraints satisfied");
	print_balance_table(&ACCOUNT_INFOS, &DIMENSION_NAMES, &final_sigma.balances);
	println!();

	let (verifier, prover) = setup_sha256(cs, LOG_INV_RATE, None)?;
	let challenger = StdChallenger::default();
	let mut prover_transcript = ProverTranscript::new(challenger.clone());
	prover.prove(witness_vec.clone(), &mut prover_transcript)?;
	let proof = prover_transcript.finalize();

	let mut verifier_transcript = VerifierTranscript::new(challenger, proof);
	verifier.verify(witness_vec.public(), &mut verifier_transcript)?;
	verifier_transcript.finalize()?;
	println!("✓ ledger squash proof verified");

	let initial_commit = host_commitment(&initial_sigma.flatten_twos_complement());
	let final_commit = host_commitment(&final_sigma.flatten_twos_complement());

	Ok((initial_commit, final_commit))
}
