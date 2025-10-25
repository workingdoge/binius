use proptest::prelude::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct TAccount {
	debit: u128,
	credit: u128,
}

impl TAccount {
	fn new(debit: u128, credit: u128) -> Self {
		let common = debit.min(credit);
		Self {
			debit: debit - common,
			credit: credit - common,
		}
	}

	fn from_i64(balance: i64) -> Self {
		if balance >= 0 {
			Self::new(balance as u128, 0)
		} else {
			Self::new(0, balance.unsigned_abs() as u128)
		}
	}

	fn identity() -> Self {
		Self::new(0, 0)
	}

	fn balance(&self) -> i128 {
		self.debit as i128 - self.credit as i128
	}

	fn add(self, other: Self) -> Self {
		Self::new(self.debit + other.debit, self.credit + other.credit)
	}

	fn inverse(self) -> Self {
		Self::new(self.credit, self.debit)
	}
}

fn t_account_strategy() -> impl Strategy<Value = TAccount> {
	any::<i64>().prop_map(TAccount::from_i64)
}

proptest! {
	#[test]
	fn addition_is_associative(a in t_account_strategy(), b in t_account_strategy(), c in t_account_strategy()) {
		let left = a.add(b).add(c);
		let right = a.add(b.add(c));
		prop_assert_eq!(left, right);
	}

	#[test]
	fn addition_is_commutative(a in t_account_strategy(), b in t_account_strategy()) {
		prop_assert_eq!(a.add(b), b.add(a));
	}

	#[test]
	fn identity_is_neutral(a in t_account_strategy()) {
		let e = TAccount::identity();
		prop_assert_eq!(a.add(e), a);
		prop_assert_eq!(e.add(a), a);
	}

	#[test]
	fn inverse_cancels(a in t_account_strategy()) {
		let e = TAccount::identity();
		let inv = a.inverse();
		prop_assert_eq!(a.add(inv), e);
		prop_assert_eq!(inv.add(a), e);
	}

	#[test]
	fn addition_matches_integer_balance(a in t_account_strategy(), b in t_account_strategy()) {
		let sum = a.add(b);
		prop_assert_eq!(sum.balance(), a.balance() + b.balance());
	}

	#[test]
	fn inverse_negates_balance(a in t_account_strategy()) {
		let inv = a.inverse();
		prop_assert_eq!(inv.balance(), -a.balance());
	}
}
