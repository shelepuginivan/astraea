use std::cmp::Ordering;
use std::ops::{Add, AddAssign, Sub, SubAssign};

use super::digit::Digit;

/// Represents a big unsigned integer number.
pub struct BigUint {
    /// Digits of BigUint, stored in little-endian order (least-significant first).
    digits: Vec<Digit>,
}

impl BigUint {
    pub fn from_big_endian(mut digits: Vec<Digit>) -> Self {
        digits.reverse();
        Self::from_little_endian(digits)
    }

    pub fn from_little_endian(mut digits: Vec<Digit>) -> Self {
        while digits.last().is_some_and(|d| *d == Digit::ZERO) {
            digits.pop();
        }

        if digits.is_empty() {
            digits.push(Digit::ZERO);
        }

        Self { digits }
    }
}

impl Eq for BigUint {}

impl PartialEq for BigUint {
    fn eq(&self, other: &Self) -> bool {
        self.digits == other.digits
    }
}

impl Ord for BigUint {
    fn cmp(&self, other: &Self) -> Ordering {
        match self.digits.len().cmp(&other.digits.len()) {
            Ordering::Equal => self.digits.iter().rev().cmp(other.digits.iter().rev()),
            other => return other,
        }
    }
}

impl PartialOrd for BigUint {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Add<&BigUint> for BigUint {
    type Output = BigUint;

    fn add(mut self, other: &BigUint) -> BigUint {
        self += other;
        self
    }
}

impl AddAssign<&BigUint> for BigUint {
    fn add_assign(&mut self, other: &BigUint) {
        let lhs_len = self.digits.len();
        let rhs_len = other.digits.len();

        if lhs_len < rhs_len {
            self.digits.resize(rhs_len, Digit::ZERO);
        }

        let mut next_carry = Digit::ZERO;

        for (index, rhs_digit) in other.digits.iter().enumerate() {
            let carry = self.digits[index].carrying_add_mut(*rhs_digit);
            let self_carry = self.digits[index].carrying_add_mut(next_carry);
            next_carry = carry.carrying_add(self_carry).0;
        }

        if next_carry == Digit::ZERO {
            return;
        }

        if lhs_len <= rhs_len {
            self.digits.push(next_carry);
            return;
        }

        for i in rhs_len..lhs_len {
            next_carry = self.digits[i].carrying_add_mut(next_carry);

            if next_carry == Digit::ZERO {
                break;
            }
        }

        if next_carry != Digit::ZERO {
            self.digits.push(next_carry);
        }
    }
}

impl Sub<&BigUint> for BigUint {
    type Output = BigUint;

    fn sub(mut self, rhs: &BigUint) -> Self::Output {
        self -= rhs;
        self
    }
}

impl SubAssign<&BigUint> for BigUint {
    fn sub_assign(&mut self, rhs: &BigUint) {
        let lhs_len = self.digits.len();
        let rhs_len = rhs.digits.len();

        if lhs_len < rhs_len {
            panic!("rhs must be less than or equal to lhs");
        }

        let mut next_borrow = Digit::ZERO;

        for (index, rhs_digit) in rhs.digits.iter().enumerate() {
            let borrow = self.digits[index].carrying_sub_mut(*rhs_digit);
            let self_borrow = self.digits[index].carrying_sub_mut(next_borrow);
            next_borrow = borrow.carrying_add(self_borrow).0;
        }

        for index in rhs_len..lhs_len {
            next_borrow = self.digits[index].carrying_sub_mut(next_borrow);

            if next_borrow == Digit::ZERO {
                return;
            }
        }

        if next_borrow != Digit::ZERO {
            panic!("rhs must be less than or equal to lhs");
        }
    }
}

#[cfg(test)]
mod tests {
    use rand::Rng;

    use super::*;

    const RANDOM_TEST_COUNT: usize = 1000;

    #[test]
    fn test_biguint_cmp() {
        let mut rng = rand::rng();

        for _ in 0..RANDOM_TEST_COUNT {
            let lhs_msd: u32 = rng.random_range((0)..(2 << 16));
            let rhs_msd: u32 = rng.random_range(lhs_msd..u32::MAX);

            let lhs = BigUint::from_little_endian(vec![Digit(lhs_msd); 128]);
            let rhs = BigUint::from_little_endian(vec![Digit(rhs_msd); 128]);

            assert!(lhs < rhs);
            assert!(rhs > lhs);

            let lhs = BigUint::from_little_endian(vec![Digit(lhs_msd); 128]);
            let rhs = BigUint::from_little_endian(vec![Digit(rhs_msd); 127]);

            assert!(lhs > rhs);
            assert!(rhs < lhs);
        }
    }
}
