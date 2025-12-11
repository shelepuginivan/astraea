use std::cmp::Ordering;
use std::iter;
use std::ops::{Add, AddAssign, Mul, MulAssign, Sub, SubAssign};

use super::digit::Digit;

/// Represents a big unsigned integer number.
#[derive(Debug)]
pub struct BigUint {
    /// Digits of BigUint, stored in little-endian order (least-significant first).
    digits: Vec<Digit>,
}

impl BigUint {
    pub fn zero() -> Self {
        Self {
            digits: vec![Digit::ZERO],
        }
    }

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

    fn split_at(&self, n: usize) -> (Self, Self) {
        let low_len = self.digits.len().min(n);
        let high_len = self.digits.len() - low_len;

        let low_digits = self.digits[..low_len].to_vec();
        let high_digits = if high_len > 0 {
            self.digits[low_len..].to_vec()
        } else {
            vec![Digit::ZERO]
        };

        (
            Self::from_little_endian(high_digits),
            Self::from_little_endian(low_digits),
        )
    }

    pub fn shift_left(&mut self, n: usize) {
        self.digits.splice(0..0, vec![Digit::ZERO; n]);
    }
}

impl Clone for BigUint {
    fn clone(&self) -> Self {
        Self {
            digits: self.digits.clone(),
        }
    }

    fn clone_from(&mut self, other: &Self) {
        self.digits.clone_from(&other.digits);
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

impl Add<&BigUint> for &BigUint {
    type Output = BigUint;

    fn add(self, rhs: &BigUint) -> BigUint {
        let lhs_len = self.digits.len();
        let rhs_len = rhs.digits.len();

        let result_digit_cap = lhs_len.max(rhs_len) + 1;
        if result_digit_cap == 1 {
            return BigUint::zero();
        }

        let mut digits: Vec<Digit> = Vec::with_capacity(result_digit_cap);
        let mut next_carry = Digit::ZERO;

        let lhs_digits = self.digits.iter();
        let rhs_digits = rhs.digits.iter();

        let (shorter, longer) = if lhs_len > rhs_len {
            (rhs_digits, lhs_digits)
        } else {
            (lhs_digits, rhs_digits)
        };

        let radix = longer.zip(shorter.chain(iter::repeat(&Digit::ZERO)));

        for (lhs_digit, rhs_digit) in radix {
            let (sum, carry) = lhs_digit.carrying_add(*rhs_digit);
            let (sum, self_carry) = sum.carrying_add(next_carry);
            let carry = carry.carrying_add(self_carry).0;

            digits.push(sum);

            next_carry = carry;
        }

        if next_carry != Digit::ZERO {
            digits.push(next_carry);
        }

        BigUint::from_little_endian(digits)
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

impl Mul<Digit> for BigUint {
    type Output = BigUint;

    fn mul(mut self, rhs: Digit) -> Self::Output {
        self *= rhs;
        self
    }
}

impl MulAssign<Digit> for BigUint {
    fn mul_assign(&mut self, rhs: Digit) {
        let mut next_carry = Digit::ZERO;

        for i in 0..self.digits.len() {
            let carry = self.digits[i].carrying_mul_mut(rhs);
            let self_carry = self.digits[i].carrying_add_mut(next_carry);
            next_carry = carry.carrying_add(self_carry).0;
        }

        if next_carry != Digit::ZERO {
            self.digits.push(next_carry);
        }
    }
}

impl Mul<&BigUint> for BigUint {
    type Output = BigUint;

    fn mul(mut self, rhs: &BigUint) -> Self::Output {
        self *= rhs;
        self
    }
}

impl MulAssign<&BigUint> for BigUint {
    fn mul_assign(&mut self, rhs: &BigUint) {
        if self.digits.len() == 1 {
            let res = rhs.clone() * self.digits[0];
            self.digits = res.digits;
            return;
        }

        if rhs.digits.len() == 1 {
            *self *= rhs.digits[0];
            return;
        }

        let m = self.digits.len().max(rhs.digits.len()) / 2;

        // lhs = ax + b
        // rhs = cx + d
        let (mut a, mut b) = self.split_at(m);
        let (c, d) = rhs.split_at(m);

        // a + b
        // c + d
        let mut s1 = &a + &b;
        let s2 = &c + &d;

        // ac
        // bd
        a *= &c;
        b *= &d;

        // (a + b)(c + d)
        // ac + bd
        s1 *= &s2;
        let mut s2 = &a + &b;

        // ac << n + bd
        a.shift_left(2 * m);
        a += &b;

        match s1.cmp(&s2) {
            Ordering::Less => {
                s2 -= &s1;
                s2.shift_left(m);
                a -= &s2;
            }
            Ordering::Equal => {}
            Ordering::Greater => {
                s1 -= &s2;
                s1.shift_left(m);
                a += &s1;
            }
        }

        self.digits = a.digits;
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
