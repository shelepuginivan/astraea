use std::cmp::Ordering;

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
