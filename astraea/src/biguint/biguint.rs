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
