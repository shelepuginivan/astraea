use std::cmp::Ordering;
use std::str::FromStr;

use crate::{Digit, ParseError};

/// Represents a natural number.
#[derive(Clone, Default)]
pub struct NaturalNumber {
    /// Digits of the natural number, stored in reverse order.
    digits: Vec<Digit>,
}

impl NaturalNumber {
    /// Creates a new instance of NaturalNumber. Digits are
    ///
    /// ```
    /// use libastraea::{Digit, NaturalNumber, digit};
    ///
    /// let digits = vec![digit!(9); 999];
    /// let n = NaturalNumber::new(digits);
    ///
    /// assert_eq!(n.to_string(), "9".repeat(999));
    /// ```
    pub fn new(mut digits: Vec<Digit>) -> Self {
        digits.reverse();
        NaturalNumber { digits }
    }

    /// Returns digits of the NaturalNumber, in reverse order.
    pub fn as_digits(&self) -> &Vec<Digit> {
        &self.digits
    }
}

impl FromStr for NaturalNumber {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let length = s.len();
        let mut digits: Vec<Digit> = vec![Digit::default(); length];

        for (index, char) in s.chars().enumerate() {
            let digit = Digit::from_char(char)?;
            digits[length - index - 1] = digit;
        }

        Ok(NaturalNumber { digits })
    }
}

impl ToString for NaturalNumber {
    fn to_string(&self) -> String {
        self.digits
            .iter()
            .rev()
            .map(|digit| digit.to_char())
            .collect()
    }
}

impl PartialEq for NaturalNumber {
    fn eq(&self, other: &Self) -> bool {
        self.digits == other.digits
    }
}

impl Eq for NaturalNumber {}

impl PartialOrd for NaturalNumber {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        let cmp_radix = self.digits.len().cmp(&other.digits.len());

        if cmp_radix != Ordering::Equal {
            return Some(cmp_radix);
        }

        let self_digits = self.digits.iter().rev();
        let other_digits = other.digits.iter().rev();

        for (lhs, rhs) in self_digits.zip(other_digits) {
            let cmp_digit = lhs.cmp(rhs);

            if cmp_digit != Ordering::Equal {
                return Some(cmp_digit);
            }
        }

        Some(Ordering::Equal)
    }
}

impl Ord for NaturalNumber {
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::digit;
    use std::cmp::Ordering;

    #[test]
    fn test_natural_number_cmp() {
        let lhs = NaturalNumber::from_str("1234").unwrap();
        let rhs = NaturalNumber::from_str("5478").unwrap();
        assert_eq!(lhs.cmp(&rhs), Ordering::Less);

        let lhs = NaturalNumber::new(vec![digit!(1); 1_000_000]);
        let rhs = NaturalNumber::new(vec![digit!(1); 1_000_000]);
        assert_eq!(lhs.cmp(&rhs), Ordering::Equal);

        let lhs_str = "2".to_owned() + "0".repeat(999_999).as_str();
        let rhs_str = "1".to_owned() + "9".repeat(999_999).as_str();

        let lhs = NaturalNumber::from_str(lhs_str.as_str()).unwrap();
        let rhs = NaturalNumber::from_str(rhs_str.as_str()).unwrap();
        assert_eq!(lhs.cmp(&rhs), Ordering::Greater);
    }

    #[test]
    fn test_natural_number_as_digits() {
        let n = NaturalNumber::from_str("123412341234").unwrap();
        let digits = n.as_digits();

        assert_eq!(digits.len(), 12);
        assert_eq!(digits[0], digit!(4));
    }

    #[test]
    fn test_natural_number_to_string() {
        let digits = vec![digit!(9); 999];
        let n = NaturalNumber::new(digits);
        assert_eq!(n.to_string(), "9".repeat(999));

        let n = NaturalNumber::from_str("3739847457938742").unwrap();
        assert_eq!(n.to_string(), "3739847457938742");
    }
}
