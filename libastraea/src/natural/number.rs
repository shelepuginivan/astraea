use std::cmp::Ordering;
use std::fmt::Display;
use std::iter;
use std::ops::Add;
use std::str::FromStr;

use crate::core::ParseError;
use crate::digit;
use crate::math::Digit;

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
    /// use libastraea::digit;
    /// use libastraea::math::Digit;
    /// use libastraea::natural::NaturalNumber;
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

    /// Reports whether the number is zero.
    pub fn is_zero(&self) -> bool {
        if self.digits.len() > 1 {
            return false;
        }

        self.digits.len() == 0 || self.digits[0] == digit!(0)
    }
}

impl Add for NaturalNumber {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        let result_digit_cap = self.digits.len().max(rhs.digits.len()) + 1;
        if result_digit_cap == 1 {
            return NaturalNumber {
                digits: vec![digit!(0)],
            };
        }

        let mut digits: Vec<Digit> = Vec::with_capacity(result_digit_cap);
        let mut next_carry = digit!(0);

        let lhs_digits = self.digits.into_iter();
        let rhs_digits = rhs.digits.into_iter();

        let (shorter, longer) = if lhs_digits.len() > rhs_digits.len() {
            (rhs_digits, lhs_digits)
        } else {
            (lhs_digits, rhs_digits)
        };

        let radix = longer.zip(shorter.chain(iter::repeat(digit!(0))));

        for (lhs_digit, rhs_digit) in radix {
            let (sum, carry) = lhs_digit + rhs_digit;
            let (sum, self_carry) = sum + next_carry;
            let (carry, _) = carry + self_carry;

            digits.push(sum);

            next_carry = carry;
        }

        if next_carry != digit!(0) {
            digits.push(next_carry);
        }

        Self { digits }
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

impl Display for NaturalNumber {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s: String = self
            .digits
            .iter()
            .rev()
            .map(|digit| digit.to_char())
            .collect();

        write!(f, "{}", s)
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
    use rand::Rng;

    use super::*;
    use crate::digit;
    use std::cmp::Ordering;

    #[test]
    fn test_natural_number_cmp() {
        let lhs = NaturalNumber::from_str("1234").unwrap();
        let rhs = NaturalNumber::from_str("5678").unwrap();
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
    fn test_natural_number_add() {
        let mut rng = rand::rng();

        for _ in 0..1000 {
            let lhs: u32 = rng.random_range(..2u32.pow(31));
            let rhs: u32 = rng.random_range(..2u32.pow(31));
            let expected = lhs + rhs;

            let lhs = NaturalNumber::from_str(&lhs.to_string()).unwrap();
            let rhs = NaturalNumber::from_str(&rhs.to_string()).unwrap();
            assert_eq!((lhs + rhs).to_string(), expected.to_string());
        }

        let lhs = NaturalNumber::from_str(&"9".repeat(999_999)).unwrap();
        let rhs = NaturalNumber::from_str("1").unwrap();

        let expected = "1".to_owned() + &"0".repeat(999_999);
        let actual = (lhs + rhs).to_string();

        assert_eq!(expected, actual);
    }

    #[test]
    fn test_natural_number_as_digits() {
        let n = NaturalNumber::from_str("123412341234").unwrap();
        let digits = n.as_digits();

        assert_eq!(digits.len(), 12);
        assert_eq!(digits[0], digit!(4));
    }

    #[test]
    fn test_natural_number_is_zero() {
        assert!(NaturalNumber::new(vec![]).is_zero());
        assert!(NaturalNumber::new(vec![digit!(0)]).is_zero());
        assert!(!NaturalNumber::new(vec![digit!(1)]).is_zero());
        assert!(!NaturalNumber::new(vec![digit!(0); 2]).is_zero());
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
