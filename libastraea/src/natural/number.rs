use std::cmp::Ordering;
use std::fmt::Display;
use std::iter;
use std::ops::{Add, Mul, Sub};
use std::str::FromStr;

use crate::core::{ParseError, ValueError};
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

    /// Returns zero-value NaturalNumber.
    pub fn zero() -> Self {
        Self {
            digits: vec![digit!(0)],
        }
    }

    /// Returns digits of the NaturalNumber, in reverse order.
    pub fn as_digits(self) -> Vec<Digit> {
        self.digits
    }

    /// Reports whether the number is zero.
    pub fn is_zero(&self) -> bool {
        if self.digits.len() > 1 {
            return false;
        }

        self.digits.len() == 0 || self.digits[0] == digit!(0)
    }

    /// Increments number by 1.
    pub fn inc(self) -> Self {
        let mut digits = self.as_digits();

        if digits.len() == 0 {
            return Self {
                digits: vec![digit!(1)],
            };
        }

        let lsd = digits[0];
        let (lsd, carry) = lsd + digit!(1);
        digits[0] = lsd;
        digits[1] = (digits[1] + carry).0;

        Self { digits }
    }

    /// Multiplies number by 10<sup>k</sup>.
    pub fn times_pow10(self, k: usize) -> Self {
        if self.is_zero() {
            return self;
        }

        let digits = [vec![digit!(0); k], self.as_digits()].concat();
        return Self { digits };
    }
}

impl Add for NaturalNumber {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        let lhs_len = self.digits.len();
        let rhs_len = rhs.digits.len();

        let result_digit_cap = lhs_len.max(rhs_len) + 1;
        if result_digit_cap == 1 {
            return NaturalNumber {
                digits: vec![digit!(0)],
            };
        }

        let mut digits: Vec<Digit> = Vec::with_capacity(result_digit_cap);
        let mut next_carry = digit!(0);

        let lhs_digits = self.digits.into_iter();
        let rhs_digits = rhs.digits.into_iter();

        let (shorter, longer) = if lhs_len > rhs_len {
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

impl Sub for NaturalNumber {
    type Output = Result<Self, ValueError>;

    fn sub(self, rhs: Self) -> Self::Output {
        if self.digits.len() < rhs.digits.len() {
            return Err(ValueError::new(
                "the right-hand side operand must not be greater than the left-hand side operand",
            ));
        }

        let result_digit_cap = self.digits.len();
        if result_digit_cap == 0 {
            return Ok(NaturalNumber {
                digits: vec![digit!(0)],
            });
        }

        let mut digits: Vec<Digit> = Vec::with_capacity(result_digit_cap);
        let mut next_carry = digit!(0);

        let lhs_digits = self.digits.into_iter();
        let rhs_digits = rhs.digits.into_iter();

        let radix = lhs_digits.zip(rhs_digits.chain(iter::repeat(digit!(0))));

        for (lhs_digit, rhs_digit) in radix {
            let (diff, carry) = lhs_digit - rhs_digit;
            let (diff, self_carry) = diff - next_carry;
            let (carry, _) = carry + self_carry;

            digits.push(diff);

            next_carry = carry;
        }

        if next_carry != digit!(0) {
            return Err(ValueError::new(
                "the right-hand side operand must not be greater than the left-hand side operand",
            ));
        }

        while digits.len() > 1 && *digits.last().unwrap() == digit!(0) {
            digits.pop();
        }

        Ok(Self { digits })
    }
}

impl Mul<Digit> for NaturalNumber {
    type Output = Self;

    fn mul(self, rhs: Digit) -> Self::Output {
        if rhs == digit!(0) {
            return NaturalNumber {
                digits: vec![digit!(0)],
            };
        }

        if rhs == digit!(1) {
            return self;
        }

        if self.digits.len() == 0 {
            return NaturalNumber {
                digits: vec![digit!(0)],
            };
        }

        let mut digits = Vec::with_capacity(self.digits.len() + 1);
        let mut next_carry = digit!(0);

        for digit in self.digits {
            let (prod, carry) = digit * rhs;
            let (prod, self_carry) = prod + next_carry;
            let (carry, _) = carry + self_carry;

            digits.push(prod);

            next_carry = carry;
        }

        if next_carry != digit!(0) {
            digits.push(next_carry);
        }

        Self { digits }
    }
}

impl Mul<Self> for NaturalNumber {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        if self.is_zero() || rhs.is_zero() {
            return Self::zero();
        }

        let mut sum = Self::zero();

        for (k, digit) in rhs.digits.into_iter().enumerate() {
            let prod = self.clone() * digit;
            sum = sum + prod.times_pow10(k);
        }

        sum
    }
}

impl FromStr for NaturalNumber {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let length = s.len();
        if length == 0 {
            return Err(ParseError::new(
                "cannot create natural number from empty string",
            ));
        }

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
    fn test_natural_number_sub() {
        let mut rng = rand::rng();

        for _ in 0..1000 {
            let rhs: u32 = rng.random_range(..2u32.pow(31));
            let lhs: u32 = rng.random_range(rhs..=u32::MAX);
            let expected = lhs - rhs;

            let lhs = NaturalNumber::from_str(&lhs.to_string()).unwrap();
            let rhs = NaturalNumber::from_str(&rhs.to_string()).unwrap();
            assert_eq!((lhs - rhs).unwrap().to_string(), expected.to_string());
        }

        let lhs_value = "1".to_owned() + &"0".repeat(999_999);
        let lhs = NaturalNumber::from_str(&lhs_value).unwrap();
        let rhs = NaturalNumber::from_str("1").unwrap();

        let expected = "9".repeat(999_999);
        let actual = (lhs - rhs).unwrap().to_string();

        assert_eq!(expected, actual);
    }

    #[test]
    fn test_natural_number_mul_digit() {
        let mut rng = rand::rng();

        for _ in 0..1000 {
            let lhs = rng.random_range(..2u32.pow(28));
            let rhs = rng.random_range(0..9);
            let expected = lhs * rhs;

            let lhs = NaturalNumber::from_str(&lhs.to_string()).unwrap();
            let rhs = digit!(rhs as u8);
            let actual = lhs * rhs;

            assert_eq!(expected.to_string(), actual.to_string());
        }
    }

    #[test]
    fn test_natural_number_mul() {
        let mut rng = rand::rng();

        for _ in 0..1000 {
            let lhs = rng.random_range(..2u32.pow(16));
            let rhs = rng.random_range(..2u32.pow(16));
            let expected = lhs * rhs;

            let lhs = NaturalNumber::from_str(&lhs.to_string()).unwrap();
            let rhs = NaturalNumber::from_str(&rhs.to_string()).unwrap();
            let actual = lhs * rhs;

            assert_eq!(expected.to_string(), actual.to_string());
        }
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
    fn test_natural_number_times_pow10() {
        let n = NaturalNumber::from_str("123").unwrap();
        let expected = "12300000000000000";
        let actual = n.times_pow10(14).to_string();

        assert_eq!(expected, actual);
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
