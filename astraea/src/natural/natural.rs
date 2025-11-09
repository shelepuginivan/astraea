use std::cmp::Ordering;
use std::fmt::Display;
use std::iter;
use std::ops::{Add, Div, Mul, Rem, Sub};
use std::str::FromStr;

use crate::algebra::*;
use crate::error::{ParseError, ValueError};
use crate::formatting::Pretty;
use crate::natural::Digit;

/// Represents a natural number.
#[derive(Clone, Debug)]
pub struct Natural {
    /// Digits of the natural number, stored in reverse order.
    digits: Vec<Digit>,
}

impl MathObject for Natural {}

impl AddClosed for Natural {}
impl AddAssociative<Self> for Natural {}

impl AddWithIdentity<Self> for Natural {
    fn zero() -> Self {
        Self {
            digits: vec![Digit::ZERO],
        }
    }

    fn is_zero(&self) -> bool {
        self.digits.len() == 1 && self.digits[0] == Digit::ZERO
    }
}

impl AddCommutative<Self> for Natural {}

impl MulClosed for Natural {}

impl MulAssociative<Self> for Natural {}

impl MulWithIdentity<Self> for Natural {
    fn one() -> Self {
        Self {
            digits: vec![Digit::ONE],
        }
    }

    fn is_one(&self) -> bool {
        self.digits.len() == 1 && self.digits[0] == Digit::ONE
    }
}

impl MulCommutative<Self> for Natural {}

impl Distributive for Natural {}

impl AddMagma for Natural {}
impl AddSemigroup for Natural {}
impl AddUnitalMagma for Natural {}
impl AddMonoid for Natural {}

impl MulMagma for Natural {}
impl MulSemigroup for Natural {}
impl MulUnitalMagma for Natural {}
impl MulMonoid for Natural {}

impl Semiring for Natural {}

impl IntegerDivision for Natural {
    fn div_rem(self, rhs: Self) -> Result<(Self, Self), ValueError> {

        if rhs.is_zero() {
            return Err(ValueError::new("division by 0 is not allowed"));
        }

        match self.cmp(&rhs) {
            Ordering::Less => return Ok((Self::zero(), self)),
            Ordering::Equal => return Ok((Self::one(), Self::zero())),
            Ordering::Greater => {}
        }

        if rhs.digits.len() == 1 {
            return self.div_rem_by_digit(rhs.digits[0]);
        }

        let mut quotient = Self::zero();
        let mut remainder = Self::zero();

        for digit in self.digits.into_iter().rev() {
            remainder = remainder.append_lsd(digit);
            let mut q_digit = 0;

            while remainder >= rhs {
                remainder = (remainder - rhs.clone())?;
                q_digit += 1;
            }

            quotient = quotient.append_lsd(Digit(q_digit));
        }

        Ok((quotient, remainder))
    }
}

impl Natural {
    /// Natural number from digits in big-endian order (most significant digits first).
    pub fn from_big_endian(mut digits: Vec<Digit>) -> Self {
        digits.reverse();
        Self::from_little_endian(digits)
    }

    /// Natural number from digits in little-endian order (least significant digits first).
    pub fn from_little_endian(mut digits: Vec<Digit>) -> Self {
        while let Some(&Digit::ZERO) = digits.last() {
            digits.pop();
        }

        if digits.is_empty() {
            digits.push(Digit::ZERO);
        }

        Natural { digits }
    }

    /// Appends digit to the number as least significant digit.
    pub fn append_lsd(self, lsd: Digit) -> Self {
        if self.is_zero() {
            return Self::from(lsd);
        }

        let mut digits = self.digits;
        digits.insert(0, lsd);
        Self { digits }
    }

    /// Returns digits of the number, in reverse order.
    pub fn as_digits(self) -> Vec<Digit> {
        self.digits
    }

    /// Increments number by 1.
    pub fn inc(self) -> Self {
        if self.is_zero() {
            return Self::one();
        }

        let mut digits = self.as_digits();
        let mut next_carry = Digit::ONE;

        for idx in 0..digits.len() {
            let (digit, carry) = digits[idx].carrying_add(next_carry);

            digits[idx] = digit;
            next_carry = carry;

            if next_carry == Digit::ZERO {
                break;
            }
        }

        if next_carry != Digit::ZERO {
            digits.push(next_carry);
        }

        Self::from_little_endian(digits)
    }

    /// Multiplies number by 10<sup>k</sup>.
    pub fn times_pow10(self, k: usize) -> Self {
        if self.is_zero() {
            return self;
        }

        self * Natural::from(10_u64.pow(k as u32))
    }

    fn shift_left(self, k: usize) -> Self {
        Self::from_little_endian([vec![Digit::ZERO; k], self.digits].concat())
    }

    /// Calculates GCD (greatest common divisor) of two natural numbers.
    pub fn gcd(self, other: Self) -> Self {
        if other.is_zero() {
            return self;
        } else if self.is_zero() {
            return other;
        }

        let (low, high) = match self.cmp(&other) {
            Ordering::Less => (self, other),
            Ordering::Equal => return self,
            Ordering::Greater => (other, self),
        };

        let r = (high % low.clone()).unwrap();

        if r.is_zero() {
            return low;
        }

        low.gcd(r)
    }

    /// Calculates LCM (least common multiple) of two natural numbers.
    pub fn lcm(self, other: Self) -> Self {
        if self.is_zero() || other.is_zero() {
            return Self::zero();
        }

        let prod = self.clone() * other.clone();
        let gcd = self.gcd(other);

        match prod / gcd {
            Ok(v) => v,
            Err(_) => Self::zero(),
        }
    }

    pub fn to_decimal_string(&self) -> String {
        let mut result = String::new();
        let mut current = self.clone();

        while !current.is_zero() {
            let (quotient, remainder) = current.div_rem(Natural::from(Digit(10))).unwrap();
            result.push(('0' as u8 + remainder.digits[0].0 as u8) as char);
            current = quotient;
        }

        if result.is_empty() {
            "0".to_string()
        } else {
            result.chars().rev().collect()
        }
    }

    fn div_rem_by_digit(self, rhs_digit: Digit) -> Result<(Self, Self), ValueError> {
        if rhs_digit == Digit::ZERO {
            return Err(ValueError::new("division by 0 is not allowed"));
        }

        let mut quotient_digits = Vec::with_capacity(self.digits.len());
        let mut remainder = 0u64;

        for digit in self.digits.into_iter().rev() {
            let current = (remainder << 32) | digit.0 as u64;
            let q = current / rhs_digit.0 as u64;
            remainder = current % rhs_digit.0 as u64;
            quotient_digits.push(q as u32);
        }

        Ok((
            Self::from_little_endian(quotient_digits.into_iter().rev().map(Digit).collect()),
            Self::from(remainder as u32),
        ))
    }
}

impl Add for Natural {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        let lhs_len = self.digits.len();
        let rhs_len = rhs.digits.len();

        let result_digit_cap = lhs_len.max(rhs_len) + 1;
        if result_digit_cap == 1 {
            return Natural::zero();
        }

        let mut digits: Vec<Digit> = Vec::with_capacity(result_digit_cap);
        let mut next_carry = Digit::ZERO;

        let lhs_digits = self.digits.into_iter();
        let rhs_digits = rhs.digits.into_iter();

        let (shorter, longer) = if lhs_len > rhs_len {
            (rhs_digits, lhs_digits)
        } else {
            (lhs_digits, rhs_digits)
        };

        let radix = longer.zip(shorter.chain(iter::repeat(Digit::ZERO)));

        for (lhs_digit, rhs_digit) in radix {
            let (sum, carry) = lhs_digit.carrying_add(rhs_digit);
            let (sum, self_carry) = sum.carrying_add(next_carry);
            let carry = carry.carrying_add(self_carry).0;

            digits.push(sum);

            next_carry = carry;
        }

        if next_carry != Digit::ZERO {
            digits.push(next_carry);
        }

        Self::from_little_endian(digits)
    }
}

impl Sub for Natural {
    type Output = Result<Self, ValueError>;

    fn sub(self, rhs: Self) -> Self::Output {
        if self.digits.len() < rhs.digits.len() {
            return Err(ValueError::new(
                "the right-hand side operand must not be greater than the left-hand side operand",
            ));
        }

        let result_digit_cap = self.digits.len();
        if result_digit_cap == 0 {
            return Ok(Self::zero());
        }

        let mut digits: Vec<Digit> = Vec::with_capacity(result_digit_cap);
        let mut next_carry = Digit::ZERO;

        let lhs_digits = self.digits.into_iter();
        let rhs_digits = rhs.digits.into_iter();

        let radix = lhs_digits.zip(rhs_digits.chain(iter::repeat(Digit::ZERO)));

        for (lhs_digit, rhs_digit) in radix {
            let (diff, carry) = lhs_digit.carrying_sub(rhs_digit);
            let (diff, self_carry) = diff.carrying_sub(next_carry);
            let carry = carry.carrying_add(self_carry).0;

            digits.push(diff);

            next_carry = carry;
        }

        if next_carry != Digit::ZERO {
            return Err(ValueError::new(
                "the right-hand side operand must not be greater than the left-hand side operand",
            ));
        }

        Ok(Self::from_little_endian(digits))
    }
}

impl Mul<Digit> for Natural {
    type Output = Self;

    fn mul(self, rhs: Digit) -> Self::Output {
        if self.is_zero() || rhs == Digit::ZERO {
            return Self::zero();
        }

        if rhs == Digit::ONE {
            return self;
        }

        let mut digits = Vec::with_capacity(self.digits.len() + 1);
        let mut carry = 0u64;

        for digit in self.digits {
            let product = digit.0 as u64 * rhs.0 as u64 + carry;
            let (low, high) = Digit::low_high(product);
            digits.push(low);
            carry = high.0 as u64;
        }

        if carry > 0 {
            digits.push(Digit(carry as u32));
        }

        Self::from_little_endian(digits)
    }
}

impl Mul<Self> for Natural {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        if self.is_zero() || rhs.is_zero() {
            return Self::zero();
        }

        let mut sum = Self::zero();

        for (k, digit) in rhs.digits.into_iter().enumerate() {
            let prod = self.clone() * digit;
            sum = sum + prod.shift_left(k);
        }

        sum
    }
}

impl Div for Natural {
    type Output = Result<Self, ValueError>;

    fn div(self, rhs: Self) -> Self::Output {
        self.div_rem(rhs).and_then(|res| Ok(res.0))
    }
}

impl Rem for Natural {
    type Output = Result<Self, ValueError>;

    fn rem(self, rhs: Self) -> Self::Output {
        self.div_rem(rhs).and_then(|res| Ok(res.1))
    }
}

impl Display for Natural {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.to_decimal_string())
    }
}

impl Pretty for Natural {
    fn prettify(&self) -> String {
        self.to_string()
    }
}

impl PartialEq for Natural {
    fn eq(&self, other: &Self) -> bool {
        self.digits == other.digits
    }
}

impl Eq for Natural {}

impl PartialOrd for Natural {
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

impl Ord for Natural {
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap()
    }
}

impl FromStr for Natural {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut result = Self::zero();

        for char in s.chars() {
            let decimal_digit = char
                .to_digit(10)
                .ok_or_else(|| ParseError::new("invalid decimal digit"))?;

            result = result * Digit(10) + Natural::from(decimal_digit);
        }

        Ok(result)
    }
}

impl From<Digit> for Natural {
    fn from(value: Digit) -> Self {
        Self {
            digits: vec![value],
        }
    }
}

impl From<u8> for Natural {
    fn from(value: u8) -> Self {
        Self {
            digits: vec![Digit(value as u32)],
        }
    }
}

impl From<u16> for Natural {
    fn from(value: u16) -> Self {
        Self {
            digits: vec![Digit(value as u32)],
        }
    }
}

impl From<u32> for Natural {
    fn from(value: u32) -> Self {
        Self {
            digits: vec![Digit(value)],
        }
    }
}

impl From<u64> for Natural {
    fn from(value: u64) -> Self {
        let (low, high) = Digit::low_high(value);

        Self::from_little_endian(vec![low, high])
    }
}

impl From<usize> for Natural {
    fn from(value: usize) -> Self {
        (value as u64).into()
    }
}

impl TryInto<usize> for Natural {
    type Error = ValueError;

    fn try_into(self) -> Result<usize, Self::Error> {
        let v: u64 = self.try_into()?;
        Ok(v as usize)
    }
}

impl TryInto<u64> for Natural {
    type Error = ValueError;

    fn try_into(self) -> Result<u64, Self::Error> {
        if self.digits.len() == 1 {
            return Ok(self.digits[0].0 as u64);
        }

        if self.digits.len() > 2 {
            return Err(ValueError::new("value is too large"));
        }

        let lo = self.digits[0].0 as u64;
        let hi = self.digits[1].0 as u64;

        Ok(lo + hi << 32)
    }
}

impl TryFrom<i32> for Natural {
    type Error = ValueError;

    fn try_from(value: i32) -> Result<Self, Self::Error> {
        if value < 0 {
            return Err(ValueError::new("natural number must not be negative"));
        }

        Ok((value as u32).into())
    }
}

impl TryFrom<i64> for Natural {
    type Error = ValueError;

    fn try_from(value: i64) -> Result<Self, Self::Error> {
        if value < 0 {
            return Err(ValueError::new("natural number must not be negative"));
        }

        Ok((value as u32).into())
    }
}

#[cfg(test)]
mod tests {
    use rand::Rng;

    use super::*;

    const RANDOM_TEST_COUNT: usize = 1000;

    #[test]
    fn test_natural_add() {
        let mut rng = rand::rng();

        for _ in 0..RANDOM_TEST_COUNT {
            let lhs: u32 = rng.random();
            let rhs: u32 = rng.random();
            let expected = lhs as u64 + rhs as u64;

            let lhs: Natural = lhs.into();
            let rhs: Natural = rhs.into();

            let expected: Natural = expected.into();
            let actual = lhs + rhs;

            assert_eq!(actual.to_string(), expected.to_string());
        }
    }

    #[test]
    fn test_natural_div_rem() {
        let mut rng = rand::rng();

        for _ in 0..RANDOM_TEST_COUNT {
            let lhs: u64 = rng.random();
            let rhs: u64 = rng.random();

            let expected_div = lhs / rhs;
            let expected_rem = lhs % rhs;

            let lhs: Natural = lhs.into();
            let rhs: Natural = rhs.into();

            let expected_div: Natural = expected_div.into();
            let expected_rem: Natural = expected_rem.into();
            let (actual_div, actual_rem) = lhs.div_rem(rhs).unwrap();

            assert_eq!(actual_div, expected_div);
            assert_eq!(actual_rem, expected_rem);
        }
    }

    #[test]
    fn test_natural_from_to_str() {
        let mut rng = rand::rng();

        for _ in 0..RANDOM_TEST_COUNT {
            let v: u64 = rng.random();
            let expected = v.to_string();
            let actual = Natural::from_str(&expected).unwrap().to_string();

            assert_eq!(actual, expected);
        }
    }
}

//#[cfg(test)]
//mod tests {
//    use rand::Rng;
//
//    use super::*;
//    use crate::digit;
//    use std::{cmp::Ordering, u32};
//
//    #[test]
//    fn test_natural_number_cmp() {
//        let lhs = Natural::from_str("1234").unwrap();
//        let rhs = Natural::from_str("5678").unwrap();
//        assert_eq!(lhs.cmp(&rhs), Ordering::Less);
//
//        let lhs = Natural::new(vec![digit!(1); 1_000_000]);
//        let rhs = Natural::new(vec![digit!(1); 1_000_000]);
//        assert_eq!(lhs.cmp(&rhs), Ordering::Equal);
//
//        let lhs_str = "2".to_owned() + "0".repeat(999_999).as_str();
//        let rhs_str = "1".to_owned() + "9".repeat(999_999).as_str();
//
//        let lhs = Natural::from_str(lhs_str.as_str()).unwrap();
//        let rhs = Natural::from_str(rhs_str.as_str()).unwrap();
//        assert_eq!(lhs.cmp(&rhs), Ordering::Greater);
//    }
//
//    #[test]
//    fn test_natural_number_inc() {
//        let mut rng = rand::rng();
//
//        for _ in 0..1000 {
//            let v: u32 = rng.random_range(..u32::MAX - 1);
//            let n = Natural::from_str(&v.to_string()).unwrap();
//            let expected = (v + 1).to_string();
//            let actual = n.inc().to_string();
//
//            assert_eq!(expected, actual);
//        }
//    }
//
//    #[test]
//    fn test_natural_number_add() {
//        let mut rng = rand::rng();
//
//        for _ in 0..1000 {
//            let lhs: u32 = rng.random_range(..2u32.pow(31));
//            let rhs: u32 = rng.random_range(..2u32.pow(31));
//            let expected = lhs + rhs;
//
//            let lhs = Natural::from_str(&lhs.to_string()).unwrap();
//            let rhs = Natural::from_str(&rhs.to_string()).unwrap();
//            assert_eq!((lhs + rhs).to_string(), expected.to_string());
//        }
//
//        let lhs = Natural::from_str(&"9".repeat(999_999)).unwrap();
//        let rhs = Natural::from_str("1").unwrap();
//
//        let expected = "1".to_owned() + &"0".repeat(999_999);
//        let actual = (lhs + rhs).to_string();
//
//        assert_eq!(expected, actual);
//    }
//
//    #[test]
//    fn test_natural_number_sub() {
//        let mut rng = rand::rng();
//
//        for _ in 0..1000 {
//            let rhs: u32 = rng.random_range(..2u32.pow(31));
//            let lhs: u32 = rng.random_range(rhs..=u32::MAX);
//            let expected = lhs - rhs;
//
//            let lhs = Natural::from_str(&lhs.to_string()).unwrap();
//            let rhs = Natural::from_str(&rhs.to_string()).unwrap();
//            assert_eq!((lhs - rhs).unwrap().to_string(), expected.to_string());
//        }
//
//        let lhs_value = "1".to_owned() + &"0".repeat(999_999);
//        let lhs = Natural::from_str(&lhs_value).unwrap();
//        let rhs = Natural::from_str("1").unwrap();
//
//        let expected = "9".repeat(999_999);
//        let actual = (lhs - rhs).unwrap().to_string();
//
//        assert_eq!(expected, actual);
//
//        let rhs_gt_lhs = Natural::from(123u8) - Natural::from(3234672789346usize);
//        assert!(rhs_gt_lhs.is_err());
//
//        let rhs_gt_lhs = Natural::from(123u8) - Natural::from(124u16);
//        assert!(rhs_gt_lhs.is_err());
//    }
//
//    #[test]
//    fn test_natural_number_mul_digit() {
//        let mut rng = rand::rng();
//
//        for _ in 0..1000 {
//            let lhs = rng.random_range(..2u32.pow(28));
//            let rhs = rng.random_range(0..9);
//            let expected = lhs * rhs;
//
//            let lhs = Natural::from_str(&lhs.to_string()).unwrap();
//            let rhs = digit!(rhs as u8);
//            let actual = lhs * rhs;
//
//            assert_eq!(expected.to_string(), actual.to_string());
//        }
//    }
//
//    #[test]
//    fn test_natural_number_mul() {
//        let mut rng = rand::rng();
//
//        for _ in 0..1000 {
//            let lhs = rng.random_range(..2u32.pow(16));
//            let rhs = rng.random_range(..2u32.pow(16));
//            let expected = lhs * rhs;
//
//            let lhs = Natural::from_str(&lhs.to_string()).unwrap();
//            let rhs = Natural::from_str(&rhs.to_string()).unwrap();
//            let actual = lhs * rhs;
//
//            assert_eq!(expected.to_string(), actual.to_string());
//        }
//    }
//
//    #[test]
//    fn test_natural_number_div() {
//        let mut rng = rand::rng();
//
//        for _ in 0..1000 {
//            let lhs = rng.random_range(..u32::MAX);
//            let rhs = rng.random_range(1..u32::MAX);
//            let expected = lhs / rhs;
//
//            let lhs = Natural::from_str(&lhs.to_string()).unwrap();
//            let rhs = Natural::from_str(&rhs.to_string()).unwrap();
//            let actual = lhs / rhs;
//
//            assert_eq!(expected.to_string(), actual.unwrap().to_string());
//        }
//
//        let zero_division = Natural::from(9u8) / Natural::from(0u8);
//        assert!(zero_division.is_err());
//    }
//
//    #[test]
//    fn test_natural_number_rem() {
//        let mut rng = rand::rng();
//
//        for _ in 0..1000 {
//            let lhs = rng.random_range(..u32::MAX);
//            let rhs = rng.random_range(1..u32::MAX);
//            let expected = lhs % rhs;
//
//            let lhs = Natural::from_str(&lhs.to_string()).unwrap();
//            let rhs = Natural::from_str(&rhs.to_string()).unwrap();
//            let actual = lhs % rhs;
//
//            assert_eq!(expected.to_string(), actual.unwrap().to_string());
//        }
//    }
//
//    #[test]
//    fn test_natural_number_gcd() {
//        let lhs = Natural::from_str("21").unwrap();
//        let rhs = Natural::from_str("6").unwrap();
//        assert_eq!("3", lhs.gcd(rhs).to_string());
//
//        let lhs = Natural::from_str("8").unwrap();
//        let rhs = Natural::from_str("0").unwrap();
//        assert_eq!("8", lhs.gcd(rhs).to_string());
//
//        let lhs = Natural::from_str("0").unwrap();
//        let rhs = Natural::from_str("6").unwrap();
//        assert_eq!("6", lhs.gcd(rhs).to_string());
//
//        let lhs = Natural::from_str("0").unwrap();
//        let rhs = Natural::from_str("0").unwrap();
//        assert_eq!("0", lhs.gcd(rhs).to_string());
//    }
//
//    #[test]
//    fn test_natural_number_lcm() {
//        let lhs = Natural::from_str("21").unwrap();
//        let rhs = Natural::from_str("14").unwrap();
//        assert_eq!("42", lhs.lcm(rhs).to_string());
//
//        let lhs = Natural::from_str("8").unwrap();
//        let rhs = Natural::from_str("0").unwrap();
//        assert_eq!("0", lhs.lcm(rhs).to_string());
//
//        let lhs = Natural::from_str("0").unwrap();
//        let rhs = Natural::from_str("6").unwrap();
//        assert_eq!("0", lhs.lcm(rhs).to_string());
//
//        let lhs = Natural::from_str("0").unwrap();
//        let rhs = Natural::from_str("0").unwrap();
//        assert_eq!("0", lhs.lcm(rhs).to_string());
//    }
//
//    #[test]
//    fn test_natural_number_as_digits() {
//        let n = Natural::from_str("123412341234").unwrap();
//        let digits = n.as_digits();
//
//        assert_eq!(digits.len(), 12);
//        assert_eq!(digits[0], digit!(4));
//    }
//
//    #[test]
//    fn test_natural_number_is_zero() {
//        assert!(Natural::new(vec![]).is_zero());
//        assert!(Natural::new(vec![digit!(0)]).is_zero());
//        assert!(!Natural::new(vec![digit!(1)]).is_zero());
//        assert!(Natural::new(vec![digit!(0); 2]).is_zero());
//    }
//
//    #[test]
//    fn test_natural_number_times_pow10() {
//        let n = Natural::from_str("123").unwrap();
//        let expected = "12300000000000000";
//        let actual = n.times_pow10(14).to_string();
//
//        assert_eq!(expected, actual);
//    }
//
//    #[test]
//    fn test_natural_number_to_string() {
//        let digits = vec![digit!(9); 999];
//        let n = Natural::new(digits);
//        assert_eq!(n.to_string(), "9".repeat(999));
//
//        let n = Natural::from_str("3739847457938742").unwrap();
//        assert_eq!(n.to_string(), "3739847457938742");
//    }
//}
