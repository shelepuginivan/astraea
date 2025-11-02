use std::cmp::Ordering;
use std::fmt::Display;
use std::iter;
use std::ops::{Add, Div, Index, IndexMut, Mul, Rem, Sub};
use std::str::FromStr;

use crate::error::{ParseError, ValueError};
use crate::formatting::Pretty;
use crate::math::{
    AddAssociative, AddClosed, AddCommutative, AddIdentity, Digit, Distributive, IntegerDivision,
    MathObject, MulAssociative, MulClosed, MulCommutative, MulIdentity, Semiring,
};

/// Represents a natural number.
#[derive(Clone, Debug)]
pub struct NaturalNumber {
    /// Digits of the natural number, stored in reverse order.
    digits: Vec<Digit>,
}

impl MathObject for NaturalNumber {}

impl AddClosed for NaturalNumber {}
impl AddAssociative<Self> for NaturalNumber {}

impl AddIdentity<Self> for NaturalNumber {
    fn zero() -> Self {
        Self {
            digits: vec![Digit::Zero],
        }
    }

    fn is_zero(&self) -> bool {
        if self.digits.len() > 1 {
            return false;
        }

        self.digits.len() == 0 || self.digits[0] == Digit::Zero
    }
}

impl AddCommutative<Self> for NaturalNumber {}

impl MulClosed for NaturalNumber {}

impl MulAssociative<Self> for NaturalNumber {}

impl MulIdentity<Self> for NaturalNumber {
    fn one() -> Self {
        Self {
            digits: vec![Digit::One],
        }
    }

    fn is_one(&self) -> bool {
        self.digits.len() == 1 && self.digits[0] == Digit::One
    }
}

impl MulCommutative<Self> for NaturalNumber {}

impl Distributive for NaturalNumber {}

impl Semiring for NaturalNumber {}

impl IntegerDivision for NaturalNumber {
    fn div_rem(self, rhs: Self) -> Result<(Self, Self), ValueError> {
        if rhs.is_zero() {
            return Err(ValueError::new("division by 0 is not allowed"));
        }

        let mut quotient = Self::zero();
        let mut remainder = Self::zero();

        for i in 0..self.len() {
            remainder = remainder.append(self[i]);

            let mut q_digit = 0;
            while remainder >= rhs {
                remainder = (remainder - rhs.clone())?;
                q_digit += 1;
            }

            quotient = quotient.append(Digit::try_from(q_digit).unwrap());
        }

        Ok((quotient, remainder))
    }
}

impl NaturalNumber {
    /// Creates a NaturalNumber from digits in direct order.
    ///
    /// ```
    /// use astraea::math::Digit;
    /// use astraea::natural::NaturalNumber;
    ///
    /// let digits = vec![Digit::Nine; 999];
    /// let n = NaturalNumber::new(digits);
    ///
    /// assert_eq!(n.to_string(), "9".repeat(999));
    /// ```
    pub fn new(mut digits: Vec<Digit>) -> Self {
        digits.reverse();
        Self::from_reversed(digits)
    }

    /// Creates a NaturalNumber from digits in reverse order.
    pub fn from_reversed(mut digits: Vec<Digit>) -> Self {
        loop {
            match digits.pop_if(|d| *d == Digit::Zero) {
                Some(..) => {}
                None => break,
            };
        }

        if digits.len() == 0 {
            digits.push(Digit::Zero);
        }

        NaturalNumber { digits }
    }

    /// Number of digits in a number.
    ///
    /// ```
    /// use astraea::natural::NaturalNumber;
    ///
    /// let n = NaturalNumber::from(12345678u32);
    ///
    /// assert_eq!(n.len(), 8);
    /// ```
    pub fn len(&self) -> usize {
        self.digits.len()
    }

    /// Returns digit by index, starting from 0 for the least significant digit of the number.
    ///
    /// ```
    /// use astraea::math::Digit;
    /// use astraea::natural::NaturalNumber;
    ///
    /// let n = NaturalNumber::from(1234u16);
    ///
    /// assert_eq!(n.lsd_at(1), Digit::Three);
    /// ```
    pub fn lsd_at(&self, idx: usize) -> Digit {
        self.digits[idx]
    }

    /// Returns digit by index, starting from 0 for the most significant digit of the number.
    ///
    /// ```
    /// use astraea::math::Digit;
    /// use astraea::natural::NaturalNumber;
    ///
    /// let n = NaturalNumber::from(1234u16);
    ///
    /// assert_eq!(n.msd_at(1), Digit::Two);
    /// ```
    pub fn msd_at(&self, idx: usize) -> Digit {
        self.digits[self.digits.len() - idx - 1]
    }

    /// Appends digit to the number as least significant digit.
    ///
    /// ```
    /// use astraea::math::Digit;
    /// use astraea::formatting::Pretty;
    /// use astraea::natural::NaturalNumber;
    /// use std::str::FromStr;
    ///
    /// let n = NaturalNumber::from_str("12345689").unwrap();
    /// let n = n.append(Digit::Zero);
    ///
    /// assert_eq!(n.prettify(), "123456890");
    /// ```
    pub fn append(self, lsd: Digit) -> Self {
        let mut digits = self.times_pow10(1).as_digits();
        digits[0] = lsd;

        Self::from_reversed(digits)
    }

    /// Returns digits of the number, in reverse order.
    ///
    /// ```
    /// use astraea::math::Digit;
    /// use astraea::natural::NaturalNumber;
    ///
    /// let n = NaturalNumber::from(123u8);
    ///
    /// assert_eq!(n.as_digits(), vec![Digit::Three, Digit::Two, Digit::One]);
    /// ```
    pub fn as_digits(self) -> Vec<Digit> {
        self.digits
    }

    /// Increments number by 1.
    ///
    /// ```
    /// use astraea::natural::NaturalNumber;
    ///
    /// let n = NaturalNumber::from(999999u32);
    /// let n = n.inc();
    ///
    /// assert_eq!(n, NaturalNumber::from(1000000u32));
    /// ```
    pub fn inc(self) -> Self {
        if self.is_zero() {
            return Self::one();
        }

        let mut digits = self.as_digits();
        let mut next_carry = Digit::One;

        for idx in 0..digits.len() {
            let (digit, carry) = digits[idx] + next_carry;

            digits[idx] = digit;
            next_carry = carry;

            if next_carry == Digit::Zero {
                break;
            }
        }

        if next_carry != Digit::Zero {
            digits.push(next_carry);
        }

        Self::from_reversed(digits)
    }

    /// Multiplies number by 10<sup>k</sup>.
    ///
    /// ```
    /// use astraea::natural::NaturalNumber;
    ///
    /// let n = NaturalNumber::from(1u8);
    /// let n = n.times_pow10(9);
    ///
    /// assert_eq!(n, NaturalNumber::from(1_000_000_000u32));
    /// ```
    pub fn times_pow10(self, k: usize) -> Self {
        if self.is_zero() {
            return self;
        }

        let digits = [vec![Digit::Zero; k], self.as_digits()].concat();

        Self::from_reversed(digits)
    }

    /// Calculates GCD (greatest common divisor) of two natural numbers.
    ///
    /// ```
    /// use astraea::prelude::*;
    ///
    /// let a = NaturalNumber::from(12u8);
    /// let b = NaturalNumber::from(18u8);
    /// let gcd = a.gcd(b);
    ///
    /// assert_eq!(gcd.to_string(), "6")
    /// ```
    ///
    /// If either of two numbers is zero, the other is returned:
    ///
    /// ```
    /// use astraea::prelude::*;
    /// use std::str::FromStr;
    ///
    /// let a = NaturalNumber::zero();
    /// let b = NaturalNumber::from_str("1234123412341234").unwrap();
    /// let gcd = a.gcd(b);
    ///
    /// assert_eq!(gcd.to_string(), "1234123412341234")
    /// ```
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
    ///
    /// ```
    /// use astraea::prelude::*;
    /// use std::str::FromStr;
    ///
    /// let a = NaturalNumber::from(12u8);
    /// let b = NaturalNumber::from(18u8);
    /// let lcm = a.lcm(b);
    ///
    /// assert_eq!(lcm.to_string(), "36")
    /// ```
    ///
    /// If either of two numbers is zero, zero is returned:
    ///
    /// ```
    /// use astraea::prelude::*;
    ///
    /// let a = NaturalNumber::from(12u8);
    /// let b = NaturalNumber::zero();
    /// let lcm = a.lcm(b);
    ///
    /// assert!(lcm.is_zero())
    /// ```
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
}

impl Add for NaturalNumber {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        let lhs_len = self.digits.len();
        let rhs_len = rhs.digits.len();

        let result_digit_cap = lhs_len.max(rhs_len) + 1;
        if result_digit_cap == 1 {
            return NaturalNumber::zero();
        }

        let mut digits: Vec<Digit> = Vec::with_capacity(result_digit_cap);
        let mut next_carry = Digit::Zero;

        let lhs_digits = self.digits.into_iter();
        let rhs_digits = rhs.digits.into_iter();

        let (shorter, longer) = if lhs_len > rhs_len {
            (rhs_digits, lhs_digits)
        } else {
            (lhs_digits, rhs_digits)
        };

        let radix = longer.zip(shorter.chain(iter::repeat(Digit::Zero)));

        for (lhs_digit, rhs_digit) in radix {
            let (sum, carry) = lhs_digit + rhs_digit;
            let (sum, self_carry) = sum + next_carry;
            let (carry, _) = carry + self_carry;

            digits.push(sum);

            next_carry = carry;
        }

        if next_carry != Digit::Zero {
            digits.push(next_carry);
        }

        Self::from_reversed(digits)
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
            return Ok(Self::zero());
        }

        let mut digits: Vec<Digit> = Vec::with_capacity(result_digit_cap);
        let mut next_carry = Digit::Zero;

        let lhs_digits = self.digits.into_iter();
        let rhs_digits = rhs.digits.into_iter();

        let radix = lhs_digits.zip(rhs_digits.chain(iter::repeat(Digit::Zero)));

        for (lhs_digit, rhs_digit) in radix {
            let (diff, carry) = lhs_digit - rhs_digit;
            let (diff, self_carry) = diff - next_carry;
            let (carry, _) = carry + self_carry;

            digits.push(diff);

            next_carry = carry;
        }

        if next_carry != Digit::Zero {
            return Err(ValueError::new(
                "the right-hand side operand must not be greater than the left-hand side operand",
            ));
        }

        while digits.len() > 1 && *digits.last().unwrap() == Digit::Zero {
            digits.pop();
        }

        Ok(Self::from_reversed(digits))
    }
}

impl Mul<Digit> for NaturalNumber {
    type Output = Self;

    fn mul(self, rhs: Digit) -> Self::Output {
        if rhs == Digit::Zero {
            return Self::zero();
        }

        if rhs == Digit::One {
            return self;
        }

        if self.digits.len() == 0 {
            return Self::zero();
        }

        let mut digits = Vec::with_capacity(self.digits.len() + 1);
        let mut next_carry = Digit::Zero;

        for digit in self.digits {
            let (prod, carry) = digit * rhs;
            let (prod, self_carry) = prod + next_carry;
            let (carry, _) = carry + self_carry;

            digits.push(prod);

            next_carry = carry;
        }

        if next_carry != Digit::Zero {
            digits.push(next_carry);
        }

        Self::from_reversed(digits)
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

impl Div for NaturalNumber {
    type Output = Result<Self, ValueError>;

    fn div(self, rhs: Self) -> Self::Output {
        self.div_rem(rhs).and_then(|res| Ok(res.0))
    }
}

impl Rem for NaturalNumber {
    type Output = Result<Self, ValueError>;

    fn rem(self, rhs: Self) -> Self::Output {
        self.div_rem(rhs).and_then(|res| Ok(res.1))
    }
}

impl Display for NaturalNumber {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s: String = self.digits.iter().rev().map(|digit| digit.char()).collect();

        write!(f, "{}", s)
    }
}

impl Pretty for NaturalNumber {
    fn prettify(&self) -> String {
        self.to_string()
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

impl Index<usize> for NaturalNumber {
    type Output = Digit;

    /// Returns digit by index, starting from 0 for the most significant digit of the number.
    fn index(&self, index: usize) -> &Self::Output {
        &self.digits[self.digits.len() - index - 1]
    }
}

impl IndexMut<usize> for NaturalNumber {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.digits[index]
    }
}

impl FromStr for NaturalNumber {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let s = s.trim();
        let length = s.len();
        if length == 0 {
            return Err(ParseError::new(
                "cannot create natural number from empty string",
            ));
        }

        let mut digits: Vec<Digit> = vec![Digit::Zero; length];

        for (index, char) in s.chars().enumerate() {
            let digit = Digit::from_char(char)?;
            digits[length - index - 1] = digit;
        }

        Ok(NaturalNumber::from_reversed(digits))
    }
}

/// Implements From<T> for NaturalNumber for every unsigned integer type.
macro_rules! impl_natural_from {
    ($($t:ty),*) => {
        $(
            impl From<$t> for NaturalNumber {
                fn from(value: $t) -> Self {
                    let mut value = value;
                    let mut digits: Vec<Digit> = Vec::new();

                    while value > 0 {
                        let digit = Digit::try_from(value % 10).unwrap();
                        digits.push(digit);
                        value /= 10;
                    }

                    Self::from_reversed(digits)
                }
            }
        )*
    };
}

impl_natural_from!(u8, u16, u32, u64, u128, usize);

/// Implements TryFrom<T> for NaturalNumber for every signed integer type.
macro_rules! impl_natural_try_from {
    ($($t:ty),*) => {
        $(
            impl TryFrom<$t> for NaturalNumber {
                type Error = ValueError;

                fn try_from(value: $t) -> Result<Self, Self::Error> {
                    if value.is_negative() {
                        return Err(ValueError::new("natural number must not be negative"));
                    }

                    let mut value = value;
                    let mut digits: Vec<Digit> = Vec::new();

                    while value > 0 {
                        let digit = Digit::try_from(value % 10).unwrap();
                        digits.push(digit);
                        value /= 10;
                    }

                    Ok(Self::from_reversed(digits))
                }
            }
        )*
    };
}

impl_natural_try_from!(i8, i16, i32, i64, i128, isize);

#[cfg(test)]
mod tests {
    use rand::Rng;

    use super::*;
    use crate::digit;
    use std::{cmp::Ordering, u32};

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
    fn test_natural_number_inc() {
        let mut rng = rand::rng();

        for _ in 0..1000 {
            let v: u32 = rng.random_range(..u32::MAX - 1);
            let n = NaturalNumber::from_str(&v.to_string()).unwrap();
            let expected = (v + 1).to_string();
            let actual = n.inc().to_string();

            assert_eq!(expected, actual);
        }
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

        let rhs_gt_lhs = NaturalNumber::from(123u8) - NaturalNumber::from(3234672789346usize);
        assert!(rhs_gt_lhs.is_err());

        let rhs_gt_lhs = NaturalNumber::from(123u8) - NaturalNumber::from(124u16);
        assert!(rhs_gt_lhs.is_err());
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
    fn test_natural_number_div() {
        let mut rng = rand::rng();

        for _ in 0..1000 {
            let lhs = rng.random_range(..u32::MAX);
            let rhs = rng.random_range(1..u32::MAX);
            let expected = lhs / rhs;

            let lhs = NaturalNumber::from_str(&lhs.to_string()).unwrap();
            let rhs = NaturalNumber::from_str(&rhs.to_string()).unwrap();
            let actual = lhs / rhs;

            assert_eq!(expected.to_string(), actual.unwrap().to_string());
        }

        let zero_division = NaturalNumber::from(9u8) / NaturalNumber::from(0u8);
        assert!(zero_division.is_err());
    }

    #[test]
    fn test_natural_number_rem() {
        let mut rng = rand::rng();

        for _ in 0..1000 {
            let lhs = rng.random_range(..u32::MAX);
            let rhs = rng.random_range(1..u32::MAX);
            let expected = lhs % rhs;

            let lhs = NaturalNumber::from_str(&lhs.to_string()).unwrap();
            let rhs = NaturalNumber::from_str(&rhs.to_string()).unwrap();
            let actual = lhs % rhs;

            assert_eq!(expected.to_string(), actual.unwrap().to_string());
        }
    }

    #[test]
    fn test_natural_number_gcd() {
        let lhs = NaturalNumber::from_str("21").unwrap();
        let rhs = NaturalNumber::from_str("6").unwrap();
        assert_eq!("3", lhs.gcd(rhs).to_string());

        let lhs = NaturalNumber::from_str("8").unwrap();
        let rhs = NaturalNumber::from_str("0").unwrap();
        assert_eq!("8", lhs.gcd(rhs).to_string());

        let lhs = NaturalNumber::from_str("0").unwrap();
        let rhs = NaturalNumber::from_str("6").unwrap();
        assert_eq!("6", lhs.gcd(rhs).to_string());

        let lhs = NaturalNumber::from_str("0").unwrap();
        let rhs = NaturalNumber::from_str("0").unwrap();
        assert_eq!("0", lhs.gcd(rhs).to_string());
    }

    #[test]
    fn test_natural_number_lcm() {
        let lhs = NaturalNumber::from_str("21").unwrap();
        let rhs = NaturalNumber::from_str("14").unwrap();
        assert_eq!("42", lhs.lcm(rhs).to_string());

        let lhs = NaturalNumber::from_str("8").unwrap();
        let rhs = NaturalNumber::from_str("0").unwrap();
        assert_eq!("0", lhs.lcm(rhs).to_string());

        let lhs = NaturalNumber::from_str("0").unwrap();
        let rhs = NaturalNumber::from_str("6").unwrap();
        assert_eq!("0", lhs.lcm(rhs).to_string());

        let lhs = NaturalNumber::from_str("0").unwrap();
        let rhs = NaturalNumber::from_str("0").unwrap();
        assert_eq!("0", lhs.lcm(rhs).to_string());
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
        assert!(NaturalNumber::new(vec![digit!(0); 2]).is_zero());
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
