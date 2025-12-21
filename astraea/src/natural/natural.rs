use std::cmp::Ordering;
use std::fmt::Display;
use std::iter;
use std::ops::{Add, Div, Index, IndexMut, Mul, Rem, Sub};
use std::str::FromStr;

use crate::algebra::*;
use crate::digit::Digit;
use crate::error::{ParseError, ValueError};
use crate::formatting::Pretty;

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

impl AddCommutative<Self> for Natural {}

impl MulClosed for Natural {}

impl MulAssociative<Self> for Natural {}

impl MulWithIdentity<Self> for Natural {
    fn one() -> Self {
        Self {
            digits: vec![Digit::One],
        }
    }

    fn is_one(&self) -> bool {
        self.digits.len() == 1 && self.digits[0] == Digit::One
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

        let mut quotient = Self::zero();
        let mut remainder = Self::zero();

        for i in 0..self.len() {
            remainder = remainder.append(self[i]);

            let mut q_digit = 0;
            while remainder >= rhs {
                remainder = (remainder - rhs.clone())?;
                q_digit += 1;
            }

            quotient = quotient.append(Digit::try_from(q_digit)?);
        }

        Ok((quotient, remainder))
    }
}

impl Natural {
    /// Creates a Natural from digits in direct order.
    ///
    /// ```
    /// use astraea::digit::Digit;
    /// use astraea::natural::Natural;
    ///
    /// let digits = vec![Digit::Nine; 999];
    /// let n = Natural::new(digits);
    ///
    /// assert_eq!(n.to_string(), "9".repeat(999));
    /// ```
    pub fn new(mut digits: Vec<Digit>) -> Self {
        digits.reverse();
        Self::from_reversed(digits)
    }

    /// Creates a Natural from digits in reverse order.
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

        Natural { digits }
    }

    /// Number of digits in a number.
    ///
    /// ```
    /// use astraea::natural::Natural;
    ///
    /// let n = Natural::from(12345678u32);
    ///
    /// assert_eq!(n.len(), 8);
    /// ```
    pub fn len(&self) -> usize {
        self.digits.len()
    }

    /// Returns digit by index, starting from 0 for the least significant digit of the number.
    ///
    /// ```
    /// use astraea::digit::Digit;
    /// use astraea::natural::Natural;
    ///
    /// let n = Natural::from(1234u16);
    ///
    /// assert_eq!(n.lsd_at(1), Digit::Three);
    /// ```
    pub fn lsd_at(&self, idx: usize) -> Digit {
        self.digits[idx]
    }

    /// Returns digit by index, starting from 0 for the most significant digit of the number.
    ///
    /// ```
    /// use astraea::digit::Digit;
    /// use astraea::natural::Natural;
    ///
    /// let n = Natural::from(1234u16);
    ///
    /// assert_eq!(n.msd_at(1), Digit::Two);
    /// ```
    pub fn msd_at(&self, idx: usize) -> Digit {
        self.digits[self.digits.len() - idx - 1]
    }

    /// Appends digit to the number as least significant digit.
    ///
    /// ```
    /// use astraea::digit::Digit;
    /// use astraea::formatting::Pretty;
    /// use astraea::natural::Natural;
    /// use std::str::FromStr;
    ///
    /// let n = Natural::from_str("12345689").expect("should parse a valid natural");
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
    /// use astraea::digit::Digit;
    /// use astraea::natural::Natural;
    ///
    /// let n = Natural::from(123u8);
    ///
    /// assert_eq!(n.as_digits(), vec![Digit::Three, Digit::Two, Digit::One]);
    /// ```
    pub fn as_digits(self) -> Vec<Digit> {
        self.digits
    }

    /// Increments number by 1.
    ///
    /// ```
    /// use astraea::natural::Natural;
    ///
    /// let n = Natural::from(999999u32);
    /// let n = n.inc();
    ///
    /// assert_eq!(n, Natural::from(1000000u32));
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
    /// use astraea::natural::Natural;
    ///
    /// let n = Natural::from(1u8);
    /// let n = n.times_pow10(9);
    ///
    /// assert_eq!(n, Natural::from(1_000_000_000u32));
    /// ```
    pub fn times_pow10(self, k: usize) -> Self {
        if self.is_zero() {
            return self;
        }

        let digits = [vec![Digit::Zero; k], self.as_digits()].concat();

        Self::from_reversed(digits)
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

        Ok(Self::from_reversed(digits))
    }
}

impl Mul<Digit> for Natural {
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

impl Mul<Self> for Natural {
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

impl Div for Natural {
    type Output = Result<Self, ValueError>;

    fn div(self, rhs: Self) -> Self::Output {
        Ok(self.div_rem(rhs)?.0)
    }
}

impl Rem for Natural {
    type Output = Result<Self, ValueError>;

    fn rem(self, rhs: Self) -> Self::Output {
        Ok(self.div_rem(rhs)?.1)
    }
}

impl Root for Natural {
    type Output = Self;

    fn root(self, power: usize) -> Result<Self::Output, ValueError> {
        if power == 0 {
            return Err(ValueError::new("root power should not be 0"));
        }

        if power == 1 {
            return Ok(self);
        }

        let power_der = power - 1;
        let mut x = Natural::one().times_pow10(self.len() / power + 1);
        let a = self;

        loop {
            let numerator = Natural::from(power_der) * x.clone().pow(power) + a.clone();
            let denominator = Natural::from(power) * x.clone().pow(power_der);

            let x_next = numerator.div(denominator)?;

            if x_next >= x {
                return Ok(x);
            }

            x = x_next
        }
    }
}

impl Display for Natural {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s: String = self.digits.iter().rev().map(|digit| digit.char()).collect();

        write!(f, "{}", s)
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
        Some(self.cmp(other))
    }
}

impl Ord for Natural {
    fn cmp(&self, other: &Self) -> Ordering {
        let cmp_radix = self.digits.len().cmp(&other.digits.len());

        if cmp_radix != Ordering::Equal {
            return cmp_radix;
        }

        let self_digits = self.digits.iter().rev();
        let other_digits = other.digits.iter().rev();

        for (lhs, rhs) in self_digits.zip(other_digits) {
            let cmp_digit = lhs.cmp(rhs);

            if cmp_digit != Ordering::Equal {
                return cmp_digit;
            }
        }

        Ordering::Equal
    }
}

impl Index<usize> for Natural {
    type Output = Digit;

    /// Returns digit by index, starting from 0 for the most significant digit of the number.
    fn index(&self, index: usize) -> &Self::Output {
        &self.digits[self.digits.len() - index - 1]
    }
}

impl IndexMut<usize> for Natural {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.digits[index]
    }
}

impl FromStr for Natural {
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
            if index == 0 && char == '-' {
                return Err(ParseError::new("natural number must not be negative"));
            }

            let digit = Digit::from_char(char)?;
            digits[length - index - 1] = digit;
        }

        Ok(Natural::from_reversed(digits))
    }
}

/// Implements From<T> for Natural for every unsigned integer type.
macro_rules! impl_natural_from {
    ($($t:ty),*) => {
        $(
            impl From<$t> for Natural {
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

/// Implements TryFrom<T> for Natural for every signed integer type.
macro_rules! impl_natural_try_from {
    ($($t:ty),*) => {
        $(
            impl TryFrom<$t> for Natural {
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

/// Implements TryInto<T> for Natural for every integer type.
macro_rules! impl_natural_try_into {
    ($($t:ty),*) => {
        $(
            impl TryInto<$t> for Natural {
                type Error = ValueError;

                fn try_into(self) -> Result<$t, Self::Error> {
                    let mut result: $t = 0;
                    let mut radix = 1;

                    for digit in self.digits.into_iter() {
                        let digit: $t = digit.into();

                        let added = match digit.checked_mul(radix) {
                            Some(v) => v,
                            None => return Err(ValueError::new("value is too large")),
                        };

                        result = match result.checked_add(added) {
                            Some(v) => v,
                            None => return Err(ValueError::new("value is too large")),
                        };

                        radix = match radix.checked_mul(10) {
                            Some(v) => v,
                            None => return Err(ValueError::new("value is too large")),
                        };
                    }

                    Ok(result)
                }
            }
        )*
    };
}

impl_natural_try_into!(
    u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize
);

#[cfg(test)]
mod tests {
    use std::cmp::Ordering;

    use rand::Rng;

    use super::*;

    #[test]
    fn test_natural_cmp() {
        let lhs = Natural::from(1234_u16);
        let rhs = Natural::from(5678_u16);
        assert_eq!(lhs.cmp(&rhs), Ordering::Less);

        let lhs = Natural::new(vec![Digit::One; 1_000_000]);
        let rhs = Natural::new(vec![Digit::One; 1_000_000]);
        assert_eq!(lhs.cmp(&rhs), Ordering::Equal);

        let lhs_str = "2".to_owned() + "0".repeat(999_999).as_str();
        let rhs_str = "1".to_owned() + "9".repeat(999_999).as_str();

        let lhs = Natural::from_str(lhs_str.as_str()).expect("should parse a valid natural");
        let rhs = Natural::from_str(rhs_str.as_str()).expect("should parse a valid natural");
        assert_eq!(lhs.cmp(&rhs), Ordering::Greater);
    }

    #[test]
    fn test_natural_inc() {
        let mut rng = rand::rng();

        for _ in 0..1000 {
            let v: u32 = rng.random_range(..u32::MAX - 1);
            let n = Natural::from(v);
            let expected = (v + 1).to_string();
            let actual = n.inc().to_string();

            assert_eq!(expected, actual);
        }
    }

    #[test]
    fn test_natural_add() {
        let mut rng = rand::rng();

        for _ in 0..1000 {
            let lhs: u32 = rng.random_range(..2u32.pow(31));
            let rhs: u32 = rng.random_range(..2u32.pow(31));
            let expected = lhs + rhs;

            let lhs = Natural::from(lhs);
            let rhs = Natural::from(rhs);
            assert_eq!((lhs + rhs).to_string(), expected.to_string());
        }

        let lhs = Natural::from_str(&"9".repeat(999_999)).expect("should parse a valid natural");
        let rhs = Natural::from(1_u8);

        let expected = "1".to_owned() + &"0".repeat(999_999);
        let actual = (lhs + rhs).to_string();

        assert_eq!(expected, actual);
    }

    #[test]
    fn test_natural_sub() {
        let mut rng = rand::rng();

        for _ in 0..1000 {
            let rhs: u32 = rng.random_range(..2u32.pow(31));
            let lhs: u32 = rng.random_range(rhs..=u32::MAX);
            let expected = lhs - rhs;

            let lhs = Natural::from(lhs);
            let rhs = Natural::from(rhs);
            let actual = (lhs - rhs).expect("should subtract");

            assert_eq!(actual.to_string(), expected.to_string());
        }

        let lhs_value = "1".to_owned() + &"0".repeat(999_999);
        let lhs = Natural::from_str(&lhs_value).expect("should parse a valid natural");
        let rhs = Natural::from(1_u8);

        let expected = "9".repeat(999_999);
        let actual = (lhs - rhs).expect("should subtract").to_string();

        assert_eq!(expected, actual);

        let rhs_gt_lhs = Natural::from(123_u8) - Natural::from(3234672789346_usize);
        assert!(rhs_gt_lhs.is_err());

        let rhs_gt_lhs = Natural::from(123_u8) - Natural::from(124_u16);
        assert!(rhs_gt_lhs.is_err());
    }

    #[test]
    fn test_natural_mul_digit() {
        let mut rng = rand::rng();

        for _ in 0..1000 {
            let lhs = rng.random_range(..2u32.pow(28));
            let rhs = rng.random_range(0..9);
            let expected = lhs * rhs;

            let lhs = Natural::from(lhs);
            let rhs = Digit::try_from(rhs).expect("should convert a valid digit");
            let actual = lhs * rhs;

            assert_eq!(expected.to_string(), actual.to_string());
        }
    }

    #[test]
    fn test_natural_mul() {
        let mut rng = rand::rng();

        for _ in 0..1000 {
            let lhs = rng.random_range(..2u32.pow(16));
            let rhs = rng.random_range(..2u32.pow(16));
            let expected = lhs * rhs;

            let lhs = Natural::from(lhs);
            let rhs = Natural::from(rhs);
            let actual = lhs * rhs;

            assert_eq!(expected.to_string(), actual.to_string());
        }
    }

    #[test]
    fn test_natural_div() {
        let mut rng = rand::rng();

        for _ in 0..1000 {
            let lhs = rng.random_range(..u32::MAX);
            let rhs = rng.random_range(1..u32::MAX);
            let expected = lhs / rhs;

            let lhs = Natural::from(lhs);
            let rhs = Natural::from(rhs);
            let actual = (lhs / rhs).expect("should divide");

            assert_eq!(expected.to_string(), actual.to_string());
        }

        let zero_division = Natural::from(9u8) / Natural::from(0u8);
        assert!(zero_division.is_err());
    }

    #[test]
    fn test_natural_rem() {
        let mut rng = rand::rng();

        for _ in 0..1000 {
            let lhs = rng.random_range(..u32::MAX);
            let rhs = rng.random_range(1..u32::MAX);
            let expected = lhs % rhs;

            let lhs = Natural::from(lhs);
            let rhs = Natural::from(rhs);
            let actual = (lhs % rhs).expect("should divide");

            assert_eq!(expected.to_string(), actual.to_string());
        }
    }

    #[test]
    fn test_natural_root() {
        let mut rng = rand::rng();

        for _ in 0..100 {
            let v: u16 = rng.random();
            let p = rng.random_range(1..10_usize);

            let expected = Natural::from(v);
            let power = expected.clone().pow(p);

            let actual = power.root(p).expect("should calculate n-th root");

            assert_eq!(expected, actual);
        }

        for _ in 0..100 {
            let v: u64 = rng.random();
            let sqrt = (v as f64).sqrt().floor() as u64;

            let expected = Natural::from(sqrt);
            let actual = Natural::from(v)
                .sqrt()
                .expect("should calculate square root");

            assert_eq!(expected, actual);
        }
    }

    #[test]
    fn test_natural_gcd() {
        let lhs = Natural::from(21_u8);
        let rhs = Natural::from(6_u8);
        assert_eq!("3", lhs.gcd(rhs).to_string());

        let lhs = Natural::from(8_u8);
        let rhs = Natural::from(0_u8);
        assert_eq!("8", lhs.gcd(rhs).to_string());

        let lhs = Natural::from(0_u8);
        let rhs = Natural::from(6_u8);
        assert_eq!("6", lhs.gcd(rhs).to_string());

        let lhs = Natural::from(0_u8);
        let rhs = Natural::from(0_u8);
        assert_eq!("0", lhs.gcd(rhs).to_string());
    }

    #[test]
    fn test_natural_lcm() {
        let lhs = Natural::from(21_u8);
        let rhs = Natural::from(14_u8);
        assert_eq!("42", lhs.lcm(rhs).to_string());

        let lhs = Natural::from(8_u8);
        let rhs = Natural::from(0_u8);
        assert_eq!("0", lhs.lcm(rhs).to_string());

        let lhs = Natural::from(0_u8);
        let rhs = Natural::from(6_u8);
        assert_eq!("0", lhs.lcm(rhs).to_string());

        let lhs = Natural::from(0_u8);
        let rhs = Natural::from(0_u8);
        assert_eq!("0", lhs.lcm(rhs).to_string());
    }

    #[test]
    fn test_natural_as_digits() {
        let n = Natural::from(123412341234_u64);
        let digits = n.as_digits();

        assert_eq!(digits.len(), 12);
        assert_eq!(digits[0], Digit::Four);
    }

    #[test]
    fn test_natural_is_zero() {
        assert!(Natural::new(vec![]).is_zero());
        assert!(Natural::new(vec![Digit::Zero]).is_zero());
        assert!(!Natural::new(vec![Digit::One]).is_zero());
        assert!(Natural::new(vec![Digit::Zero; 2]).is_zero());
    }

    #[test]
    fn test_natural_times_pow10() {
        let n = Natural::from(123_u8);
        let expected = "12300000000000000";
        let actual = n.times_pow10(14).to_string();

        assert_eq!(expected, actual);
    }

    #[test]
    fn test_natural_to_string() {
        let digits = vec![Digit::Nine; 999];
        let n = Natural::new(digits);
        assert_eq!(n.to_string(), "9".repeat(999));

        let n = Natural::from(3739847457938742_u64);
        assert_eq!(n.to_string(), "3739847457938742");
    }
}
