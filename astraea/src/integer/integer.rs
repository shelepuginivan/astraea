use std::cmp::Ordering;
use std::fmt::Display;
use std::ops::{Add, Div, Mul, Neg, Rem, Sub};
use std::str::FromStr;

use crate::error::{ParseError, ValueError};
use crate::formatting::Pretty;
use crate::math::{EuclideanRing, MathObject, Ring, SemiRing, Sign, Signed};
use crate::natural::NaturalNumber;

// Represents an integer.
#[derive(Clone, Debug)]
pub struct Integer {
    value: NaturalNumber,
    sign: Sign,
}

impl MathObject for Integer {}
impl EuclideanRing for Integer {}
impl Ring for Integer {}
impl SemiRing for Integer {
    fn zero() -> Self {
        Self {
            value: NaturalNumber::zero(),
            sign: Sign::Zero,
        }
    }

    fn one() -> Self {
        Self {
            value: NaturalNumber::one(),
            sign: Sign::Positive,
        }
    }

    fn is_zero(&self) -> bool {
        self.value.is_zero() || self.sign == Sign::Zero
    }

    fn is_one(&self) -> bool {
        self.value.is_one()
    }
}

impl Integer {
    /// Creates a new Integer from natural value and sign.
    pub fn new(value: NaturalNumber, sign: Sign) -> Self {
        Self { value, sign }
    }

    /// Creates a positive Integer from natural number.
    ///
    /// ```
    /// use astraea::natural::NaturalNumber;
    /// use astraea::integer::Integer;
    ///
    /// let n = NaturalNumber::from(123u8);
    /// let i = Integer::from_natural(n);
    ///
    /// assert_eq!(i, Integer::from(123));
    /// ```
    pub fn from_natural(n: NaturalNumber) -> Self {
        Self {
            value: n,
            sign: Sign::Positive,
        }
    }

    /// Converts integer to natural. Returns error for negative integers.
    ///
    /// ```
    /// use astraea::natural::NaturalNumber;
    /// use astraea::integer::Integer;
    ///
    /// let i = Integer::from(1000);
    /// let n = i.to_natural().unwrap();
    /// assert_eq!(n, NaturalNumber::from(1000u16));
    ///
    /// let i = Integer::from(-1000);
    /// assert!(i.to_natural().is_err());
    /// ```
    pub fn to_natural(self) -> Result<NaturalNumber, ValueError> {
        match self.sign {
            Sign::Negative => Err(ValueError::new(
                "cannot convert negative integer to natural",
            )),
            _ => Ok(self.value),
        }
    }

    /// Divides number by rhs, returning the quotient and the remainder. Error is returned if and
    /// only if rhs is zero.
    ///
    /// ```
    /// use astraea::integer::Integer;
    ///
    /// let lhs = Integer::from(100);
    /// let rhs = Integer::from(3);
    ///
    /// let (quotient, remainder) = lhs.divide(rhs).unwrap();
    ///
    /// assert_eq!(quotient, Integer::from(33));
    /// assert_eq!(remainder, Integer::from(1));
    /// ```
    ///
    /// The sign of the remainder is the same as the sign of the original number:
    ///
    /// ```
    /// use astraea::integer::Integer;
    ///
    /// let lhs = Integer::from(-100);
    /// let rhs = Integer::from(3);
    ///
    /// let (quotient, remainder) = lhs.divide(rhs).unwrap();
    ///
    /// assert_eq!(quotient, Integer::from(-33));
    /// assert_eq!(remainder, Integer::from(-1));
    /// ```
    pub fn divide(self, rhs: Self) -> Result<(Self, Self), ValueError> {
        if rhs.is_zero() {
            return Err(ValueError::new("division by 0 is not allowed"));
        }

        if rhs.value > self.value {
            return Ok((Self::zero(), self));
        }

        let res_sign = self.sign * rhs.sign;
        let (quotient, remainder) = self.value.divide(rhs.value).unwrap();

        let quotient = Self {
            value: quotient,
            sign: res_sign,
        };

        let remainder = if remainder.is_zero() {
            Self::zero()
        } else {
            Self {
                value: remainder,
                sign: self.sign,
            }
        };

        Ok((quotient, remainder))
    }

    /// Calculates GCD (greatest common divisor) of two integers. The returned value is a
    /// non-negative integer.
    ///
    /// ```
    /// use astraea::integer::Integer;
    ///
    /// let a = Integer::from(8);
    /// let b = Integer::from(-12);
    ///
    /// let gcd = a.gcd(b);
    ///
    /// assert_eq!(gcd, Integer::from(4));
    /// ```
    pub fn gcd(self, other: Self) -> Self {
        Self {
            value: self.value.gcd(other.value),
            sign: Sign::Positive,
        }
    }

    /// Calculates LCM (least common multiple) of two natural numbers. The returned value is a
    /// non-negative integer.
    ///
    /// ```
    /// use astraea::integer::Integer;
    ///
    /// let a = Integer::from(-6);
    /// let b = Integer::from(9);
    ///
    /// let lcm = a.lcm(b);
    ///
    /// assert_eq!(lcm, Integer::from(18));
    /// ```
    pub fn lcm(self, other: Self) -> Self {
        Self {
            value: self.value.lcm(other.value),
            sign: Sign::Positive,
        }
    }
}

impl Add for Integer {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        match (self.is_zero(), rhs.is_zero()) {
            (true, true) => return Self::zero(),
            (true, false) => return rhs,
            (false, true) => return self,
            (false, false) => {}
        }

        let (max, min, diff_sign) = match self.value.cmp(&rhs.value) {
            Ordering::Less => (rhs.value, self.value, rhs.sign),
            Ordering::Equal => (self.value, rhs.value, Sign::Zero),
            Ordering::Greater => (self.value, rhs.value, self.sign),
        };

        match (self.sign, rhs.sign) {
            (Sign::Positive, Sign::Positive) | (Sign::Negative, Sign::Negative) => Self {
                value: max + min,
                sign: self.sign,
            },

            (Sign::Positive, Sign::Negative) | (Sign::Negative, Sign::Positive) => Self {
                value: (max - min).unwrap(),
                sign: diff_sign,
            },

            _ => unreachable!(),
        }
    }
}

impl Sub for Integer {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        self.add(-rhs)
    }
}

impl Mul for Integer {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        Self {
            value: self.value * rhs.value,
            sign: self.sign * rhs.sign,
        }
    }
}

impl Div for Integer {
    type Output = Result<Self, ValueError>;

    fn div(self, rhs: Self) -> Self::Output {
        Ok(self.divide(rhs)?.0)
    }
}

impl Rem for Integer {
    type Output = Result<Self, ValueError>;

    fn rem(self, rhs: Self) -> Self::Output {
        Ok(self.divide(rhs)?.1)
    }
}

impl Neg for Integer {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self {
            value: self.value,
            sign: -self.sign,
        }
    }
}

impl Signed for Integer {
    fn sign(&self) -> Sign {
        self.sign
    }
}

impl PartialEq for Integer {
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value && self.sign == other.sign
    }
}

impl Eq for Integer {}

impl PartialOrd for Integer {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match self.sign().cmp(&other.sign()) {
            Ordering::Greater => return Some(Ordering::Greater),
            Ordering::Equal => {}
            Ordering::Less => return Some(Ordering::Less),
        };

        match self.sign {
            Sign::Negative => Some(other.value.cmp(&self.value)),
            Sign::Zero => Some(Ordering::Equal),
            Sign::Positive => Some(self.value.cmp(&other.value)),
        }
    }
}

impl Ord for Integer {
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap()
    }
}

impl Display for Integer {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let sign = if self.sign == Sign::Negative { "-" } else { "" };
        write!(f, "{}{}", sign, self.value)
    }
}

impl Pretty for Integer {
    fn prettify(&self) -> String {
        self.to_string()
    }
}

impl FromStr for Integer {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut s = s.trim();

        if s.is_empty() {
            return Err(ParseError::new("cannot create integer from empty string"));
        }

        let mut minus_count = 0;

        while s.starts_with("-") {
            s = s.strip_prefix('-').unwrap();
            minus_count += 1;
        }

        let mut sign = if minus_count % 2 == 0 {
            Sign::Positive
        } else {
            Sign::Negative
        };

        let value = NaturalNumber::from_str(s)?;
        if value.is_zero() {
            sign = Sign::Zero;
        }

        Ok(Integer { value, sign })
    }
}

/// Implements From<T> for Integer for every signed integer type.
macro_rules! impl_integer_from_signed {
    ($($t:ty),*) => {
        $(
            impl From<$t> for Integer {
                fn from(value: $t) -> Self {
                    let (sign, value) = match value.cmp(&0) {
                        Ordering::Less => (Sign::Negative, -value),
                        Ordering::Equal => return Self::zero(),
                        Ordering::Greater => (Sign::Positive, value),
                    };

                    Self::new(value.try_into().unwrap(), sign)
                }
            }
        )*
    };
}

impl_integer_from_signed!(i8, i16, i32, i64, i128, isize);

/// Implements From<T> for Integer for every unsigned integer type.
macro_rules! impl_integer_from_unsigned {
    ($($t:ty),*) => {
        $(
            impl From<$t> for Integer {
                fn from(value: $t) -> Self {
                    Self::new(value.into(), Sign::Positive)
                }
            }
        )*
    };
}

impl_integer_from_unsigned!(u8, u16, u32, u64, u128, usize);

#[cfg(test)]
mod tests {
    use super::*;
    use rand::Rng;

    #[test]
    fn test_integer_from_str() {
        let mut rng = rand::rng();

        for _ in 0..1000 {
            let i: i64 = rng.random();
            let expected = i.to_string();
            let actual = Integer::from_str(expected.as_str()).unwrap().to_string();

            assert_eq!(expected, actual);
        }
    }

    #[test]
    fn test_integer_to_natural() {
        let mut rng = rand::rng();

        for _ in 0..1000 {
            let i: i64 = rng.random();
            let v: Integer = i.into();

            if i < 0 {
                assert!(v.to_natural().is_err());
                continue;
            }

            let actual = v.to_natural().unwrap();
            let expected: NaturalNumber = i.try_into().unwrap();

            assert_eq!(actual, expected);
        }
    }

    #[test]
    fn test_integer_add() {
        let mut rng = rand::rng();

        for _ in 0..1000 {
            let min_value = i32::MIN / 2;
            let max_value = i32::MAX / 2;

            let lhs = rng.random_range(min_value..max_value);
            let rhs = rng.random_range(min_value..max_value);
            let expected = (lhs + rhs).to_string();

            let lhs = Integer::from(lhs);
            let rhs = Integer::from(rhs);
            let actual = (lhs + rhs).to_string();

            assert_eq!(expected, actual);
        }

        assert_eq!(Integer::zero() + Integer::zero(), Integer::zero());

        for _ in 0..1000 {
            let v: i32 = rng.random();

            assert_eq!(Integer::from(v) + Integer::zero(), Integer::from(v));
            assert_eq!(Integer::zero() + Integer::from(v), Integer::from(v));
        }
    }

    #[test]
    fn test_integer_sub() {
        let mut rng = rand::rng();

        for _ in 0..1000 {
            let min_value = i32::MIN / 2;
            let max_value = i32::MAX / 2;

            let lhs = rng.random_range(min_value..max_value);
            let rhs = rng.random_range(min_value..max_value);
            let expected = (lhs - rhs).to_string();

            let lhs = Integer::from_str(&lhs.to_string()).unwrap();
            let rhs = Integer::from_str(&rhs.to_string()).unwrap();
            let actual = (lhs - rhs).to_string();

            assert_eq!(expected, actual);
        }
    }

    #[test]
    fn test_integer_mul() {
        let mut rng = rand::rng();

        for _ in 0..1000 {
            let min_value = i16::MIN as i32;
            let max_value = i16::MAX as i32;

            let lhs = rng.random_range(min_value..max_value);
            let rhs = rng.random_range(min_value..max_value);
            let expected = (lhs * rhs).to_string();

            let lhs = Integer::from_str(&lhs.to_string()).unwrap();
            let rhs = Integer::from_str(&rhs.to_string()).unwrap();
            let actual = (lhs * rhs).to_string();

            assert_eq!(expected, actual);
        }
    }

    #[test]
    fn test_integer_div() {
        let mut rng = rand::rng();

        for _ in 0..1000 {
            let min_value = i16::MIN as i32;
            let max_value = i16::MAX as i32;

            let lhs = rng.random_range(min_value..max_value);
            let rhs = rng.random_range(min_value..max_value);
            if rhs == 0 {
                continue;
            }

            let expected = (lhs / rhs).to_string();

            let lhs = Integer::from_str(&lhs.to_string()).unwrap();
            let rhs = Integer::from_str(&rhs.to_string()).unwrap();
            let actual = (lhs / rhs).unwrap().to_string();

            assert_eq!(expected, actual);
        }

        let zero_division = Integer::from(234234i32) / Integer::from(0i8);
        assert!(zero_division.is_err());
    }

    #[test]
    fn test_integer_rem() {
        let mut rng = rand::rng();

        for _ in 0..1000 {
            let min_value = i16::MIN as i32;
            let max_value = i16::MAX as i32;

            let lhs = rng.random_range(min_value..max_value);
            let rhs = rng.random_range(min_value..max_value);
            if rhs == 0 {
                continue;
            }

            let expected = (lhs % rhs).to_string();

            let lhs = Integer::from_str(&lhs.to_string()).unwrap();
            let rhs = Integer::from_str(&rhs.to_string()).unwrap();
            let actual = (lhs % rhs).unwrap().to_string();

            assert_eq!(expected, actual);
        }
    }

    #[test]
    fn test_integer_fmt() {
        let mut rng = rand::rng();

        for _ in 0..1000 {
            let i: i32 = rng.random();
            let v = Integer::from(i);

            let actual_prettify = v.prettify();
            let actual_to_string = v.to_string();

            let expected = i.to_string();

            assert_eq!(actual_prettify, expected);
            assert_eq!(actual_to_string, expected);
        }
    }

    #[test]
    fn test_integer_ord() {
        let mut rng = rand::rng();

        for _ in 0..1000 {
            let lhs: i32 = rng.random();
            let rhs: i32 = rng.random();
            let expected = lhs.cmp(&rhs);

            let lhs: Integer = lhs.into();
            let rhs: Integer = rhs.into();
            let actual = lhs.cmp(&rhs);

            assert_eq!(actual, expected, "{} ? {}", lhs, rhs);
        }

        assert!(Integer::zero() == Integer::zero());
    }
}
