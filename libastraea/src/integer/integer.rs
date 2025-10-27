use std::cmp::Ordering;
use std::fmt::Display;
use std::ops::{Add, Div, Mul, Neg, Rem, Sub};
use std::str::FromStr;

use crate::core::{ParseError, Pretty, ValueError};
use crate::math::{IntegralDomain, Ring, Sign, Signed};
use crate::natural::NaturalNumber;

// Represents an integer.
#[derive(Clone, Eq, PartialEq)]
pub struct Integer {
    value: NaturalNumber,
    sign: Sign,
}

impl IntegralDomain for Integer {}
impl Ring for Integer {
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
}

impl Integer {
    pub fn new(value: NaturalNumber, sign: Sign) -> Self {
        Self { value, sign }
    }

    pub fn from_natural(n: NaturalNumber) -> Self {
        Self {
            value: n,
            sign: Sign::Positive,
        }
    }

    pub fn to_natural(self) -> Result<NaturalNumber, ValueError> {
        match self.sign {
            Sign::Negative => Err(ValueError::new(
                "cannot convert negative integer to natural",
            )),
            _ => Ok(self.value),
        }
    }

    pub fn is_zero(&self) -> bool {
        self.value.is_zero() || self.sign == Sign::Zero
    }

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

    pub fn gcd(self, other: Self) -> Self {
        Self {
            value: self.value.gcd(other.value),
            sign: Sign::Positive,
        }
    }

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
        if s.is_empty() {
            return Err(ParseError::new("cannot create integer from empty string"));
        }

        let mut minus_count = 0;
        let mut s = s;

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
    fn test_integer_add() {
        let mut rng = rand::rng();

        for _ in 0..1000 {
            let min_value = i32::MIN / 2;
            let max_value = i32::MAX / 2;

            let lhs = rng.random_range(min_value..max_value);
            let rhs = rng.random_range(min_value..max_value);
            let expected = (lhs + rhs).to_string();

            let lhs = Integer::from_str(&lhs.to_string()).unwrap();
            let rhs = Integer::from_str(&rhs.to_string()).unwrap();
            let actual = (lhs + rhs).to_string();

            assert_eq!(expected, actual);
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
}
