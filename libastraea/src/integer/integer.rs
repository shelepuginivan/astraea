use std::fmt::Display;
use std::ops::Neg;
use std::str::FromStr;

use crate::core::{ParseError, ValueError};
use crate::math::Sign;
use crate::natural::NaturalNumber;

// Represents an integer.
pub struct Integer {
    value: NaturalNumber,
    sign: Sign,
}

impl Integer {
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

    pub fn zero() -> Self {
        Self {
            value: NaturalNumber::zero(),
            sign: Sign::Zero,
        }
    }

    pub fn abs(self) -> Self {
        if self.is_zero() {
            return Self::zero();
        }

        Self {
            value: self.value,
            sign: self.sign,
        }
    }

    pub fn is_zero(&self) -> bool {
        self.value.is_zero() || self.sign == Sign::Zero
    }

    pub fn sign(&self) -> Sign {
        self.sign
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

impl Display for Integer {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let sign = if self.sign == Sign::Negative { "-" } else { "" };
        write!(f, "{}{}", sign, self.value)
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
}
