use std::fmt::Display;
use std::str::FromStr;

use crate::core::{ParseError, ValueError};
use crate::integer::Integer;
use crate::natural::NaturalNumber;

/// Represents a rational number.
#[derive(Clone)]
pub struct RationalNumber {
    numerator: Integer,
    denominator: NaturalNumber,
}

impl RationalNumber {
    pub fn new(numerator: Integer, denominator: NaturalNumber) -> Result<Self, ValueError> {
        if denominator.is_zero() {
            return Err(ValueError::new("denominator cannot be 0"));
        }

        Ok(Self {
            numerator,
            denominator,
        })
    }

    pub fn from_integer(integer: Integer) -> Self {
        Self {
            numerator: integer,
            denominator: NaturalNumber::one(),
        }
    }

    pub fn reduce(self) -> Self {
        let Self {
            numerator,
            denominator,
        } = self;

        let gcd = numerator
            .clone()
            .gcd(Integer::from_natural(denominator.clone()));

        let numerator = (numerator / gcd.clone()).unwrap();
        let denominator = (denominator / gcd.to_natural().unwrap()).unwrap();

        Self {
            numerator,
            denominator,
        }
    }

    pub fn is_integer(&self) -> bool {
        let rem = self.numerator.clone() % Integer::from_natural(self.denominator.clone());

        rem.unwrap().is_zero()
    }
}

impl FromStr for RationalNumber {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut tokens = s.split('/').map(|token| token.trim());

        let numerator = match tokens.next() {
            Some(token) => Integer::from_str(token),
            None => return Err(ParseError::new("numerator was not provied")),
        };
        let numerator = match numerator {
            Ok(v) => v,
            Err(e) => return Err(ParseError::new(e.message)),
        };

        let denominator = match tokens.next() {
            Some(token) => Integer::from_str(token),
            None => Ok(Integer::one()),
        };
        let denominator = match denominator {
            Ok(v) => v,
            Err(e) => return Err(ParseError::new(e.message)),
        };

        let sign = numerator.sign() * denominator.sign();
        let numerator = Integer::new(numerator.abs().to_natural().unwrap(), sign);
        let denominator = denominator.abs().to_natural().unwrap();

        match Self::new(numerator, denominator) {
            Ok(v) => Ok(v),
            Err(e) => Err(ParseError::new(e.message)),
        }
    }
}

impl Display for RationalNumber {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}/{}", self.numerator, self.denominator)
    }
}

#[cfg(test)]
mod tests {
    use rand::Rng;

    use super::*;

    #[test]
    fn test_rational_number_from_str() {
        let expected = "8/7";
        let actual = RationalNumber::from_str("8/7").unwrap().to_string();
        assert_eq!(expected, actual);

        let expected = "-6/5";
        let actual = RationalNumber::from_str("-6 /  5 ").unwrap().to_string();
        assert_eq!(expected, actual);

        let expected = "-37/29";
        let actual = RationalNumber::from_str(" 37/ -29").unwrap().to_string();
        assert_eq!(expected, actual);

        let expected = "13/11";
        let actual = RationalNumber::from_str("-13 / -11").unwrap().to_string();
        assert_eq!(expected, actual);

        let expected = "1/1";
        let actual = RationalNumber::from_str("1").unwrap().to_string();
        assert_eq!(expected, actual);

        assert!(RationalNumber::from_str("1/").is_err());
        assert!(RationalNumber::from_str("/23435").is_err());
        assert!(RationalNumber::from_str("   / ").is_err());
        assert!(RationalNumber::from_str("1/0").is_err());
    }

    #[test]
    fn test_rational_number_reduce() {
        let expected = "2/1";
        let actual = RationalNumber::from_str("8/4")
            .unwrap()
            .reduce()
            .to_string();
        assert_eq!(expected, actual);

        let expected = "2/3";
        let actual = RationalNumber::from_str("2/3")
            .unwrap()
            .reduce()
            .to_string();
        assert_eq!(expected, actual);

        let expected = "1/334";
        let actual = RationalNumber::from_str("1324234 / 442294156")
            .unwrap()
            .reduce()
            .to_string();
        assert_eq!(expected, actual);

        let expected = "0/1";
        let actual = RationalNumber::from_str("0/2495734985739854")
            .unwrap()
            .reduce()
            .to_string();
        assert_eq!(expected, actual);

        let expected = "7/5";
        let actual = RationalNumber::from_str("42/30")
            .unwrap()
            .reduce()
            .to_string();
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_rational_number_is_integer() {
        let mut rng = rand::rng();

        for _ in 0..1000 {
            let numerator: i32 = rng.random();
            let denominator: i32 = rng.random();
            if denominator == 0 {
                continue;
            }

            let expected = numerator % denominator == 0;
            let actual = RationalNumber::from_str(&format!("{}/{}", numerator, denominator))
                .unwrap()
                .is_integer();

            assert_eq!(expected, actual);
        }

        let is_integer = RationalNumber::from_str("8/4").unwrap().is_integer();
        assert!(is_integer);

        let is_integer = RationalNumber::from_str("2/3").unwrap().is_integer();
        assert!(!is_integer);

        let is_integer = RationalNumber::from_str("30/42").unwrap().is_integer();
        assert!(!is_integer);

        let is_integer = RationalNumber::from_str("900/30").unwrap().is_integer();
        assert!(is_integer);

        let is_integer = RationalNumber::from_str("0/1").unwrap().is_integer();
        assert!(is_integer);

        let is_integer = RationalNumber::from_str("1").unwrap().is_integer();
        assert!(is_integer);
    }
}
