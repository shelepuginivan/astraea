use std::fmt::Display;
use std::str::FromStr;

use crate::core::{ParseError, ValueError};
use crate::integer::Integer;
use crate::natural::NaturalNumber;

/// Represents a rational number.
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
}
