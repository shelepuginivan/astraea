use std::fmt::Display;
use std::ops::{Add, Div, Mul, Neg, Sub};
use std::str::FromStr;

use crate::core::{ParseError, Pretty, ValueError};
use crate::integer::Integer;
use crate::math::{Field, Ring, Sign, Signed};
use crate::natural::NaturalNumber;

/// Represents a rational number.
#[derive(Clone)]
pub struct RationalNumber {
    numerator: Integer,
    denominator: NaturalNumber,
}

impl Field for RationalNumber {}
impl Ring for RationalNumber {
    fn zero() -> Self {
        Self {
            numerator: Integer::zero(),
            denominator: NaturalNumber::one(),
        }
    }

    fn one() -> Self {
        Self {
            numerator: Integer::one(),
            denominator: NaturalNumber::one(),
        }
    }

    fn is_zero(&self) -> bool {
        self.numerator.is_zero()
    }

    fn is_one(&self) -> bool {
        match self.clone().to_integer() {
            Ok(i) => i.is_one(),
            Err(..) => false,
        }
    }
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

    pub fn to_integer(self) -> Result<Integer, ValueError> {
        let reduced = self.reduce();

        if reduced.denominator != NaturalNumber::one() {
            return Err(ValueError::new("not an integer"));
        }

        Ok(reduced.numerator)
    }

    pub fn as_values(self) -> (Integer, NaturalNumber) {
        (self.numerator, self.denominator)
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

impl Neg for RationalNumber {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self {
            numerator: -self.numerator,
            denominator: self.denominator,
        }
    }
}

impl Add for RationalNumber {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        if self.is_zero() && rhs.is_zero() {
            return Self::zero();
        }

        if self.is_zero() {
            return rhs;
        }

        if rhs.is_zero() {
            return self;
        }

        let lhs_denominator = Integer::from_natural(self.denominator.clone());
        let rhs_denominator = Integer::from_natural(rhs.denominator.clone());

        let lcm = lhs_denominator.clone().lcm(rhs_denominator.clone());
        let lhs_factor = (lcm.clone() / lhs_denominator).unwrap();
        let rhs_factor = (lcm.clone() / rhs_denominator).unwrap();
        let lhs_numerator = self.numerator * lhs_factor;
        let rhs_numerator = rhs.numerator * rhs_factor;
        let numerator = lhs_numerator + rhs_numerator;
        let denominator = lcm.to_natural().unwrap();

        Self {
            numerator,
            denominator,
        }
    }
}

impl Sub for RationalNumber {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        self.add(-rhs)
    }
}

impl Mul for RationalNumber {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        Self {
            numerator: self.numerator * rhs.numerator,
            denominator: self.denominator * rhs.denominator,
        }
    }
}

impl Signed for RationalNumber {
    fn sign(&self) -> Sign {
        self.numerator.sign()
    }
}

impl Div for RationalNumber {
    type Output = Result<Self, ValueError>;

    fn div(self, rhs: Self) -> Self::Output {
        if rhs.is_zero() {
            return Err(ValueError::new("division by 0 is not allowed"));
        }

        let sign = self.sign() * rhs.sign();

        let lhs_numerator = self.numerator.abs().to_natural().unwrap();
        let rhs_numerator = rhs.numerator.abs().to_natural().unwrap();

        let lhs_denominator = self.denominator;
        let rhs_denominator = rhs.denominator;

        let numerator = lhs_numerator * rhs_denominator;
        let denominator = rhs_numerator * lhs_denominator;

        Ok(Self {
            numerator: Integer::new(numerator, sign),
            denominator,
        })
    }
}

impl Display for RationalNumber {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}/{}", self.numerator, self.denominator)
    }
}

impl Pretty for RationalNumber {
    fn prettify(&self) -> String {
        let r = self.clone().reduce();

        match r.is_integer() {
            true => r.to_integer().unwrap().prettify(),
            false => r.to_string(),
        }
    }
}

#[cfg(test)]
mod tests {
    use rand::Rng;

    use super::*;

    fn rat(numerator: i32, denominator: i32) -> RationalNumber {
        RationalNumber::from_str(&format!("{}/{}", numerator, denominator)).unwrap()
    }

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

    #[test]
    fn test_rational_number_add() {
        let expected = "5/6";
        let lhs = rat(1, 2);
        let rhs = rat(1, 3);
        let actual = (lhs + rhs).to_string();
        assert_eq!(expected, actual);

        let expected = "1/2";
        let lhs = rat(1, 4);
        let rhs = rat(1, 4);
        let actual = (lhs + rhs).reduce().to_string();
        assert_eq!(expected, actual);

        let expected = "124253465/1231232314";
        let lhs = rat(0, 2343425);
        let rhs = rat(124253465, 1231232314);
        let actual = (lhs + rhs).reduce().to_string();
        assert_eq!(expected, actual);

        let expected = "999999/1111111";
        let lhs = rat(999999, 1111111);
        let rhs = rat(0, 42694269);
        let actual = (lhs + rhs).reduce().to_string();
        assert_eq!(expected, actual);

        let expected = "0/1";
        let lhs = rat(0, 777);
        let rhs = rat(0, 888);
        let actual = (lhs + rhs).reduce().to_string();
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_rational_number_sub() {
        let expected = "1/6";
        let lhs = rat(1, 2);
        let rhs = rat(1, 3);
        let actual = (lhs - rhs).to_string();
        assert_eq!(expected, actual);

        let expected = "0/1";
        let lhs = rat(1, 4);
        let rhs = rat(1, 4);
        let actual = (lhs - rhs).reduce().to_string();
        assert_eq!(expected, actual);

        let expected = "-1/6";
        let lhs = rat(1, 3);
        let rhs = rat(1, 2);
        let actual = (lhs - rhs).to_string();
        assert_eq!(expected, actual);

        let expected = "124253465/1231232314";
        let lhs = rat(124253465, 1231232314);
        let rhs = rat(0, 2343425);
        let actual = (lhs - rhs).reduce().to_string();
        assert_eq!(expected, actual);

        let expected = "-999999/1111111";
        let lhs = rat(0, 42694269);
        let rhs = rat(999999, 1111111);
        let actual = (lhs - rhs).reduce().to_string();
        assert_eq!(expected, actual);

        let expected = "0/1";
        let lhs = rat(0, 777);
        let rhs = rat(0, 888);
        let actual = (lhs - rhs).reduce().to_string();
        assert_eq!(expected, actual);

        let expected = "1/2";
        let lhs = rat(3, 4);
        let rhs = rat(1, 4);
        let actual = (lhs - rhs).reduce().to_string();
        assert_eq!(expected, actual);

        let expected = "1/6";
        let lhs = rat(1, -2);
        let rhs = rat(2, -3);
        let actual = (lhs - rhs).reduce().to_string();
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_rational_number_mul() {
        let expected = "1/6";
        let lhs = rat(1, 2);
        let rhs = rat(1, 3);
        let actual = (lhs * rhs).to_string();
        assert_eq!(expected, actual);

        let expected = "1/1";
        let lhs = rat(3, 4);
        let rhs = rat(4, 3);
        let actual = (lhs * rhs).reduce().to_string();
        assert_eq!(expected, actual);

        let expected = "0/1";
        let lhs = rat(124253465, 1231232314);
        let rhs = rat(0, 2343425);
        let actual = (lhs * rhs).reduce().to_string();
        assert_eq!(expected, actual);

        let expected = "0/1";
        let lhs = rat(0, 42694269);
        let rhs = rat(999999, 1111111);
        let actual = (lhs * rhs).reduce().to_string();
        assert_eq!(expected, actual);

        let expected = "0/1";
        let lhs = rat(0, 777);
        let rhs = rat(0, 888);
        let actual = (lhs * rhs).reduce().to_string();
        assert_eq!(expected, actual);

        let expected = "3/4";
        let lhs = rat(3, 4);
        let rhs = rat(1, 1);
        let actual = (lhs * rhs).reduce().to_string();
        assert_eq!(expected, actual);

        let expected = "2/5";
        let lhs = rat(4, 15);
        let rhs = rat(3, 2);
        let actual = (lhs * rhs).reduce().to_string();
        assert_eq!(expected, actual);

        let expected = "-1/4";
        let lhs = rat(1, 2);
        let rhs = rat(-1, 2);
        let actual = (lhs * rhs).reduce().to_string();
        assert_eq!(expected, actual);

        let expected = "1/4";
        let lhs = rat(-1, 2);
        let rhs = rat(-1, 2);
        let actual = (lhs * rhs).reduce().to_string();
        assert_eq!(expected, actual);

        let expected = "1/4";
        let lhs = rat(1, -2);
        let rhs = rat(-1, 2);
        let actual = (lhs * rhs).reduce().to_string();
        assert_eq!(expected, actual);

        let expected = "1/4";
        let lhs = rat(12345, 24690);
        let rhs = rat(24690, 49380);
        let actual = (lhs * rhs).reduce().to_string();
        assert_eq!(expected, actual);

        let expected = "2/3";
        let lhs = rat(4, 9);
        let rhs = rat(3, 2);
        let actual = (lhs * rhs).reduce().to_string();
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_rational_number_div() {
        let expected = "3/2";
        let lhs = rat(1, 2);
        let rhs = rat(1, 3);
        let actual = (lhs / rhs).unwrap().to_string();
        assert_eq!(expected, actual);

        let expected = "3/4";
        let lhs = rat(3, 4);
        let rhs = rat(1, 1);
        let actual = (lhs / rhs).unwrap().reduce().to_string();
        assert_eq!(expected, actual);

        let expected = "1/1";
        let lhs = rat(3, 4);
        let rhs = rat(3, 4);
        let actual = (lhs / rhs).unwrap().reduce().to_string();
        assert_eq!(expected, actual);

        let expected = "0/1";
        let lhs = rat(0, 777);
        let rhs = rat(999999, 1111111);
        let actual = (lhs / rhs).unwrap().reduce().to_string();
        assert_eq!(expected, actual);

        let expected = "16/9";
        let lhs = rat(4, 3);
        let rhs = rat(3, 4);
        let actual = (lhs / rhs).unwrap().reduce().to_string();
        assert_eq!(expected, actual);

        let expected = "2/3";
        let lhs = rat(4, 15);
        let rhs = rat(2, 5);
        let actual = (lhs / rhs).unwrap().reduce().to_string();
        assert_eq!(expected, actual);

        let expected = "-2/1";
        let lhs = rat(1, 2);
        let rhs = rat(-1, 4);
        let actual = (lhs / rhs).unwrap().reduce().to_string();
        assert_eq!(expected, actual);

        let expected = "2/1";
        let lhs = rat(-1, 2);
        let rhs = rat(-1, 4);
        let actual = (lhs / rhs).unwrap().reduce().to_string();
        assert_eq!(expected, actual);

        let expected = "-2/1";
        let lhs = rat(1, 2);
        let rhs = rat(1, -4);
        let actual = (lhs / rhs).unwrap().reduce().to_string();
        assert_eq!(expected, actual);

        let expected = "1/2";
        let lhs = rat(12345, 49380);
        let rhs = rat(24690, 49380);
        let actual = (lhs / rhs).unwrap().reduce().to_string();
        assert_eq!(expected, actual);

        let expected = "5/6";
        let lhs = rat(10, 18);
        let rhs = rat(12, 18);
        let actual = (lhs / rhs).unwrap().reduce().to_string();
        assert_eq!(expected, actual);

        let expected = "8/15";
        let lhs = rat(2, 3);
        let rhs = rat(5, 4);
        let actual = (lhs / rhs).unwrap().reduce().to_string();
        assert_eq!(expected, actual);

        let expected = "1/1";
        let lhs = rat(4, 6);
        let rhs = rat(2, 3);
        let actual = (lhs / rhs).unwrap().reduce().to_string();
        assert_eq!(expected, actual);

        let lhs = rat(4, 6);
        let rhs = rat(0, 3);
        assert!((lhs / rhs).is_err());

        let lhs = rat(0, 1);
        let rhs = rat(0, 1);
        assert!((lhs / rhs).is_err());
    }
}
