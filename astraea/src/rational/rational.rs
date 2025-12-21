use std::cmp::Ordering;
use std::fmt::Display;
use std::ops::{Add, Div, Mul, Neg, Sub};
use std::str::FromStr;

use crate::algebra::*;
use crate::error::{ParseError, ValueError};
use crate::formatting::Pretty;
use crate::integer::Integer;
use crate::natural::Natural;
use crate::sign::Sign;

/// Represents a rational number.
#[derive(Clone, Debug)]
pub struct Rational {
    numerator: Integer,
    denominator: Natural,
}

impl MathObject for Rational {}

impl AddClosed for Rational {}

impl AddAssociative<Self> for Rational {}

impl AddWithIdentity<Self> for Rational {
    fn zero() -> Self {
        Self {
            numerator: Integer::zero(),
            denominator: Natural::one(),
        }
    }

    fn is_zero(&self) -> bool {
        self.numerator.is_zero()
    }
}

impl AddInvertible<Self> for Rational {}

impl AddCommutative<Self> for Rational {}

impl Signed for Rational {
    fn sign(&self) -> Sign {
        self.numerator.sign()
    }
}

impl MulClosed for Rational {}

impl MulAssociative<Self> for Rational {}

impl MulWithIdentity<Self> for Rational {
    fn one() -> Self {
        Self {
            numerator: Integer::one(),
            denominator: Natural::one(),
        }
    }

    fn is_one(&self) -> bool {
        match self.clone().to_integer() {
            Ok(i) => i.is_one(),
            Err(..) => false,
        }
    }
}

impl MulInvertible<Self> for Rational {
    fn inverse(self) -> Result<Self, ValueError> {
        let Self {
            numerator,
            denominator,
        } = self;

        if numerator.is_zero() {
            return Err(ValueError::new("cannot invert zero element"));
        }

        let new_numerator = Integer::from(denominator).with_sign(numerator.sign());
        let new_denominator = numerator.into_natural();

        Self::new(new_numerator, new_denominator)
    }
}

impl MulCommutative<Self> for Rational {}

impl Distributive for Rational {}

impl NoZeroDivisors for Rational {}

impl AddMagma for Rational {}
impl AddSemigroup for Rational {}
impl AddQuasigroup for Rational {}
impl AddUnitalMagma for Rational {}
impl AddMonoid for Rational {}
impl AddLoop for Rational {}
impl AddInvertibleSemigroup for Rational {}
impl AddGroup for Rational {}
impl AddAbelianGroup for Rational {}

impl MulMagma for Rational {}
impl MulSemigroup for Rational {}
impl MulQuasigroup for Rational {}
impl MulUnitalMagma for Rational {}
impl MulMonoid for Rational {}
impl MulLoop for Rational {}
impl MulInvertibleSemigroup for Rational {}
impl MulGroup for Rational {}
impl MulAbelianGroup for Rational {}

impl Semiring for Rational {}
impl Rng for Rational {}
impl Ring for Rational {}
impl CommutativeRing for Rational {}
impl Field for Rational {}

impl Rational {
    /// Creates a new Rational with specified numerator and denominator.
    pub fn new(numerator: Integer, denominator: Natural) -> Result<Self, ValueError> {
        if denominator.is_zero() {
            return Err(ValueError::new("denominator cannot be 0"));
        }

        Ok(Self {
            numerator,
            denominator,
        }
        .reduce())
    }

    /// Converts integer to rational number with denominator set to 1.
    ///
    /// ```
    /// use astraea::prelude::*;
    ///
    /// let i = Integer::from(1_000_000);
    /// let r = Rational::from_integer(i);
    ///
    /// let (numerator, denominator) = r.as_values();
    ///
    /// assert_eq!(numerator, Integer::from(1_000_000));
    /// assert!(denominator.is_one());
    /// ```
    pub fn from_integer(integer: Integer) -> Self {
        Self {
            numerator: integer,
            denominator: Natural::one(),
        }
    }

    /// Reduces the rational number. This is done automatically after operations with rational
    /// numbers.
    ///
    /// ```
    /// use astraea::formatting::Pretty;
    /// use astraea::rational::Rational;
    /// use std::str::FromStr;
    ///
    /// // This automatically reduces the rational number.
    /// let r = Rational::from_str("6/9").expect("should parse rational");
    ///
    /// assert_eq!(r.prettify(), "2/3");
    /// ```
    pub fn reduce(self) -> Self {
        if self.numerator.is_zero() {
            return Self::zero();
        }

        if self.numerator.is_one() || self.denominator.is_one() {
            return self;
        }

        let Self {
            numerator,
            denominator,
        } = self;

        let gcd = numerator.clone().gcd(Integer::from(denominator.clone()));

        let numerator =
            (numerator / gcd.clone()).expect("should divide integer by another non-zero integer");

        let denominator = (denominator / gcd.into_natural())
            .expect("should divide natural by another non-zero natural");

        Self {
            numerator,
            denominator,
        }
    }

    /// Reports whether the rational number is an integer, i.e. its numerator is divisible by its
    /// denominator.
    ///
    /// ```
    /// use astraea::rational::Rational;
    /// use std::str::FromStr;
    ///
    /// let r = Rational::from_str("22/11").expect("should parse rational");
    /// assert!(r.is_integer());
    ///
    /// let r = Rational::from_str("23/11").expect("should parse rational");
    /// assert!(!r.is_integer());
    /// ```
    pub fn is_integer(&self) -> bool {
        let rem = self.numerator.clone() % Integer::from(self.denominator.clone());

        rem.is_ok_and(|rem| rem.is_zero())
    }

    /// Converts rational number to integer, if possible.
    ///
    /// ```
    /// use astraea::integer::Integer;
    /// use astraea::rational::Rational;
    /// use std::str::FromStr;
    ///
    /// let r = Rational::from_str("22/11").expect("should parse rational");
    /// let i = r.to_integer().expect("should convert to integer");
    /// assert_eq!(i, Integer::from(2));
    ///
    /// let r = Rational::from_str("23/11").expect("should parse rational");
    /// assert!(r.to_integer().is_err());
    /// ```
    pub fn to_integer(self) -> Result<Integer, ValueError> {
        let reduced = self.reduce();

        if reduced.denominator != Natural::one() {
            return Err(ValueError::new("not an integer"));
        }

        Ok(reduced.numerator)
    }

    /// Destructs rational number into its numerator and denominator.
    ///
    /// ```
    /// use astraea::integer::Integer;
    /// use astraea::natural::Natural;
    /// use astraea::rational::Rational;
    /// use std::str::FromStr;
    ///
    /// let r = Rational::from_str("-34 / 23").expect("should parse rational");
    ///
    /// let (numerator, denominator) = r.as_values();
    ///
    /// assert_eq!(numerator, Integer::from(-34));
    /// assert_eq!(denominator, Natural::from(23u8));
    /// ```
    pub fn as_values(self) -> (Integer, Natural) {
        (self.numerator, self.denominator)
    }
}

impl FromStr for Rational {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut tokens = s.split('/');

        let numerator = match tokens.next() {
            Some(token) => Integer::from_str(token),
            None => return Err(ParseError::new("numerator was not provided")),
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

        if tokens.next() != None {
            return Err(ParseError::new("too many delimiters"));
        }

        let sign = numerator.sign() * denominator.sign();

        let numerator = numerator.abs().with_sign(sign);
        let denominator = denominator.into_natural();

        match Self::new(numerator, denominator) {
            Ok(v) => Ok(v),
            Err(e) => Err(ParseError::new(e.message)),
        }
    }
}

impl Neg for Rational {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self {
            numerator: -self.numerator,
            denominator: self.denominator,
        }
    }
}

impl Add for Rational {
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

        let lhs_denominator = Integer::from(self.denominator.clone());
        let rhs_denominator = Integer::from(rhs.denominator.clone());

        let lcm = lhs_denominator.clone().lcm(rhs_denominator.clone());
        let lhs_factor = (lcm.clone() / lhs_denominator)
            .expect("should divide integer by another non-zero integer");
        let rhs_factor = (lcm.clone() / rhs_denominator)
            .expect("should divide integer by another non-zero integer");
        let lhs_numerator = self.numerator * lhs_factor;
        let rhs_numerator = rhs.numerator * rhs_factor;
        let numerator = lhs_numerator + rhs_numerator;
        let denominator = lcm.into_natural();

        Self {
            numerator,
            denominator,
        }
        .reduce()
    }
}

impl Sub for Rational {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        self.add(-rhs)
    }
}

impl Mul for Rational {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        Self {
            numerator: self.numerator * rhs.numerator,
            denominator: self.denominator * rhs.denominator,
        }
        .reduce()
    }
}

impl Div for Rational {
    type Output = Result<Self, ValueError>;

    fn div(self, rhs: Self) -> Self::Output {
        if rhs.is_zero() {
            return Err(ValueError::new("division by 0 is not allowed"));
        }

        let sign = self.sign() * rhs.sign();

        let lhs_numerator = self.numerator.into_natural();
        let rhs_numerator = rhs.numerator.into_natural();

        let lhs_denominator = self.denominator;
        let rhs_denominator = rhs.denominator;

        let numerator = lhs_numerator * rhs_denominator;
        let denominator = rhs_numerator * lhs_denominator;

        Ok(Self {
            numerator: Integer::new(numerator, sign),
            denominator,
        }
        .reduce())
    }
}

impl PartialEq for Rational {
    fn eq(&self, other: &Self) -> bool {
        self.numerator == other.numerator && self.denominator == other.denominator
    }
}

impl Eq for Rational {}

impl PartialOrd for Rational {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Rational {
    fn cmp(&self, other: &Self) -> Ordering {
        let lhs = self.numerator.clone() * Integer::from(other.denominator.clone());
        let rhs = other.numerator.clone() * Integer::from(self.denominator.clone());

        lhs.cmp(&rhs)
    }
}

impl Display for Rational {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}/{}", self.numerator, self.denominator)
    }
}

impl Pretty for Rational {
    fn prettify(&self) -> String {
        match self.clone().to_integer() {
            Ok(int) => int.to_string(),
            Err(..) => self.to_string(),
        }
    }
}

#[cfg(test)]
mod tests {
    use rand::Rng;

    use super::*;

    fn rat(numerator: i32, denominator: i32) -> Rational {
        Rational::from_str(&format!("{}/{}", numerator, denominator)).unwrap()
    }

    #[test]
    fn test_rational_number_from_str() {
        let expected = "8/7";
        let actual = Rational::from_str("8/7").unwrap().to_string();
        assert_eq!(expected, actual);

        let expected = "-6/5";
        let actual = Rational::from_str("-6 /  5 ").unwrap().to_string();
        assert_eq!(expected, actual);

        let expected = "-37/29";
        let actual = Rational::from_str(" 37/ -29").unwrap().to_string();
        assert_eq!(expected, actual);

        let expected = "13/11";
        let actual = Rational::from_str("-13 / -11").unwrap().to_string();
        assert_eq!(expected, actual);

        let expected = "1/1";
        let actual = Rational::from_str("1").unwrap().to_string();
        assert_eq!(expected, actual);

        assert!(Rational::from_str("1/").is_err());
        assert!(Rational::from_str("/23435").is_err());
        assert!(Rational::from_str("   / ").is_err());
        assert!(Rational::from_str("1/0").is_err());
        assert!(Rational::from_str("").is_err());
    }

    #[test]
    fn test_rational_number_reduce() {
        let expected = "2/1";
        let actual = Rational::from_str("8/4").unwrap().reduce().to_string();
        assert_eq!(expected, actual);

        let expected = "2/3";
        let actual = Rational::from_str("2/3").unwrap().reduce().to_string();
        assert_eq!(expected, actual);

        let expected = "1/334";
        let actual = Rational::from_str("1324234 / 442294156")
            .unwrap()
            .reduce()
            .to_string();
        assert_eq!(expected, actual);

        let expected = "0/1";
        let actual = Rational::from_str("0/2495734985739854")
            .unwrap()
            .reduce()
            .to_string();
        assert_eq!(expected, actual);

        let expected = "7/5";
        let actual = Rational::from_str("42/30").unwrap().reduce().to_string();
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
            let actual = Rational::from_str(&format!("{}/{}", numerator, denominator))
                .unwrap()
                .is_integer();

            assert_eq!(expected, actual);
        }

        let is_integer = Rational::from_str("8/4").unwrap().is_integer();
        assert!(is_integer);

        let is_integer = Rational::from_str("2/3").unwrap().is_integer();
        assert!(!is_integer);

        let is_integer = Rational::from_str("30/42").unwrap().is_integer();
        assert!(!is_integer);

        let is_integer = Rational::from_str("900/30").unwrap().is_integer();
        assert!(is_integer);

        let is_integer = Rational::from_str("0/1").unwrap().is_integer();
        assert!(is_integer);

        let is_integer = Rational::from_str("1").unwrap().is_integer();
        assert!(is_integer);
    }

    #[test]
    fn test_rational_number_to_integer() {
        let mut rng = rand::rng();

        for _ in 0..1000 {
            let numerator: i32 = rng.random();
            let denominator: i32 = rng.random_range(1..10);

            let v = Rational::from_str(&format!("{}/{}", numerator, denominator)).unwrap();

            if numerator % denominator == 0 {
                assert_eq!(
                    v.to_integer().unwrap(),
                    Integer::from(numerator / denominator)
                );
            } else {
                assert!(v.to_integer().is_err());
            }
        }
    }

    #[test]
    fn test_rational_number_from_integer() {
        let mut rng = rand::rng();

        for _ in 0..1000 {
            let v: i32 = rng.random();
            let expected_numerator = Integer::from(v);
            let expected_denominator = Natural::one();

            let (actual_numerator, actual_denominator) =
                Rational::from_integer(Integer::from(v)).as_values();

            assert_eq!(actual_numerator, expected_numerator);
            assert_eq!(actual_denominator, expected_denominator);
        }
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

    #[test]
    fn test_rational_number_ord() {
        let mut rng = rand::rng();

        for _ in 0..1000 {
            let lhs_numerator: i32 = rng.random();
            let lhs_denominator = rng.random::<u16>().max(1);

            let rhs_numerator: i32 = rng.random();
            let rhs_denominator = rng.random::<u16>().max(1);

            let lhs = Rational::new(Integer::from(lhs_numerator), Natural::from(lhs_denominator))
                .unwrap();
            let rhs = Rational::new(Integer::from(rhs_numerator), Natural::from(rhs_denominator))
                .unwrap();

            assert_eq!(
                lhs.cmp(&rhs),
                (lhs_numerator as i64 * rhs_denominator as i64)
                    .cmp(&(lhs_denominator as i64 * rhs_numerator as i64))
            );
        }

        assert!(rat(1, 2) == rat(2, 4));
        assert!(rat(-3, 5) == rat(-6, 10));
        assert!(rat(1, 3) < rat(1, 2));
        assert!(rat(-2, 3) < rat(-1, 3));
        assert!(rat(3, 4) <= rat(3, 4));
        assert!(rat(2, 5) <= rat(3, 5));
        assert!(rat(5, 6) > rat(4, 6));
        assert!(rat(1, 1) > rat(999, 1000));
        assert!(rat(7, 8) >= rat(7, 8));
        assert!(rat(9, 10) >= rat(8, 10));
        assert!(rat(-1, 2) == rat(-2, 4));
        assert!(rat(-3, 5) == rat(-6, 10));
        assert!(rat(-3, 4) < rat(-1, 2));
        assert!(rat(-5, 6) < rat(-2, 3));
        assert!(rat(-7, 8) <= rat(-7, 8));
        assert!(rat(-4, 5) <= rat(-3, 5));
        assert!(rat(-1, 2) > rat(-3, 4));
        assert!(rat(-2, 3) > rat(-5, 6));
        assert!(rat(-9, 10) >= rat(-9, 10));
        assert!(rat(-3, 5) >= rat(-4, 5));
        assert!(rat(-1, 2) < rat(1, 2));
        assert!(rat(1, 3) > rat(-1, 3));
    }

    #[test]
    fn test_rational_number_fmt() {
        assert_eq!(rat(1, 1).prettify(), "1");
        assert_eq!(rat(222, 2).prettify(), "111");
        assert_eq!(rat(-24, 12).prettify(), "-2");
        assert_eq!(rat(0, 1).prettify(), "0");
        assert_eq!(rat(1, 3).prettify(), "1/3");
        assert_eq!(rat(-2, 5).prettify(), "-2/5");
    }
}
