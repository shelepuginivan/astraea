use std::{
    cmp::Ordering,
    fmt::Display,
    ops::{Mul, Neg},
};

use crate::core::ParseError;
use crate::formatting::Pretty;

/// Sign represents sign of the number.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Sign {
    Negative,
    Zero,
    Positive,
}

impl Sign {
    /// Converts char ("+", "-") to Sign.
    pub fn from_char(c: char) -> Result<Self, ParseError> {
        match c {
            '-' => Ok(Self::Negative),
            '+' => Ok(Self::Positive),

            _ => Err(ParseError::new(format!("'{}' is not a sign", c))),
        }
    }

    /// Char representation of sign.
    pub fn char(&self) -> char {
        match self {
            Self::Negative => '-',
            Self::Zero => ' ',
            Self::Positive => '+',
        }
    }
}

impl Display for Sign {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.char())
    }
}

impl Pretty for Sign {
    fn prettify(&self) -> String {
        self.to_string()
    }
}

impl Neg for Sign {
    type Output = Self;

    fn neg(self) -> Self::Output {
        match self {
            Self::Positive => Self::Negative,
            Self::Zero => Self::Zero,
            Self::Negative => Self::Positive,
        }
    }
}

impl Mul for Sign {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        if self == Self::Zero || rhs == Self::Zero {
            return Self::Zero;
        }

        if self != rhs {
            return Self::Negative;
        }

        Self::Positive
    }
}

impl PartialOrd for Sign {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match (self, other) {
            (Sign::Negative, Sign::Negative) => Some(Ordering::Equal),
            (Sign::Negative, Sign::Zero) => Some(Ordering::Less),
            (Sign::Negative, Sign::Positive) => Some(Ordering::Less),
            (Sign::Zero, Sign::Negative) => Some(Ordering::Greater),
            (Sign::Zero, Sign::Zero) => Some(Ordering::Equal),
            (Sign::Zero, Sign::Positive) => Some(Ordering::Less),
            (Sign::Positive, Sign::Negative) => Some(Ordering::Greater),
            (Sign::Positive, Sign::Zero) => Some(Ordering::Greater),
            (Sign::Positive, Sign::Positive) => Some(Ordering::Equal),
        }
    }
}

impl Ord for Sign {
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap()
    }
}

/// Implements Into<T> for Sign for every signed integer type.
macro_rules! impl_sign_into {
    ($($t:ty),*) => {
        $(
            impl Into<$t> for Sign {
                fn into(self) -> $t {
                    match self {
                        Sign::Positive => 1,
                        Sign::Zero => 0,
                        Sign::Negative => -1,
                    }
                }
            }
        )*
    };
}

impl_sign_into!(i8, i16, i32, i64, i128, isize);

/// Implements From<T> for Sign for every integer type.
macro_rules! impl_sign_from {
    ($($t:ty),*) => {
        $(
            impl From<$t> for Sign {
                fn from(value: $t) -> Self {
                    value.cmp(&0).into()
                }
            }
        )*
    };
}

impl_sign_from!(
    u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize
);

impl Into<Sign> for Ordering {
    fn into(self) -> Sign {
        match self {
            Self::Less => Sign::Negative,
            Self::Equal => Sign::Zero,
            Self::Greater => Sign::Positive,
        }
    }
}

#[cfg(test)]
mod tests {
    use rand::Rng;

    use super::*;

    #[test]
    fn test_sign_from_char() {
        assert_eq!(Sign::from_char('+').unwrap(), Sign::Positive);
        assert_eq!(Sign::from_char('-').unwrap(), Sign::Negative);

        assert!(Sign::from_char('9').is_err())
    }

    #[test]
    fn test_sign_char() {
        assert_eq!(Sign::Positive.char(), '+');
        assert_eq!(Sign::Zero.char(), ' ');
        assert_eq!(Sign::Negative.char(), '-');
    }

    #[test]
    fn test_sign_fmt() {
        assert_eq!(Sign::Positive.to_string(), "+");
        assert_eq!(Sign::Zero.to_string(), " ");
        assert_eq!(Sign::Negative.to_string(), "-");

        assert_eq!(Sign::Positive.prettify(), "+");
        assert_eq!(Sign::Zero.prettify(), " ");
        assert_eq!(Sign::Negative.prettify(), "-");
    }

    #[test]
    fn test_sign_from_ordering() {
        assert_eq!(Into::<Sign>::into(Ordering::Greater), Sign::Positive);
        assert_eq!(Into::<Sign>::into(Ordering::Equal), Sign::Zero);
        assert_eq!(Into::<Sign>::into(Ordering::Less), Sign::Negative);
    }

    #[test]
    fn test_sign_from_integer() {
        let mut rng = rand::rng();

        for _ in 0..1000 {
            let v: i32 = rng.random();

            let expected: Sign = v.cmp(&0).into();
            let actual = Sign::from(v);

            assert_eq!(actual, expected);
        }
    }

    #[test]
    fn test_sign_into() {
        assert_eq!(Into::<i32>::into(Sign::Positive), 1);
        assert_eq!(Into::<i32>::into(Sign::Zero), 0);
        assert_eq!(Into::<i32>::into(Sign::Negative), -1);
    }

    #[test]
    fn test_sign_ord() {
        assert!(Sign::Positive == Sign::Positive);
        assert!(Sign::Positive > Sign::Zero);
        assert!(Sign::Positive > Sign::Negative);

        assert!(Sign::Zero < Sign::Positive);
        assert!(Sign::Zero == Sign::Zero);
        assert!(Sign::Zero > Sign::Negative);

        assert!(Sign::Negative < Sign::Positive);
        assert!(Sign::Negative < Sign::Zero);
        assert!(Sign::Negative == Sign::Negative);
    }
}
