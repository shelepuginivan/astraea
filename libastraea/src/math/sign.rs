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
    /// Returns integer representation of Sign (-1 for Negative, 1 for Positive, 0 otherwise).
    pub fn value(&self) -> i32 {
        match self {
            Self::Negative => -1,
            Self::Zero => 0,
            Self::Positive => 1,
        }
    }

    /// Converts std::cmp::Ordering to Sign.
    pub fn from_ordering(o: &Ordering) -> Self {
        match o {
            Ordering::Less => Self::Negative,
            Ordering::Equal => Self::Zero,
            Ordering::Greater => Self::Positive,
        }
    }

    /// Converts char ("+", "-") to Sign.
    pub fn from_char(c: char) -> Result<Self, ParseError> {
        match c {
            '-' => Ok(Self::Negative),
            '+' => Ok(Self::Positive),

            _ => Err(ParseError::new(format!("'{}' is not a sign", c))),
        }
    }

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
        write!(f, "{}", self.value())
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

pub trait ToSign {
    fn to_sign(&self) -> Sign;
}

impl ToSign for Ordering {
    fn to_sign(&self) -> Sign {
        Sign::from_ordering(self)
    }
}
