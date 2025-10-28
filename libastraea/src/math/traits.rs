use std::{
    fmt::{Debug, Display},
    ops::{Add, Div, Mul, Neg, Rem, Sub},
    str::FromStr,
};

use crate::{core::ValueError, math::Sign};

pub trait MathSet: Sized + Clone + FromStr<Err: Debug> + Display {}

/// Ring represents an algebraic ring structure.
///
/// A ring is a set equipped with two binary operations: addition and multiplication,
/// satisfying properties such as associativity, distributivity, and the existence of
/// additive and multiplicative identities.
pub trait Ring: MathSet + Add<Output = Self> + Mul<Output = Self> {
    /// Returns the additive identity.
    fn zero() -> Self;

    /// Returns the multiplicative identity.
    fn one() -> Self;

    /// Reports whether the element is an additive identity.
    fn is_zero(&self) -> bool;

    /// Reports whether the element is a multiplicative identity.
    fn is_one(&self) -> bool;
}

/// IntegralDomain represents an integral domain.
///
/// Supports integer division and remainder operations.
pub trait IntegralDomain:
    Ring + Div<Output = Result<Self, ValueError>> + Rem<Output = Result<Self, ValueError>>
{
}

/// Signed represents a math set with positive and negative values.
pub trait Signed: Neg<Output = Self> + Ring {
    fn sign(&self) -> Sign;

    fn is_positive(&self) -> bool {
        self.sign() == Sign::Positive
    }

    fn is_negative(&self) -> bool {
        self.sign() == Sign::Negative
    }

    fn with_sign(self, sign: Sign) -> Self {
        match sign {
            Sign::Negative => -self,
            Sign::Zero => Self::zero(),
            Sign::Positive => self,
        }
    }

    fn abs(self) -> Self {
        match self.sign() {
            Sign::Negative => -self,
            Sign::Zero => Self::zero(),
            Sign::Positive => self,
        }
    }
}

/// Field represents an algebraic field structure.
///
/// A field is a set with addition, subtraction, multiplication, and division.
pub trait Field: Ring + Sub + Div<Output = Result<Self, ValueError>> + Signed {}
