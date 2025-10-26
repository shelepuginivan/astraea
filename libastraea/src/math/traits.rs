use std::ops::{Add, Div, Mul, Neg, Rem, Sub};

use crate::math::Sign;

/// Ring represents an algebraic ring structure.
///
/// A ring is a set equipped with two binary operations: addition and multiplication,
/// satisfying properties such as associativity, distributivity, and the existence of
/// additive and multiplicative identities.
pub trait Ring: Add + Sub + Mul + Sized {
    /// Returns the additive identity.
    fn zero() -> Self;

    /// Returns the multiplicative identity.
    fn one() -> Self;
}

/// IntegralDomain represents an integral domain.
///
/// Supports integer division and remainder operations.
pub trait IntegralDomain: Ring + Div + Rem {}

/// Field represents an algebraic field structure.
///
/// A field is a set with addition, subtraction, multiplication, and division.
pub trait Field: Ring + Div {}

pub trait Signed: Neg<Output = Self> + Sized {
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
            _ => self,
        }
    }
}
