use std::fmt::Debug;
use std::ops::{Add, Div, Mul, Neg, Rem, Sub};
use std::str::FromStr;

use crate::error::ValueError;
use crate::math::Sign;

// MathObject is a base trait for every mathematical object
pub trait MathObject: Sized + Clone + FromStr<Err: Debug> {}

/// SemiRing is a generalization of algebraic rings, dropping the requirement that each element
/// must have an additive inverse.
pub trait SemiRing: MathObject + Add<Output = Self> + Mul<Output = Self> {
    /// Returns the additive identity.
    fn zero() -> Self;

    /// Returns the multiplicative identity.
    fn one() -> Self;

    /// Reports whether the element is an additive identity.
    fn is_zero(&self) -> bool;

    /// Reports whether the element is a multiplicative identity.
    fn is_one(&self) -> bool;
}

/// EuclideanRing is a semiring ring that can be endowed with a Euclidean function.
///
/// Supports integer division and remainder operations.
pub trait EuclideanRing:
    SemiRing + Div<Output = Result<Self, ValueError>> + Rem<Output = Result<Self, ValueError>>
{
}

/// Signed represents a math set with positive and negative values.
pub trait Signed: Neg<Output = Self> + SemiRing {
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

/// Ring represents an algebraic ring structure.
///
/// A ring is a set equipped with two binary operations: addition and multiplication,
/// satisfying properties such as associativity, distributivity, and the existence of
/// additive and multiplicative identities.
pub trait Ring: SemiRing + Signed {}

/// Field represents an algebraic field structure.
///
/// A field is a set with addition, subtraction, multiplication, and division.
pub trait Field: Ring + Sub + Div<Output = Result<Self, ValueError>> + Signed {}

/// Pow provides the exponentiation operation.
pub trait Pow {
    fn pow(self, power: usize) -> Self;
}

impl<T: Ring> Pow for T {
    fn pow(self, power: usize) -> Self {
        let mut a = self;
        let mut res = Self::one();
        let mut power = power;

        while power > 0 {
            if power & 1 == 1 {
                res = res * a.clone();
            }

            a = a.clone() * a;
            power >>= 1;
        }

        res
    }
}
