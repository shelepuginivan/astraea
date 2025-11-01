use std::fmt::Debug;
use std::ops::{Add, Div, Mul, Neg, Rem, Sub};
use std::str::FromStr;

use crate::error::ValueError;
use crate::math::Sign;

/// The base trait for all mathematical objects in the system.
///
/// This trait serves as a marker for types that represent mathematical entities, requiring cloning
/// and parsing capabilities.
pub trait MathObject: Sized + Clone + FromStr<Err: Debug> {}

/// A Semiring is an algebraic structure consisting of a set equipped with two binary operations:
/// addition and multiplication, where addition is associative and commutative with an identity element,
/// multiplication is associative with an identity element, and multiplication distributes over addition.
///
/// Unlike rings, semirings do not require additive inverses.
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
///
/// This trait generalizes the classical notion of Euclidean rings (which are integral domains) to
/// include structures such as semirings (e.g., the natural numbers with 0) that may lack additive
/// inverses but still support a division-with-remainder property.
pub trait EuclideanRing:
    SemiRing + Div<Output = Result<Self, ValueError>> + Rem<Output = Result<Self, ValueError>>
{
}

/// Ring represents an algebraic ring structure.
///
/// A ring is a set equipped with two binary operations: addition and multiplication,
/// satisfying properties such as associativity, distributivity, and the existence of
/// additive and multiplicative identities.
pub trait Ring: Neg<Output = Self> + SemiRing + Sub {
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

/// A Field is an algebraic structure in which addition, subtraction, multiplication,
/// and division (except by zero) are defined and satisfy the usual properties.
pub trait Field: Ring + Div<Output = Result<Self, ValueError>> {}

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
