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

pub trait AddClosed: MathObject + Add<Output = Self> {}

pub trait AddAssociative<T>: MathObject + Add<Output = T> {}

pub trait AddIdentity<T>: MathObject + Add<Output = T> {
    /// Returns the additive identity.
    fn zero() -> Self;

    /// Reports whether the element is an additive identity.
    fn is_zero(&self) -> bool;
}

pub trait AddInversion<T>:
    MathObject + Add<Output = T> + Sub<Output = T> + Neg<Output = Self>
{
}

pub trait AddCommutative<T>: MathObject + Add<Output = T> {}

pub trait MulClosed: MathObject + Mul<Output = Self> {}

pub trait MulAssociative<T>: MathObject + Mul<T> {}

pub trait MulIdentity<T>: MathObject + Mul<T> {
    /// Returns the multiplicative identity.
    fn one() -> Self;

    /// Reports whether the element is a multiplicative identity.
    fn is_one(&self) -> bool;
}

pub trait MulInversion<T>: MathObject + Mul<T> + Div<Output = Result<T, ValueError>> {
    fn inverse(self) -> Result<Self, ValueError>;
}

pub trait MulCommutative<T>: MathObject + Mul<T> {}

pub trait Distributive: MathObject {}

pub trait NoZeroDivisors: MathObject {}

pub trait Signed: MathObject + AddIdentity<Self> + AddInversion<Self> {
    fn sign(&self) -> Sign;

    fn opposite(self) -> Self {
        -self
    }

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

/// A Semiring is an algebraic structure consisting of a set equipped with two binary operations:
/// addition and multiplication, where addition is associative and commutative with an identity element,
/// multiplication is associative with an identity element, and multiplication distributes over addition.
///
/// Unlike rings, semirings do not require additive inverses.
pub trait Semiring:
    AddClosed
    + AddAssociative<Self>
    + AddIdentity<Self>
    + AddCommutative<Self>
    + MulClosed
    + MulAssociative<Self>
    + Distributive
{
}

pub trait IntegerDivision:
    Semiring + Div<Output = Result<Self, ValueError>> + Rem<Output = Result<Self, ValueError>>
{
    fn div_rem(self, rhs: Self) -> Result<(Self, Self), ValueError>;
}

pub trait Rng:
    AddClosed
    + AddAssociative<Self>
    + AddIdentity<Self>
    + AddInversion<Self>
    + AddCommutative<Self>
    + MulClosed
    + MulAssociative<Self>
    + Distributive
{
}

/// A Ring is an algebraic structure in which addition (subtraction) and multiplication are defined
/// and satisfy the ring axioms.
pub trait Ring:
    AddClosed
    + AddAssociative<Self>
    + AddIdentity<Self>
    + AddInversion<Self>
    + AddCommutative<Self>
    + MulClosed
    + MulAssociative<Self>
    + MulIdentity<Self>
    + Distributive
{
}

/// A Field is an algebraic structure in which addition (subtraction), multiplication,
/// and division (except by zero) are defined and satisfy the field axioms.
pub trait Field:
    AddClosed
    + AddAssociative<Self>
    + AddIdentity<Self>
    + AddInversion<Self>
    + AddCommutative<Self>
    + MulClosed
    + MulAssociative<Self>
    + MulIdentity<Self>
    + MulInversion<Self>
    + MulCommutative<Self>
    + Distributive
{
}

/// Pow provides the exponentiation operation.
pub trait Pow {
    fn pow(self, power: usize) -> Self;
}

impl<T: Ring + MulIdentity<Self> + MulCommutative<Self>> Pow for T {
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
