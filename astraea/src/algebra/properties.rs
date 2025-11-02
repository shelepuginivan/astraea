use std::ops::{Add, Div, Mul, Neg, Sub};

use crate::algebra::MathObject;
use crate::error::ValueError;

/// AddClosed marks type as closed under addition.
///
/// The sum of two elements is always another element of the same type.
pub trait AddClosed: MathObject + Add<Output = Self> {}

/// AddAssociative marks type as associative under addition.
///
/// > a + (b + c) = (a + b) + c
pub trait AddAssociative<T>: MathObject + Add<Output = T> {}

/// AddIdentity marks type as a structure with an additive identity, often referred to as zero.
///
/// > 0 + a = a
pub trait AddWithIdentity<T>: MathObject + Add<Output = T> {
    /// Returns the additive identity.
    fn zero() -> Self;

    /// Reports whether the element is an additive identity.
    fn is_zero(&self) -> bool;
}

/// AddInvertible marks type as inversible under addition.
///
/// > a + (-a) = 0
pub trait AddInvertible<T>:
    MathObject + Add<Output = T> + Sub<Output = T> + Neg<Output = Self>
{
}

/// AddCommutative marks type as commutative under addition.
///
/// > a + b = b + a
pub trait AddCommutative<T>: MathObject + Add<Output = T> {}

/// MulClosed marks type as closed under multiplication.
///
/// The product of two elements is always another element of the same type.
pub trait MulClosed: MathObject + Mul<Output = Self> {}

/// MulAssociative marks type as associative under multiplication.
///
/// > a · (b · c) = (a · b) · c
pub trait MulAssociative<T>: MathObject + Mul<T> {}

/// MulIdentity marks type as a structure with a multiplicative identity, often referred to as one.
///
/// > 1 · a = a
pub trait MulWithIdentity<T>: MathObject + Mul<T> {
    /// Returns the multiplicative identity.
    fn one() -> Self;

    /// Reports whether the element is a multiplicative identity.
    fn is_one(&self) -> bool;
}

/// MulInvertible marks type as inversible under multiplication.
///
/// > a · a⁻¹ = 1
pub trait MulInvertible<T>: MathObject + Mul<T> + Div<Output = Result<T, ValueError>> {
    fn inverse(self) -> Result<Self, ValueError>;
}

/// MulCommutative marks type as commutative under multiplication.
///
/// > a · b = b · a
pub trait MulCommutative<T>: MathObject + Mul<T> {}

/// Distributive marks type as a structure where multiplication distributes over addition.
///
/// > a · (b + c) = a · b + a · c
pub trait Distributive: MathObject {}

/// NoZeroDivisors marks type as a structure with no zero divisors.
///
/// > If a · b = 0, then a = 0 or b = 0.
pub trait NoZeroDivisors: MathObject {}
