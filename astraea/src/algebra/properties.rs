use std::ops::{Add, Div, Mul, Neg, Sub};

use crate::{algebra::MathObject, error::ValueError};

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
