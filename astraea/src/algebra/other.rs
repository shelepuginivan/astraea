use std::ops::{Div, Rem};

use crate::algebra::*;
use crate::error::ValueError;
use crate::sign::Sign;

/// Signed is a trait for algebraic structures with a sign.
pub trait Signed: MathObject + AddWithIdentity<Self> + AddInvertible<Self> {
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

/// IntegerDivision is a trait that defines integer division.
pub trait IntegerDivision:
    Semiring + Div<Output = Result<Self, ValueError>> + Rem<Output = Result<Self, ValueError>>
{
    fn div_rem(self, rhs: Self) -> Result<(Self, Self), ValueError>;
}

/// Gcd is a trait that defines greatest common divisor.
pub trait Gcd {
    type Output;

    /// Greatest common divisor.
    fn gcd(self, other: Self) -> Self::Output;
}

/// Lcm is a trait that defines least common multiple.
pub trait Lcm {
    type Output;

    /// Least common multiple.
    fn lcm(self, other: Self) -> Self::Output;
}

impl<T: IntegerDivision> Gcd for T {
    type Output = Self;

    fn gcd(self, other: Self) -> Self::Output {
        if self.is_zero() {
            return other;
        } else if other.is_zero() {
            return self;
        }

        return other.clone().gcd(
            self.rem(other)
                .expect("should return remainder for non-zero divisor"),
        );
    }
}

impl<T: IntegerDivision> Lcm for T {
    type Output = Self;

    fn lcm(self, other: Self) -> Self::Output {
        if self.is_zero() || other.is_zero() {
            return Self::zero();
        }

        let prod = self.clone() * other.clone();
        let gcd = self.gcd(other);

        match prod / gcd {
            Ok(v) => v,
            Err(_) => Self::zero(),
        }
    }
}

/// Pow provides the exponentiation operation.
pub trait Pow {
    type Output;

    fn pow(self, power: usize) -> Self::Output;
}

impl<T: MulClosed + MulWithIdentity<Self> + MulAssociative<Self>> Pow for T {
    type Output = Self;

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

/// Root provides the n-th root operation.
pub trait Root: MathObject {
    type Output;

    fn root(self, power: usize) -> Result<Self::Output, ValueError>;

    fn sqrt(self) -> Result<Self::Output, ValueError> {
        self.root(2)
    }

    fn cbrt(self) -> Result<Self::Output, ValueError> {
        self.root(3)
    }
}
