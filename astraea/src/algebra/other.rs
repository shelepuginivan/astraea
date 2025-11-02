use std::ops::{Div, Rem};

use crate::algebra::{
    AddWithIdentity, AddInvertible, MathObject, MulCommutative, MulWithIdentity, Ring, Semiring,
};
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

/// Pow provides the exponentiation operation.
pub trait Pow {
    fn pow(self, power: usize) -> Self;
}

impl<T: Ring + MulWithIdentity<Self> + MulCommutative<Self>> Pow for T {
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
