use std::ops::Neg;

use crate::math::Sign;

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
