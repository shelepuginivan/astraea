use std::ops::Mul;
use std::str::FromStr;

use crate::algebra::*;
use crate::error::ParseError;
use crate::natural::NaturalNumber;

/// Matrix representation of the Fibonacci sequence.
#[derive(Clone, Debug)]
struct FibMatrix {
    a: NaturalNumber,
    b: NaturalNumber,
    c: NaturalNumber,
    d: NaturalNumber,
}

impl MathObject for FibMatrix {}

impl MulClosed for FibMatrix {}

impl MulAssociative<Self> for FibMatrix {}

impl MulWithIdentity<Self> for FibMatrix {
    fn one() -> Self {
        Self {
            a: NaturalNumber::one(),
            b: NaturalNumber::zero(),
            c: NaturalNumber::zero(),
            d: NaturalNumber::one(),
        }
    }

    fn is_one(&self) -> bool {
        self.a.is_one() && self.b.is_zero() && self.c.is_one() && self.c.is_zero()
    }
}

impl FibMatrix {
    /// Matrix that transforms (Fₙ, Fₙ₊₁)ᵀ to (Fₙ₊₁, Fₙ₊₂)ᵀ.
    ///
    /// > 1 1
    /// > 1 0
    fn new() -> Self {
        Self {
            a: NaturalNumber::one(),
            b: NaturalNumber::one(),
            c: NaturalNumber::one(),
            d: NaturalNumber::zero(),
        }
    }

    /// Matrix representation of nth Fibonacci number.
    ///
    /// > Fₙ₊₁ Fₙ
    /// > Fₙ   Fₙ₋₁
    fn nth(n: &NaturalNumber) -> Self {
        let n: usize = n.clone().try_into().expect("value is too large");

        Self::new().pow(n)
    }
}

impl Mul for FibMatrix {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        let Self {
            a: a1,
            b: b1,
            c: c1,
            d: d1,
        } = self;

        let Self {
            a: a2,
            b: b2,
            c: c2,
            d: d2,
        } = rhs;

        Self {
            a: a1.clone() * a2.clone() + b1.clone() * c2.clone(),
            b: a1 * b2.clone() + b1 * d2.clone(),
            c: c1.clone() * a2 + d1.clone() * c2,
            d: c1 * b2 + d1 * d2,
        }
    }
}

impl FromStr for FibMatrix {
    type Err = ParseError;

    fn from_str(_: &str) -> Result<Self, Self::Err> {
        Err(ParseError::new("parsing is unsupported for this type"))
    }
}

/// Calculates nth Fibonacci number, starting with 0 for n = 0.
///
/// ```
/// use astraea::combinatorics::fibonacci;
/// use astraea::natural::NaturalNumber;
///
/// let n = NaturalNumber::from(300_u16);
/// let fib = fibonacci(&n);
///
/// assert_eq!(fib.to_string(), "222232244629420445529739893461909967206666939096499764990979600");
/// ```
///
/// Panics if n cannot be converted to usize.
pub fn fibonacci(n: &NaturalNumber) -> NaturalNumber {
    FibMatrix::nth(n).c
}

#[cfg(test)]
mod tests {
    use crate::natural::NaturalNumber;

    use super::fibonacci;

    #[test]
    fn test_fibonacci() {
        let tests: Vec<usize> = vec![0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144, 233, 377, 610];

        for (n, expected) in tests.into_iter().enumerate() {
            let n = NaturalNumber::from(n);
            let expected = NaturalNumber::from(expected);
            let actual = fibonacci(&n);

            assert_eq!(actual, expected, "mismatched for n={}", n.to_string());
        }

        assert_eq!(
            fibonacci(&NaturalNumber::from(300_u16)).to_string(),
            "222232244629420445529739893461909967206666939096499764990979600",
        );
    }
}
