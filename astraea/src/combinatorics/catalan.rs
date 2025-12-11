use std::ops::Div;

use crate::algebra::MulWithIdentity;
use crate::natural::Natural;

/// Calculates nth Catalan number.
///
/// ```
/// use astraea::combinatorics::catalan;
/// use astraea::natural::Natural;
///
/// let n = Natural::from(10_u8);
/// let c = catalan(&n);
///
/// assert_eq!(c, Natural::from(16796_u32));
/// ```
pub fn catalan(n: &Natural) -> Natural {
    let mut res = Natural::one();
    let mut numerator = Natural::from(2_u8);
    let mut denominator = Natural::one();

    while denominator <= *n {
        denominator.inc();
        res = (res * numerator.clone()).div(denominator.clone()).unwrap();
        numerator = numerator + Natural::from(4_u8);
    }

    res
}

#[cfg(test)]
mod tests {
    use super::catalan;

    use crate::natural::Natural;

    #[test]
    fn test_catalan() {
        let tests: Vec<usize> = vec![
            1, 1, 2, 5, 14, 42, 132, 429, 1430, 4862, 16796, 58786, 208012, 742900, 2674440,
            9694845,
        ];

        for (n, expected) in tests.into_iter().enumerate() {
            let n = Natural::from(n);
            let expected = Natural::from(expected);
            let actual = catalan(&n);

            assert_eq!(actual, expected);
        }
    }
}
