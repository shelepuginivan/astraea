use std::ops::{Div, Sub};

use crate::algebra::{AddWithIdentity, MulWithIdentity};
use crate::natural::NaturalNumber;

/// Calculates number of combinations.
///
/// Combination is a selection of k elements from a set with n elements, such that order of
/// elements does not matter.
///
/// Number of combinations equals to the corresponding binomial coefficient.
///
/// ```
/// use astraea::combinatorics::combinations;
/// use astraea::natural::NaturalNumber;
///
/// let n = NaturalNumber::from(20_u8);
/// let k = NaturalNumber::from(3_u8);
/// let c = combinations(&n, &k);
///
/// assert_eq!(c, NaturalNumber::from(1140_u16));
/// ```
pub fn combinations(n: &NaturalNumber, k: &NaturalNumber) -> NaturalNumber {
    let mut res = NaturalNumber::one();
    let mut numerator = n.clone();

    let k = match n.clone() - k.clone() {
        Ok(v) => k.to_owned().min(v),
        Err(..) => return NaturalNumber::zero(),
    };

    let mut denominator = NaturalNumber::one();

    while denominator <= k {
        res = (res * numerator.clone()).div(denominator.clone()).unwrap();
        denominator = denominator.inc();
        numerator = numerator.sub(NaturalNumber::one()).unwrap();
    }

    res
}

#[cfg(test)]
mod tests {
    use std::ops::Div;

    use super::combinations;
    use crate::combinatorics::factorial;
    use crate::natural::NaturalNumber;

    #[test]
    fn test_combinations() {
        let tests = vec![
            ((0_usize, 0_usize), "1"),
            ((5, 0), "1"),
            ((5, 1), "5"),
            ((5, 2), "10"),
            ((5, 3), "10"),
            ((5, 4), "5"),
            ((5, 5), "1"),
            ((10, 0), "1"),
            ((10, 1), "10"),
            ((10, 5), "252"),
            ((10, 10), "1"),
            ((20, 1), "20"),
            ((20, 10), "184756"),
            ((20, 20), "1"),
            ((1000000000000, 1), "1000000000000"),
        ];

        for ((n, k), expected) in tests {
            let n_val = NaturalNumber::from(n);
            let k_val = NaturalNumber::from(k);
            let actual = combinations(&n_val, &k_val);
            assert_eq!(actual.to_string(), expected);
        }
    }

    #[test]
    fn test_combinations_against_formula() {
        for n in 0u8..=15 {
            for k in 0u8..=n {
                let n_val = NaturalNumber::from(n);
                let k_val = NaturalNumber::from(k);

                let actual = combinations(&n_val.clone(), &k_val.clone());

                let fact_n = factorial(&n_val);
                let fact_k = factorial(&k_val);
                let n_minus_k = n_val.clone() - k_val.clone();
                let fact_n_minus_k = factorial(&n_minus_k.unwrap());

                let denom = fact_k * fact_n_minus_k;
                let expected = fact_n.div(denom).unwrap();

                assert_eq!(actual, expected,);
            }
        }
    }
}
