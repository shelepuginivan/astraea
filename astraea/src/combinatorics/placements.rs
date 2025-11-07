use crate::algebra::{AddWithIdentity, MulWithIdentity};
use crate::natural::NaturalNumber;

/// Calculates number of placements, or partial permutations of set with n elements into sequences
/// of k elements, such that order of elements matters.
///
/// ```
/// use astraea::combinatorics::placements;
/// use astraea::natural::NaturalNumber;
///
/// let n = NaturalNumber::from(5_u8);
/// let k = NaturalNumber::from(3_u8);
/// let p = placements(&n, &k);
///
/// assert_eq!(p, NaturalNumber::from(60_u8));
/// ```
pub fn placements(n: &NaturalNumber, k: &NaturalNumber) -> NaturalNumber {
    if n < k {
        return NaturalNumber::zero();
    }

    let mut multiplier = (n.clone() - k.clone()).unwrap() + NaturalNumber::one();
    let mut res = NaturalNumber::one();

    while multiplier <= *n {
        res = res * multiplier.clone();
        multiplier = multiplier.inc();
    }

    res
}

#[cfg(test)]
mod tests {
    use std::ops::Div;

    use super::*;
    use crate::combinatorics::factorial;

    #[test]
    fn test_placements() {
        let tests = vec![
            ((0_u8, 0_u8), "1"),
            ((5, 0), "1"),
            ((5, 1), "5"),
            ((5, 2), "20"),
            ((5, 3), "60"),
            ((5, 4), "120"),
            ((5, 5), "120"),
            ((10, 0), "1"),
            ((10, 1), "10"),
            ((10, 5), "30240"),
            ((10, 10), "3628800"),
            ((20, 1), "20"),
            ((20, 10), "670442572800"),
            ((20, 20), "2432902008176640000"),
        ];

        for ((n, k), expected) in tests {
            let n_val = NaturalNumber::from(n);
            let k_val = NaturalNumber::from(k);
            let actual = placements(&n_val, &k_val);
            assert_eq!(actual.to_string(), expected);
        }
    }

    #[test]
    fn test_placements_against_formula() {
        for n in 0u8..=15 {
            for k in 0u8..=n {
                let n_val = NaturalNumber::from(n);
                let k_val = NaturalNumber::from(k);

                let actual = placements(&n_val.clone(), &k_val.clone());

                let fact_n = factorial(&n_val);
                let n_minus_k = n_val.clone() - k_val.clone();
                let fact_n_minus_k = factorial(&n_minus_k.unwrap());

                let expected = fact_n.div(fact_n_minus_k).unwrap();

                assert_eq!(actual, expected);
            }
        }
    }
}
