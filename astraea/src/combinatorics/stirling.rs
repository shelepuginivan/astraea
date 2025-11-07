use std::mem;

use crate::algebra::{AddWithIdentity, MulWithIdentity};
use crate::natural::NaturalNumber;

/// Calculates Stirling number of first kind (unsigned).
///
/// Stirling numbers of first kind equals to thehe number of permutations of n elements into k
/// cycles.
///
/// ```
/// use astraea::combinatorics::stirling_first_kind;
/// use astraea::natural::NaturalNumber;
///
/// let n = NaturalNumber::from(5_u8);
/// let k = NaturalNumber::from(3_u8);
/// let p = stirling_first_kind(&n, &k);
///
/// assert_eq!(p, NaturalNumber::from(35_u8));
/// ```
///
/// Panics if n or k cannot be converted to usize.
pub fn stirling_first_kind(n: &NaturalNumber, k: &NaturalNumber) -> NaturalNumber {
    if n.is_zero() && k.is_zero() || n == k {
        return NaturalNumber::one();
    }

    if k > n || n.is_zero() || k.is_zero() {
        return NaturalNumber::zero();
    }

    let n: usize = n.clone().try_into().expect("value is too large");
    let k: usize = k.clone().try_into().expect("value is too large");

    let mut current_row = vec![NaturalNumber::zero(); n + 1];
    current_row[0] = NaturalNumber::one();

    for i in 1..=n {
        for k in (0..i + 1).rev() {
            if k == 0 {
                current_row[k] = NaturalNumber::zero();
                continue;
            }

            let prev = mem::replace(&mut current_row[k], NaturalNumber::zero());
            let row_index = NaturalNumber::from(i - 1);
            current_row[k] = current_row[k - 1].clone() + prev * row_index;
        }
    }

    current_row.swap_remove(k)
}

#[cfg(test)]
mod tests {
    use crate::natural::NaturalNumber;

    use super::stirling_first_kind;

    #[test]
    fn test_stirling_first_kind() {
        #[rustfmt::skip]
        let tests = vec![
            vec![1_usize],
            vec![0, 1],
            vec![0, 1,      1],
            vec![0, 2,      3,       1],
            vec![0, 6,      11,      6,       1],
            vec![0, 24,     50,      35,      10,     1],
            vec![0, 120,    274,     225,     85,     15,     1],
            vec![0, 720,    1764,    1624,    735,    175,    21,    1],
            vec![0, 5040,   13068,   13132,   6769,   1960,   322,   28,   1],
            vec![0, 40320,  109584,  118124,  67284,  22449,  4536,  546,  36,  1],
            vec![0, 362880, 1026576, 1172700, 723680, 269325, 63273, 9450, 870, 45, 1],
        ];

        for (n, row) in tests.into_iter().enumerate() {
            for (k, expected) in row.into_iter().enumerate() {
                let n = NaturalNumber::from(n);
                let k = NaturalNumber::from(k);

                let expected = NaturalNumber::from(expected);
                let actual = stirling_first_kind(&n, &k);

                assert_eq!(actual, expected, "mismatch for n={}, k={}", n, k);
            }
        }
    }
}
