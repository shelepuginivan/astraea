use std::mem;

use crate::algebra::{AddWithIdentity, MulWithIdentity};
use crate::natural::Natural;

/// Calculates Stirling number of the first kind (unsigned).
///
/// Stirling numbers of the first kind equals to the number of permutations of n elements into k
/// cycles.
///
/// ```
/// use astraea::combinatorics::stirling_first_kind;
/// use astraea::natural::Natural;
///
/// let n = Natural::from(5_u8);
/// let k = Natural::from(3_u8);
/// let p = stirling_first_kind(&n, &k);
///
/// assert_eq!(p, Natural::from(35_u8));
/// ```
///
/// Panics if n or k cannot be converted to usize.
pub fn stirling_first_kind(n: &Natural, k: &Natural) -> Natural {
    if n.is_zero() && k.is_zero() || n == k {
        return Natural::one();
    }

    if k > n || n.is_zero() || k.is_zero() {
        return Natural::zero();
    }

    let n: usize = n.clone().try_into().expect("value is too large");
    let k: usize = k.clone().try_into().expect("value is too large");

    let mut current_row = vec![Natural::zero(); n + 1];
    current_row[0] = Natural::one();

    for i in 1..=n {
        for k in (0..i + 1).rev() {
            if k == 0 {
                current_row[k] = Natural::zero();
                continue;
            }

            let prev = mem::replace(&mut current_row[k], Natural::zero());
            let row_index = Natural::from(i - 1);
            current_row[k] = current_row[k - 1].clone() + prev * row_index;
        }
    }

    current_row.swap_remove(k)
}

/// Returns nth row of the triangular array representation of the Stirling numbers of the second
/// kind.
fn stirling_second_kind_nth_row(n: usize) -> Vec<Natural> {
    let mut current_row = vec![Natural::zero(); n + 1];
    current_row[0] = Natural::one();

    for i in 1..=n {
        for k in (0..i + 1).rev() {
            if k == 0 {
                current_row[k] = Natural::zero();
                continue;
            }

            let prev = mem::replace(&mut current_row[k], Natural::zero());
            let col_index = Natural::from(k);
            current_row[k] = current_row[k - 1].clone() + prev * col_index;
        }
    }

    current_row
}

/// Calculates Stirling number of the second kind.
///
/// Stirling numbers of the second kind equals to the number of ways to partition a set with n
/// elements into k non-empty subsets.
///
/// ```
/// use astraea::combinatorics::stirling_second_kind;
/// use astraea::natural::Natural;
///
/// let n = Natural::from(6_u8);
/// let k = Natural::from(2_u8);
/// let p = stirling_second_kind(&n, &k);
///
/// assert_eq!(p, Natural::from(31_u8));
/// ```
///
/// Panics if n or k cannot be converted to usize.
pub fn stirling_second_kind(n: &Natural, k: &Natural) -> Natural {
    if n.is_zero() && k.is_zero() || n == k {
        return Natural::one();
    }

    if k > n || n.is_zero() || k.is_zero() {
        return Natural::zero();
    }

    let n: usize = n.clone().try_into().expect("value is too large");
    let k: usize = k.clone().try_into().expect("value is too large");

    stirling_second_kind_nth_row(n).swap_remove(k)
}

/// Calculates nth Bell number.
///
/// Bell number is the number of partitions of a set with n elements.
///
/// ```
/// use astraea::combinatorics::bell;
/// use astraea::natural::Natural;
///
/// let n = Natural::from(6_u8);
/// let b = bell(&n);
///
/// assert_eq!(b, Natural::from(203_u8));
/// ```
///
/// Panics if n cannot be converted to usize.
pub fn bell(n: &Natural) -> Natural {
    let n: usize = n.clone().try_into().expect("value is too large");
    let mut res = Natural::zero();

    for v in stirling_second_kind_nth_row(n).into_iter() {
        res = res + v;
    }

    res
}

#[cfg(test)]
mod tests {
    use crate::natural::Natural;

    use super::*;

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
                let n = Natural::from(n);
                let k = Natural::from(k);

                let expected = Natural::from(expected);
                let actual = stirling_first_kind(&n, &k);

                assert_eq!(actual, expected, "mismatch for n={}, k={}", n, k);
            }
        }
    }

    #[test]
    fn test_stirling_second_kind() {
        #[rustfmt::skip]
        let tests = vec![
            vec![1_usize],
            vec![0, 1],
            vec![0, 1, 1],
            vec![0, 1, 3,   1],
            vec![0, 1, 7,   6,    1],
            vec![0, 1, 15,  25,   10,    1],
            vec![0, 1, 31,  90,   65,    15,    1],
            vec![0, 1, 63,  301,  350,   140,   21,    1],
            vec![0, 1, 127, 966,  1701,  1050,  266,   28,   1],
            vec![0, 1, 255, 3025, 7770,  6951,  2646,  462,  36,  1],
            vec![0, 1, 511, 9330, 34105, 42525, 22827, 5880, 750, 45, 1],
        ];

        for (n, row) in tests.into_iter().enumerate() {
            for (k, expected) in row.into_iter().enumerate() {
                let n = Natural::from(n);
                let k = Natural::from(k);

                let expected = Natural::from(expected);
                let actual = stirling_second_kind(&n, &k);

                assert_eq!(actual, expected, "mismatch for n={}, k={}", n, k);
            }
        }
    }

    #[test]
    fn test_bell() {
        let tests: Vec<usize> = vec![
            1, 1, 2, 5, 15, 52, 203, 877, 4140, 21147, 115975, 678570, 4213597, 27644437,
        ];

        for (n, expected) in tests.into_iter().enumerate() {
            let n = Natural::from(n);

            let expected = Natural::from(expected);
            let actual = bell(&n);

            assert_eq!(actual, expected);
        }
    }
}
