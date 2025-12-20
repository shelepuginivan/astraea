use crate::combinatorics::combinations;
use crate::natural::Natural;

/// Returns the n-th k-dimensional simplex (k-simplex) number.
///
/// A k-dimensional simplex number generalizes triangular and tetrahedral numbers to arbitrary
/// dimensions. It represents the number of points that can be arranged in a k-dimensional simplex
/// of size n.
///
/// k-th diagonal of the Pascal Triangle consists of k-simplex numbers.
///
/// Both `n` and `k` are 0-indexed:
/// - `n = 0` gives the smallest simplex (a single point).
/// - `k = 0` gives the sequence of ones (0-dimensional simplexes).
///
/// ```
/// use astraea::combinatorics::simplex;
/// use astraea::natural::Natural;
///
/// let n = Natural::from(3_u8);
/// let k = Natural::from(2_u8);
///
/// let s = simplex(&k, &n);    // 1, 3, 6, [10]
///
/// assert_eq!(s, Natural::from(10_u8));
/// ```
pub fn simplex(k: &Natural, n: &Natural) -> Natural {
    combinations(&(n.clone() + k.clone()), k)
}

#[cfg(test)]
mod tests {
    use crate::natural::Natural;

    use super::*;

    #[test]
    fn test_simplex() {
        #[rustfmt::skip]
        let tests: Vec<Vec<usize>> = vec![
            vec![1, 1,  1,  1,  1,   1,   1,   1],
            vec![1, 2,  3,  4,  5,   6,   7,   8],
            vec![1, 3,  6, 10, 15,  21,  28,  36],
            vec![1, 4, 10, 20, 35,  56,  84, 120],
            vec![1, 5, 15, 35, 70, 126, 210, 330],
        ];

        for (k, row) in tests.into_iter().enumerate() {
            for (n, expected) in row.into_iter().enumerate() {
                let k = Natural::from(k);
                let n = Natural::from(n);

                let expected = Natural::from(expected);
                let actual = simplex(&k, &n);

                assert_eq!(actual, expected, "mismatch for n={}, k={}", n, k);
            }
        }
    }
}
