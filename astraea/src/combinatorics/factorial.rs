use crate::algebra::MulWithIdentity;
use crate::natural::Natural;

/// Calculates factorial of n.
///
/// > n! = 1 * 2 * ... * n
///
/// ```
/// use astraea::combinatorics::factorial;
/// use astraea::natural::Natural;
///
/// let n = Natural::from(7_u8);
/// let n_factorial = factorial(&n);
///
/// assert_eq!(n_factorial, Natural::from(5040_u16));
/// ```
pub fn factorial(n: &Natural) -> Natural {
    let mut result = Natural::one();
    let mut multiplier = Natural::from(2_u8);

    while multiplier <= *n {
        result = result * multiplier.clone();
        multiplier = multiplier.inc();
    }

    result
}

#[cfg(test)]
mod tests {
    use crate::natural::Natural;

    use super::factorial;

    #[test]
    fn test_factorial() {
        let tests = vec![
            (0_u8, "1"),
            (1, "1"),
            (2, "2"),
            (3, "6"),
            (4, "24"),
            (5, "120"),
            (6, "720"),
            (7, "5040"),
            (8, "40320"),
            (9, "362880"),
            (10, "3628800"),
            (11, "39916800"),
            (12, "479001600"),
            (13, "6227020800"),
            (14, "87178291200"),
            (15, "1307674368000"),
            (16, "20922789888000"),
            (17, "355687428096000"),
            (18, "6402373705728000"),
            (19, "121645100408832000"),
            (20, "2432902008176640000"),
        ];

        for (v, expected) in tests {
            let value = Natural::from(v);
            let actual = factorial(&value);

            assert_eq!(actual.to_string(), expected);
        }
    }
}
