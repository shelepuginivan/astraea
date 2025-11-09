use crate::algebra::{AddWithIdentity, MulWithIdentity};
use crate::natural::Natural;

/// Calculates subfactorial of n.
///
/// Subfactorial represents number of derangements of a set with n elements.
///
/// ```
/// use astraea::combinatorics::subfactorial;
/// use astraea::natural::Natural;
///
/// let n = Natural::from(8_u8);
/// let n_subfactorial = subfactorial(&n);
///
/// assert_eq!(n_subfactorial, Natural::from(14833_u16));
/// ```
pub fn subfactorial(n: &Natural) -> Natural {
    if n.is_zero() {
        return Natural::one();
    }

    if n.is_one() {
        return Natural::zero();
    }

    let mut prev = Natural::one();
    let mut curr = Natural::zero();
    let mut multiplier = Natural::from(1_u8);

    while &multiplier < n {
        let prev_tmp = curr.clone();
        curr = multiplier.clone() * (curr + prev);
        prev = prev_tmp;
        multiplier = multiplier.inc()
    }

    curr
}

#[cfg(test)]
mod tests {
    use super::subfactorial;
    use crate::natural::Natural;

    #[test]
    fn test_subfactorial() {
        let tests = vec![
            (0_u8, "1"),
            (1, "0"),
            (2, "1"),
            (3, "2"),
            (4, "9"),
            (5, "44"),
            (6, "265"),
            (7, "1854"),
            (8, "14833"),
            (9, "133496"),
            (10, "1334961"),
            (11, "14684570"),
            (12, "176214841"),
            (13, "2290792932"),
            (14, "32071101049"),
            (15, "481066515734"),
            (16, "7697064251745"),
            (17, "130850092279664"),
            (18, "2355301661033953"),
            (19, "44750731559645106"),
            (20, "895014631192902121"),
        ];

        for (v, expected) in tests {
            let value = Natural::from(v);
            let actual = subfactorial(&value);

            assert_eq!(actual.to_string(), expected);
        }
    }
}
