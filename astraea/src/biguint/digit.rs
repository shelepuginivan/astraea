use std::str::FromStr;

use crate::error::ParseError;

/// Represents a digit in base-4294967296 (u32) numbering system.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Digit(pub u32);

impl Digit {
    /// Bit depth of the digit.
    const BIT_DEPTH: u8 = 32;

    /// Bit mask for lower u32 of u64 value.
    const LOW_MASK: u64 = 0x00000000_ffffffff;

    pub const ZERO: Self = Self(0);
    pub const ONE: Self = Self(1);

    /// Splits u64 into low 32 bits and high 32 bits, producing two digits. The first returned
    /// value is low 32-bit digit, the second is high 32-bit digit.
    ///
    /// ```
    /// use astraea::natural::Digit;
    ///
    /// let (lo, hi) = Digit::low_high(0x12345678_87654321);
    ///
    /// assert_eq!(lo, Digit(0x87654321));
    /// assert_eq!(hi, Digit(0x12345678));
    /// ```
    pub fn low_high(value: u64) -> (Self, Self) {
        let lo = value & Self::LOW_MASK;
        let hi = value >> Self::BIT_DEPTH;

        (Digit(lo as u32), Digit(hi as u32))
    }

    /// Concatenates 32 bits of the first digit with 32 bits of the second digit, producing 64-bit
    /// unsigned integer.
    ///
    /// ```
    /// use astraea::natural::Digit;
    ///
    /// let lo = Digit(0x87654321);
    /// let hi = Digit(0x12345678);
    ///
    /// assert_eq!(hi.concat(lo), 0x12345678_87654321);
    /// ```
    pub fn concat(self, other: Self) -> u64 {
        (self.0 as u64) << 32 | other.0 as u64
    }

    /// Add two digits. The first returned value is the digit in the same position, and the second
    /// is the carry digit.
    ///
    /// ```
    /// use astraea::natural::Digit;
    ///
    /// let (result, carry) = Digit(u32::MAX).carrying_add(Digit(1));
    ///
    /// assert_eq!(result, Digit(0));
    /// assert_eq!(carry, Digit(1));
    /// ```
    pub fn carrying_add(self, rhs: Self) -> (Self, Self) {
        let sum = self.0 as u64 + rhs.0 as u64;
        Self::low_high(sum)
    }

    /// Add a digit to this digit in place, returning the carry.
    ///
    /// ```
    /// use astraea::natural::Digit;
    ///
    /// let mut digit = Digit(u32::MAX);
    /// let carry = digit.carrying_add_mut(Digit(1));
    ///
    /// assert_eq!(digit, Digit(0));
    /// assert_eq!(carry, Digit(1));
    /// ```
    pub fn carrying_add_mut(&mut self, rhs: Self) -> Self {
        let sum = self.0 as u64 + rhs.0 as u64;
        let low = sum & Self::LOW_MASK;
        let high = sum >> Self::BIT_DEPTH;

        self.0 = low as u32;
        Self(high as u32)
    }

    /// Subtract second digit from first. The first returned value is the digit in the same
    /// position, and the second is the carry digit.
    ///
    /// ```
    /// use astraea::natural::Digit;
    ///
    /// let (result, carry) = Digit(0).carrying_sub(Digit(1));
    ///
    /// assert_eq!(result, Digit(u32::MAX));
    /// assert_eq!(carry, Digit(1));
    /// ```
    pub fn carrying_sub(self, rhs: Self) -> (Self, Self) {
        if self.0 >= rhs.0 {
            return (Self(self.0 - rhs.0), Self::ZERO);
        }

        let result = self.0.wrapping_sub(rhs.0);
        (Self(result), Self::ONE)
    }

    /// Subtract a digit from this digit in place, returning the borrow.
    ///
    /// ```
    /// use astraea::natural::Digit;
    ///
    /// let mut digit = Digit(0);
    /// let borrow = digit.carrying_sub_mut(Digit(1));
    ///
    /// assert_eq!(digit, Digit(u32::MAX));
    /// assert_eq!(borrow, Digit::ONE);
    /// ```
    pub fn carrying_sub_mut(&mut self, rhs: Self) -> Self {
        if self.0 >= rhs.0 {
            self.0 -= rhs.0;
            return Self::ZERO;
        }

        self.0 = self.0.wrapping_sub(rhs.0);
        Self::ONE
    }

    /// Multiply two digits. The first returned value is the digit in the same position, and the
    /// second is the carry digit.
    ///
    /// ```
    /// use astraea::natural::Digit;
    ///
    /// let (result, carry) = Digit(u32::MAX).carrying_mul(Digit(2));
    ///
    /// assert_eq!(result, Digit(u32::MAX - 1));
    /// assert_eq!(carry, Digit(1));
    /// ```
    pub fn carrying_mul(self, rhs: Self) -> (Self, Self) {
        let product = self.0 as u64 * rhs.0 as u64;
        Self::low_high(product)
    }

    /// Multiply this digit by another in place, returning the carry.
    ///
    /// ```
    /// use astraea::natural::Digit;
    ///
    /// let mut digit = Digit(0x80000000); // 2^31
    /// let carry = digit.carrying_mul_mut(Digit(2));
    ///
    /// assert_eq!(digit, Digit(0));
    /// assert_eq!(carry, Digit(1));
    /// ```
    pub fn carrying_mul_mut(&mut self, rhs: Self) -> Self {
        let product = self.0 as u64 * rhs.0 as u64;
        let low = product & Self::LOW_MASK;
        let high = product >> Self::BIT_DEPTH;

        self.0 = low as u32;
        Self(high as u32)
    }
}

impl FromStr for Digit {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match u32::from_str(s) {
            Ok(v) => Ok(Digit(v)),
            Err(..) => Err(ParseError::new(format!(
                "'{}' is not a valid base-u32 digit",
                s
            ))),
        }
    }
}

#[cfg(test)]
mod tests {
    use rand::Rng;

    use super::*;

    const RANDOM_TEST_COUNT: usize = 1000;

    #[test]
    fn test_digit_from_str() {
        let mut rng = rand::rng();

        for _ in 0..RANDOM_TEST_COUNT {
            let v: u32 = rng.random();
            let s = v.to_string();
            let expected = Digit(v);
            let actual = Digit::from_str(&s).unwrap();

            assert_eq!(actual, expected);
        }

        assert!(Digit::from_str(&"1".repeat(100)).is_err());
        assert!(Digit::from_str("not numeric").is_err());
    }

    #[test]
    fn test_digit_low_high() {
        let mut rng = rand::rng();

        for _ in 0..RANDOM_TEST_COUNT {
            let v: u64 = rng.random();
            let expected_high = (v >> 32) as u32;
            let expected_low = v as u32;

            let (actual_low, actual_high) = Digit::low_high(v);

            assert_eq!(actual_low, Digit(expected_low));
            assert_eq!(actual_high, Digit(expected_high));
        }
    }

    #[test]
    fn test_digit_concat() {
        let mut rng = rand::rng();

        for _ in 0..RANDOM_TEST_COUNT {
            let lo: u32 = rng.random();
            let hi: u32 = rng.random();

            let expected = (lo as u64) | (hi as u64) << 32;
            let actual = Digit(hi).concat(Digit(lo));

            assert_eq!(actual, expected);
        }
    }

    #[test]
    fn test_digit_carrying_add() {
        let mut rng = rand::rng();

        for _ in 0..RANDOM_TEST_COUNT {
            let a: u32 = rng.random();
            let b: u32 = rng.random();

            let (result, carry) = Digit(a).carrying_add(Digit(b));

            let expected_sum = a as u64 + b as u64;
            let expected_result = (expected_sum & 0xFFFFFFFF) as u32;
            let expected_carry = (expected_sum >> 32) as u32;

            assert_eq!(result, Digit(expected_result));
            assert_eq!(carry, Digit(expected_carry));
        }

        let (result, carry) = Digit(u32::MAX).carrying_add(Digit(1));
        assert_eq!(result, Digit(0));
        assert_eq!(carry, Digit(1));

        let (result, carry) = Digit(u32::MAX).carrying_add(Digit(u32::MAX));
        assert_eq!(result, Digit(u32::MAX - 1));
        assert_eq!(carry, Digit(1));
    }

    #[test]
    fn test_digit_carrying_add_mut() {
        let mut rng = rand::rng();

        for _ in 0..RANDOM_TEST_COUNT {
            let a: u32 = rng.random();
            let b: u32 = rng.random();

            let mut digit = Digit(a);
            let carry = digit.carrying_add_mut(Digit(b));

            let expected_sum = a as u64 + b as u64;
            let expected_digit = (expected_sum & 0xFFFFFFFF) as u32;
            let expected_carry = (expected_sum >> 32) as u32;

            assert_eq!(digit, Digit(expected_digit));
            assert_eq!(carry, Digit(expected_carry));
        }

        let mut digit = Digit(u32::MAX);
        let carry = digit.carrying_add_mut(Digit(1));
        assert_eq!(digit, Digit(0));
        assert_eq!(carry, Digit(1));

        let mut digit = Digit(0);
        let carry = digit.carrying_add_mut(Digit(0));
        assert_eq!(digit, Digit(0));
        assert_eq!(carry, Digit(0));
    }

    #[test]
    fn test_digit_carrying_sub() {
        let mut rng = rand::rng();

        for _ in 0..RANDOM_TEST_COUNT {
            let a: u32 = rng.random();
            let b: u32 = rng.random();

            let (result, carry) = Digit(a).carrying_sub(Digit(b));

            if a >= b {
                assert_eq!(result, Digit(a - b));
                assert_eq!(carry, Digit(0));
            } else {
                let expected_result = a.wrapping_sub(b);
                assert_eq!(result, Digit(expected_result));
                assert_eq!(carry, Digit(1));
            }
        }

        let (result, carry) = Digit(0).carrying_sub(Digit(1));
        assert_eq!(result, Digit(u32::MAX));
        assert_eq!(carry, Digit(1));

        let (result, carry) = Digit(100).carrying_sub(Digit(100));
        assert_eq!(result, Digit(0));
        assert_eq!(carry, Digit(0));

        let (result, carry) = Digit(0).carrying_sub(Digit(0));
        assert_eq!(result, Digit(0));
        assert_eq!(carry, Digit(0));
    }

    #[test]
    fn test_digit_carrying_sub_mut() {
        let mut rng = rand::rng();

        for _ in 0..RANDOM_TEST_COUNT {
            let a: u32 = rng.random();
            let b: u32 = rng.random();

            let mut digit = Digit(a);
            let borrow = digit.carrying_sub_mut(Digit(b));

            if a >= b {
                assert_eq!(digit, Digit(a - b));
                assert_eq!(borrow, Digit::ZERO);
            } else {
                let expected_digit = a.wrapping_sub(b);
                assert_eq!(digit, Digit(expected_digit));
                assert_eq!(borrow, Digit::ONE);
            }
        }

        let mut digit = Digit(0);
        let borrow = digit.carrying_sub_mut(Digit(1));
        assert_eq!(digit, Digit(u32::MAX));
        assert_eq!(borrow, Digit::ONE);

        let mut digit = Digit(100);
        let borrow = digit.carrying_sub_mut(Digit(100));
        assert_eq!(digit, Digit(0));
        assert_eq!(borrow, Digit::ZERO);

        let mut digit = Digit(u32::MAX);
        let borrow = digit.carrying_sub_mut(Digit(u32::MAX));
        assert_eq!(digit, Digit(0));
        assert_eq!(borrow, Digit::ZERO);
    }

    #[test]
    fn test_digit_carrying_mul() {
        let mut rng = rand::rng();

        for _ in 0..RANDOM_TEST_COUNT {
            let a: u32 = rng.random();
            let b: u32 = rng.random();

            let (result, carry) = Digit(a).carrying_mul(Digit(b));

            let expected_product = a as u64 * b as u64;
            let expected_result = (expected_product & 0xFFFFFFFF) as u32;
            let expected_carry = (expected_product >> 32) as u32;

            assert_eq!(result, Digit(expected_result));
            assert_eq!(carry, Digit(expected_carry));
        }

        let (result, carry) = Digit(u32::MAX).carrying_mul(Digit(1));
        assert_eq!(result, Digit(u32::MAX));
        assert_eq!(carry, Digit(0));

        let (result, carry) = Digit(u32::MAX).carrying_mul(Digit(2));
        assert_eq!(result, Digit(u32::MAX - 1));
        assert_eq!(carry, Digit(1));

        let (result, carry) = Digit(0).carrying_mul(Digit(u32::MAX));
        assert_eq!(result, Digit(0));
        assert_eq!(carry, Digit(0));
    }

    #[test]
    fn test_digit_carrying_mul_mut() {
        let mut rng = rand::rng();

        for _ in 0..RANDOM_TEST_COUNT {
            let a: u32 = rng.random();
            let b: u32 = rng.random();

            let mut digit = Digit(a);
            let carry = digit.carrying_mul_mut(Digit(b));

            let expected_product = a as u64 * b as u64;
            let expected_digit = (expected_product & 0xFFFFFFFF) as u32;
            let expected_carry = (expected_product >> 32) as u32;

            assert_eq!(digit, Digit(expected_digit));
            assert_eq!(carry, Digit(expected_carry));
        }

        let mut digit = Digit(u32::MAX);
        let carry = digit.carrying_mul_mut(Digit(1));
        assert_eq!(digit, Digit(u32::MAX));
        assert_eq!(carry, Digit(0));

        let mut digit = Digit(0);
        let carry = digit.carrying_mul_mut(Digit(u32::MAX));
        assert_eq!(digit, Digit(0));
        assert_eq!(carry, Digit(0));

        let mut digit = Digit(0x80000000); // 2^31
        let carry = digit.carrying_mul_mut(Digit(2));
        assert_eq!(digit, Digit(0));
        assert_eq!(carry, Digit(1));
    }
}
