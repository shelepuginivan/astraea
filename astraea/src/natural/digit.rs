use crate::error::ParseError;
use std::str::FromStr;

/// Represents a digit in base-4294967296 (u32) numbering system.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Digit(pub u32);

impl Digit {
    /// Bit depth of the digit.
    const BIT_DEPTH: u8 = 32;

    /// Bit mask for lower u32 of u64 value.
    const LOW_MASK: u64 = 0x00000000_FFFFFFFF;

    pub const ZERO: Self = Self(0);
    pub const ONE: Self = Self(1);

    /// Value of the digit.
    pub fn value(&self) -> u32 {
        self.0
    }

    pub fn low_high(value: u64) -> (Self, Self) {
        let lo = value & Self::LOW_MASK;
        let hi = value >> Self::BIT_DEPTH;

        (Digit(lo as u32), Digit(hi as u32))
    }

    /// Add two digits. The first returned value is the digit in the same position, and the second
    /// is the carry digit.
    pub fn carrying_add(self, rhs: Self) -> (Self, Self) {
        let sum = self.0 as u64 + rhs.0 as u64;
        let low = sum & Self::LOW_MASK;
        let high = sum >> Self::BIT_DEPTH;

        (Self(low as u32), Self(high as u32))
    }

    /// Subtract second digit from first. The first returned value is the digit in the same
    /// position, and the second is the carry digit.
    pub fn carrying_sub(self, rhs: Self) -> (Self, Self) {
        if self.0 >= rhs.0 {
            return (Self(self.0 - rhs.0), Self(0));
        }

        let result = self.0.wrapping_sub(rhs.0);
        (Self(result), Self(1))
    }

    /// Multiply two digits. The first returned value is the digit in the same position, and the
    /// second is the carry digit.
    pub fn carrying_mul(self, rhs: Self) -> (Self, Self) {
        let product = self.0 as u64 * rhs.0 as u64;
        let low = product & Self::LOW_MASK;
        let high = product >> Self::BIT_DEPTH;

        (Self(low as u32), Self(high as u32))
    }

    /// Divides second digit from first. The first returned value is the digit in the same
    /// position, and the second is the carry digit.
    pub fn carrying_div(self, rhs: Self) -> (Self, Self) {
        let dividend = self.0 as u64;
        let divisor = rhs.0 as u64;

        let quotient = dividend / divisor;
        let remainder = dividend % divisor;

        (Self(quotient as u32), Self(remainder as u32))
    }
}

impl FromStr for Digit {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match u32::from_str(s) {
            Ok(v) => Ok(Digit(v)),
            Err(..) => Err(ParseError::new("")),
        }
    }
}

//#[cfg(test)]
//mod tests {
//    use super::*;
//    use std::cmp::Ordering;
//
//    #[test]
//    fn test_digit_new() {
//        assert_eq!(Digit::new(0).unwrap(), Digit::Zero);
//        assert_eq!(Digit::new(1).unwrap(), Digit::One);
//        assert_eq!(Digit::new(2).unwrap(), Digit::Two);
//        assert_eq!(Digit::new(3).unwrap(), Digit::Three);
//        assert_eq!(Digit::new(4).unwrap(), Digit::Four);
//        assert_eq!(Digit::new(5).unwrap(), Digit::Five);
//        assert_eq!(Digit::new(6).unwrap(), Digit::Six);
//        assert_eq!(Digit::new(7).unwrap(), Digit::Seven);
//        assert_eq!(Digit::new(8).unwrap(), Digit::Eight);
//        assert_eq!(Digit::new(9).unwrap(), Digit::Nine);
//
//        assert!(Digit::new(28).is_err());
//    }
//
//    #[test]
//    fn test_digit_from_char() {
//        assert_eq!(Digit::from_char('0').unwrap(), Digit::Zero);
//        assert_eq!(Digit::from_char('1').unwrap(), Digit::One);
//        assert_eq!(Digit::from_char('2').unwrap(), Digit::Two);
//        assert_eq!(Digit::from_char('3').unwrap(), Digit::Three);
//        assert_eq!(Digit::from_char('4').unwrap(), Digit::Four);
//        assert_eq!(Digit::from_char('5').unwrap(), Digit::Five);
//        assert_eq!(Digit::from_char('6').unwrap(), Digit::Six);
//        assert_eq!(Digit::from_char('7').unwrap(), Digit::Seven);
//        assert_eq!(Digit::from_char('8').unwrap(), Digit::Eight);
//        assert_eq!(Digit::from_char('9').unwrap(), Digit::Nine);
//
//        assert!(Digit::from_char('a').is_err());
//    }
//
//    #[test]
//    fn test_digit_cmp() {
//        let lhs = Digit::new(9).unwrap();
//        let rhs = Digit::new(8).unwrap();
//        assert_eq!(lhs.cmp(&rhs), Ordering::Greater);
//
//        let lhs = Digit::new(3).unwrap();
//        let rhs = Digit::new(4).unwrap();
//        assert_eq!(lhs.cmp(&rhs), Ordering::Less);
//
//        let lhs = Digit::new(6).unwrap();
//        let rhs = Digit::new(6).unwrap();
//        assert_eq!(lhs.cmp(&rhs), Ordering::Equal);
//    }
//
//    #[test]
//    fn test_digit_macro() {
//        for v in 0..10 {
//            assert_eq!(digit!(v), Digit::new(v).unwrap())
//        }
//
//        assert_eq!(digit!(0), Digit::Zero);
//        assert_eq!(digit!(1), Digit::One);
//        assert_eq!(digit!(2), Digit::Two);
//        assert_eq!(digit!(3), Digit::Three);
//        assert_eq!(digit!(4), Digit::Four);
//        assert_eq!(digit!(5), Digit::Five);
//        assert_eq!(digit!(6), Digit::Six);
//        assert_eq!(digit!(7), Digit::Seven);
//        assert_eq!(digit!(8), Digit::Eight);
//        assert_eq!(digit!(9), Digit::Nine);
//    }
//
//    #[test]
//    fn test_digit_add() {
//        for lhs in 0..10 {
//            for rhs in 0..10 {
//                let expected_res: Digit = ((lhs + rhs) % 10).try_into().unwrap();
//                let expected_carry: Digit = ((lhs + rhs) / 10).try_into().unwrap();
//
//                let lhs: Digit = lhs.try_into().unwrap();
//                let rhs: Digit = rhs.try_into().unwrap();
//
//                let (actual_res, actual_carry) = lhs + rhs;
//
//                assert_eq!(actual_res, expected_res);
//                assert_eq!(actual_carry, expected_carry);
//            }
//        }
//    }
//
//    #[test]
//    fn test_digit_div() {
//        for lhs in 0..10 {
//            for rhs in 1..10 {
//                let expected: Digit = (lhs / rhs).try_into().unwrap();
//
//                let lhs: Digit = lhs.try_into().unwrap();
//                let rhs: Digit = rhs.try_into().unwrap();
//
//                let actual = lhs / rhs;
//
//                assert_eq!(actual, expected);
//            }
//        }
//    }
//
//    #[test]
//    fn test_format() {
//        assert_eq!(Digit::Zero.to_string(), "0");
//        assert_eq!(Digit::One.to_string(), "1");
//        assert_eq!(Digit::Two.to_string(), "2");
//        assert_eq!(Digit::Three.to_string(), "3");
//        assert_eq!(Digit::Four.to_string(), "4");
//        assert_eq!(Digit::Five.to_string(), "5");
//        assert_eq!(Digit::Six.to_string(), "6");
//        assert_eq!(Digit::Seven.to_string(), "7");
//        assert_eq!(Digit::Eight.to_string(), "8");
//        assert_eq!(Digit::Nine.to_string(), "9");
//
//        assert_eq!(Digit::Zero.prettify(), "0");
//        assert_eq!(Digit::One.prettify(), "1");
//        assert_eq!(Digit::Two.prettify(), "2");
//        assert_eq!(Digit::Three.prettify(), "3");
//        assert_eq!(Digit::Four.prettify(), "4");
//        assert_eq!(Digit::Five.prettify(), "5");
//        assert_eq!(Digit::Six.prettify(), "6");
//        assert_eq!(Digit::Seven.prettify(), "7");
//        assert_eq!(Digit::Eight.prettify(), "8");
//        assert_eq!(Digit::Nine.prettify(), "9");
//    }
//
//    #[test]
//    fn test_from_str() {
//        assert_eq!(Digit::from_str("0").unwrap(), Digit::Zero);
//        assert_eq!(Digit::from_str("1").unwrap(), Digit::One);
//        assert_eq!(Digit::from_str("2").unwrap(), Digit::Two);
//        assert_eq!(Digit::from_str("3").unwrap(), Digit::Three);
//        assert_eq!(Digit::from_str("4").unwrap(), Digit::Four);
//        assert_eq!(Digit::from_str("5").unwrap(), Digit::Five);
//        assert_eq!(Digit::from_str("6").unwrap(), Digit::Six);
//        assert_eq!(Digit::from_str("7").unwrap(), Digit::Seven);
//        assert_eq!(Digit::from_str("8").unwrap(), Digit::Eight);
//        assert_eq!(Digit::from_str("9").unwrap(), Digit::Nine);
//
//        assert!(Digit::from_str("").is_err());
//        assert!(Digit::from_str("123").is_err());
//        assert!(Digit::from_str("a").is_err());
//    }
//}
