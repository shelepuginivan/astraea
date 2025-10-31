use std::fmt::Display;
use std::i16;
use std::ops::{Add, Div, Mul, Sub};
use std::str::FromStr;

use crate::core::{ParseError, ValueError};
use crate::formatting::Pretty;

/// Creates a Digit from the argument.
#[macro_export]
macro_rules! digit {
    ($v:literal) => {
        Digit::try_from($v).unwrap()
    };
    ($v:expr) => {
        Digit::try_from($v).unwrap()
    };
}

/// Represents a single decimal digit of a natural number.
#[derive(Clone, Copy, Debug, Eq, PartialEq, PartialOrd, Ord)]
pub enum Digit {
    Zero,
    One,
    Two,
    Three,
    Four,
    Five,
    Six,
    Seven,
    Eight,
    Nine,
}

impl Digit {
    /// Creates a new instance of Digit. Value must be a valid decimal digit, i.e. in range [0, 9].
    ///
    /// ```
    /// use astraea::math::Digit;
    ///
    /// let d = Digit::new(9).unwrap();
    /// assert_eq!(d, Digit::Nine);
    /// ```
    pub fn new(value: u8) -> Result<Self, ValueError> {
        match value {
            0 => Ok(Digit::Zero),
            1 => Ok(Digit::One),
            2 => Ok(Digit::Two),
            3 => Ok(Digit::Three),
            4 => Ok(Digit::Four),
            5 => Ok(Digit::Five),
            6 => Ok(Digit::Six),
            7 => Ok(Digit::Seven),
            8 => Ok(Digit::Eight),
            9 => Ok(Digit::Nine),
            v => Err(ValueError::new(format!(
                "expected value to be in range [0, 9], got '{}'",
                v
            ))),
        }
    }

    /// Value of the digit.
    pub fn value(&self) -> u8 {
        match self {
            Self::Zero => 0,
            Digit::One => 1,
            Digit::Two => 2,
            Digit::Three => 3,
            Digit::Four => 4,
            Digit::Five => 5,
            Digit::Six => 6,
            Digit::Seven => 7,
            Digit::Eight => 8,
            Digit::Nine => 9,
        }
    }

    /// Parses Digit from char.
    ///
    /// ```
    /// use astraea::math::Digit;
    ///
    /// let d = Digit::from_char('7').unwrap();
    /// assert_eq!(d, Digit::Seven);
    /// ```
    pub fn from_char(char: char) -> Result<Self, ParseError> {
        match char {
            '0' => Ok(Digit::Zero),
            '1' => Ok(Digit::One),
            '2' => Ok(Digit::Two),
            '3' => Ok(Digit::Three),
            '4' => Ok(Digit::Four),
            '5' => Ok(Digit::Five),
            '6' => Ok(Digit::Six),
            '7' => Ok(Digit::Seven),
            '8' => Ok(Digit::Eight),
            '9' => Ok(Digit::Nine),
            chr => Err(ParseError::new(format!("'{}' is not a digit", chr))),
        }
    }

    /// Char representation of the digit.
    ///
    /// ```
    /// use astraea::math::Digit;
    ///
    /// assert_eq!(Digit::Four.char(), '4');
    /// ```
    pub fn char(&self) -> char {
        match self {
            Digit::Zero => '0',
            Digit::One => '1',
            Digit::Two => '2',
            Digit::Three => '3',
            Digit::Four => '4',
            Digit::Five => '5',
            Digit::Six => '6',
            Digit::Seven => '7',
            Digit::Eight => '8',
            Digit::Nine => '9',
        }
    }
}

impl Add for Digit {
    type Output = (Self, Self);

    /// Returns sum of two digits. The first returned value is the digit in the same position, and
    /// the second is the carry digit.
    ///
    /// ```
    /// use astraea::digit;
    /// use astraea::math::Digit;
    ///
    /// let lhs = digit!(6);
    /// let rhs = digit!(7);
    /// let (sum, carry) = lhs + rhs;
    ///
    /// assert_eq!(sum, digit!(3));
    /// assert_eq!(carry, digit!(1));
    /// ```
    fn add(self, rhs: Self) -> Self::Output {
        let sum = self.value() + rhs.value();
        let result = sum % 10;
        let carry = sum / 10;

        (digit!(result), digit!(carry))
    }
}

impl Sub for Digit {
    type Output = (Self, Self);

    /// Returns difference between two digits. The first returned value is the digit in the same
    /// position, and the second is the carry digit.
    ///
    /// ```
    /// use astraea::digit;
    /// use astraea::math::Digit;
    ///
    /// let lhs = digit!(6);
    /// let rhs = digit!(9);
    /// let (diff, carry) = lhs - rhs;
    ///
    /// assert_eq!(diff, digit!(7));
    /// assert_eq!(carry, digit!(1));
    /// ```
    fn sub(self, rhs: Self) -> Self::Output {
        let diff = (self.value() as i16) - (rhs.value() as i16);
        let res = (diff + 10) % 10;
        let result = digit!(res as u8);
        let carry = if diff >= 0 { digit!(0) } else { digit!(1) };

        (result, carry)
    }
}

impl Mul for Digit {
    type Output = (Self, Self);

    /// Returns product of two digits. The first returned value is the digit in the same position,
    /// and the second is the carry digit.
    ///
    /// ```
    /// use astraea::digit;
    /// use astraea::math::Digit;
    ///
    /// let lhs = digit!(6);
    /// let rhs = digit!(7);
    /// let (sum, carry) = lhs * rhs;
    ///
    /// assert_eq!(sum, digit!(2));
    /// assert_eq!(carry, digit!(4));
    /// ```
    fn mul(self, rhs: Self) -> Self::Output {
        let product = self.value() * rhs.value();
        let result = product % 10;
        let carry = product / 10;

        (digit!(result), digit!(carry))
    }
}

impl Div for Digit {
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        let value = self.value() / rhs.value();
        Self::new(value).unwrap()
    }
}

impl Display for Digit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.char())
    }
}

impl Pretty for Digit {
    fn prettify(&self) -> String {
        self.to_string()
    }
}

impl FromStr for Digit {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if s.len() != 1 {
            return Err(Self::Err::new("expected string of length 1".to_string()));
        }

        Self::from_char(s.chars().next().unwrap())
    }
}

/// Implements Into<T> for Digit for every integer type.
macro_rules! impl_digit_into {
    ($($t:ty),*) => {
        $(
            impl Into<$t> for Digit {
                fn into(self) -> $t {
                    match self {
                        Digit::Zero => 0,
                        Digit::One => 1,
                        Digit::Two => 2,
                        Digit::Three => 3,
                        Digit::Four => 4,
                        Digit::Five => 5,
                        Digit::Six => 6,
                        Digit::Seven => 7,
                        Digit::Eight => 8,
                        Digit::Nine => 9,
                    }
                }
            }
        )*
    };
}

impl_digit_into!(
    u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize
);

/// Implements TryFrom<T> for Digit for every integer type.
macro_rules! impl_digit_try_from {
    ($($t:ty),*) => {
        $(
            impl TryFrom<$t> for Digit {
                type Error = ValueError;

                fn try_from(value: $t) -> Result<Self, Self::Error> {
                    match value {
                        0 => Ok(Digit::Zero),
                        1 => Ok(Digit::One),
                        2 => Ok(Digit::Two),
                        3 => Ok(Digit::Three),
                        4 => Ok(Digit::Four),
                        5 => Ok(Digit::Five),
                        6 => Ok(Digit::Six),
                        7 => Ok(Digit::Seven),
                        8 => Ok(Digit::Eight),
                        9 => Ok(Digit::Nine),
                        v => Err(Self::Error::new(format!(
                            "expected value to be in range [0, 9], got '{}'",
                            v
                        ))),
                    }
                }
            }
        )*
    };
}

impl_digit_try_from!(
    u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize
);

#[cfg(test)]
mod tests {
    use super::*;
    use std::cmp::Ordering;

    #[test]
    fn test_digit_new() {
        assert_eq!(Digit::new(0).unwrap(), Digit::Zero);
        assert_eq!(Digit::new(1).unwrap(), Digit::One);
        assert_eq!(Digit::new(2).unwrap(), Digit::Two);
        assert_eq!(Digit::new(3).unwrap(), Digit::Three);
        assert_eq!(Digit::new(4).unwrap(), Digit::Four);
        assert_eq!(Digit::new(5).unwrap(), Digit::Five);
        assert_eq!(Digit::new(6).unwrap(), Digit::Six);
        assert_eq!(Digit::new(7).unwrap(), Digit::Seven);
        assert_eq!(Digit::new(8).unwrap(), Digit::Eight);
        assert_eq!(Digit::new(9).unwrap(), Digit::Nine);

        assert!(Digit::new(28).is_err());
    }

    #[test]
    fn test_digit_from_char() {
        assert_eq!(Digit::from_char('0').unwrap(), Digit::Zero);
        assert_eq!(Digit::from_char('1').unwrap(), Digit::One);
        assert_eq!(Digit::from_char('2').unwrap(), Digit::Two);
        assert_eq!(Digit::from_char('3').unwrap(), Digit::Three);
        assert_eq!(Digit::from_char('4').unwrap(), Digit::Four);
        assert_eq!(Digit::from_char('5').unwrap(), Digit::Five);
        assert_eq!(Digit::from_char('6').unwrap(), Digit::Six);
        assert_eq!(Digit::from_char('7').unwrap(), Digit::Seven);
        assert_eq!(Digit::from_char('8').unwrap(), Digit::Eight);
        assert_eq!(Digit::from_char('9').unwrap(), Digit::Nine);

        assert!(Digit::from_char('a').is_err());
    }

    #[test]
    fn test_digit_cmp() {
        let lhs = Digit::new(9).unwrap();
        let rhs = Digit::new(8).unwrap();
        assert_eq!(lhs.cmp(&rhs), Ordering::Greater);

        let lhs = Digit::new(3).unwrap();
        let rhs = Digit::new(4).unwrap();
        assert_eq!(lhs.cmp(&rhs), Ordering::Less);

        let lhs = Digit::new(6).unwrap();
        let rhs = Digit::new(6).unwrap();
        assert_eq!(lhs.cmp(&rhs), Ordering::Equal);
    }

    #[test]
    fn test_digit_macro() {
        for v in 0..10 {
            assert_eq!(digit!(v), Digit::new(v).unwrap())
        }

        assert_eq!(digit!(0), Digit::Zero);
        assert_eq!(digit!(1), Digit::One);
        assert_eq!(digit!(2), Digit::Two);
        assert_eq!(digit!(3), Digit::Three);
        assert_eq!(digit!(4), Digit::Four);
        assert_eq!(digit!(5), Digit::Five);
        assert_eq!(digit!(6), Digit::Six);
        assert_eq!(digit!(7), Digit::Seven);
        assert_eq!(digit!(8), Digit::Eight);
        assert_eq!(digit!(9), Digit::Nine);
    }

    #[test]
    fn test_digit_add() {
        for lhs in 0..10 {
            for rhs in 0..10 {
                let expected_res: Digit = ((lhs + rhs) % 10).try_into().unwrap();
                let expected_carry: Digit = ((lhs + rhs) / 10).try_into().unwrap();

                let lhs: Digit = lhs.try_into().unwrap();
                let rhs: Digit = rhs.try_into().unwrap();

                let (actual_res, actual_carry) = lhs + rhs;

                assert_eq!(actual_res, expected_res);
                assert_eq!(actual_carry, expected_carry);
            }
        }
    }

    #[test]
    fn test_digit_div() {
        for lhs in 0..10 {
            for rhs in 1..10 {
                let expected: Digit = (lhs / rhs).try_into().unwrap();

                let lhs: Digit = lhs.try_into().unwrap();
                let rhs: Digit = rhs.try_into().unwrap();

                let actual = lhs / rhs;

                assert_eq!(actual, expected);
            }
        }
    }

    #[test]
    fn test_format() {
        assert_eq!(Digit::Zero.to_string(), "0");
        assert_eq!(Digit::One.to_string(), "1");
        assert_eq!(Digit::Two.to_string(), "2");
        assert_eq!(Digit::Three.to_string(), "3");
        assert_eq!(Digit::Four.to_string(), "4");
        assert_eq!(Digit::Five.to_string(), "5");
        assert_eq!(Digit::Six.to_string(), "6");
        assert_eq!(Digit::Seven.to_string(), "7");
        assert_eq!(Digit::Eight.to_string(), "8");
        assert_eq!(Digit::Nine.to_string(), "9");

        assert_eq!(Digit::Zero.prettify(), "0");
        assert_eq!(Digit::One.prettify(), "1");
        assert_eq!(Digit::Two.prettify(), "2");
        assert_eq!(Digit::Three.prettify(), "3");
        assert_eq!(Digit::Four.prettify(), "4");
        assert_eq!(Digit::Five.prettify(), "5");
        assert_eq!(Digit::Six.prettify(), "6");
        assert_eq!(Digit::Seven.prettify(), "7");
        assert_eq!(Digit::Eight.prettify(), "8");
        assert_eq!(Digit::Nine.prettify(), "9");
    }

    #[test]
    fn test_from_str() {
        assert_eq!(Digit::from_str("0").unwrap(), Digit::Zero);
        assert_eq!(Digit::from_str("1").unwrap(), Digit::One);
        assert_eq!(Digit::from_str("2").unwrap(), Digit::Two);
        assert_eq!(Digit::from_str("3").unwrap(), Digit::Three);
        assert_eq!(Digit::from_str("4").unwrap(), Digit::Four);
        assert_eq!(Digit::from_str("5").unwrap(), Digit::Five);
        assert_eq!(Digit::from_str("6").unwrap(), Digit::Six);
        assert_eq!(Digit::from_str("7").unwrap(), Digit::Seven);
        assert_eq!(Digit::from_str("8").unwrap(), Digit::Eight);
        assert_eq!(Digit::from_str("9").unwrap(), Digit::Nine);

        assert!(Digit::from_str("").is_err());
        assert!(Digit::from_str("123").is_err());
        assert!(Digit::from_str("a").is_err());
    }
}
