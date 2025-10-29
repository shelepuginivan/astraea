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
        Digit::new($v).unwrap()
    };
    ($v:expr) => {
        Digit::new($v).unwrap()
    };
}

/// Represents a single digit of a natural number.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, PartialOrd, Ord)]
pub struct Digit {
    pub value: u8,
}

impl Digit {
    /// Creates a new instance of Digit. Value must be a valid digit, i.e. in range [0, 9].
    ///
    /// ```
    /// use libastraea::math::Digit;
    ///
    /// let d = Digit::new(9).unwrap();
    /// assert_eq!(d.value, 9)
    /// ```
    pub fn new(value: u8) -> Result<Self, ValueError> {
        if value >= 10 {
            return Err(ValueError::new(format!(
                "expected value to be in range [0, 9], got {}",
                value
            )));
        }

        Ok(Digit { value })
    }

    /// Parses Digit from char.
    ///
    /// ```
    /// use libastraea::math::Digit;
    ///
    /// let d = Digit::from_char('7').unwrap();
    /// assert_eq!(d.value, 7);
    /// ```
    pub fn from_char(char: char) -> Result<Self, ParseError> {
        let digit: u8 = match char {
            '0' => 0,
            '1' => 1,
            '2' => 2,
            '3' => 3,
            '4' => 4,
            '5' => 5,
            '6' => 6,
            '7' => 7,
            '8' => 8,
            '9' => 9,
            _ => return Err(ParseError::new(format!("{} is not a digit", char))),
        };

        Ok(Digit { value: digit })
    }

    /// Converts Digit to char.
    ///
    /// ```
    /// use libastraea::math::Digit;
    ///
    /// let d = Digit::new(4).unwrap();
    /// assert_eq!(d.to_char(), '4');
    /// ```
    pub fn to_char(&self) -> char {
        match self.value {
            0 => '0',
            1 => '1',
            2 => '2',
            3 => '3',
            4 => '4',
            5 => '5',
            6 => '6',
            7 => '7',
            8 => '8',
            9 => '9',
            _ => unreachable!(),
        }
    }
}

impl Add for Digit {
    type Output = (Self, Self);

    /// Returns sum of two digits. The first returned value is the digit in the same position, and
    /// the second is the carry digit.
    ///
    /// ```
    /// use libastraea::digit;
    /// use libastraea::math::Digit;
    ///
    /// let lhs = digit!(6);
    /// let rhs = digit!(7);
    /// let (sum, carry) = lhs + rhs;
    ///
    /// assert_eq!(sum, digit!(3));
    /// assert_eq!(carry, digit!(1));
    /// ```
    fn add(self, rhs: Self) -> Self::Output {
        let sum = self.value + rhs.value;
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
    /// use libastraea::digit;
    /// use libastraea::math::Digit;
    ///
    /// let lhs = digit!(6);
    /// let rhs = digit!(9);
    /// let (diff, carry) = lhs - rhs;
    ///
    /// assert_eq!(diff, digit!(7));
    /// assert_eq!(carry, digit!(1));
    /// ```
    fn sub(self, rhs: Self) -> Self::Output {
        let diff = (self.value as i16) - (rhs.value as i16);
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
    /// use libastraea::digit;
    /// use libastraea::math::Digit;
    ///
    /// let lhs = digit!(6);
    /// let rhs = digit!(7);
    /// let (sum, carry) = lhs * rhs;
    ///
    /// assert_eq!(sum, digit!(2));
    /// assert_eq!(carry, digit!(4));
    /// ```
    fn mul(self, rhs: Self) -> Self::Output {
        let product = self.value * rhs.value;
        let result = product % 10;
        let carry = product / 10;

        (digit!(result), digit!(carry))
    }
}

impl Div for Digit {
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        let value = self.value / rhs.value;
        Self { value }
    }
}

impl Display for Digit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value)
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

#[cfg(test)]
mod tests {
    use super::*;
    use std::cmp::Ordering;

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

        assert_eq!(digit!(0), Digit::new(0).unwrap());
        assert_eq!(digit!(1), Digit::new(1).unwrap());
        assert_eq!(digit!(2), Digit::new(2).unwrap());
        assert_eq!(digit!(3), Digit::new(3).unwrap());
        assert_eq!(digit!(4), Digit::new(4).unwrap());
        assert_eq!(digit!(5), Digit::new(5).unwrap());
        assert_eq!(digit!(6), Digit::new(6).unwrap());
        assert_eq!(digit!(7), Digit::new(7).unwrap());
        assert_eq!(digit!(8), Digit::new(8).unwrap());
        assert_eq!(digit!(9), Digit::new(9).unwrap());
    }
}
