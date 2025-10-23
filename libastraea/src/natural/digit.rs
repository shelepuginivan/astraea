use std::str::FromStr;

use crate::{ParseError, ValueError};

/// Represents a single digit of a natural number.
#[derive(Clone, Debug, Default, Eq, PartialEq, PartialOrd, Ord)]
pub struct Digit {
    pub value: u8,
}

impl Digit {
    /// Creates a new instance of Digit. Value must be a valid digit, i.e. in range [0, 9].
    ///
    /// ```
    /// use libastraea::Digit;
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
    /// use libastraea::Digit;
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
    /// use libastraea::Digit;
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

impl ToString for Digit {
    fn to_string(&self) -> String {
        self.value.to_string()
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
}
