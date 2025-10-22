use std::str::FromStr;

use crate::ParseError;

/// Represents a single digit of a natural number.
#[derive(Clone, Default)]
pub struct Digit {
    pub value: u8,
}

impl Digit {
    pub fn new(value: u8) -> Self {
        Digit { value }
    }

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
