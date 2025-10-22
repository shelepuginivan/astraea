use std::str::FromStr;

use crate::{Digit, ParseError};

/// Represents a natural number.
#[derive(Clone, Default)]
pub struct NaturalNumber {
    /// Digits of the natural number, stored in reverse order.
    pub digits: Vec<Digit>,
}

impl FromStr for NaturalNumber {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let length = s.len();
        let mut digits: Vec<Digit> = vec![Digit::default(); length];

        for (index, char) in s.chars().enumerate() {
            let digit = Digit::from_char(char)?;
            digits[length - index - 1] = digit;
        }

        Ok(NaturalNumber { digits })
    }
}

impl ToString for NaturalNumber {
    fn to_string(&self) -> String {
        self.digits
            .iter()
            .rev()
            .map(|digit| digit.to_char())
            .collect()
    }
}
