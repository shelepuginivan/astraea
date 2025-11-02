use std::str::FromStr;
use std::usize;

use crate::algebra::Field;
use crate::error::ParseError;
use crate::formatting;

/// Monomial represents a single term of a polynomial, written as k &middot; x<sup>a</sup>, where k
/// is a rational coefficient and a is an exponent of type usize.
pub struct Monomial<T: Field> {
    pub coefficient: T,
    pub exponent: usize,
}

struct MonomialParser {
    source: Vec<char>,
    cursor: usize,

    has_multiplication_sign: bool,
    has_variable: bool,
    has_exponent: bool,
    exponent_as_superscript: bool,

    coefficient_chars: Vec<char>,
    exponent_chars: Vec<char>,
}

impl MonomialParser {
    fn new(source: String) -> Self {
        MonomialParser {
            source: source.chars().collect(),
            cursor: 0,
            has_multiplication_sign: false,
            has_variable: false,
            has_exponent: false,
            exponent_as_superscript: false,
            coefficient_chars: Vec::new(),
            exponent_chars: Vec::new(),
        }
    }

    fn advance(&mut self) {
        self.cursor += 1;
    }

    fn can_advance(&self) -> bool {
        self.cursor < self.source.len()
    }

    fn char(&self) -> char {
        self.source[self.cursor]
    }

    fn collect_coefficient(&mut self) {
        while self.can_advance() {
            let char = self.char();

            if !char.is_numeric() && char != '/' {
                break;
            }

            self.coefficient_chars.push(char);
            self.advance();
        }
    }

    fn collect_variable(&mut self) -> Result<(), ParseError> {
        while self.can_advance() {
            match self.char() {
                ' ' => self.advance(),
                '*' | '·' | '×' => {
                    if self.has_multiplication_sign {
                        return Err(ParseError::new("unexpected multiplication sign"));
                    }

                    self.has_multiplication_sign = true;
                    self.advance();
                }
                'x' => {
                    self.has_variable = true;
                    self.advance();
                    break;
                }
                char => return Err(ParseError::new(format!("unexpected char: \"{}\"", char))),
            };
        }

        Ok(())
    }

    fn collect_exponent_sign(&mut self) -> Result<(), ParseError> {
        while self.can_advance() {
            match self.char() {
                ' ' => self.advance(),
                '^' => {
                    self.advance();
                    self.has_exponent = true;
                    break;
                }
                '⁰' | '¹' | '²' | '³' | '⁴' | '⁵' | '⁶' | '⁷' | '⁸' | '⁹' => {
                    self.has_exponent = true;
                    self.exponent_as_superscript = true;
                    break;
                }

                char => return Err(ParseError::new(format!("unexpected char: \"{}\"", char))),
            };
        }

        Ok(())
    }

    fn skip_spaces(&mut self) {
        while self.can_advance() {
            if self.char() != ' ' {
                break;
            }
            self.advance();
        }
    }

    fn collect_exponent(&mut self) -> Result<(), ParseError> {
        while self.can_advance() {
            let char = self.char();

            if self.exponent_as_superscript {
                match formatting::from_superscript(char) {
                    Some(c) => {
                        self.exponent_chars.push(c);
                        self.advance();
                        continue;
                    }
                    None => break,
                }
            }

            if !char.is_numeric() {
                break;
            }

            self.exponent_chars.push(char);
            self.advance();
        }

        Ok(())
    }

    fn finalize(&mut self) -> Result<(), ParseError> {
        if self.can_advance() {
            return Err(ParseError::new("unexpected junk at the end"));
        }

        Ok(())
    }
}

impl<T: Field> FromStr for Monomial<T> {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut parser = MonomialParser::new(s.trim().to_string());

        parser.collect_coefficient();
        parser.collect_variable()?;
        parser.collect_exponent_sign()?;
        parser.skip_spaces();
        parser.collect_exponent()?;
        parser.finalize()?;

        let coefficient_chars: String = parser.coefficient_chars.into_iter().collect();
        let exponent_chars: String = parser.exponent_chars.into_iter().collect();

        let coefficient = if !parser.has_multiplication_sign
            && parser.has_variable
            && coefficient_chars.is_empty()
        {
            T::one()
        } else {
            match T::from_str(&coefficient_chars) {
                Ok(v) => v,
                Err(..) => {
                    return Err(ParseError::new("cannot parse coefficient"));
                }
            }
        };

        let exponent = if !parser.has_variable {
            0
        } else if !parser.has_exponent {
            1
        } else {
            match usize::from_str(&exponent_chars) {
                Ok(v) => v,
                Err(..) => {
                    return Err(ParseError::new(format!(
                        "cannot parse '{}' as exponent",
                        exponent_chars
                    )));
                }
            }
        };

        Ok(Self {
            coefficient,
            exponent,
        })
    }
}

#[cfg(test)]
mod tests {
    use crate::rational::RationalNumber;

    use super::*;
    use std::str::FromStr;

    #[test]
    fn test_monomial_from_str() {
        let cases = vec![
            ("5*x^6", "5/1", 6),
            ("x^123", "1/1", 123),
            ("123x^0", "123/1", 0),
            ("0*x^1", "0/1", 1),
            ("42 * x ^ 3", "42/1", 3),
            ("7/3·x^2", "7/3", 2),
            ("9/2342×x^4", "9/2342", 4),
            ("3/4*x^2", "3/4", 2),
            ("2", "2/1", 0),
            ("34*x", "34/1", 1),
            ("x^2", "1/1", 2),
            ("x", "1/1", 1),
            ("2x⁵", "2/1", 5),
            ("123 * x⁴²", "123/1", 42),
        ];

        for (input, expected_coeff, expected_exp) in cases {
            let monomial = Monomial::<RationalNumber>::from_str(input)
                .expect(&format!("Failed to parse '{}'", input));
            assert_eq!(
                expected_coeff.to_string(),
                monomial.coefficient.to_string(),
                "Coefficient mismatch for '{}'",
                input
            );
            assert_eq!(
                expected_exp.to_string(),
                monomial.exponent.to_string(),
                "Exponent mismatch for '{}'",
                input
            );
        }

        // Invalid inputs - expect errors
        let invalid_cases = vec![
            "",
            "5*x^",
            "5*x^a",
            "5**x^2",
            "5x^2junk",
            "-5*x^2",
            "5*x^-2",
            "2342*x234^324",
            "*x^3",
            "x^",
            "234x^3⁸",
        ];

        for input in invalid_cases {
            assert!(
                Monomial::<RationalNumber>::from_str(input).is_err(),
                "Expected error for '{}'",
                input
            );
        }
    }
}
