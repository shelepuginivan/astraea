use std::{
    char,
    fmt::Display,
    ops::{Mul, Neg},
    str::FromStr,
};

use crate::{core::ParseError, math::Sign, natural::NaturalNumber, rational::RationalNumber};

/// Monomial represents a single term of a polynomial, written as k &middot; x<sup>a</sup>, where k
/// is a rational coefficient and a is a natural exponent.
pub struct Monomial {
    coefficient: RationalNumber,
    exponent: NaturalNumber,
}

impl Monomial {
    pub fn sign(&self) -> Sign {
        self.coefficient.sign()
    }
}

impl Display for Monomial {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}*x^{}", self.coefficient, self.exponent)
    }
}

impl Neg for Monomial {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self {
            coefficient: -self.coefficient,
            exponent: self.exponent,
        }
    }
}

impl Mul<Sign> for Monomial {
    type Output = Self;

    fn mul(self, rhs: Sign) -> Self::Output {
        Self {
            coefficient: self.coefficient * rhs,
            exponent: self.exponent,
        }
    }
}

struct MonomialParser {
    source: Vec<char>,
    cursor: usize,

    has_multiplication_sign: bool,
    has_variable: bool,
    has_exponent: bool,

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
}

impl FromStr for Monomial {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut parser = MonomialParser::new(s.trim().to_string());

        // Coefficient.
        while parser.can_advance() {
            let char = parser.char();

            if !char.is_numeric() && char != '/' {
                break;
            }

            parser.coefficient_chars.push(char);
            parser.advance();
        }

        // Variable ("x").
        while parser.can_advance() {
            match parser.char() {
                ' ' => parser.advance(),
                '*' | '·' | '×' => {
                    if parser.has_multiplication_sign {
                        return Err(ParseError::new("unexpected multiplication sign"));
                    }

                    parser.has_multiplication_sign = true;
                    parser.advance();
                }
                'x' => {
                    parser.has_variable = true;
                    parser.advance();
                    break;
                }
                char => return Err(ParseError::new(format!("unexpected char: \"{}\"", char))),
            };
        }

        // Exponent sign ("^").
        while parser.can_advance() {
            match parser.char() {
                ' ' => parser.advance(),
                '^' => {
                    parser.advance();
                    parser.has_exponent = true;
                    break;
                }
                char => return Err(ParseError::new(format!("unexpected char: \"{}\"", char))),
            };
        }

        // Exponent.
        while parser.can_advance() {
            let char = parser.char();

            if char == ' ' {
                parser.advance();
                continue;
            }

            if !char.is_numeric() {
                break;
            }

            parser.exponent_chars.push(char);
            parser.advance();
        }

        if parser.can_advance() {
            return Err(ParseError::new(format!(
                "unexpected junk at the end: \"{}\"",
                &s[parser.cursor..],
            )));
        }

        let coefficient_chars: String = parser.coefficient_chars.into_iter().collect();
        let exponent_chars: String = parser.exponent_chars.into_iter().collect();

        let coefficient = if !parser.has_multiplication_sign
            && parser.has_variable
            && coefficient_chars.is_empty()
        {
            RationalNumber::one()
        } else {
            match RationalNumber::from_str(&coefficient_chars) {
                Ok(v) => v,
                Err(e) => {
                    return Err(ParseError::new(format!(
                        "cannot parse coefficient: {}",
                        e.message
                    )));
                }
            }
        };

        let exponent = if !parser.has_variable {
            NaturalNumber::zero()
        } else if !parser.has_exponent {
            NaturalNumber::one()
        } else {
            match NaturalNumber::from_str(&exponent_chars) {
                Ok(v) => v,
                Err(e) => {
                    return Err(ParseError::new(format!(
                        "cannot parse exponent: {}",
                        e.message
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
    use super::*;
    use std::str::FromStr;

    #[test]
    fn test_monomial_from_str() {
        let cases = vec![
            ("5*x^6", "5/1", 6),
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
        ];

        for (input, expected_coeff, expected_exp) in cases {
            let monomial =
                Monomial::from_str(input).expect(&format!("Failed to parse '{}'", input));
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
        ];

        for input in invalid_cases {
            assert!(
                Monomial::from_str(input).is_err(),
                "Expected error for '{}'",
                input
            );
        }
    }
}
