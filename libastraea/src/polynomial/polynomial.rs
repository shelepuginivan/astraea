use std::collections::LinkedList;
use std::fmt::Display;
use std::str::FromStr;

use crate::core::ParseError;
use crate::math::{Ring, Sign, Signed};
use crate::polynomial::Monomial;
use crate::rational::RationalNumber;

pub struct Polynomial {
    coefficients: Vec<RationalNumber>,
}

impl Polynomial {
    pub fn from_canonical_form<S: Into<String>>(s: S) -> Result<Self, ParseError> {
        let chars: Vec<char> = s.into().trim().chars().collect();

        let mut monomials: LinkedList<Monomial> = LinkedList::new();
        let mut polynomial_degree = 0;
        let mut cursor = 0;
        let mut monomial_chars: Vec<char> = Vec::new();
        let mut next_sign = Sign::Positive;

        while cursor < chars.len() {
            match chars[cursor] {
                '+' | '-' => {
                    let monomial_str: String = monomial_chars.iter().collect();
                    let mut monomial = Monomial::from_str(monomial_str.as_str())?;
                    polynomial_degree = polynomial_degree.max(monomial.exponent);
                    monomial.coefficient = monomial.coefficient.with_sign(next_sign);
                    monomials.push_back(monomial);
                    next_sign = Sign::from_char(chars[cursor])?;
                    monomial_chars.clear();
                }

                char => {
                    monomial_chars.push(char);
                }
            }

            cursor += 1;
        }

        let monomial_str: String = monomial_chars.iter().collect();
        let mut monomial = Monomial::from_str(monomial_str.as_str())?;
        polynomial_degree = polynomial_degree.max(monomial.exponent);
        monomial.coefficient = monomial.coefficient.with_sign(next_sign);
        monomials.push_back(monomial);

        let mut coefficients = vec![RationalNumber::zero(); polynomial_degree + 1];

        for monomial in monomials {
            coefficients[monomial.exponent] = monomial.coefficient;
        }

        Ok(Self { coefficients })
    }
}

impl Display for Polynomial {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut is_first_coefficient = true;

        for (exponent, coefficient) in self.coefficients.iter().enumerate().rev() {
            if coefficient.is_zero() {
                continue;
            }

            let variable = match exponent {
                0 => "".to_string(),
                1 => "*x".to_string(),
                e => format!("*x^{}", e),
            };
            let separator = if is_first_coefficient { "" } else { " " };
            let sign = if !is_first_coefficient && coefficient.is_positive() {
                "+"
            } else {
                ""
            };

            write!(f, "{}{}{}{}", separator, sign, coefficient, variable)?;
            is_first_coefficient = false;
        }

        Ok(())
    }
}

impl FromStr for Polynomial {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Polynomial::from_canonical_form(s)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn q(numerator: i32, denominator: i32) -> RationalNumber {
        RationalNumber::from_str(&format!("{}/{}", numerator, denominator)).unwrap()
    }

    #[test]
    fn test_polynomial_from_canonical_form() {
        let tests = vec![
            ("x^2 - 2x + 1", vec![q(1, 1), q(-2, 1), q(1, 1)]),
            ("5/6", vec![q(5, 6)]),
        ];

        for (canonical_form, expected) in tests {
            let p = Polynomial::from_canonical_form(canonical_form)
                .expect(&format!("failed to parse '{}'", canonical_form));

            for (expected_exponent, actual_exponent) in expected.iter().zip(p.coefficients) {
                assert_eq!(expected_exponent.to_string(), actual_exponent.to_string());
            }
        }
    }
}
