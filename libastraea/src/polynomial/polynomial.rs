use std::{collections::LinkedList, fmt::Display, str::FromStr};

use crate::{
    core::ParseError,
    math::{Sign, Signed},
    polynomial::Monomial,
};

pub struct Polynomial {
    monomials: LinkedList<Monomial>,
}

impl Polynomial {
    pub fn from_canonical_form(s: &str) -> Result<Self, ParseError> {
        let mut monomials: LinkedList<Monomial> = LinkedList::new();
        let mut cursor = 0;
        let chars: Vec<char> = s.trim().chars().collect();
        let mut monomial_chars: Vec<char> = Vec::new();
        let mut next_sign = Sign::Positive;

        while cursor < chars.len() {
            match chars[cursor] {
                '+' => {
                    let monomial_str: String = monomial_chars.iter().collect();
                    let monomial = Monomial::from_str(monomial_str.as_str())?.with_sign(next_sign);
                    monomials.push_back(monomial);
                    monomial_chars.clear();
                    next_sign = Sign::Positive;
                    cursor += 1;
                }

                '-' => {
                    let monomial_str: String = monomial_chars.iter().collect();
                    let monomial = Monomial::from_str(monomial_str.as_str())?.with_sign(next_sign);
                    monomials.push_back(monomial);
                    monomial_chars.clear();
                    next_sign = Sign::Negative;
                    cursor += 1;
                }

                char => {
                    monomial_chars.push(char);
                    cursor += 1;
                }
            }
        }

        let monomial_str: String = monomial_chars.iter().collect();
        let monomial = Monomial::from_str(monomial_str.as_str())?.with_sign(next_sign);
        monomials.push_back(monomial);

        Ok(Self { monomials })
    }
}

impl Display for Polynomial {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (i, monomial) in self.monomials.iter().enumerate() {
            if i == 0 {
                write!(f, "{}", monomial)?;
                continue;
            }

            let sign = if monomial.sign() == Sign::Positive {
                "+"
            } else {
                ""
            };
            write!(f, " {}{}", sign, monomial)?;
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

    #[test]
    fn test_polynomial_from_canonical_form() {
        let tests = vec![("x^2 - 2x + 1", "1/1*x^2 -2/1*x^1 +1/1*x^0")];

        for (canonical_form, expected) in tests {
            let p = Polynomial::from_canonical_form(canonical_form).unwrap();
            let actual = p.to_string();

            assert_eq!(expected, actual);
        }
    }
}
