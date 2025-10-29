use std::cmp::Ordering;
use std::collections::LinkedList;
use std::fmt::Display;
use std::ops::{Add, Div, Mul, Neg, Rem, Sub};
use std::str::FromStr;

use crate::core::{ParseError, Pretty, ValueError};
use crate::integer::Integer;
use crate::math::{Field, IntegralDomain, MathSet, Ring, Sign};
use crate::natural::NaturalNumber;
use crate::polynomial::Monomial;
use crate::rational::RationalNumber;

#[derive(Clone)]
pub struct Polynomial<T: Field> {
    coefficients: Vec<T>,
}

impl<T: Field> Polynomial<T> {
    /// Keeps the invariant of the polynomial - its leading coefficient must not be zero, unless
    /// the degree of the polynomial is 0.
    fn normalize(mut self) -> Self {
        while self.coefficients.pop_if(|c| c.is_zero()).is_some() {}
        if self.coefficients.len() == 0 {
            self.coefficients.push(T::zero());
        }
        self
    }

    pub fn new(coefficients: Vec<T>) -> Self {
        Self { coefficients }.normalize()
    }

    pub fn from_canonical_form<S: Into<String>>(s: S) -> Result<Self, ParseError> {
        let chars: Vec<char> = s.into().trim().chars().collect();

        let mut monomials: LinkedList<Monomial<T>> = LinkedList::new();
        let mut polynomial_degree = 0;
        let mut cursor = 0;
        let mut monomial_chars: Vec<char> = Vec::new();
        let mut next_sign = Sign::Positive;

        while cursor < chars.len() {
            match chars[cursor] {
                '+' | '-' => {
                    let monomial_str: String = monomial_chars.iter().collect();
                    let mut monomial = Monomial::<T>::from_str(monomial_str.as_str())?;
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
        let mut monomial = Monomial::<T>::from_str(monomial_str.as_str())?;
        polynomial_degree = polynomial_degree.max(monomial.exponent);
        monomial.coefficient = monomial.coefficient.with_sign(next_sign);
        monomials.push_back(monomial);

        let mut coefficients = vec![T::zero(); polynomial_degree + 1];

        for monomial in monomials {
            coefficients[monomial.exponent] = monomial.coefficient;
        }

        Ok(Self::new(coefficients))
    }

    pub fn as_coefficients(self) -> Vec<T> {
        self.coefficients
    }

    pub fn degree(&self) -> usize {
        self.coefficients.len().max(1) - 1
    }

    pub fn leading_coefficient(&self) -> T {
        self.coefficients
            .last()
            .and_then(|v| Some(v.clone()))
            .or_else(|| Some(T::zero()))
            .unwrap()
    }

    pub fn times_pow_x(self, k: usize) -> Self {
        Self {
            coefficients: [vec![T::zero(); k], self.coefficients].concat(),
        }
    }

    pub fn divide(self, rhs: Self) -> Result<(Self, Self), ValueError> {
        let mut quotient = Self::zero();
        let mut remainder = self.clone();

        while remainder.degree() >= rhs.degree() && !remainder.is_zero() {
            let coeff = (remainder.leading_coefficient() / rhs.leading_coefficient())?;
            let degree = remainder.degree() - rhs.degree();
            let t = Polynomial::new(vec![coeff]).times_pow_x(degree);

            quotient = quotient + t.clone();
            remainder = remainder - t * rhs.clone();
        }

        Ok((quotient.normalize(), remainder.normalize()))
    }

    pub fn derivative(self) -> Self {
        let mut coefficients = vec![T::zero(); self.degree()];

        for (i, coefficient) in self.coefficients.into_iter().enumerate() {
            if i == 0 {
                continue;
            }

            let exponent = T::from_str(&format!("{}", i)).unwrap();

            coefficients[i - 1] = coefficient * exponent;
        }

        Self::new(coefficients)
    }

    pub fn gcd(self, other: Self) -> Self {
        if other.is_zero() {
            return self;
        } else if self.is_zero() {
            return other;
        }

        let r = (self % other.clone()).unwrap();

        other.gcd(r).monic()
    }

    pub fn monic(self) -> Self {
        let mut coefficients = vec![T::zero(); self.degree() + 1];
        let leading = self.leading_coefficient();

        for (exponent, coefficient) in self.coefficients.into_iter().enumerate() {
            coefficients[exponent] = (coefficient / leading.clone()).unwrap();
        }

        Self::new(coefficients)
    }

    pub fn flatten(self) -> Self {
        let mut p = self;
        let mut result = Self::one();

        while p.degree() > 0 && !p.is_zero() {
            let derivative = p.clone().derivative();
            let r = p.clone().gcd(derivative.clone());
            let s = (p / r.clone()).unwrap();
            let m = s.clone().gcd(derivative);
            result = result * (s / m).unwrap();
            p = r;
        }

        result
    }
}

impl<T: Field> MathSet for Polynomial<T> {}
impl<T: Field> IntegralDomain for Polynomial<T> {}
impl<T: Field> Ring for Polynomial<T> {
    fn zero() -> Self {
        Self {
            coefficients: vec![T::zero()],
        }
    }

    fn one() -> Self {
        Self {
            coefficients: vec![T::one()],
        }
    }

    fn is_zero(&self) -> bool {
        self.degree() == 0 && self.coefficients[0].is_zero()
    }

    fn is_one(&self) -> bool {
        self.degree() == 0 && self.coefficients[0].is_one()
    }
}

impl<T: Field> Neg for Polynomial<T> {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self {
            coefficients: self.coefficients.into_iter().map(|c| -c).collect(),
        }
    }
}

impl<T: Field> Add for Polynomial<T> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        let (min, mut max) = match self.degree().cmp(&rhs.degree()) {
            Ordering::Greater | Ordering::Equal => (rhs, self),
            Ordering::Less => (self, rhs),
        };

        for (exponent, rhs_coefficient) in min.coefficients.into_iter().enumerate() {
            let lhs_coefficient = max.coefficients[exponent].clone();
            max.coefficients[exponent] = lhs_coefficient + rhs_coefficient;
        }

        max.normalize()
    }
}

impl<T: Field> Sub for Polynomial<T> {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        self.add(-rhs)
    }
}

impl<T: Field> Mul<T> for Polynomial<T> {
    type Output = Self;

    fn mul(self, rhs: T) -> Self::Output {
        Self {
            coefficients: self
                .coefficients
                .into_iter()
                .map(|c| c * rhs.clone())
                .collect(),
        }
        .normalize()
    }
}

impl<T: Field> Mul for Polynomial<T> {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        let result_degree = self.degree() + rhs.degree();
        let mut result = Polynomial {
            coefficients: vec![T::zero(); result_degree + 1],
        };

        for (k, rhs_coefficient) in rhs.coefficients.into_iter().enumerate() {
            let prod = self.clone() * rhs_coefficient;
            result = result + prod.times_pow_x(k);
        }

        result.normalize()
    }
}

impl<T: Field> Div for Polynomial<T> {
    type Output = Result<Self, ValueError>;

    fn div(self, rhs: Self) -> Self::Output {
        Ok(self.divide(rhs)?.0)
    }
}

impl<T: Field> Rem for Polynomial<T> {
    type Output = Result<Self, ValueError>;

    fn rem(self, rhs: Self) -> Self::Output {
        Ok(self.divide(rhs)?.1)
    }
}

impl<T: Field> Display for Polynomial<T> {
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

impl<T: Field> Pretty for Polynomial<T> {
    fn prettify(&self) -> String {
        let mut is_first_coefficient = true;
        let mut parts = Vec::<String>::with_capacity(self.degree() + 1);

        for (exponent, coefficient) in self.coefficients.iter().enumerate().rev() {
            if coefficient.is_zero() {
                continue;
            }

            let sign = coefficient.sign().char();
            let sep = if !is_first_coefficient {
                format!(" {} ", sign)
            } else {
                "".to_string()
            };

            let coefficient_str = if exponent == 0 || !coefficient.is_one() {
                &coefficient.prettify()
            } else {
                ""
            };

            let variable_str = match exponent {
                0 => "".to_string(),
                1 => "x".to_string(),
                e => format!("x^{}", e),
            };

            parts.push(format!("{}{}{}", sep, coefficient_str, variable_str));
            is_first_coefficient = false;
        }

        parts.join("")
    }
}

impl<T: Field> FromStr for Polynomial<T> {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Polynomial::from_canonical_form(s)
    }
}

impl Polynomial<RationalNumber> {
    pub fn content(self) -> RationalNumber {
        let mut numerator_gcd = Integer::zero();
        let mut denumerator_lcm = NaturalNumber::one();

        for coefficient in self.coefficients {
            let (numerator, denumerator) = coefficient.as_values();

            numerator_gcd = numerator_gcd.gcd(numerator);
            denumerator_lcm = denumerator_lcm.lcm(denumerator);
        }

        RationalNumber::new(numerator_gcd, denumerator_lcm).unwrap()
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
            ("0x^100 + x^2 + 4x + 4", vec![q(4, 1), q(4, 1), q(1, 1)]),
        ];

        for (canonical_form, expected) in tests {
            let p = Polynomial::<RationalNumber>::from_canonical_form(canonical_form)
                .expect(&format!("failed to parse '{}'", canonical_form));

            for (expected_exponent, actual_exponent) in expected.iter().zip(p.coefficients) {
                assert_eq!(expected_exponent.to_string(), actual_exponent.to_string());
            }
        }
    }

    #[test]
    fn test_polynomial_leading_coefficient() {
        let tests = vec![
            (vec![q(1, 1), q(2, 3), q(5, 4)], q(5, 4)),
            (vec![q(7, 2)], q(7, 2)),
            (vec![q(0, 1), q(0, 1), q(0, 1)], q(0, 1)),
            (vec![], q(0, 1)),
            (vec![q(1, 1), q(0, 1), q(0, 1)], q(1, 1)),
            (vec![q(3, 2), q(-7, 3)], q(-7, 3)),
        ];

        for (coefficients, expected) in tests {
            let p = Polynomial::new(coefficients);
            let actual = p.leading_coefficient();

            assert_eq!(expected.to_string(), actual.to_string());
        }
    }

    #[test]
    fn test_polynomial_add() {
        let tests = vec![
            (
                vec![q(1, 1), q(2, 3), q(5, 4)],
                vec![q(3, 1), q(1, 3), q(1, 4)],
                vec![q(4, 1), q(3, 3), q(6, 4)],
            ),
            (
                vec![q(1, 1), q(2, 3)],
                vec![q(3, 1), q(1, 3), q(1, 4)],
                vec![q(4, 1), q(3, 3), q(1, 4)],
            ),
            (
                vec![q(3, 1), q(1, 3), q(1, 4)],
                vec![q(1, 1), q(2, 3)],
                vec![q(4, 1), q(3, 3), q(1, 4)],
            ),
            (vec![q(1, 1), q(2, 3)], vec![], vec![q(1, 1), q(2, 3)]),
            (
                vec![q(1, 1), q(-2, 3), q(3, 4)],
                vec![q(-1, 1), q(2, 3), q(-3, 4)],
                vec![q(0, 1)],
            ),
            (
                vec![q(-3, 2), q(4, 5)],
                vec![q(3, 2), q(-1, 5)],
                vec![q(0, 2), q(3, 5)],
            ),
            (vec![q(5, 1)], vec![q(2, 1)], vec![q(7, 1)]),
        ];

        for (lhs_coeffs, rhs_coeffs, expected_coeffs) in tests {
            let lhs = Polynomial::new(lhs_coeffs);
            let rhs = Polynomial::new(rhs_coeffs);
            let expected = Polynomial::new(expected_coeffs);

            let actual = lhs + rhs;

            assert_eq!(
                expected.coefficients.len(),
                actual.coefficients.len(),
                "Coefficient length mismatch",
            );

            for (i, (expected, actual)) in expected
                .coefficients
                .iter()
                .zip(actual.coefficients.iter())
                .enumerate()
            {
                assert_eq!(
                    expected.to_string(),
                    actual.to_string(),
                    "Mismatch at coefficient index {}",
                    i,
                );
            }
        }
    }

    #[test]
    fn test_polynomial_mul() {
        let tests = vec![
            (
                vec![q(1, 1), q(2, 3), q(5, 4)],
                vec![q(0, 1)],
                vec![q(0, 1)],
            ),
            (
                vec![q(1, 1), q(2, 3), q(5, 4)],
                vec![q(1, 1)],
                vec![q(1, 1), q(2, 3), q(5, 4)],
            ),
            (
                vec![q(1, 1), q(1, 1)],          // 1 + x
                vec![q(1, 1), q(1, 1)],          // 1 + x
                vec![q(1, 1), q(2, 1), q(1, 1)], // 1 + 2x + x^2
            ),
            (
                vec![q(2, 1), q(0, 1), q(3, 1)],           // 2 + 0x + 3x^2
                vec![q(1, 1), q(4, 1)],                    // 1 + 4x
                vec![q(2, 1), q(8, 1), q(3, 1), q(12, 1)], // 2 + 8x + 3x^2 + 12x^3
            ),
            (
                vec![q(1, 1), q(-1, 1)],          // 1 - x
                vec![q(1, 1), q(1, 1)],           // 1 + x
                vec![q(1, 1), q(0, 1), q(-1, 1)], // 1 + 0x - x^2
            ),
            (
                vec![q(3, 2), q(-1, 3)], // 3/2 - (1/3)x
                vec![q(2, 1), q(1, 4)],  // 2 + (1/4)x
                vec![
                    q(6, 2),   // 3/2 * 2 = 3
                    q(-7, 24), // 3/2 * 1/4 + (-1/3)*2 = 3/8 - 2/3 = 9/24 - 16/24 = -7/24
                    q(-1, 12), // (-1/3) * (1/4) = -1/12
                ],
            ),
            (vec![q(0, 1)], vec![q(1, 1), q(2, 1)], vec![q(0, 1)]),
        ];

        for (lhs_coeffs, rhs_coeffs, expected_coeffs) in tests {
            let lhs = Polynomial::new(lhs_coeffs);
            let rhs = Polynomial::new(rhs_coeffs);
            let expected = Polynomial::new(expected_coeffs);

            let actual = lhs * rhs;

            assert_eq!(
                expected.coefficients.len(),
                actual.coefficients.len(),
                "Coefficient length mismatch",
            );

            for (i, (expected, actual)) in expected
                .coefficients
                .iter()
                .zip(actual.coefficients.iter())
                .enumerate()
            {
                assert_eq!(
                    expected.to_string(),
                    actual.to_string(),
                    "Mismatch at coefficient index {}",
                    i,
                );
            }
        }
    }

    #[test]
    fn test_polynomial_derivative() {
        let tests = vec![
            (vec![q(0, 1)], vec![q(0, 1)]),
            (
                vec![q(1, 1), q(2, 1), q(1, 1)], // 1 + 2x + x^2
                vec![q(2, 1), q(2, 1)],          // 2 + 2x
            ),
            (
                vec![q(1, 1), q(1, 1), q(1, 1), q(1, 1)], // 1 + x + x^2 + x^3
                vec![q(1, 1), q(2, 1), q(3, 1)],          // 1 + 2x + 3x^2
            ),
        ];

        for (coeffs, expected_coeffs) in tests {
            let expected = Polynomial::new(expected_coeffs);
            let actual = Polynomial::new(coeffs).derivative();

            assert_eq!(
                expected.coefficients.len(),
                actual.coefficients.len(),
                "Coefficient length mismatch",
            );

            for (i, (expected, actual)) in expected
                .coefficients
                .iter()
                .zip(actual.coefficients.iter())
                .enumerate()
            {
                assert_eq!(
                    expected.to_string(),
                    actual.to_string(),
                    "Mismatch at coefficient index {}",
                    i,
                );
            }
        }
    }

    #[test]
    fn test_polynomial_content() {
        let tests = vec![
            (vec![q(6, 1), q(5, 3), q(3, 2)], q(1, 6)),
            (vec![q(0, 1)], q(0, 1)),
            (vec![], q(0, 1)),
        ];

        for (coeffs, expected) in tests {
            let actual = Polynomial::new(coeffs).content();
            assert_eq!(expected.to_string(), actual.to_string());
        }
    }

    #[test]
    fn test_polynomial_divide() {
        let tests = vec![(
            vec![q(7, 1), q(-6, 1), q(9, 1), q(3, 1), q(5, 1)],
            vec![q(1, 1), q(-2, 1), q(1, 1)],
            vec![q(30, 1), q(13, 1), q(5, 1)],
            vec![q(-23, 1), q(41, 1)],
        )];

        for (lhs, rhs, expected_quotient, expected_remainder) in tests {
            let lhs = Polynomial::new(lhs);
            let rhs = Polynomial::new(rhs);

            let (actual_quotient, actual_remainder) = lhs.divide(rhs).expect("should divide");
            let actual_quotient = actual_quotient.as_coefficients();
            let actual_remainder = actual_remainder.as_coefficients();

            assert_eq!(
                expected_quotient.len(),
                actual_quotient.len(),
                "Quotient coefficient len mismatch",
            );

            for (i, (expected, actual)) in expected_quotient.iter().zip(actual_quotient).enumerate()
            {
                assert_eq!(
                    expected.to_string(),
                    actual.to_string(),
                    "Quotient coefficient mismatch at index {}",
                    i,
                )
            }

            assert_eq!(
                expected_remainder.len(),
                actual_remainder.len(),
                "Remainder coefficient len mismatch",
            );

            for (i, (expected, actual)) in
                expected_remainder.iter().zip(actual_remainder).enumerate()
            {
                assert_eq!(
                    expected.to_string(),
                    actual.to_string(),
                    "Quotient coefficient mismatch at index {}",
                    i,
                )
            }
        }
    }
}
