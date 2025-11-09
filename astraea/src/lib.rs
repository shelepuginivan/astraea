//! astraea is a library for arbitrary-precision arithmetic and a computer algebra system.
//!
//! # Examples
//!
//! ## Natural numbers
//!
//! ```
//! use std::str::FromStr;
//!
//! use astraea::prelude::*;
//!
//! let a = Natural::from_str(&"9".repeat(1_000_000)).unwrap();
//! let b = Natural::one();
//!
//! let sum = a + b;
//!
//! println!("The result contains {} digits!", sum.len());
//! ```
//!
//! See: [`natural::Natural`].
//!
//! ## Integers
//!
//! ```
//! use astraea::prelude::*;
//!
//! let a = Integer::from(2_u64.pow(60));
//! let b = Integer::from(2_u128.pow(120));
//!
//! let gcd = a.gcd(b);
//!
//! println!("Greatest common divisor is {}", gcd);
//! ```
//!
//! See: [`integer::Integer`].
//!
//! ## Rational numbers
//!
//! ```
//! use std::str::FromStr;
//!
//! use astraea::prelude::*;
//!
//! let a = Rational::from_str("1111111111111111/6666666666666666").unwrap();
//! let b = Rational::from_str("1111111111111111/3333333333333333").unwrap();
//! let c = Rational::from_str("1111111111111111/2222222222222222").unwrap();
//!
//! let sum = a + b + c;
//!
//! assert!(sum.is_integer());
//! ```
//!
//! See: [`rational::Rational`].
//!
//! ## Polynomials
//!
//! ```
//! use std::str::FromStr;
//!
//! use astraea::prelude::*;
//!
//! let lhs = Polynomial::<Rational>::from_str("x^100 + 1").unwrap();
//! let rhs = Polynomial::<Rational>::from_str("100x + 1").unwrap();
//!
//! let quotient = (lhs / rhs).unwrap();
//!
//! println!("Quotient degree: {}", quotient.degree());
//! println!("Quotient leading coefficient: {}", quotient.leading_coefficient());
//! ```
//!
//! See: [`polynomial::Polynomial`].
pub mod algebra;
pub mod combinatorics;
pub mod error;
pub mod formatting;
pub mod integer;
pub mod natural;
pub mod polynomial;
pub mod prelude;
pub mod rational;
pub mod sign;
