//! astraea is a library for arbitrary-precision arithmetic and a computer algebra system.
//!
//! # Examples
//!
//! ## Natural numbers
//!
//! ```
//! use std::str::FromStr;
//!
//! use astraea::math::SemiRing;
//! use astraea::natural::NaturalNumber;
//!
//! let a = NaturalNumber::from_str(&"9".repeat(1_000_000)).unwrap();
//! let b = NaturalNumber::one();
//!
//! let sum = a + b;
//!
//! println!("The result contains {} digits!", sum.len());
//! ```
//!
//! See: [`natural::NaturalNumber`].
//!
//! ## Integers
//!
//! ```
//! use astraea::integer::Integer;
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
//! use astraea::formatting::Pretty;
//! use astraea::math::Ring;
//! use astraea::rational::RationalNumber;
//!
//! let a = RationalNumber::from_str("1111111111111111/6666666666666666").unwrap();
//! let b = RationalNumber::from_str("1111111111111111/3333333333333333").unwrap();
//! let c = RationalNumber::from_str("1111111111111111/2222222222222222").unwrap();
//!
//! let sum = a + b + c;
//!
//! assert!(sum.is_integer());
//! ```
//!
//! See: [`rational::RationalNumber`].
//!
//! ## Polynomials
//!
//! ```
//! use std::str::FromStr;
//!
//! use astraea::polynomial::Polynomial;
//! use astraea::rational::RationalNumber;
//!
//! let lhs = Polynomial::<RationalNumber>::from_str("x^100 + 1").unwrap();
//! let rhs = Polynomial::<RationalNumber>::from_str("100x + 1").unwrap();
//!
//! let quotient = (lhs / rhs).unwrap();
//!
//! println!("Quotient degree: {}", quotient.degree());
//! println!("Quotient leading coefficient: {}", quotient.leading_coefficient());
//! ```
//!
//! See: [`polynomial::Polynomial`].
pub mod error;
pub mod formatting;
pub mod integer;
pub mod math;
pub mod natural;
pub mod polynomial;
pub mod rational;
