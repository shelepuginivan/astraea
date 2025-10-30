use std::{fmt::Display, str::FromStr};

use crate::core::InstructionError;
use crate::math::{Digit, Field};
use crate::natural::NaturalNumber;
use crate::polynomial::Polynomial;
use crate::rational::RationalNumber;

/// Ensures number of arguments provided to the instruction call.
pub fn ensure_args_count(args: &Vec<String>, expected: usize) -> Result<(), InstructionError> {
    if args.len() != expected {
        return Err(InstructionError::count(expected, args.len()));
    }

    Ok(())
}

/// Parses arguments provided to the particular instruction and ensures their validity.
pub fn ensure_args<T>(args: Vec<String>, count: usize) -> Result<Vec<T>, InstructionError>
where
    T: FromStr,
    T::Err: Display,
{
    ensure_args_count(&args, count)?;

    let mut res = Vec::with_capacity(count);

    for i in 0..count {
        let arg = match T::from_str(&args[i]) {
            Ok(v) => v,
            Err(e) => {
                return Err(InstructionError::invalid_arg(
                    format!("cannot parse: {}", e),
                    i,
                ));
            }
        };

        res.push(arg);
    }

    Ok(res)
}

/// Parses argument at the specified index as usize.
pub fn get_usize(args: &Vec<String>, arg_index: usize) -> Result<usize, InstructionError> {
    let v = &args[arg_index];
    usize::from_str(v).or_else(|_| {
        Err(InstructionError::invalid_arg(
            format!("cannot convert \"{}\" to usize", v),
            arg_index,
        ))
    })
}

/// Parses argument at the specified index as Digit.
pub fn get_digit(args: &Vec<String>, arg_index: usize) -> Result<Digit, InstructionError> {
    Digit::from_str(&args[arg_index])
        .or_else(|e| Err(InstructionError::invalid_arg(e.message, arg_index)))
}

/// Parses argument at the specified index as NaturalNumber.
pub fn get_natural(
    args: &Vec<String>,
    arg_index: usize,
) -> Result<NaturalNumber, InstructionError> {
    NaturalNumber::from_str(&args[arg_index])
        .or_else(|e| Err(InstructionError::invalid_arg(e.message, arg_index)))
}

/// Parses argument at the specified index as RationalNumber.
pub fn get_rational(
    args: &Vec<String>,
    arg_index: usize,
) -> Result<RationalNumber, InstructionError> {
    RationalNumber::from_str(&args[arg_index])
        .or_else(|e| Err(InstructionError::invalid_arg(e.message, arg_index)))
}

/// Parses argument at the specified index as Polynomial.
pub fn get_polynomial<T: Field>(
    args: &Vec<String>,
    arg_index: usize,
) -> Result<Polynomial<T>, InstructionError> {
    Polynomial::from_str(&args[arg_index])
        .or_else(|e| Err(InstructionError::invalid_arg(e.message, arg_index)))
}

/// Ensures 1 argument was provided and parses it to the corresponding type.
pub fn one_arg<T>(args: Vec<String>) -> Result<T, InstructionError>
where
    T: FromStr,
    T::Err: Display,
{
    let args = ensure_args(args, 1)?;
    let mut args_iter = args.into_iter();
    let first = args_iter.next().unwrap();

    Ok(first)
}

/// Ensures 2 arguments was provided and parses them to the corresponding type.
pub fn two_args<T>(args: Vec<String>) -> Result<(T, T), InstructionError>
where
    T: FromStr,
    T::Err: Display,
{
    let args = ensure_args(args, 2)?;
    let mut args_iter = args.into_iter();
    let first = args_iter.next().unwrap();
    let second = args_iter.next().unwrap();

    Ok((first, second))
}
