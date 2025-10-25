use std::{fmt::Display, str::FromStr};

use crate::core::InstructionError;
use crate::math::Digit;
use crate::natural::NaturalNumber;

pub fn ensure_args_count(args: &Vec<String>, expected: usize) -> Result<(), InstructionError> {
    if args.len() != expected {
        return Err(InstructionError::count(expected, args.len()));
    }

    Ok(())
}

pub fn get_digit(args: &Vec<String>, arg_index: usize) -> Result<Digit, InstructionError> {
    Digit::from_str(&args[arg_index])
        .or_else(|e| Err(InstructionError::invalid_arg(e.message, arg_index)))
}

pub fn get_natural(
    args: &Vec<String>,
    arg_index: usize,
) -> Result<NaturalNumber, InstructionError> {
    NaturalNumber::from_str(&args[arg_index])
        .or_else(|e| Err(InstructionError::invalid_arg(e.message, arg_index)))
}

pub fn get_usize(args: &Vec<String>, arg_index: usize) -> Result<usize, InstructionError> {
    let v = &args[arg_index];
    usize::from_str(v).or_else(|_| {
        Err(InstructionError::invalid_arg(
            format!("cannot convert \"{}\" to usize", v),
            arg_index,
        ))
    })
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

pub fn three_args<T>(args: Vec<String>) -> Result<(T, T, T), InstructionError>
where
    T: FromStr,
    T::Err: Display,
{
    let args = ensure_args(args, 3)?;
    let mut args_iter = args.into_iter();
    let first = args_iter.next().unwrap();
    let second = args_iter.next().unwrap();
    let third = args_iter.next().unwrap();

    Ok((first, second, third))
}
