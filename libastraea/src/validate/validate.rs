use std::{fmt::Display, str::FromStr};

use crate::{
    core::{Instruction, InstructionError},
    math::Digit,
    natural::NaturalNumber,
};

pub fn ensure_args_count(
    instruction: &Instruction,
    args: &Vec<String>,
    expected: usize,
) -> Result<(), InstructionError> {
    if args.len() != expected {
        return Err(InstructionError::new(format!(
            "{} expected {} arg(s), got {}",
            instruction,
            expected,
            args.len()
        )));
    }

    Ok(())
}

pub fn digit(value: &str) -> Result<Digit, InstructionError> {
    Digit::from_str(value).or_else(|e| Err(InstructionError::new(e.message)))
}

pub fn natural(value: &str) -> Result<NaturalNumber, InstructionError> {
    NaturalNumber::from_str(value).or_else(|e| Err(InstructionError::new(e.message)))
}

pub fn usize(value: &str) -> Result<usize, InstructionError> {
    usize::from_str(value)
        .or_else(|_| Err(InstructionError::new(r#"cannot convert "{}" to usize"#)))
}

/// Parses arguments provided to the particular instruction and ensures their validity.
pub fn ensure_args<T>(
    instruction: &Instruction,
    args: Vec<String>,
    count: usize,
) -> Result<Vec<T>, InstructionError>
where
    T: FromStr,
    T::Err: Display,
{
    ensure_args_count(instruction, &args, count)?;

    let mut res = Vec::with_capacity(count);

    for i in 0..count {
        let arg = match T::from_str(&args[i]) {
            Ok(v) => v,
            Err(e) => {
                return Err(InstructionError::new(format!(
                    "cannot parse argument {}: {}",
                    i + 1,
                    e,
                )));
            }
        };

        res.push(arg);
    }

    Ok(res)
}

pub fn one_arg<T>(instruction: &Instruction, args: Vec<String>) -> Result<T, InstructionError>
where
    T: FromStr,
    T::Err: Display,
{
    let args = ensure_args(instruction, args, 1)?;
    let mut args_iter = args.into_iter();
    let first = args_iter.next().unwrap();

    Ok(first)
}

pub fn two_args<T>(instruction: &Instruction, args: Vec<String>) -> Result<(T, T), InstructionError>
where
    T: FromStr,
    T::Err: Display,
{
    let args = ensure_args(instruction, args, 2)?;
    let mut args_iter = args.into_iter();
    let first = args_iter.next().unwrap();
    let second = args_iter.next().unwrap();

    Ok((first, second))
}

pub fn three_args<T>(
    instruction: &Instruction,
    args: Vec<String>,
) -> Result<(T, T, T), InstructionError>
where
    T: FromStr,
    T::Err: Display,
{
    let args = ensure_args(instruction, args, 3)?;
    let mut args_iter = args.into_iter();
    let first = args_iter.next().unwrap();
    let second = args_iter.next().unwrap();
    let third = args_iter.next().unwrap();

    Ok((first, second, third))
}
