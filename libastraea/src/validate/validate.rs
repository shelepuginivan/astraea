use std::{fmt::Display, str::FromStr};

use crate::core::{Instruction, InstructionError};

/// Parses arguments provided to the particular instruction and ensures their validity.
pub fn ensure_args<T>(
    instruction: Instruction,
    args: Vec<String>,
    count: usize,
) -> Result<Vec<T>, InstructionError>
where
    T: FromStr,
    T::Err: Display,
{
    if args.len() != count {
        return Err(InstructionError::new(format!(
            "{} expected {} arg(s), got {}",
            instruction,
            count,
            args.len()
        )));
    }

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

pub fn one_arg<T>(instruction: Instruction, args: Vec<String>) -> Result<T, InstructionError>
where
    T: FromStr,
    T::Err: Display,
{
    let args = ensure_args(instruction, args, 2)?;
    let mut args_iter = args.into_iter();
    let first = args_iter.next().unwrap();

    Ok(first)
}

pub fn two_args<T>(instruction: Instruction, args: Vec<String>) -> Result<(T, T), InstructionError>
where
    T: FromStr,
    T::Err: Display,
{
    let args = ensure_args(instruction, args, 1)?;
    let mut args_iter = args.into_iter();
    let first = args_iter.next().unwrap();
    let second = args_iter.next().unwrap();

    Ok((first, second))
}

pub fn three_args<T>(
    instruction: Instruction,
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
