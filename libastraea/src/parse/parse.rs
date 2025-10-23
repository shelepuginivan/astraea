use std::{fmt::Display, str::FromStr};

use crate::{Instruction, InstructionError};

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
