use astraea::digit;
use astraea::prelude::*;
use std::collections::HashSet;

use crate::instruction::Instruction;
use crate::module::Module;
use crate::validate::{self, InstructionError};

pub struct NaturalModule {}

impl NaturalModule {
    pub fn new() -> Self {
        NaturalModule {}
    }
}

impl Module for NaturalModule {
    fn process_instruction(
        &self,
        instruction: Instruction,
        args: Vec<String>,
    ) -> Result<Box<dyn Pretty>, InstructionError> {
        match instruction {
            Instruction::NaturalCompare => {
                let (lhs, rhs) = validate::two_args::<Natural>(args)?;
                Ok(Box::new(lhs.cmp(&rhs)))
            }

            Instruction::NaturalIsZero => {
                let n: Natural = validate::one_arg(args)?;
                Ok(Box::new(n.is_zero()))
            }

            Instruction::NaturalIncrement => {
                let n: Natural = validate::one_arg(args)?;
                Ok(Box::new(n.inc()))
            }

            Instruction::NaturalAdd => {
                let (lhs, rhs) = validate::two_args::<Natural>(args)?;
                Ok(Box::new(lhs + rhs))
            }

            Instruction::NaturalSubtract => {
                let (lhs, rhs) = validate::two_args::<Natural>(args)?;

                match lhs - rhs {
                    Ok(res) => Ok(Box::new(res)),
                    Err(err) => Err(InstructionError::calculation(1, err.message)),
                }
            }

            Instruction::NaturalMultiplyByDigit => {
                validate::ensure_args_count(&args, 2)?;

                let lhs = validate::get_natural(&args, 0)?;
                let rhs = validate::get_digit(&args, 1)?;

                Ok(Box::new(lhs * rhs))
            }

            Instruction::NaturalMultiplyByPowerOfTen => {
                validate::ensure_args_count(&args, 2)?;

                let lhs = validate::get_natural(&args, 0)?;
                let rhs = validate::get_usize(&args, 1)?;

                Ok(Box::new(lhs.times_pow10(rhs)))
            }

            Instruction::NaturalMultiply => {
                let (lhs, rhs) = validate::two_args::<Natural>(args)?;
                Ok(Box::new(lhs * rhs))
            }

            Instruction::NaturalSubtractMultipliedByDigit => {
                validate::ensure_args_count(&args, 3)?;

                let lhs = validate::get_natural(&args, 0)?;
                let rhs = validate::get_natural(&args, 1)?;
                let digit = validate::get_digit(&args, 2)?;

                match lhs - rhs * digit {
                    Ok(v) => Ok(Box::new(v)),
                    Err(e) => Err(InstructionError::calculation(1, e.message)),
                }
            }

            Instruction::NaturalCalculateDivisionDigit => {
                validate::ensure_args_count(&args, 3)?;

                let lhs = validate::get_natural(&args, 0)?;
                let rhs = validate::get_natural(&args, 1)?;
                let k = validate::get_usize(&args, 2)?;

                if k + rhs.len() > lhs.len() {
                    return Ok(Box::new(digit!(0)));
                }

                let lhs_digit = lhs.lsd_at(k + rhs.len() - 1);
                let rhs_digit = rhs.msd_at(0);

                Ok(Box::new(lhs_digit / rhs_digit))
            }

            Instruction::NaturalQuotient => {
                let (lhs, rhs) = validate::two_args::<Natural>(args)?;

                match lhs / rhs {
                    Ok(v) => Ok(Box::new(v)),
                    Err(e) => Err(InstructionError::calculation(1, e.message)),
                }
            }

            Instruction::NaturalRemainder => {
                let (lhs, rhs) = validate::two_args::<Natural>(args)?;

                match lhs % rhs {
                    Ok(v) => Ok(Box::new(v)),
                    Err(e) => Err(InstructionError::calculation(1, e.message)),
                }
            }

            Instruction::NaturalGCD => {
                let (lhs, rhs) = validate::two_args::<Natural>(args)?;
                Ok(Box::new(lhs.gcd(rhs)))
            }

            Instruction::NaturalLCM => {
                let (lhs, rhs) = validate::two_args::<Natural>(args)?;
                Ok(Box::new(lhs.lcm(rhs)))
            }

            Instruction::NaturalRoot => {
                validate::ensure_args_count(&args, 2)?;

                let n = validate::get_natural(&args, 0)?;
                let p = validate::get_usize(&args, 1)?;

                match n.root(p) {
                    Ok(res) => Ok(Box::new(res)),
                    Err(e) => Err(InstructionError::calculation(1, e.message)),
                }
            }

            _ => Err(InstructionError::unknown_instruction(instruction)),
        }
    }

    fn implements(&self, instruction: Instruction) -> bool {
        self.instructions().contains(&instruction)
    }

    fn instructions(&self) -> HashSet<Instruction> {
        [
            Instruction::NaturalCompare,
            Instruction::NaturalIsZero,
            Instruction::NaturalIncrement,
            Instruction::NaturalAdd,
            Instruction::NaturalSubtract,
            Instruction::NaturalMultiplyByDigit,
            Instruction::NaturalMultiplyByPowerOfTen,
            Instruction::NaturalMultiply,
            Instruction::NaturalSubtractMultipliedByDigit,
            Instruction::NaturalCalculateDivisionDigit,
            Instruction::NaturalQuotient,
            Instruction::NaturalRemainder,
            Instruction::NaturalGCD,
            Instruction::NaturalLCM,
            Instruction::NaturalRoot,
        ]
        .into_iter()
        .collect()
    }
}
