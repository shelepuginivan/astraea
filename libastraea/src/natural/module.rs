use std::{collections::HashSet, fmt::Display};

use crate::core::{Instruction, InstructionError, Module};
use crate::digit;
use crate::math::Digit;
use crate::math::sign::ToSign;
use crate::natural::NaturalNumber;
use crate::validate::{self, ensure_args_count};

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
    ) -> Result<Box<dyn Display>, InstructionError> {
        match instruction {
            Instruction::NaturalCompare => {
                let (lhs, rhs) = validate::two_args::<NaturalNumber>(&instruction, args)?;
                Ok(Box::new(lhs.cmp(&rhs).to_sign()))
            }

            Instruction::NaturalIsZero => {
                let n: NaturalNumber = validate::one_arg(&instruction, args)?;
                Ok(Box::new(n.is_zero()))
            }

            Instruction::NaturalIncrement => {
                let n: NaturalNumber = validate::one_arg(&instruction, args)?;
                Ok(Box::new(n.inc()))
            }

            Instruction::NaturalAdd => {
                let (lhs, rhs) = validate::two_args::<NaturalNumber>(&instruction, args)?;
                Ok(Box::new(lhs + rhs))
            }

            Instruction::NaturalSubtract => {
                let (lhs, rhs) = validate::two_args::<NaturalNumber>(&instruction, args)?;

                match lhs - rhs {
                    Ok(res) => Ok(Box::new(res)),
                    Err(err) => Err(InstructionError::new(err.message)),
                }
            }

            Instruction::NaturalMultiplyByDigit => {
                ensure_args_count(&instruction, &args, 2)?;

                let lhs = validate::natural(&args[0])?;
                let rhs = validate::digit(&args[1])?;

                Ok(Box::new(lhs * rhs))
            }

            Instruction::NaturalMultiplyByPowerOfTen => {
                ensure_args_count(&instruction, &args, 2)?;

                let lhs = validate::natural(&args[0])?;
                let rhs = validate::usize(&args[1])?;

                Ok(Box::new(lhs.times_pow10(rhs)))
            }

            Instruction::NaturalMultiply => {
                let (lhs, rhs) = validate::two_args::<NaturalNumber>(&instruction, args)?;
                Ok(Box::new(lhs * rhs))
            }

            Instruction::NaturalSubtractMultipliedByDigit => {
                validate::ensure_args_count(&instruction, &args, 3)?;

                let lhs = validate::natural(&args[0])?;
                let rhs = validate::natural(&args[1])?;
                let digit = validate::digit(&args[2])?;

                match lhs - rhs * digit {
                    Ok(v) => Ok(Box::new(v)),
                    Err(e) => Err(InstructionError::new(e.message)),
                }
            }

            Instruction::NaturalCalculateDivisionDigit => {
                validate::ensure_args_count(&instruction, &args, 3)?;

                let lhs = validate::natural(&args[0])?;
                let rhs = validate::natural(&args[1])?;
                let k = validate::usize(&args[2])?;

                if k + rhs.len() > lhs.len() {
                    return Ok(Box::new(digit!(0)));
                }

                let lhs_digit = lhs.lsd_at(k + rhs.len() - 1);
                let rhs_digit = rhs.msd_at(0);

                Ok(Box::new(lhs_digit / rhs_digit))
            }

            Instruction::NaturalQuotient => {
                let (lhs, rhs) = validate::two_args::<NaturalNumber>(&instruction, args)?;

                match lhs / rhs {
                    Ok(v) => Ok(Box::new(v)),
                    Err(e) => Err(InstructionError::new(e.message)),
                }
            }

            Instruction::NaturalRemainder => {
                let (lhs, rhs) = validate::two_args::<NaturalNumber>(&instruction, args)?;

                match lhs % rhs {
                    Ok(v) => Ok(Box::new(v)),
                    Err(e) => Err(InstructionError::new(e.message)),
                }
            }

            Instruction::NaturalGCD => {
                let (lhs, rhs) = validate::two_args::<NaturalNumber>(&instruction, args)?;
                Ok(Box::new(lhs.gcd(rhs)))
            }

            Instruction::NaturalLCM => {
                let (lhs, rhs) = validate::two_args::<NaturalNumber>(&instruction, args)?;
                Ok(Box::new(lhs.lcm(rhs)))
            }

            _ => Err(InstructionError::new(format!(
                "unknown instruction: {:?}",
                instruction
            ))),
        }
    }

    fn implements(&self, instruction: Instruction) -> bool {
        self.methods().contains(&instruction)
    }

    fn methods(&self) -> HashSet<Instruction> {
        let mut method_set: HashSet<Instruction> = HashSet::new();

        method_set.insert(Instruction::NaturalCompare);
        method_set.insert(Instruction::NaturalIsZero);
        method_set.insert(Instruction::NaturalIncrement);
        method_set.insert(Instruction::NaturalAdd);
        method_set.insert(Instruction::NaturalSubtract);
        method_set.insert(Instruction::NaturalMultiplyByDigit);
        method_set.insert(Instruction::NaturalMultiplyByPowerOfTen);
        method_set.insert(Instruction::NaturalMultiply);
        method_set.insert(Instruction::NaturalSubtractMultipliedByDigit);
        method_set.insert(Instruction::NaturalCalculateDivisionDigit);
        method_set.insert(Instruction::NaturalQuotient);
        method_set.insert(Instruction::NaturalRemainder);
        method_set.insert(Instruction::NaturalGCD);
        method_set.insert(Instruction::NaturalLCM);

        method_set
    }
}
