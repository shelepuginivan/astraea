use std::collections::HashSet;

use crate::core::{Instruction, InstructionError, Module};
use crate::formatting::Pretty;
use crate::integer::Integer;
use crate::rational::RationalNumber;
use crate::validate;

pub struct RationalModule {}

impl RationalModule {
    pub fn new() -> Self {
        RationalModule {}
    }
}

impl Module for RationalModule {
    fn process_instruction(
        &self,
        instruction: Instruction,
        args: Vec<String>,
    ) -> Result<Box<dyn Pretty>, InstructionError> {
        match instruction {
            Instruction::RationalReduce => {
                let v: RationalNumber = validate::one_arg(args)?;

                Ok(Box::new(v.reduce()))
            }

            Instruction::RationalIsInteger => {
                let v: RationalNumber = validate::one_arg(args)?;

                Ok(Box::new(v.is_integer()))
            }

            Instruction::RationalFromInteger => {
                let v: Integer = validate::one_arg(args)?;

                Ok(Box::new(RationalNumber::from_integer(v)))
            }

            Instruction::RationalToInteger => {
                let v: RationalNumber = validate::one_arg(args)?;

                match v.to_integer() {
                    Ok(int) => Ok(Box::new(int)),
                    Err(err) => Err(InstructionError::calculation(0, err.message)),
                }
            }

            Instruction::RationalAdd => {
                let (lhs, rhs) = validate::two_args::<RationalNumber>(args)?;

                Ok(Box::new((lhs + rhs).reduce()))
            }

            Instruction::RationalSubtract => {
                let (lhs, rhs) = validate::two_args::<RationalNumber>(args)?;

                Ok(Box::new((lhs - rhs).reduce()))
            }

            Instruction::RationalMultiply => {
                let (lhs, rhs) = validate::two_args::<RationalNumber>(args)?;

                Ok(Box::new((lhs * rhs).reduce()))
            }

            Instruction::RationalDivide => {
                let (lhs, rhs) = validate::two_args::<RationalNumber>(args)?;

                match lhs / rhs {
                    Ok(v) => Ok(Box::new(v.reduce())),
                    Err(err) => Err(InstructionError::calculation(0, err.message)),
                }
            }

            _ => Err(InstructionError::unknown_instruction(instruction)),
        }
    }

    fn implements(&self, instruction: Instruction) -> bool {
        self.methods().contains(&instruction)
    }

    fn methods(&self) -> HashSet<Instruction> {
        [
            Instruction::RationalReduce,
            Instruction::RationalIsInteger,
            Instruction::RationalFromInteger,
            Instruction::RationalToInteger,
            Instruction::RationalAdd,
            Instruction::RationalSubtract,
            Instruction::RationalMultiply,
            Instruction::RationalDivide,
        ]
        .into_iter()
        .collect()
    }
}
