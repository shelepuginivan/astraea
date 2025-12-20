use astraea::prelude::*;
use std::collections::HashSet;

use crate::instruction::Instruction;
use crate::module::Module;
use crate::validate::{self, InstructionError};

pub struct IntegerModule {}

impl IntegerModule {
    pub fn new() -> Self {
        IntegerModule {}
    }
}

impl Module for IntegerModule {
    fn process_instruction(
        &self,
        instruction: Instruction,
        args: Vec<String>,
    ) -> Result<Box<dyn Pretty>, InstructionError> {
        match instruction {
            Instruction::IntegerAbs => {
                let v: Integer = validate::one_arg(args)?;

                Ok(Box::new(v.abs()))
            }

            Instruction::IntegerSgn => {
                let v: Integer = validate::one_arg(args)?;

                Ok(Box::new(v.abs()))
            }

            Instruction::IntegerNeg => {
                let v: Integer = validate::one_arg(args)?;

                Ok(Box::new(-v))
            }

            Instruction::IntegerFromNatural => {
                let v: Natural = validate::one_arg(args)?;

                Ok(Box::new(Integer::from_natural(v)))
            }

            Instruction::IntegerToNatural => {
                let v: Integer = validate::one_arg(args)?;

                match v.to_natural() {
                    Ok(v) => Ok(Box::new(v)),
                    Err(e) => Err(InstructionError::calculation(0, e.message)),
                }
            }

            Instruction::IntegerAdd => {
                let (lhs, rhs) = validate::two_args::<Integer>(args)?;

                Ok(Box::new(lhs + rhs))
            }

            Instruction::IntegerSubtract => {
                let (lhs, rhs) = validate::two_args::<Integer>(args)?;

                Ok(Box::new(lhs - rhs))
            }

            Instruction::IntegerMultiply => {
                let (lhs, rhs) = validate::two_args::<Integer>(args)?;

                Ok(Box::new(lhs * rhs))
            }

            Instruction::IntegerQuotient => {
                let (lhs, rhs) = validate::two_args::<Integer>(args)?;

                match lhs / rhs {
                    Ok(v) => Ok(Box::new(v)),
                    Err(e) => Err(InstructionError::calculation(1, e.message)),
                }
            }

            Instruction::IntegerRemainder => {
                let (lhs, rhs) = validate::two_args::<Integer>(args)?;

                match lhs % rhs {
                    Ok(v) => Ok(Box::new(v)),
                    Err(e) => Err(InstructionError::calculation(1, e.message)),
                }
            }

            Instruction::IntegerRoot => {
                validate::ensure_args_count(&args, 2)?;

                let n = validate::get_integer(&args, 0)?;
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
            Instruction::IntegerAbs,
            Instruction::IntegerSgn,
            Instruction::IntegerNeg,
            Instruction::IntegerFromNatural,
            Instruction::IntegerToNatural,
            Instruction::IntegerAdd,
            Instruction::IntegerSubtract,
            Instruction::IntegerMultiply,
            Instruction::IntegerQuotient,
            Instruction::IntegerRemainder,
            Instruction::IntegerRoot,
        ]
        .into_iter()
        .collect()
    }
}
