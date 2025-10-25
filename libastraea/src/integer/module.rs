use std::{collections::HashSet, fmt::Display};

use crate::core::{Instruction, InstructionError, Module};
use crate::integer::Integer;
use crate::natural::NaturalNumber;
use crate::validate::{one_arg, two_args};

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
    ) -> Result<Box<dyn Display>, InstructionError> {
        match instruction {
            Instruction::IntegerAbs => {
                let v: Integer = one_arg(args)?;

                Ok(Box::new(v.abs()))
            }

            Instruction::IntegerSgn => {
                let v: Integer = one_arg(args)?;

                Ok(Box::new(v.abs()))
            }

            Instruction::IntegerNeg => {
                let v: Integer = one_arg(args)?;

                Ok(Box::new(-v))
            }

            Instruction::IntegerFromNatural => {
                let v: NaturalNumber = one_arg(args)?;

                Ok(Box::new(Integer::from_natural(v)))
            }

            Instruction::IntegerToNatural => {
                let v: Integer = one_arg(args)?;

                match v.to_natural() {
                    Ok(v) => Ok(Box::new(v)),
                    Err(e) => Ok(Box::new(InstructionError::calculation(e.message))),
                }
            }

            Instruction::IntegerAdd => {
                let (lhs, rhs) = two_args::<Integer>(args)?;

                Ok(Box::new(lhs + rhs))
            }

            Instruction::IntegerSubtract => {
                let (lhs, rhs) = two_args::<Integer>(args)?;

                Ok(Box::new(lhs - rhs))
            }

            Instruction::IntegerMultiply => {
                let (lhs, rhs) = two_args::<Integer>(args)?;

                Ok(Box::new(lhs * rhs))
            }

            Instruction::IntegerQuotient => {
                let (lhs, rhs) = two_args::<Integer>(args)?;

                match lhs / rhs {
                    Ok(v) => Ok(Box::new(v)),
                    Err(e) => Ok(Box::new(InstructionError::calculation(e.message))),
                }
            }

            Instruction::IntegerRemainder => {
                let (lhs, rhs) = two_args::<Integer>(args)?;

                match lhs % rhs {
                    Ok(v) => Ok(Box::new(v)),
                    Err(e) => Ok(Box::new(InstructionError::calculation(e.message))),
                }
            }

            _ => Err(InstructionError::unknown_instruction(instruction)),
        }
    }

    fn implements(&self, instruction: Instruction) -> bool {
        self.methods().contains(&instruction)
    }

    fn methods(&self) -> HashSet<Instruction> {
        let mut method_set: HashSet<Instruction> = HashSet::new();

        method_set.insert(Instruction::IntegerAbs);
        method_set.insert(Instruction::IntegerSgn);
        method_set.insert(Instruction::IntegerNeg);
        method_set.insert(Instruction::IntegerFromNatural);
        method_set.insert(Instruction::IntegerToNatural);
        method_set.insert(Instruction::IntegerAdd);
        method_set.insert(Instruction::IntegerSubtract);
        method_set.insert(Instruction::IntegerMultiply);
        method_set.insert(Instruction::IntegerQuotient);
        method_set.insert(Instruction::IntegerRemainder);

        method_set
    }
}
