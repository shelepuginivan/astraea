use std::{collections::HashSet, fmt::Display};

use crate::core::{Instruction, InstructionError, Module};
use crate::math::sign::ToSign;
use crate::natural::NaturalNumber;
use crate::validate;

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
                let (lhs, rhs) = validate::two_args::<NaturalNumber>(instruction, args)?;
                Ok(Box::new(lhs.cmp(&rhs).to_sign()))
            }

            Instruction::NaturalIsZero => {
                let n: NaturalNumber = validate::one_arg(instruction, args)?;
                Ok(Box::new(n.is_zero()))
            }

            Instruction::NaturalIncrement => {
                let n: NaturalNumber = validate::one_arg(instruction, args)?;
                Ok(Box::new(n.inc()))
            }

            Instruction::NaturalAdd => {
                let (lhs, rhs) = validate::two_args::<NaturalNumber>(instruction, args)?;
                Ok(Box::new(lhs + rhs))
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
