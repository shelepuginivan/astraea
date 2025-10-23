use std::{collections::HashSet, fmt::Display};

use crate::core::{Instruction, InstructionError, Module};
use crate::math::sign::ToSign;
use crate::natural::NaturalNumber;
use crate::validate::ensure_args;

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
                let args: Vec<NaturalNumber> = ensure_args(instruction, args, 2)?;
                let lhs = &args[0];
                let rhs = &args[1];
                let result = lhs.cmp(rhs).to_sign();

                Ok(Box::new(result))
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
