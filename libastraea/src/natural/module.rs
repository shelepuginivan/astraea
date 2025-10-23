use std::{cmp::Ordering, collections::HashSet, fmt::Display, str::FromStr};

use crate::{Instruction, InstructionError, Module, NaturalNumber, math::sign::ToSign};

pub struct NaturalModule {}

impl NaturalModule {
    pub fn new() -> Self {
        NaturalModule {}
    }

    pub fn compare(lhs: NaturalNumber, rhs: NaturalNumber) -> Ordering {
        lhs.cmp(&rhs)
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
                if args.len() != 2 {
                    return Err(InstructionError::new(format!(
                        "expected 2 arguments, got {}",
                        args.len(),
                    )));
                }

                let lhs = match NaturalNumber::from_str(&args[0]) {
                    Ok(v) => v,
                    Err(e) => {
                        return Err(InstructionError::new(format!(
                            "cannot parse first argument: {}",
                            e.message
                        )));
                    }
                };

                let rhs = match NaturalNumber::from_str(&args[1]) {
                    Ok(v) => v,
                    Err(e) => {
                        return Err(InstructionError::new(format!(
                            "cannot parse second argument: {}",
                            e.message
                        )));
                    }
                };

                let result = Self::compare(lhs, rhs).to_sign();

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
