use astraea::combinatorics;
use astraea::formatting::Pretty;
use astraea::natural::Natural;
use std::collections::HashSet;

use crate::instruction::Instruction;
use crate::module::Module;
use crate::validate::{self, InstructionError};

pub struct CombinatoricsModule {}

impl CombinatoricsModule {
    pub fn new() -> Self {
        CombinatoricsModule {}
    }
}

impl Module for CombinatoricsModule {
    fn process_instruction(
        &self,
        instruction: Instruction,
        args: Vec<String>,
    ) -> Result<Box<dyn Pretty>, InstructionError> {
        match instruction {
            Instruction::CombinatoricsFactorial => {
                let n: Natural = validate::one_arg(args)?;
                Ok(Box::new(combinatorics::factorial(&n)))
            }

            Instruction::CombinatoricsSubfactorial => {
                let n: Natural = validate::one_arg(args)?;
                Ok(Box::new(combinatorics::subfactorial(&n)))
            }

            Instruction::CombinatoricsCombinations => {
                let (n, k) = validate::two_args::<Natural>(args)?;
                Ok(Box::new(combinatorics::combinations(&n, &k)))
            }

            Instruction::CombinatoricsPlacements => {
                let (n, k) = validate::two_args::<Natural>(args)?;
                Ok(Box::new(combinatorics::placements(&n, &k)))
            }

            Instruction::CombinatoricsStirlingFirstKind => {
                let (n, k) = validate::two_args::<Natural>(args)?;
                let n = validate::natural_can_cast_to_usize(n, 0)?;
                let k = validate::natural_can_cast_to_usize(k, 0)?;
                Ok(Box::new(combinatorics::stirling_first_kind(&n, &k)))
            }

            Instruction::CombinatoricsStirlingSecondKind => {
                let (n, k) = validate::two_args::<Natural>(args)?;
                let n = validate::natural_can_cast_to_usize(n, 0)?;
                let k = validate::natural_can_cast_to_usize(k, 0)?;
                Ok(Box::new(combinatorics::stirling_second_kind(&n, &k)))
            }

            Instruction::CombinatoricsBell => {
                let n: Natural = validate::one_arg(args)?;
                let n = validate::natural_can_cast_to_usize(n, 0)?;
                Ok(Box::new(combinatorics::bell(&n)))
            }

            Instruction::CombinatoricsFibonacci => {
                let n: Natural = validate::one_arg(args)?;
                let n = validate::natural_can_cast_to_usize(n, 0)?;
                Ok(Box::new(combinatorics::fibonacci(&n)))
            }

            Instruction::CombinatoricsLucas => {
                let n: Natural = validate::one_arg(args)?;
                let n = validate::natural_can_cast_to_usize(n, 0)?;
                Ok(Box::new(combinatorics::lucas(&n)))
            }

            Instruction::CombinatoricsCatalan => {
                let n: Natural = validate::one_arg(args)?;
                Ok(Box::new(combinatorics::catalan(&n)))
            }

            Instruction::CombinatoricsSimplex => {
                let (k, n) = validate::two_args::<Natural>(args)?;
                Ok(Box::new(combinatorics::simplex(&k, &n)))
            }

            _ => Err(InstructionError::unknown_instruction(instruction)),
        }
    }

    fn implements(&self, instruction: Instruction) -> bool {
        self.instructions().contains(&instruction)
    }

    fn instructions(&self) -> HashSet<Instruction> {
        [
            Instruction::CombinatoricsFactorial,
            Instruction::CombinatoricsSubfactorial,
            Instruction::CombinatoricsCombinations,
            Instruction::CombinatoricsPlacements,
            Instruction::CombinatoricsStirlingFirstKind,
            Instruction::CombinatoricsStirlingSecondKind,
            Instruction::CombinatoricsBell,
            Instruction::CombinatoricsFibonacci,
            Instruction::CombinatoricsLucas,
            Instruction::CombinatoricsCatalan,
            Instruction::CombinatoricsSimplex,
        ]
        .into_iter()
        .collect()
    }
}
