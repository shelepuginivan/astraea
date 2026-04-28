use std::collections::HashSet;

use astraea::prelude::*;
use astraea_parser::ast::{AST, ASTNode, BinaryOp};

use crate::{Instruction, InstructionError, Module};

pub struct SymbolicModule {}

impl SymbolicModule {
    pub fn new() -> Self {
        SymbolicModule {}
    }
}

impl Module for SymbolicModule {
    fn process_instruction(
        &self,
        instruction: Instruction,
        args: Vec<String>,
    ) -> Result<Box<dyn Pretty>, InstructionError> {
        match instruction {
            Instruction::SymbolicPrefix => {
                let ast = AST::new(ASTNode::BinaryOp {
                    operator: BinaryOp::Add,
                    lhs: Box::new(ASTNode::Literal {
                        value: "6".to_string(),
                    }),
                    rhs: Box::new(ASTNode::Literal {
                        value: "7".to_string(),
                    }),
                });

                ast.prefix_notation();

                Err(InstructionError::unknown_instruction(instruction))
            }

            _ => Err(InstructionError::unknown_instruction(instruction)),
        }
    }

    fn implements(&self, instruction: Instruction) -> bool {
        self.instructions().contains(&instruction)
    }

    fn instructions(&self) -> HashSet<Instruction> {
        [Instruction::SymbolicPrefix].into_iter().collect()
    }
}
