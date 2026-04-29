use std::collections::HashSet;

use astraea::prelude::*;
use astraea_symbol::{AST, Node};

use crate::{Instruction, InstructionError, Module};

pub struct SymbolModule;

impl Module for SymbolModule {
    fn process_instruction(
        &self,
        instruction: Instruction,
        args: Vec<String>,
    ) -> Result<Box<dyn Pretty>, InstructionError> {
        match instruction {
            Instruction::SymbolicPrefix => {
                let ast = AST::new(Node::add(Node::literal(6.0), Node::literal(9.0)));

                Ok(Box::new(ast.prefix_notation()))
            }

            Instruction::SymbolicPostfix => {
                let ast = AST::new(Node::add(Node::literal(6.0), Node::sin(Node::var("x"))));

                Ok(Box::new(ast.full_notation()))
            }

            Instruction::SymbolicDerivative => {
                let ast = AST::new(Node::add(Node::literal(6.0), Node::cos(Node::var("x"))));

                Ok(Box::new(ast.derivative("x").full_notation()))
            }

            _ => Err(InstructionError::unknown_instruction(instruction)),
        }
    }

    fn instructions(&self) -> HashSet<Instruction> {
        [
            Instruction::SymbolicPrefix,
            Instruction::SymbolicPostfix,
            Instruction::SymbolicDerivative,
        ]
        .into_iter()
        .collect()
    }
}
