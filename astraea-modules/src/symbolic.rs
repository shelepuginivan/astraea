use std::collections::HashSet;

use astraea::prelude::*;
use astraea_parser::ast::{AST, ASTNode, BinaryOp, Function};

use crate::{Instruction, InstructionError, Module};

pub struct SymbolicModule;

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
                    lhs: Box::new(ASTNode::Literal(6.0)),
                    rhs: Box::new(ASTNode::Literal(9.0)),
                });

                Ok(Box::new(ast.prefix_notation()))
            }

            Instruction::SymbolicPostfix => {
                let ast = AST::new(ASTNode::BinaryOp {
                    operator: BinaryOp::Mul,
                    lhs: Box::new(ASTNode::Literal(2.0)),
                    rhs: Box::new(ASTNode::Function(Function::Sin(Box::new(
                        ASTNode::BinaryOp {
                            operator: BinaryOp::Div,
                            lhs: Box::new(ASTNode::Variable("pi".to_string())),
                            rhs: Box::new(ASTNode::Literal(2.0)),
                        },
                    )))),
                });

                Ok(Box::new(ast.full_notation()))
            }

            Instruction::SymbolicDerivative => {
                let ast = AST::new(ASTNode::BinaryOp {
                    operator: BinaryOp::Mul,
                    lhs: Box::new(ASTNode::Literal(2.0)),
                    rhs: Box::new(ASTNode::Variable("x".to_string())),
                });

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
