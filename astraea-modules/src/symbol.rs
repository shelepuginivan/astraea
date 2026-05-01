use std::collections::HashSet;

use astraea::prelude::*;
use astraea_symbol::reduce::*;
use astraea_symbol::{AST, parse_postfix_notation, parse_prefix_notation};

use crate::{Instruction, InstructionError, InstructionErrorReason, Module, validate};

pub struct SymbolModule;

impl Module for SymbolModule {
    fn process_instruction(
        &self,
        instruction: Instruction,
        args: Vec<String>,
    ) -> Result<Box<dyn Pretty>, InstructionError<'_>> {
        match instruction {
            Instruction::SymbolicFromPrefix => {
                let s: String = validate::one_arg(args)?;
                let source = Box::leak(Box::new(s));
                let ast: AST<Rational> = match parse_prefix_notation(source) {
                    Ok(ast) => ast,
                    Err(err) => {
                        return Err(InstructionError::new(
                            "invalid prefix notation",
                            InstructionErrorReason::Symbol { arg: 0, err },
                        ));
                    }
                };

                Ok(Box::new(ast))
            }

            Instruction::SymbolicFromPostfix => {
                let s: String = validate::one_arg(args)?;
                let source = Box::leak(Box::new(s));
                let ast: AST<Rational> = match parse_postfix_notation(source) {
                    Ok(ast) => ast,
                    Err(err) => {
                        return Err(InstructionError::new(
                            "invalid postfix notation",
                            InstructionErrorReason::Symbol { arg: 0, err },
                        ));
                    }
                };

                Ok(Box::new(ast))
            }

            Instruction::SymbolicToPrefix => {
                let ast: AST<Rational> = validate::one_arg(args)?;
                Ok(Box::new(ast.prefix_notation()))
            }

            Instruction::SymbolicToPostfix => {
                let ast: AST<Rational> = validate::one_arg(args)?;
                Ok(Box::new(ast.postfix_notation()))
            }

            Instruction::SymbolicReduce => {
                let ast: AST<Rational> = validate::one_arg(args)?;

                Ok(Box::new(ast.reduce(&[
                    reduce_literal_add,
                    reduce_literal_sub,
                    reduce_literal_mul,
                    reduce_zero_add,
                    reduce_one_mul,
                    reduce_zero_mul,
                    reduce_structural_cancellation,
                ])))
            }

            Instruction::SymbolicDerivative => {
                let ast: AST<Rational> = validate::one_arg(args)?;
                Ok(Box::new(ast.derivative("x").field_reduce()))
            }

            _ => Err(InstructionError::unknown_instruction(instruction)),
        }
    }

    fn instructions(&self) -> HashSet<Instruction> {
        [
            Instruction::SymbolicFromPrefix,
            Instruction::SymbolicFromPostfix,
            Instruction::SymbolicToPrefix,
            Instruction::SymbolicToPostfix,
            Instruction::SymbolicDerivative,
            Instruction::SymbolicReduce,
        ]
        .into_iter()
        .collect()
    }
}
