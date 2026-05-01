use std::collections::HashSet;

use astraea::prelude::*;
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
            Instruction::SymbolicPrefix => {
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

            Instruction::SymbolicPostfix => {
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

            Instruction::SymbolicDerivative => {
                let ast: AST<Rational> = parse_prefix_notation("").unwrap();

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
