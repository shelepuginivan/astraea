use astraea::formatting::Pretty;
use astraea::polynomial::Polynomial;
use astraea::rational::RationalNumber;
use std::collections::HashSet;

use crate::instruction::Instruction;
use crate::module::Module;
use crate::validate::{self, InstructionError};

pub struct PolynomialModule {}

impl PolynomialModule {
    pub fn new() -> Self {
        PolynomialModule {}
    }
}

impl Module for PolynomialModule {
    fn process_instruction(
        &self,
        instruction: Instruction,
        args: Vec<String>,
    ) -> Result<Box<dyn Pretty>, InstructionError> {
        match instruction {
            Instruction::PolynomialAdd => {
                let (lhs, rhs) = validate::two_args::<Polynomial<RationalNumber>>(args)?;

                Ok(Box::new(lhs + rhs))
            }

            Instruction::PolynomialSubtract => {
                let (lhs, rhs) = validate::two_args::<Polynomial<RationalNumber>>(args)?;

                Ok(Box::new(lhs - rhs))
            }

            Instruction::PolynomialMultiplyByRational => {
                validate::ensure_args_count(&args, 2)?;

                let lhs = validate::get_polynomial::<RationalNumber>(&args, 0)?;
                let rhs = validate::get_rational(&args, 1)?;

                Ok(Box::new(lhs * rhs))
            }

            Instruction::PolynomialMultiplyByPowerOfX => {
                validate::ensure_args_count(&args, 2)?;

                let lhs = validate::get_polynomial::<RationalNumber>(&args, 0)?;
                let rhs = validate::get_usize(&args, 1)?;

                Ok(Box::new(lhs.times_pow_x(rhs)))
            }

            Instruction::PolynomialLeadingCoefficient => {
                let p: Polynomial<RationalNumber> = validate::one_arg(args)?;

                Ok(Box::new(p.leading_coefficient()))
            }

            Instruction::PolynomialDegree => {
                let p: Polynomial<RationalNumber> = validate::one_arg(args)?;

                Ok(Box::new(p.degree()))
            }

            Instruction::PolynomialContent => {
                let p: Polynomial<RationalNumber> = validate::one_arg(args)?;

                Ok(Box::new(p.content()))
            }

            Instruction::PolynomialMultiply => {
                let (lhs, rhs) = validate::two_args::<Polynomial<RationalNumber>>(args)?;

                Ok(Box::new(lhs * rhs))
            }

            Instruction::PolynomialQuotient => {
                let (lhs, rhs) = validate::two_args::<Polynomial<RationalNumber>>(args)?;

                match lhs / rhs {
                    Ok(v) => Ok(Box::new(v)),
                    Err(e) => Err(InstructionError::calculation(1, e.message)),
                }
            }

            Instruction::PolynomialRemainder => {
                let (lhs, rhs) = validate::two_args::<Polynomial<RationalNumber>>(args)?;

                match lhs % rhs {
                    Ok(v) => Ok(Box::new(v)),
                    Err(e) => Err(InstructionError::calculation(1, e.message)),
                }
            }

            Instruction::PolynomialGCD => {
                let (lhs, rhs) = validate::two_args::<Polynomial<RationalNumber>>(args)?;

                Ok(Box::new(lhs.gcd(rhs)))
            }

            Instruction::PolynomialDerivative => {
                let p: Polynomial<RationalNumber> = validate::one_arg(args)?;

                Ok(Box::new(p.derivative()))
            }

            Instruction::PolynomialFlatten => {
                let p: Polynomial<RationalNumber> = validate::one_arg(args)?;

                Ok(Box::new(p.flatten()))
            }

            _ => Err(InstructionError::unknown_instruction(instruction)),
        }
    }

    fn implements(&self, instruction: Instruction) -> bool {
        self.instructions().contains(&instruction)
    }

    fn instructions(&self) -> HashSet<Instruction> {
        [
            Instruction::PolynomialAdd,
            Instruction::PolynomialSubtract,
            Instruction::PolynomialMultiplyByRational,
            Instruction::PolynomialMultiplyByPowerOfX,
            Instruction::PolynomialLeadingCoefficient,
            Instruction::PolynomialDegree,
            Instruction::PolynomialContent,
            Instruction::PolynomialMultiply,
            Instruction::PolynomialQuotient,
            Instruction::PolynomialRemainder,
            Instruction::PolynomialGCD,
            Instruction::PolynomialDerivative,
            Instruction::PolynomialFlatten,
        ]
        .into_iter()
        .collect()
    }
}
