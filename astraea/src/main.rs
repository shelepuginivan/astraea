mod cli;

use clap::Parser;
use libastraea::{
    core::{Instruction, InstructionErrorReason, Module, ModuleGroup},
    integer::IntegerModule,
    natural::NaturalModule,
    polynomial::PolynomialModule,
    rational::RationalModule,
};
use std::str::FromStr;

use crate::cli::{Args, Error};

fn main() {
    let args = Args::parse();
    let modules = ModuleGroup::new(vec![
        Box::new(NaturalModule::new()),
        Box::new(IntegerModule::new()),
        Box::new(RationalModule::new()),
        Box::new(PolynomialModule::new()),
    ]);

    let instruction = match Instruction::from_str(&args.instruction) {
        Ok(i) => i,
        Err(..) => Error::UnknownInstruction.print(&args),
    };

    if !modules.implements(instruction) {
        Error::InstructionNotImplemented.print(&args)
    }

    let result = match modules.process_instruction(instruction, args.args.clone()) {
        Ok(res) => res,
        Err(e) => match e.reason {
            InstructionErrorReason::Argument(arg_index) => {
                Error::InvalidArgument(arg_index, e.message).print(&args)
            }

            InstructionErrorReason::ArgumentsCount(expected, actual) => {
                Error::InvalidNumberOfArguments(expected, actual).print(&args)
            }

            InstructionErrorReason::Calculation(caused_by) => {
                Error::Calculation(caused_by, e.message).print(&args);
            }

            InstructionErrorReason::Instruction => unreachable!(),
        },
    };

    println!("{}", result.prettify());
}
