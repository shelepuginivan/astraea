mod cli;

use std::{process, str::FromStr};

use crate::cli::Args;
use clap::Parser;
use libastraea::{
    core::{Instruction, Module, ModuleGroup},
    integer::IntegerModule,
    natural::NaturalModule,
};

fn main() {
    let args = Args::parse();
    let modules = ModuleGroup::new(vec![
        Box::new(NaturalModule::new()),
        Box::new(IntegerModule::new()),
    ]);

    let instruction = match Instruction::from_str(&args.instruction) {
        Ok(i) => i,
        Err(e) => {
            eprintln!("{}", e.message);
            process::exit(1);
        }
    };

    if !modules.implements(instruction) {
        eprintln!("instruction {} is not implemented", instruction);
        process::exit(1);
    }

    let result = match modules.process_instruction(instruction, args.params) {
        Ok(res) => res,
        Err(e) => {
            eprintln!("{}", e.message);
            process::exit(1);
        }
    };

    println!("{}", result);
}
