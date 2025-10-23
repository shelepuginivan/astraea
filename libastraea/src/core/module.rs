use std::collections::HashSet;
use std::fmt::Display;

use crate::core::{Instruction, InstructionError};

/// Module is a part of computer algebra system responsible for a set of instructions.
pub trait Module {
    /// Calls a method of the module specified by instruction, with given args.
    fn process_instruction(
        &self,
        instruction: Instruction,
        args: Vec<String>,
    ) -> Result<Box<dyn Display>, InstructionError>;

    /// Reports whether module implements the given instruction.
    fn implements(&self, instruction: Instruction) -> bool;

    /// Returns all instructions implemented by the module.
    fn methods(&self) -> HashSet<Instruction>;
}
