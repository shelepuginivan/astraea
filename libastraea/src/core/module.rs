use std::collections::HashSet;

use crate::{Instruction, InstructionError};

/// Module is a part of computer algebra system responsible for a set of instructions.
pub trait Module {
    /// Type for the data which module operates on.
    type Data;

    /// Calls a method of the module specified by instruction, with given args.
    fn call(
        &self,
        instruction: Instruction,
        args: Vec<String>,
    ) -> Result<Self::Data, InstructionError>;

    /// Reports whether module implements the given instruction.
    fn implements(&self, instruction: Instruction) -> bool;

    /// Returns all instructions implemented by the module.
    fn methods(&self) -> HashSet<Instruction>;
}
