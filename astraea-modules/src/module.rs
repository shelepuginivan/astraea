use astraea::formatting::Pretty;
use std::collections::HashSet;

use crate::instruction::Instruction;
use crate::validate::InstructionError;

/// Module is a part of computer algebra system responsible for a set of instructions.
pub trait Module {
    /// Calls a method of the module specified by instruction, with given args.
    fn process_instruction(
        &self,
        instruction: Instruction,
        args: Vec<String>,
    ) -> Result<Box<dyn Pretty>, InstructionError>;

    /// Reports whether module implements the given instruction.
    fn implements(&self, instruction: Instruction) -> bool;

    /// Returns all instructions implemented by the module.
    fn instructions(&self) -> HashSet<Instruction>;
}

pub struct ModuleGroup {
    modules: Vec<Box<dyn Module>>,
}

/// ModuleGroup is a composite for modules.
impl ModuleGroup {
    pub fn new(modules: Vec<Box<dyn Module>>) -> Self {
        Self { modules }
    }

    pub fn add_module(&mut self, module: Box<dyn Module>) {
        self.modules.push(module);
    }
}

impl Module for ModuleGroup {
    fn process_instruction(
        &self,
        instruction: Instruction,
        args: Vec<String>,
    ) -> Result<Box<dyn Pretty>, InstructionError> {
        for module in &self.modules {
            if module.implements(instruction) {
                return module.process_instruction(instruction, args);
            }
        }

        Err(InstructionError::unknown_instruction(instruction))
    }

    fn implements(&self, instruction: Instruction) -> bool {
        for module in &self.modules {
            if module.implements(instruction) {
                return true;
            }
        }

        false
    }

    fn instructions(&self) -> HashSet<Instruction> {
        let mut method_set: HashSet<Instruction> = HashSet::new();

        for module in &self.modules {
            method_set.extend(&module.instructions());
        }

        method_set
    }
}
