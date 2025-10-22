use std::fmt::Display;

pub struct InstructionError {
    message: String,
}

impl InstructionError {
    pub fn new(message: String) -> Self {
        InstructionError { message }
    }
}

impl Display for InstructionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.message)
    }
}
