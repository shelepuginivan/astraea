use std::fmt::Display;

#[derive(Debug)]
pub enum InstructionErrorReason {
    Instruction,
    Argument(usize),
    ArgumentsCount(usize, usize),
    Calculation(usize),
}

#[derive(Debug)]
pub struct InstructionError {
    pub message: String,
    pub reason: InstructionErrorReason,
}

impl InstructionError {
    pub fn new<S: Into<String>>(message: S, reason: InstructionErrorReason) -> Self {
        Self {
            reason,
            message: message.into(),
        }
    }

    pub fn unknown_instruction<S: Into<String>>(instruction: S) -> Self {
        Self {
            message: format!("unknown instruction: \"{}\"", instruction.into()),
            reason: InstructionErrorReason::Instruction,
        }
    }

    pub fn calculation<S: Into<String>>(caused_by_arg: usize, message: S) -> Self {
        Self {
            message: message.into(),
            reason: InstructionErrorReason::Calculation(caused_by_arg),
        }
    }

    pub fn invalid_arg<S: Into<String>>(message: S, arg_index: usize) -> Self {
        Self {
            message: message.into(),
            reason: InstructionErrorReason::Argument(arg_index),
        }
    }

    pub fn count(expected: usize, got: usize) -> Self {
        let args_word = if expected == 1 { "arg" } else { "args" };
        let message = format!("expected {} {}, got {}", expected, args_word, got);

        Self {
            message,
            reason: InstructionErrorReason::ArgumentsCount(expected, got),
        }
    }
}

impl Display for InstructionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.message)
    }
}

#[derive(Debug)]
pub struct ParseError {
    pub message: String,
}

impl ParseError {
    pub fn new<S: Into<String>>(message: S) -> Self {
        Self {
            message: message.into(),
        }
    }
}

impl Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.message)
    }
}

#[derive(Debug)]
pub struct ValueError {
    pub message: String,
}

impl ValueError {
    pub fn new<S: Into<String>>(message: S) -> Self {
        Self {
            message: message.into(),
        }
    }
}

impl Display for ValueError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.message)
    }
}
