use std::str::FromStr;

use crate::InstructionError;

/// Instructions available in the computer algebra system.
#[derive(Debug, Eq, Hash, PartialEq)]
pub enum Instruction {
    /// Compares two natural numbers.
    ///
    /// - Index: N-1
    /// - Opcode: COM_NN_D
    NaturalCompare,

    /// Reports whether the natural number is zero.
    ///
    /// - Index: N-2
    /// - Opcode: NZER_N_B
    NaturalIsZero,

    /// Increments the natural number.
    ///
    /// - Index: N-3
    /// - Opcode: ADD_1N_N
    NaturalIncrement,

    /// Adds two natural numbers.
    ///
    /// - Index: N-4
    /// - Opcode: ADD_NN_N
    NaturalAdd,

    /// Subtracts second natural number from first.
    ///
    /// - Index: N-5
    /// - Opcode: SUB_NN_N
    NaturalSubtract,

    /// Multiplies natural number by a single digit.
    ///
    /// - Index: N-6
    /// - Opcode: MUL_ND_N
    NaturalMultiplyByDigit,

    /// Multiplies natural number by a power of 10, essentially performing a left shift.
    ///
    /// - Index: N-7
    /// - Opcode: MUL_Nk_N
    NaturalMultiplyByPowerOfTen,

    /// Multiplies two natural numbers.
    ///
    /// - Index: N-8
    /// - Opcode: MUL_NN_N
    NaturalMultiply,

    /// Subtracts natural number multiplied by digit from another natural number.
    ///
    /// - Index: N-9
    /// - Opcode: SUB_NDN_N
    NaturalSubtractMultipliedByDigit,

    /// Calculates the first digit of the division of a larger natural number by a smaller one,
    /// multiplied by 10<sup>k</sup>, where k is the position of the digit (zero-indexed).
    ///
    /// - Index: N-10
    /// - Opcode: DIV_NN_Dk
    NaturalCalculateDivisionDigit,

    /// Calculates the quotient of dividing the first natural number by the second.
    ///
    /// - Index: N-11
    /// - Opcode: DIV_NN_N
    NaturalQuotient,

    /// Calculates the remainder of dividing the first natural number by the second.
    ///
    /// - Index: N-12
    /// - Opcode: MOD_NN_N
    NaturalRemainder,

    /// Calculates GCD (greatest common divisor) of two natural numbers.
    ///
    /// - Index: N-13
    /// - Opcode: GCF_NN_N
    NaturalGCD,

    /// Calculates LCM (least common multiplier) of two natural numbers.
    ///
    /// - Index: N-14
    /// - Opcode: LCM_NN_N
    NaturalLCM,
}

impl Instruction {
    /// Returns opcode of the instruction.
    pub fn opcode(&self) -> String {
        match self {
            Instruction::NaturalCompare => "COM_NN_D".to_string(),
            Instruction::NaturalIsZero => "NZER_N_B".to_string(),
            Instruction::NaturalIncrement => "ADD_1N_N".to_string(),
            Instruction::NaturalAdd => "ADD_NN_N".to_string(),
            Instruction::NaturalSubtract => "SUB_NN_N".to_string(),
            Instruction::NaturalMultiplyByDigit => "MUL_ND_N".to_string(),
            Instruction::NaturalMultiplyByPowerOfTen => "MUL_Nk_N".to_string(),
            Instruction::NaturalMultiply => "MUL_NN_N".to_string(),
            Instruction::NaturalSubtractMultipliedByDigit => "SUB_NDN_N".to_string(),
            Instruction::NaturalCalculateDivisionDigit => "DIV_NN_Dk".to_string(),
            Instruction::NaturalQuotient => "DIV_NN_N".to_string(),
            Instruction::NaturalRemainder => "MOD_NN_N".to_string(),
            Instruction::NaturalGCD => "GCF_NN_N".to_string(),
            Instruction::NaturalLCM => "LCM_NN_N".to_string(),
        }
    }

    /// Returns index of the instruction.
    pub fn index(&self) -> String {
        match self {
            Instruction::NaturalCompare => "N-1".to_string(),
            Instruction::NaturalIsZero => "N-2".to_string(),
            Instruction::NaturalIncrement => "N-3".to_string(),
            Instruction::NaturalAdd => "N-4".to_string(),
            Instruction::NaturalSubtract => "N-5".to_string(),
            Instruction::NaturalMultiplyByDigit => "N-6".to_string(),
            Instruction::NaturalMultiplyByPowerOfTen => "N-7".to_string(),
            Instruction::NaturalMultiply => "N-8".to_string(),
            Instruction::NaturalSubtractMultipliedByDigit => "N-9".to_string(),
            Instruction::NaturalCalculateDivisionDigit => "N-10".to_string(),
            Instruction::NaturalQuotient => "N-11".to_string(),
            Instruction::NaturalRemainder => "N-12".to_string(),
            Instruction::NaturalGCD => "N-13".to_string(),
            Instruction::NaturalLCM => "N-14".to_string(),
        }
    }
}

impl FromStr for Instruction {
    type Err = InstructionError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "N-1" | "COM_NN_D" | "NaturalCompare" => Ok(Self::NaturalCompare),
            "N-2" | "NZER_N_B" | "NaturalIsZero" => Ok(Self::NaturalIsZero),
            "N-3" | "ADD_1N_N" | "NaturalIncrement" => Ok(Self::NaturalIncrement),
            "N-4" | "ADD_NN_N" | "NaturalAdd" => Ok(Self::NaturalAdd),
            "N-5" | "SUB_NN_N" | "NaturalSubtract" => Ok(Self::NaturalSubtract),
            "N-6" | "MUL_ND_N" | "NaturalMultiplyByDigit" => Ok(Self::NaturalMultiplyByDigit),
            "N-7" | "MUL_Nk_N" | "NaturalMultiplyByPowerOfTen" => {
                Ok(Self::NaturalMultiplyByPowerOfTen)
            }
            "N-8" | "MUL_NN_N" | "NaturalMultiply" => Ok(Self::NaturalMultiply),
            "N-9" | "SUB_NDN_N" | "NaturalSubtractMultipliedByDigit" => {
                Ok(Self::NaturalSubtractMultipliedByDigit)
            }
            "N-10" | "DIV_NN_Dk" | "NaturalCalculateDivisionDigit" => {
                Ok(Self::NaturalCalculateDivisionDigit)
            }
            "N-11" | "DIV_NN_N" | "NaturalQuotient" => Ok(Self::NaturalQuotient),
            "N-12" | "MOD_NN_N" | "NaturalRemainder" => Ok(Self::NaturalRemainder),
            "N-13" | "GCF_NN_N" | "NaturalGCD" => Ok(Self::NaturalGCD),
            "N-14" | "LCM_NN_N" | "NaturalLCM" => Ok(Self::NaturalLCM),

            _ => Err(InstructionError::new(format!("unknown instruction: {}", s))),
        }
    }
}

impl ToString for Instruction {
    fn to_string(&self) -> String {
        return format!("{:?}", self).to_string();
    }
}
