use std::fmt::Display;

pub struct InstructionError {
    message: String,
}

impl Display for InstructionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.message)
    }
}

/// Instructions available in the computer algebra system.
pub enum Instruction {
    /// Compares two natural numbers.
    ///
    /// Opcode: COM_NN_D
    NaturalCompare,

    /// Reports whether the natural number is zero.
    ///
    /// Opcode: NZER_N_B
    NaturalIsZero,

    /// Increments the natural number.
    ///
    /// Opcode: ADD_1N_N
    NaturalIncrement,

    /// Adds two natural numbers.
    ///
    /// Opcode: ADD_NN_N
    NaturalAdd,

    /// Subtracts second natural number from first.
    ///
    /// Opcode: SUB_NN_N
    NaturalSubtract,

    /// Multiplies natural number by a single digit.
    ///
    /// Opcode: MUL_ND_N
    NaturalMultiplyByDigit,

    /// Multiplies natural number by a power of 10, essentially performing a left shift.
    ///
    /// Opcode: MUL_Nk_N
    NaturalMultiplyByPowerOfTen,

    /// Multiplies two natural numbers.
    ///
    /// Opcode: MUL_NN_N
    NaturalMultiply,

    /// Subtracts natural number multiplied by digit from another natural number.
    ///
    /// Opcode: SUB_NDN_N
    NaturalSubtractMultipliedByDigit,

    /// Calculates the first digit of the division of a larger natural number by a smaller one,
    /// multiplied by 10<sup>k</sup>, where k is the position of the digit (zero-indexed).
    ///
    /// Opcode: DIV_NN_Dk
    NaturalCalculateDivisionDigit,

    /// Calculates the quotient of dividing the first natural number by the second.
    ///
    /// Opcode: DIV_NN_N
    NaturalQuotient,

    /// Calculates the remainder of dividing the first natural number by the second.
    ///
    /// Opcode: MOD_NN_N
    NaturalRemainder,

    /// Calculates GCD (greatest common divisor) of two natural numbers.
    ///
    /// Opcode: GCF_NN_N
    NaturalGCD,

    /// Calculates LCM (least common multiplier) of two natural numbers.
    ///
    /// Opcode: LCM_NN_N
    NaturalLCM,
}
