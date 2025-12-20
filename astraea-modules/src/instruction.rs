use std::fmt::Display;
use strum::{EnumProperty, EnumString};

/// Instructions available in the computer algebra system.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq, EnumProperty, EnumString)]
pub enum Instruction {
    /// Compares two natural numbers.
    ///
    /// - Index: N-1
    /// - Opcode: COM_NN_D
    #[strum(
        props(opcode = "COM_NN_D", index = "N-1"),
        serialize = "COM_NN_D",
        serialize = "N-1",
        serialize = "NaturalCompare"
    )]
    NaturalCompare,

    /// Reports whether the natural number is zero.
    ///
    /// - Index: N-2
    /// - Opcode: NZER_N_B
    #[strum(
        props(opcode = "NZER_N_B", index = "N-2"),
        serialize = "NZER_N_B",
        serialize = "N-2",
        serialize = "NaturalIsZero"
    )]
    NaturalIsZero,

    /// Increments the natural number.
    ///
    /// - Index: N-3
    /// - Opcode: ADD_1N_N
    #[strum(
        props(opcode = "ADD_1N_N", index = "N-3"),
        serialize = "ADD_1N_N",
        serialize = "N-3",
        serialize = "NaturalIncrement"
    )]
    NaturalIncrement,

    /// Adds two natural numbers.
    ///
    /// - Index: N-4
    /// - Opcode: ADD_NN_N
    #[strum(
        props(opcode = "ADD_NN_N", index = "N-4"),
        serialize = "ADD_NN_N",
        serialize = "N-4",
        serialize = "NaturalAdd"
    )]
    NaturalAdd,

    /// Subtracts second natural number from first.
    ///
    /// - Index: N-5
    /// - Opcode: SUB_NN_N
    #[strum(
        props(opcode = "SUB_NN_N", index = "N-5"),
        serialize = "SUB_NN_N",
        serialize = "N-5",
        serialize = "NaturalSubtract"
    )]
    NaturalSubtract,

    /// Multiplies natural number by a single digit.
    ///
    /// - Index: N-6
    /// - Opcode: MUL_ND_N
    #[strum(
        props(opcode = "MUL_ND_N", index = "N-6"),
        serialize = "MUL_ND_N",
        serialize = "N-6",
        serialize = "NaturalMultiplyByDigit"
    )]
    NaturalMultiplyByDigit,

    /// Multiplies natural number by a power of 10, essentially performing a left shift.
    ///
    /// - Index: N-7
    /// - Opcode: MUL_Nk_N
    #[strum(
        props(opcode = "MUL_Nk_N", index = "N-7"),
        serialize = "MUL_Nk_N",
        serialize = "N-7",
        serialize = "NaturalMultiplyByPowerOfTen"
    )]
    NaturalMultiplyByPowerOfTen,

    /// Multiplies two natural numbers.
    ///
    /// - Index: N-8
    /// - Opcode: MUL_NN_N
    #[strum(
        props(opcode = "MUL_NN_N", index = "N-8"),
        serialize = "MUL_NN_N",
        serialize = "N-8",
        serialize = "NaturalMultiply"
    )]
    NaturalMultiply,

    /// Subtracts natural number multiplied by digit from another natural number.
    ///
    /// - Index: N-9
    /// - Opcode: SUB_NDN_N
    #[strum(
        props(opcode = "SUB_NDN_N", index = "N-9"),
        serialize = "SUB_NDN_N",
        serialize = "N-9",
        serialize = "NaturalSubtractMultipliedByDigit"
    )]
    NaturalSubtractMultipliedByDigit,

    /// Calculates the first digit of the division of a larger natural number by a smaller one,
    /// multiplied by 10<sup>k</sup>, where k is the position of the digit (zero-indexed).
    ///
    /// - Index: N-10
    /// - Opcode: DIV_NN_Dk
    #[strum(
        props(opcode = "DIV_NN_Dk", index = "N-10"),
        serialize = "DIV_NN_Dk",
        serialize = "N-10",
        serialize = "NaturalCalculateDivisionDigit"
    )]
    NaturalCalculateDivisionDigit,

    /// Calculates the quotient of dividing the first natural number by the second.
    ///
    /// - Index: N-11
    /// - Opcode: DIV_NN_N
    #[strum(
        props(opcode = "DIV_NN_N", index = "N-11"),
        serialize = "DIV_NN_N",
        serialize = "N-11",
        serialize = "NaturalQuotient"
    )]
    NaturalQuotient,

    /// Calculates the remainder of dividing the first natural number by the second.
    ///
    /// - Index: N-12
    /// - Opcode: MOD_NN_N
    #[strum(
        props(opcode = "MOD_NN_N", index = "N-12"),
        serialize = "MOD_NN_N",
        serialize = "N-12",
        serialize = "NaturalRemainder"
    )]
    NaturalRemainder,

    /// Calculates GCD (greatest common divisor) of two natural numbers.
    ///
    /// - Index: N-13
    /// - Opcode: GCF_NN_N
    #[strum(
        props(opcode = "GCF_NN_N", index = "N-13"),
        serialize = "GCF_NN_N",
        serialize = "N-13",
        serialize = "NaturalGCD"
    )]
    NaturalGCD,

    /// Calculates LCM (least common multiplier) of two natural numbers.
    ///
    /// - Index: N-14
    /// - Opcode: LCM_NN_N
    #[strum(
        props(opcode = "LCM_NN_N", index = "N-14"),
        serialize = "LCM_NN_N",
        serialize = "N-14",
        serialize = "NaturalLCM"
    )]
    NaturalLCM,

    /// Calculates n-th root of the natural number.
    ///
    /// - Index: N-15
    /// - Opcode: ROOT_NN_N
    #[strum(
        props(opcode = "ROOT_NN_N", index = "N-15"),
        serialize = "ROOT_NN_N",
        serialize = "N-15",
        serialize = "NaturalRoot"
    )]
    NaturalRoot,

    /// Returns absolute value of the integer.
    ///
    /// - Index: Z-1
    /// - Opcode: ABS_Z_Z
    #[strum(
        props(opcode = "ABS_Z_Z", index = "Z-1"),
        serialize = "ABS_Z_Z",
        serialize = "Z-1",
        serialize = "IntegerAbs"
    )]
    IntegerAbs,

    /// Returns sign of the integer.
    ///
    /// - Index: Z-2
    /// - Opcode: SGN_Z_D
    #[strum(
        props(opcode = "SGN_Z_D", index = "Z-2"),
        serialize = "SGN_Z_D",
        serialize = "Z-2",
        serialize = "IntegerSgn"
    )]
    IntegerSgn,

    /// Multiplies integer by -1.
    ///
    /// - Index: Z-3
    /// - Opcode: NEG_ZM_Z
    #[strum(
        props(opcode = "NEG_ZM_Z", index = "Z-3"),
        serialize = "NEG_ZM_Z",
        serialize = "Z-3",
        serialize = "IntegerNeg"
    )]
    IntegerNeg,

    /// Converts natural number to integer.
    ///
    /// - Index: Z-4
    /// - Opcode: TRANS_N_Z
    #[strum(
        props(opcode = "TRANS_N_Z", index = "Z-4"),
        serialize = "TRANS_N_Z",
        serialize = "Z-4",
        serialize = "IntegerFromNatural"
    )]
    IntegerFromNatural,

    /// Converts integer to natural number.
    ///
    /// - Index: Z-5
    /// - Opcode: TRANS_Z_N
    #[strum(
        props(opcode = "TRANS_Z_N", index = "Z-5"),
        serialize = "TRANS_Z_N",
        serialize = "Z-5",
        serialize = "IntegerToNatural"
    )]
    IntegerToNatural,

    /// Adds two integers.
    ///
    /// - Index: Z-6
    /// - Opcode: ADD_ZZ_Z
    #[strum(
        props(opcode = "ADD_ZZ_Z", index = "Z-6"),
        serialize = "ADD_ZZ_Z",
        serialize = "Z-6",
        serialize = "IntegerAdd"
    )]
    IntegerAdd,

    /// Subtracts second integer from first.
    ///
    /// - Index: Z-7
    /// - Opcode: SUB_ZZ_Z
    #[strum(
        props(opcode = "SUB_ZZ_Z", index = "Z-7"),
        serialize = "SUB_ZZ_Z",
        serialize = "Z-7",
        serialize = "IntegerSubtract"
    )]
    IntegerSubtract,

    /// Multiplies two integers.
    ///
    /// - Index: Z-8
    /// - Opcode: MUL_ZZ_Z
    #[strum(
        props(opcode = "MUL_ZZ_Z", index = "Z-8"),
        serialize = "MUL_ZZ_Z",
        serialize = "Z-8",
        serialize = "IntegerMultiply"
    )]
    IntegerMultiply,

    /// Calculates the quotient of dividing the first integer by the second.
    ///
    /// - Index: Z-9
    /// - Opcode: DIV_ZZ_Z
    #[strum(
        props(opcode = "DIV_ZZ_Z", index = "Z-9"),
        serialize = "DIV_ZZ_Z",
        serialize = "Z-9",
        serialize = "IntegerQuotient"
    )]
    IntegerQuotient,

    /// Calculates the remainder of dividing the first integer by the second.
    ///
    /// - Index: Z-10
    /// - Opcode: MOD_ZZ_Z
    #[strum(
        props(opcode = "MOD_ZZ_Z", index = "Z-10"),
        serialize = "MOD_ZZ_Z",
        serialize = "Z-10",
        serialize = "IntegerRemainder"
    )]
    IntegerRemainder,

    /// Calculates n-th root of the integer.
    ///
    /// - Index: Z-15
    /// - Opcode: ROOT_ZN_Z
    #[strum(
        props(opcode = "ROOT_ZN_N", index = "Z-15"),
        serialize = "ROOT_ZN_Z",
        serialize = "Z-15",
        serialize = "IntegerRoot"
    )]
    IntegerRoot,

    /// Reduces rational number.
    ///
    /// - Index: Q-1
    /// - Opcode: RED_Q_Q
    #[strum(
        props(opcode = "RED_Q_Q", index = "Q-1"),
        serialize = "RED_Q_Q",
        serialize = "Q-1",
        serialize = "RationalReduce"
    )]
    RationalReduce,

    /// Reports whether rational number is integer.
    ///
    /// - Index: Q-2
    /// - Opcode: INT_Q_B
    #[strum(
        props(opcode = "INT_Q_B", index = "Q-2"),
        serialize = "INT_Q_B",
        serialize = "Q-2",
        serialize = "RationalIsInteger"
    )]
    RationalIsInteger,

    /// Converts integer to rational number.
    ///
    /// - Index: Q-3
    /// - Opcode: TRANS_Z_Q
    #[strum(
        props(opcode = "TRANS_Z_Q", index = "Q-3"),
        serialize = "TRANS_Z_Q",
        serialize = "Q-3",
        serialize = "RationalFromInteger"
    )]
    RationalFromInteger,

    /// Converts rational number to integer, if possible.
    ///
    /// - Index: Q-4
    /// - Opcode: TRANS_Q_Z
    #[strum(
        props(opcode = "TRANS_Q_Z", index = "Q-4"),
        serialize = "TRANS_Q_Z",
        serialize = "Q-4",
        serialize = "RationalToInteger"
    )]
    RationalToInteger,

    /// Adds two rational numbers.
    ///
    /// - Index: Q-5
    /// - Opcode: ADD_QQ_Q
    #[strum(
        props(opcode = "ADD_QQ_Q", index = "Q-5"),
        serialize = "ADD_QQ_Q",
        serialize = "Q-5",
        serialize = "RationalAdd"
    )]
    RationalAdd,

    /// Subtracts second rational number from first.
    ///
    /// - Index: Q-6
    /// - Opcode: SUB_QQ_Q
    #[strum(
        props(opcode = "SUB_QQ_Q", index = "Q-6"),
        serialize = "SUB_QQ_Q",
        serialize = "Q-6",
        serialize = "RationalSubtract"
    )]
    RationalSubtract,

    /// Multiplies two rational numbers.
    ///
    /// - Index: Q-7
    /// - Opcode: MUL_QQ_Q
    #[strum(
        props(opcode = "MUL_QQ_Q", index = "Q-7"),
        serialize = "MUL_QQ_Q",
        serialize = "Q-7",
        serialize = "RationalMultiply"
    )]
    RationalMultiply,

    /// Divides first rational number by second.
    ///
    /// - Index: Q-8
    /// - Opcode: DIV_QQ_Q
    #[strum(
        props(opcode = "DIV_QQ_Q", index = "Q-8"),
        serialize = "DIV_QQ_Q",
        serialize = "Q-8",
        serialize = "RationalDivide"
    )]
    RationalDivide,

    /// Adds two polynomials.
    ///
    /// - Index: P-1
    /// - Opcode: ADD_PP_P
    #[strum(
        props(opcode = "ADD_PP_P", index = "P-1"),
        serialize = "ADD_PP_P",
        serialize = "P-1",
        serialize = "PolynomialAdd"
    )]
    PolynomialAdd,

    /// Subtracts second polynomial from first.
    ///
    /// - Index: P-2
    /// - Opcode: SUB_PP_P
    #[strum(
        props(opcode = "SUB_PP_P", index = "P-2"),
        serialize = "SUB_PP_P",
        serialize = "P-2",
        serialize = "PolynomialSubtract"
    )]
    PolynomialSubtract,

    /// Multiplies polynomial by rational number.
    ///
    /// - Index: P-3
    /// - Opcode: MUL_PQ_P
    #[strum(
        props(opcode = "MUL_PQ_P", index = "P-3"),
        serialize = "MUL_PQ_P",
        serialize = "P-3",
        serialize = "PolynomialMultiplyByRational"
    )]
    PolynomialMultiplyByRational,

    /// Multiplies polynomial by x<sup>k</sup>.
    ///
    /// - Index: P-4
    /// - Opcode: MUL_Pxk_P
    #[strum(
        props(opcode = "MUL_Pxk_P", index = "P-4"),
        serialize = "MUL_Pxk_P",
        serialize = "P-4",
        serialize = "PolynomialMultiplyByPowerOfX"
    )]
    PolynomialMultiplyByPowerOfX,

    /// Returns leading coefficient of the polynomial.
    ///
    /// - Index: P-5
    /// - Opcode: LED_P_Q
    #[strum(
        props(opcode = "LED_P_Q", index = "P-5"),
        serialize = "LED_P_Q",
        serialize = "P-5",
        serialize = "PolynomialLeadingCoefficient"
    )]
    PolynomialLeadingCoefficient,

    /// Returns degree of the polynomial.
    ///
    /// - Index: P-6
    /// - Opcode: DEG_P_N
    #[strum(
        props(opcode = "DEG_P_N", index = "P-6"),
        serialize = "DEG_P_N",
        serialize = "P-6",
        serialize = "PolynomialDegree"
    )]
    PolynomialDegree,

    /// Returns content of the polynomial, which is defined as a rational number with numerator
    /// equal to GCD of numerators of polynomial coefficients, and denominator equal to LCM of
    /// denominators of polynomial coefficients.
    ///
    /// - Index: P-7
    /// - Opcode: FAC_P_Q
    #[strum(
        props(opcode = "FAC_P_Q", index = "P-7"),
        serialize = "FAC_P_Q",
        serialize = "P-7",
        serialize = "PolynomialContent"
    )]
    PolynomialContent,

    /// Multiplies two polynomials.
    ///
    /// - Index: P-8
    /// - Opcode: MUL_PP_P
    #[strum(
        props(opcode = "MUL_PP_P", index = "P-8"),
        serialize = "MUL_PP_P",
        serialize = "P-8",
        serialize = "PolynomialMultiply"
    )]
    PolynomialMultiply,

    /// Calculates the quotient of dividing the first polynomial by the second.
    ///
    /// - Index: P-9
    /// - Opcode: DIV_PP_P
    #[strum(
        props(opcode = "DIV_PP_P", index = "P-9"),
        serialize = "DIV_PP_P",
        serialize = "P-9",
        serialize = "PolynomialQuotient"
    )]
    PolynomialQuotient,

    /// Calculates the remainder of dividing the first polynomial by the second.
    ///
    /// - Index: P-10
    /// - Opcode: MOD_PP_P
    #[strum(
        props(opcode = "MOD_PP_P", index = "P-10"),
        serialize = "MOD_PP_P",
        serialize = "P-10",
        serialize = "PolynomialRemainder"
    )]
    PolynomialRemainder,

    /// Calculates GCD of two polynomials.
    ///
    /// - Index: P-11
    /// - Opcode: GCF_PP_P
    #[strum(
        props(opcode = "GCF_PP_P", index = "P-11"),
        serialize = "GCF_PP_P",
        serialize = "P-11",
        serialize = "PolynomialGCD"
    )]
    PolynomialGCD,

    /// Returns derivative of polynomial.
    ///
    /// - Index: P-12
    /// - Opcode: DER_P_P
    #[strum(
        props(opcode = "DER_P_P", index = "P-12"),
        serialize = "DER_P_P",
        serialize = "P-12",
        serialize = "PolynomialDerivative"
    )]
    PolynomialDerivative,

    /// Converts multiple roots of polynomial to simple roots.
    ///
    /// - Index: P-13
    /// - Opcode: NMR_P_P
    #[strum(
        props(opcode = "NMR_P_P", index = "P-13"),
        serialize = "NMR_P_P",
        serialize = "P-13",
        serialize = "PolynomialFlatten"
    )]
    PolynomialFlatten,

    /// Calculates n!
    ///
    /// - Index: CMB-1
    /// - Opcode: FAC_N_N
    #[strum(
        props(opcode = "FAC_N_N", index = "CMB-1"),
        serialize = "FAC_N_N",
        serialize = "CMB-1",
        serialize = "CombinatoricsFactorial"
    )]
    CombinatoricsFactorial,

    /// Calculates !n
    ///
    /// - Index: CMB-2
    /// - Opcode: SBF_N_N
    #[strum(
        props(opcode = "SBF_N_N", index = "CMB-2"),
        serialize = "SBF_N_N",
        serialize = "CMB-2",
        serialize = "CombinatoricsSubfactorial"
    )]
    CombinatoricsSubfactorial,

    /// Calculates number of combinations.
    ///
    /// - Index: CMB-3
    /// - Opcode: Cnk_NN_N
    #[strum(
        props(opcode = "Cnk_NN_N", index = "CMB-3"),
        serialize = "Cnk_NN_N",
        serialize = "CMB-3",
        serialize = "CombinatoricsCombinations"
    )]
    CombinatoricsCombinations,

    /// Calculates number of placements.
    ///
    /// - Index: CMB-4
    /// - Opcode: PLC_NN_N
    #[strum(
        props(opcode = "PLC_NN_N", index = "CMB-4"),
        serialize = "PLC_NN_N",
        serialize = "CMB-4",
        serialize = "CombinatoricsPlacements"
    )]
    CombinatoricsPlacements,

    /// Calculates Stirling number of the first kind (unsigned).
    ///
    /// - Index: CMB-5
    /// - Opcode: ST1_NN_N
    #[strum(
        props(opcode = "ST1_NN_N", index = "CMB-5"),
        serialize = "ST1_NN_N",
        serialize = "CMB-5",
        serialize = "CombinatoricsStirlingFirstKind"
    )]
    CombinatoricsStirlingFirstKind,

    /// Calculates Stirling number of the second kind (unsigned).
    ///
    /// - Index: CMB-6
    /// - Opcode: ST2_NN_N
    #[strum(
        props(opcode = "ST2_NN_N", index = "CMB-6"),
        serialize = "ST2_NN_N",
        serialize = "CMB-6",
        serialize = "CombinatoricsStirlingSecondKind"
    )]
    CombinatoricsStirlingSecondKind,

    /// Calculates nth Bell number.
    ///
    /// - Index: CMB-7
    /// - Opcode: BEL_N_N
    #[strum(
        props(opcode = "BEL_N_N", index = "CMB-7"),
        serialize = "bel_n_n",
        serialize = "CMB-7",
        serialize = "CombinatoricsBell"
    )]
    CombinatoricsBell,

    /// Calculates nth Fibonacci number.
    ///
    /// - Index: CMB-8
    /// - Opcode: FIB_N_N
    #[strum(
        props(opcode = "FIB_N_N", index = "CMB-8"),
        serialize = "FIB_N_N",
        serialize = "CMB-8",
        serialize = "CombinatoricsFibonacci"
    )]
    CombinatoricsFibonacci,

    /// Calculates nth Lucas number.
    ///
    /// - Index: CMB-9
    /// - Opcode: LUK_N_N
    #[strum(
        props(opcode = "LUK_N_N", index = "CMB-9"),
        serialize = "LUK_N_N",
        serialize = "CMB-9",
        serialize = "CombinatoricsLucas"
    )]
    CombinatoricsLucas,

    /// Calculates nth Catalan number.
    ///
    /// - Index: CMB-10
    /// - Opcode: CAT_N_N
    #[strum(
        props(opcode = "CAT_N_N", index = "CMB-10"),
        serialize = "CAT_N_N",
        serialize = "CMB-10",
        serialize = "CombinatoricsCatalan"
    )]
    CombinatoricsCatalan,

    /// Calculates nth k-simplex number.
    ///
    /// - Index: CMB-11
    /// - Opcode: SPX_NN_N
    #[strum(
        props(opcode = "CPX_NN_N", index = "CMB-11"),
        serialize = "CPX_NN_N",
        serialize = "CMB-11",
        serialize = "CombinatoricsSimplex"
    )]
    CombinatoricsSimplex,
}

impl Instruction {
    /// Returns opcode of the instruction.
    pub fn opcode(&self) -> &str {
        self.get_str("opcode").unwrap()
    }

    /// Returns index of the instruction.
    pub fn index(&self) -> &str {
        self.get_str("index").unwrap()
    }
}

impl Display for Instruction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl Into<String> for Instruction {
    fn into(self) -> String {
        self.to_string()
    }
}
