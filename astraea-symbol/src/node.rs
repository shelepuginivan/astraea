use std::fmt::{self, Display};

#[derive(Clone, Copy)]
pub enum BinaryOp {
    Add,
    Sub,
    Mul,
    Div,
    Pow,
}

impl Display for BinaryOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            Self::Add => "+",
            Self::Sub => "-",
            Self::Mul => "*",
            Self::Div => "/",
            Self::Pow => "^",
        };
        write!(f, "{s}")
    }
}

#[derive(Clone)]
pub enum Function {
    Log {
        base: Box<ASTNode>,
        arg: Box<ASTNode>,
    },

    // Trigonometry.
    Sin(Box<ASTNode>),
    Cos(Box<ASTNode>),
    Tan(Box<ASTNode>),
    Cot(Box<ASTNode>),
}

impl Function {
    pub fn name(&self) -> String {
        match self {
            Function::Log { .. } => String::from("log"),
            Function::Sin(..) => String::from("sin"),
            Function::Cos(..) => String::from("cos"),
            Function::Tan(..) => String::from("tan"),
            Function::Cot(..) => String::from("cot"),
        }
    }

    pub fn full_notation(&self) -> String {
        match self {
            Function::Log { base, arg } => {
                format!("log({}, {})", base.full_notation(), arg.full_notation())
            }
            Function::Sin(arg) => format!("sin({})", arg.full_notation()),
            Function::Cos(arg) => format!("cos({})", arg.full_notation()),
            Function::Tan(arg) => format!("tan({})", arg.full_notation()),
            Function::Cot(arg) => format!("cot({})", arg.full_notation()),
        }
    }

    pub fn args(&self) -> Vec<&ASTNode> {
        match self {
            Function::Log { base, arg } => vec![base, arg],
            Function::Sin(arg) => vec![arg],
            Function::Cos(arg) => vec![arg],
            Function::Tan(arg) => vec![arg],
            Function::Cot(arg) => vec![arg],
        }
    }

    pub fn derivative(&self, var: &str) -> ASTNode {
        todo!()
    }
}

#[derive(Clone)]
pub enum ASTNode {
    Literal(f64),
    Variable(String),
    BinaryOp {
        operator: BinaryOp,
        lhs: Box<ASTNode>,
        rhs: Box<ASTNode>,
    },
    Function(Function),
}

impl ASTNode {
    pub fn full_notation(&self) -> String {
        match self {
            ASTNode::Literal(value) => value.to_string(),
            ASTNode::Variable(name) => name.to_string(),
            ASTNode::BinaryOp { operator, lhs, rhs } => {
                format!(
                    "({} {operator} {})",
                    lhs.full_notation(),
                    rhs.full_notation()
                )
            }
            ASTNode::Function(func) => func.full_notation(),
        }
    }

    /// Symbolic derivative with respect to `var`.
    pub fn derivative(&self, var: &str) -> Self {
        match self {
            Self::Literal(_) => Self::Literal(0.0),
            Self::Variable(name) => {
                if var == name {
                    Self::Literal(1.0)
                } else {
                    Self::Literal(0.0)
                }
            }
            Self::BinaryOp { operator, lhs, rhs } => match operator {
                BinaryOp::Add => Self::BinaryOp {
                    operator: BinaryOp::Add,
                    lhs: Box::new(lhs.derivative(var)),
                    rhs: Box::new(rhs.derivative(var)),
                },
                BinaryOp::Sub => Self::BinaryOp {
                    operator: BinaryOp::Sub,
                    lhs: Box::new(lhs.derivative(var)),
                    rhs: Box::new(rhs.derivative(var)),
                },
                BinaryOp::Mul => Self::BinaryOp {
                    operator: BinaryOp::Add,
                    lhs: Box::new(Self::BinaryOp {
                        operator: BinaryOp::Mul,
                        lhs: Box::new(lhs.derivative(var)),
                        rhs: rhs.clone(),
                    }),
                    rhs: Box::new(Self::BinaryOp {
                        operator: BinaryOp::Mul,
                        lhs: lhs.clone(),
                        rhs: Box::new(rhs.derivative(var)),
                    }),
                },
                BinaryOp::Div => Self::BinaryOp {
                    operator: BinaryOp::Div,
                    lhs: Box::new(Self::BinaryOp {
                        operator: BinaryOp::Sub,
                        lhs: Box::new(Self::BinaryOp {
                            operator: BinaryOp::Mul,
                            lhs: Box::new(lhs.derivative(var)),
                            rhs: rhs.clone(),
                        }),
                        rhs: Box::new(Self::BinaryOp {
                            operator: BinaryOp::Mul,
                            lhs: lhs.clone(),
                            rhs: Box::new(rhs.derivative(var)),
                        }),
                    }),
                    rhs: Box::new(Self::BinaryOp {
                        operator: BinaryOp::Pow,
                        lhs: rhs.clone(),
                        rhs: Box::new(ASTNode::Literal(2.0)),
                    }),
                },
                BinaryOp::Pow => {
                    let pow = Self::BinaryOp {
                        operator: BinaryOp::Sub,
                        lhs: rhs.clone(),
                        rhs: Box::new(Self::Literal(1.0)),
                    };

                    Self::BinaryOp {
                        operator: BinaryOp::Mul,
                        lhs: Box::new(lhs.derivative(var)),
                        rhs: Box::new(Self::BinaryOp {
                            operator: BinaryOp::Mul,
                            lhs: Box::new(pow.clone()),
                            rhs: Box::new(Self::BinaryOp {
                                operator: BinaryOp::Pow,
                                lhs: lhs.clone(),
                                rhs: Box::new(pow),
                            }),
                        }),
                    }
                }
            },
            Self::Function(func) => func.derivative(var),
        }
    }
}
