use std::fmt::{self, Display};

pub enum BinaryOp {
    Add,
    Sub,
    Mul,
    Div,
}

impl Display for BinaryOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            Self::Add => "+",
            Self::Sub => "-",
            Self::Mul => "*",
            Self::Div => "/",
        };
        write!(f, "{s}")
    }
}

pub enum Function {
    Root {
        index: Box<ASTNode>,
        radicand: Box<ASTNode>,
    },

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
            Function::Root { .. } => String::from("root"),
            Function::Log { .. } => String::from("log"),
            Function::Sin(..) => String::from("sin"),
            Function::Cos(..) => String::from("cos"),
            Function::Tan(..) => String::from("tan"),
            Function::Cot(..) => String::from("cot"),
        }
    }

    pub fn full_notation(&self) -> String {
        match self {
            Function::Root { index, radicand } => {
                format!(
                    "root({}, {})",
                    index.full_notation(),
                    radicand.full_notation()
                )
            }
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
            Function::Root { index, radicand } => vec![index, radicand],
            Function::Log { base, arg } => vec![base, arg],
            Function::Sin(arg) => vec![arg],
            Function::Cos(arg) => vec![arg],
            Function::Tan(arg) => vec![arg],
            Function::Cot(arg) => vec![arg],
        }
    }
}

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
}
