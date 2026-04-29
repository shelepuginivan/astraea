use std::fmt::{self, Display};

#[derive(Debug)]
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

#[derive(Debug)]
pub enum ASTNode {
    Literal {
        value: String,
    },
    Variable {
        name: String,
    },
    BinaryOp {
        operator: BinaryOp,
        lhs: Box<ASTNode>,
        rhs: Box<ASTNode>,
    },
    Function {
        name: String,
        args: Vec<ASTNode>,
    },
}

impl ASTNode {
    pub fn full_notation(&self) -> String {
        match self {
            ASTNode::Literal { value } => value.to_string(),
            ASTNode::Variable { name } => name.to_string(),
            ASTNode::BinaryOp { operator, lhs, rhs } => {
                format!(
                    "({} {operator} {})",
                    lhs.full_notation(),
                    rhs.full_notation()
                )
            }
            ASTNode::Function { name, args } => {
                let mut s = format!("{name}(");

                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        s.push_str(", ");
                    }

                    s.push_str(&arg.full_notation());
                }

                s.push_str(")");
                s
            }
        }
    }
}
