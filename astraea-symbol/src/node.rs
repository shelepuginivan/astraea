use std::fmt::{self, Display};
use std::str::FromStr;

use astraea::algebra::{Field, MathObject};
use astraea::error::ParseError;
use astraea::prelude::Pretty;

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

impl FromStr for BinaryOp {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "+" => Ok(Self::Add),
            "-" => Ok(Self::Sub),
            "*" => Ok(Self::Mul),
            "/" => Ok(Self::Div),
            "^" => Ok(Self::Pow),
            &_ => Err(ParseError::new(format!("unknown binary operator: '{s}'"))),
        }
    }
}

#[derive(Clone)]
pub enum Function<T: MathObject + Pretty> {
    Sin(Box<Node<T>>),
    Cos(Box<Node<T>>),
    Tan(Box<Node<T>>),
    Cot(Box<Node<T>>),
}

impl<T: MathObject + Pretty> Function<T> {
    pub fn name(&self) -> String {
        match self {
            Function::Sin(..) => String::from("sin"),
            Function::Cos(..) => String::from("cos"),
            Function::Tan(..) => String::from("tan"),
            Function::Cot(..) => String::from("cot"),
        }
    }

    pub fn full_notation(&self) -> String {
        match self {
            Function::Sin(arg) => format!("sin({})", arg.full_notation()),
            Function::Cos(arg) => format!("cos({})", arg.full_notation()),
            Function::Tan(arg) => format!("tan({})", arg.full_notation()),
            Function::Cot(arg) => format!("cot({})", arg.full_notation()),
        }
    }

    pub fn args(&self) -> Vec<&Node<T>> {
        match self {
            Function::Sin(arg) => vec![arg],
            Function::Cos(arg) => vec![arg],
            Function::Tan(arg) => vec![arg],
            Function::Cot(arg) => vec![arg],
        }
    }
}

impl<T: MathObject + Pretty + Field> Function<T> {
    pub fn derivative(&self, var: &str) -> Box<Node<T>> {
        match self {
            Function::Sin(arg) => Node::mul(arg.derivative(var), Node::cos(arg.clone())),
            Function::Cos(arg) => Node::mul(arg.derivative(var), Node::neg(Node::sin(arg.clone()))),
            Function::Tan(arg) => Node::mul(
                arg.derivative(var),
                Node::div(
                    Node::literal(T::one()),
                    Node::square(Node::cos(arg.clone())),
                ),
            ),
            Function::Cot(arg) => Node::mul(
                arg.derivative(var),
                Node::div(
                    Node::literal(-T::one()),
                    Node::square(Node::sin(arg.clone())),
                ),
            ),
        }
    }
}

#[derive(Clone)]
pub enum Node<T: MathObject + Pretty> {
    Literal(T),
    Variable(String),
    BinaryOp {
        operator: BinaryOp,
        lhs: Box<Node<T>>,
        rhs: Box<Node<T>>,
    },
    Function(Function<T>),
}

// Convenient named constructors.
impl<T: MathObject + Pretty> Node<T> {
    pub fn literal(v: T) -> Box<Self> {
        Box::new(Self::Literal(v))
    }

    pub fn var<S: Into<String>>(name: S) -> Box<Self> {
        Box::new(Self::Variable(name.into()))
    }

    pub fn add(lhs: Box<Self>, rhs: Box<Self>) -> Box<Self> {
        Box::new(Self::BinaryOp {
            operator: BinaryOp::Add,
            lhs,
            rhs,
        })
    }

    pub fn sub(lhs: Box<Self>, rhs: Box<Self>) -> Box<Self> {
        Box::new(Self::BinaryOp {
            operator: BinaryOp::Sub,
            lhs,
            rhs,
        })
    }

    pub fn mul(lhs: Box<Self>, rhs: Box<Self>) -> Box<Self> {
        Box::new(Self::BinaryOp {
            operator: BinaryOp::Mul,
            lhs,
            rhs,
        })
    }

    pub fn div(lhs: Box<Self>, rhs: Box<Self>) -> Box<Self> {
        Box::new(Self::BinaryOp {
            operator: BinaryOp::Div,
            lhs,
            rhs,
        })
    }

    pub fn pow(lhs: Box<Self>, rhs: Box<Self>) -> Box<Self> {
        Box::new(Self::BinaryOp {
            operator: BinaryOp::Pow,
            lhs,
            rhs,
        })
    }

    pub fn square(arg: Box<Self>) -> Box<Self> {
        Self::mul(arg.clone(), arg)
    }

    pub fn sin(arg: Box<Self>) -> Box<Self> {
        Box::new(Self::Function(Function::Sin(arg)))
    }

    pub fn cos(arg: Box<Self>) -> Box<Self> {
        Box::new(Self::Function(Function::Cos(arg)))
    }

    pub fn tan(arg: Box<Self>) -> Box<Self> {
        Box::new(Self::Function(Function::Tan(arg)))
    }

    pub fn cot(arg: Box<Self>) -> Box<Self> {
        Box::new(Self::Function(Function::Cot(arg)))
    }
}

impl<T: MathObject + Field + Pretty> Node<T> {
    pub fn neg(rhs: Box<Self>) -> Box<Self> {
        Self::mul(Self::literal(-T::one()), rhs)
    }
}

impl<T: MathObject + Pretty> Node<T> {
    pub fn full_notation(&self) -> String {
        match self {
            Node::Literal(value) => value.prettify(),
            Node::Variable(name) => name.to_string(),
            Node::BinaryOp { operator, lhs, rhs } => {
                format!(
                    "({} {operator} {})",
                    lhs.full_notation(),
                    rhs.full_notation()
                )
            }
            Node::Function(func) => func.full_notation(),
        }
    }
}

impl<T: MathObject + Pretty + Field> Node<T> {
    /// Symbolic derivative with respect to `var`.
    pub fn derivative(&self, var: &str) -> Box<Self> {
        match self {
            Self::Literal(_) => Self::literal(T::zero()),
            Self::Variable(name) => {
                if var == name {
                    Self::literal(T::one())
                } else {
                    Self::literal(T::zero())
                }
            }
            Self::BinaryOp { operator, lhs, rhs } => match operator {
                BinaryOp::Add => Self::add(lhs.derivative(var), rhs.derivative(var)),
                BinaryOp::Sub => Self::sub(lhs.derivative(var), rhs.derivative(var)),
                BinaryOp::Mul => Self::add(
                    Self::mul(lhs.derivative(var), rhs.clone()),
                    Self::mul(lhs.clone(), rhs.derivative(var)),
                ),
                BinaryOp::Div => Self::div(
                    Self::sub(
                        Self::mul(lhs.derivative(var), rhs.clone()),
                        Self::mul(lhs.clone(), rhs.derivative(var)),
                    ),
                    Self::square(rhs.clone()),
                ),

                BinaryOp::Pow => {
                    let pow = Self::sub(rhs.clone(), Self::literal(T::one()));

                    Self::mul(
                        lhs.derivative(var),
                        Self::mul(pow.clone(), Self::pow(lhs.clone(), pow)),
                    )
                }
            },
            Self::Function(func) => func.derivative(var),
        }
    }
}
