use std::fmt::{self, Display};
use std::str::FromStr;

use astraea::error::ParseError;
use astraea::prelude::*;

#[derive(Clone, Copy, PartialEq, Eq)]
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

#[derive(Clone, Copy)]
pub enum UnaryFunction {
    // Trigonometry.
    Sin,
    Cos,
    Tan,
    Cot,
}

impl Display for UnaryFunction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            Self::Sin => "sin",
            Self::Cos => "cos",
            Self::Tan => "tan",
            Self::Cot => "cot",
        };
        write!(f, "{s}")
    }
}

impl FromStr for UnaryFunction {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "sin" => Ok(Self::Sin),
            "cos" => Ok(Self::Cos),
            "tan" | "tg" => Ok(Self::Tan),
            "cot" | "ctg" => Ok(Self::Cot),
            &_ => Err(ParseError::new(format!("unknown unary function: '{s}'"))),
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
    UnaryFunctionCall {
        func: UnaryFunction,
        arg: Box<Node<T>>,
    },
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
        Box::new(Self::UnaryFunctionCall {
            func: UnaryFunction::Sin,
            arg,
        })
    }

    pub fn cos(arg: Box<Self>) -> Box<Self> {
        Box::new(Self::UnaryFunctionCall {
            func: UnaryFunction::Cos,
            arg,
        })
    }

    pub fn tan(arg: Box<Self>) -> Box<Self> {
        Box::new(Self::UnaryFunctionCall {
            func: UnaryFunction::Tan,
            arg,
        })
    }

    pub fn cot(arg: Box<Self>) -> Box<Self> {
        Box::new(Self::UnaryFunctionCall {
            func: UnaryFunction::Cot,
            arg,
        })
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
            Node::UnaryFunctionCall { func, arg } => {
                format!("{}({})", func, arg.full_notation())
            }
        }
    }

    fn fmt_with_indent(&self, indent: usize, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let spaces = " ".repeat(indent);

        match self {
            Node::Literal(value) => {
                write!(f, "{spaces}{}", value.prettify())
            }
            Node::Variable(name) => {
                write!(f, "{spaces}@{name}")
            }
            Node::BinaryOp { operator, lhs, rhs } => {
                writeln!(f, "{spaces}{operator} {{")?;
                lhs.fmt_with_indent(indent + 4, f)?;
                writeln!(f)?;
                rhs.fmt_with_indent(indent + 4, f)?;
                writeln!(f)?;
                write!(f, "{spaces}}}")
            }
            Node::UnaryFunctionCall { func, arg } => {
                writeln!(f, "{spaces}{func} {{")?;
                arg.fmt_with_indent(indent + 4, f)?;
                writeln!(f)?;
                write!(f, "{spaces}}}")
            }
        }
    }
}

impl<T: MathObject + Pretty> Display for Node<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.fmt_with_indent(0, f)
    }
}

impl<T: MathObject + Pretty + AddWithIdentity<T>> Node<T> {
    fn reduce_additive_identity_once(self) -> Self {
        if let Self::BinaryOp { operator, lhs, rhs } = self {
            if operator == BinaryOp::Add {
                if let Self::Literal(v) = lhs.as_ref() {
                    if v.is_zero() {
                        return *rhs;
                    }
                }
                if let Self::Literal(v) = rhs.as_ref() {
                    if v.is_zero() {
                        return *lhs;
                    }
                }
            }
            Self::BinaryOp { operator, lhs, rhs }
        } else {
            self
        }
    }

    #[must_use]
    pub fn reduce_additive_identity(self) -> Box<Self> {
        match self {
            Self::UnaryFunctionCall { func, arg } => Box::new(Self::UnaryFunctionCall {
                func,
                arg: arg.reduce_additive_identity(),
            }),
            Self::BinaryOp { operator, lhs, rhs } => {
                let lhs = lhs.reduce_additive_identity();
                let rhs = rhs.reduce_additive_identity();
                Box::new(Self::BinaryOp { operator, lhs, rhs }.reduce_additive_identity_once())
            }
            _ => Box::new(self),
        }
    }
}

impl<T: MathObject + Pretty + MulWithIdentity<T>> Node<T> {
    fn reduce_multiplicative_identity_once(self) -> Self {
        if let Self::BinaryOp { operator, lhs, rhs } = self {
            if operator == BinaryOp::Mul {
                if let Self::Literal(v) = lhs.as_ref() {
                    if v.is_one() {
                        return *rhs;
                    }
                }
                if let Self::Literal(v) = rhs.as_ref() {
                    if v.is_one() {
                        return *lhs;
                    }
                }
            }
            Self::BinaryOp { operator, lhs, rhs }
        } else {
            self
        }
    }

    #[must_use]
    pub fn reduce_multiplicative_identity(self) -> Box<Self> {
        match self {
            Self::UnaryFunctionCall { func, arg } => Box::new(Self::UnaryFunctionCall {
                func,
                arg: arg.reduce_multiplicative_identity(),
            }),
            Self::BinaryOp { operator, lhs, rhs } => {
                let lhs = lhs.reduce_multiplicative_identity();
                let rhs = rhs.reduce_multiplicative_identity();
                Box::new(
                    Self::BinaryOp { operator, lhs, rhs }.reduce_multiplicative_identity_once(),
                )
            }
            _ => Box::new(self),
        }
    }
}

impl<T: MathObject + Pretty + Field> Node<T> {
    #[must_use]
    pub fn normalize(self) -> Box<Self> {
        self.reduce_additive_identity()
            .reduce_multiplicative_identity()
    }

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
            Self::UnaryFunctionCall { func, arg } => match func {
                UnaryFunction::Sin => Node::mul(arg.derivative(var), Node::cos(arg.clone())),
                UnaryFunction::Cos => {
                    Node::mul(arg.derivative(var), Node::neg(Node::sin(arg.clone())))
                }
                UnaryFunction::Tan => Node::mul(
                    arg.derivative(var),
                    Node::div(
                        Node::literal(T::one()),
                        Node::square(Node::cos(arg.clone())),
                    ),
                ),
                UnaryFunction::Cot => Node::mul(
                    arg.derivative(var),
                    Node::div(
                        Node::literal(-T::one()),
                        Node::square(Node::sin(arg.clone())),
                    ),
                ),
            },
        }
    }
}
