use std::fmt::{self, Display};
use std::str::FromStr;

use astraea::error::ParseError;
use astraea::prelude::*;

use super::reduce::*;

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

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum UnaryFunction {
    Sqrt,
    Ln,

    // Trigonometry.
    Sin,
    Cos,
    Tan,
    Cot,
}

impl Display for UnaryFunction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            Self::Sqrt => "sqrt",
            Self::Ln => "ln",
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
            "sqrt" => Ok(Self::Sqrt),
            "ln" => Ok(Self::Ln),
            "sin" => Ok(Self::Sin),
            "cos" => Ok(Self::Cos),
            "tan" | "tg" => Ok(Self::Tan),
            "cot" | "ctg" => Ok(Self::Cot),
            &_ => Err(ParseError::new(format!("unknown unary function: '{s}'"))),
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum MultiFunction {
    Sum,
    Product,
}

impl Display for MultiFunction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            Self::Sum => "sum",
            Self::Product => "product",
        };
        write!(f, "{s}")
    }
}

impl FromStr for MultiFunction {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "sum" => Ok(Self::Sum),
            "prod" | "product" => Ok(Self::Product),
            &_ => Err(ParseError::new(format!("unknown multi function: '{s}'"))),
        }
    }
}

#[derive(Clone, PartialEq, Eq)]
pub enum Node<T: MathObject> {
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
    MultiFunctionCall {
        func: MultiFunction,
        args: Vec<Box<Node<T>>>,
    },
}

// Convenient named constructors.
impl<T: MathObject> Node<T> {
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

impl<T: MathObject + Pretty> Node<T> {
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
            Node::MultiFunctionCall { func, args } => {
                writeln!(f, "{spaces}{func} {{")?;
                for arg in args {
                    arg.fmt_with_indent(indent + 4, f)?;
                    writeln!(f)?;
                }
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

impl<T: MathObject + Field> Node<T> {
    pub fn neg(rhs: Box<Self>) -> Box<Self> {
        Self::mul(Self::literal(-T::one()), rhs)
    }

    /// Applies AST reduction in the given field.
    #[must_use]
    pub fn field_reduce(self) -> Box<Self> {
        self.reduce(&[
            reduce_literal_add,
            reduce_literal_sub,
            reduce_literal_mul,
            // reduce_literal_div, FIXME: refactor MulIntertible to Div<Output = Self>
            reduce_zero_add,
            reduce_one_mul,
            reduce_zero_mul,
        ])
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
                UnaryFunction::Sqrt => Node::mul(
                    arg.derivative(var),
                    Node::div(
                        Node::literal(T::one()),
                        Node::add(Box::new(self.clone()), Box::new(self.clone())),
                    ),
                ),
                UnaryFunction::Ln => Node::mul(
                    arg.derivative(var),
                    Node::div(Node::literal(T::one()), arg.clone()),
                ),
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
            Self::MultiFunctionCall { func, args } => match func {
                MultiFunction::Sum => Box::new(Self::MultiFunctionCall {
                    func: MultiFunction::Sum,
                    args: args.iter().map(|s| s.derivative(var)).collect(),
                }),
                MultiFunction::Product => {
                    let mut new_args = Vec::with_capacity(args.len());

                    for i in 0..args.len() {
                        let mut product = args.clone();
                        product[i] = product[i].derivative(var);

                        new_args.push(Box::new(Self::MultiFunctionCall {
                            func: MultiFunction::Product,
                            args: product,
                        }));
                    }

                    Box::new(Self::MultiFunctionCall {
                        func: MultiFunction::Sum,
                        args: new_args,
                    })
                }
            },
        }
    }
}
