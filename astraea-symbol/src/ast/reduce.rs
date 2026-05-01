use std::ops::{Add, Div, Mul, Sub};

use astraea::prelude::*;

use super::node::{BinaryOp, Node};

pub type ReduceFn<T> = fn(Node<T>) -> Node<T>;

enum MaybeLiteralBinop<T: MathObject> {
    Yes { operator: BinaryOp, lhs: T, rhs: T },
    No(Node<T>),
}

impl<T: MathObject> From<Node<T>> for MaybeLiteralBinop<T> {
    fn from(value: Node<T>) -> Self {
        let (operator, lhs, rhs) = match value {
            Node::BinaryOp { operator, lhs, rhs } => (operator, lhs, rhs),
            _ => return Self::No(value),
        };

        let lhs = match *lhs {
            Node::Literal(v) => v,
            _ => return Self::No(Node::BinaryOp { operator, lhs, rhs }),
        };

        let rhs = match *rhs {
            Node::Literal(v) => v,
            _ => {
                return Self::No(Node::BinaryOp {
                    operator,
                    lhs: Box::new(Node::Literal(lhs)),
                    rhs,
                });
            }
        };

        return MaybeLiteralBinop::Yes { operator, lhs, rhs };
    }
}

// Reduces binary addition of literals.
pub fn reduce_literal_add<T>(node: Node<T>) -> Node<T>
where
    T: MathObject + Add<Output = T>,
{
    match MaybeLiteralBinop::from(node) {
        MaybeLiteralBinop::No(n) => n,
        MaybeLiteralBinop::Yes { operator, lhs, rhs } => {
            if operator == BinaryOp::Add {
                Node::Literal(lhs + rhs)
            } else {
                Node::BinaryOp {
                    operator,
                    lhs: Box::new(Node::Literal(lhs)),
                    rhs: Box::new(Node::Literal(rhs)),
                }
            }
        }
    }
}

// Reduces binary subtraction of literals.
pub fn reduce_literal_sub<T>(node: Node<T>) -> Node<T>
where
    T: MathObject + Sub<Output = T>,
{
    match MaybeLiteralBinop::from(node) {
        MaybeLiteralBinop::No(n) => n,
        MaybeLiteralBinop::Yes { operator, lhs, rhs } => {
            if operator == BinaryOp::Sub {
                Node::Literal(lhs - rhs)
            } else {
                Node::BinaryOp {
                    operator,
                    lhs: Box::new(Node::Literal(lhs)),
                    rhs: Box::new(Node::Literal(rhs)),
                }
            }
        }
    }
}

// Reduces binary multiplication of literals.
pub fn reduce_literal_mul<T>(node: Node<T>) -> Node<T>
where
    T: MathObject + Mul<Output = T>,
{
    match MaybeLiteralBinop::from(node) {
        MaybeLiteralBinop::No(n) => n,
        MaybeLiteralBinop::Yes { operator, lhs, rhs } => {
            if operator == BinaryOp::Mul {
                Node::Literal(lhs * rhs)
            } else {
                Node::BinaryOp {
                    operator,
                    lhs: Box::new(Node::Literal(lhs)),
                    rhs: Box::new(Node::Literal(rhs)),
                }
            }
        }
    }
}

// Reduces binary division of literals.
pub fn reduce_literal_div<T>(node: Node<T>) -> Node<T>
where
    T: MathObject + Div<Output = T>,
{
    match MaybeLiteralBinop::from(node) {
        MaybeLiteralBinop::No(n) => n,
        MaybeLiteralBinop::Yes { operator, lhs, rhs } => {
            if operator == BinaryOp::Div {
                Node::Literal(lhs / rhs)
            } else {
                Node::BinaryOp {
                    operator,
                    lhs: Box::new(Node::Literal(lhs)),
                    rhs: Box::new(Node::Literal(rhs)),
                }
            }
        }
    }
}

// Reduces binary addition with additive identity.
//
// > a + 0 = a
// > 0 + a = a
pub fn reduce_zero_add<T>(node: Node<T>) -> Node<T>
where
    T: MathObject + AddWithIdentity<T>,
{
    if let Node::BinaryOp { operator, lhs, rhs } = node {
        if operator == BinaryOp::Add {
            if let Node::Literal(v) = lhs.as_ref() {
                if v.is_zero() {
                    return *rhs;
                }
            }
            if let Node::Literal(v) = rhs.as_ref() {
                if v.is_zero() {
                    return *lhs;
                }
            }
        }
        Node::BinaryOp { operator, lhs, rhs }
    } else {
        node
    }
}

// Reduces binary multiplication with multiplicative identity.
//
// > a * 1 = a
// > 1 * a = a
pub fn reduce_one_mul<T>(node: Node<T>) -> Node<T>
where
    T: MathObject + MulWithIdentity<T>,
{
    if let Node::BinaryOp { operator, lhs, rhs } = node {
        if operator == BinaryOp::Mul {
            if let Node::Literal(v) = lhs.as_ref() {
                if v.is_one() {
                    return *rhs;
                }
            }
            if let Node::Literal(v) = rhs.as_ref() {
                if v.is_one() {
                    return *lhs;
                }
            }
        }
        Node::BinaryOp { operator, lhs, rhs }
    } else {
        node
    }
}

// Reduces binary multiplication with additive identity (absorption law).
//
// > a * 0 = 0
// > 0 * a = 0
//
// This reduce requires distribution:
//
// > a * 0 = a * (0 + 0) = a * 0 + a * 0 <=> a * 0 = 0
pub fn reduce_zero_mul<T>(node: Node<T>) -> Node<T>
where
    T: MathObject + AddWithIdentity<T> + Distributive,
{
    if let Node::BinaryOp { operator, lhs, rhs } = node {
        if operator == BinaryOp::Mul {
            if let Node::Literal(v) = lhs.as_ref() {
                if v.is_zero() {
                    return *lhs;
                }
            }
            if let Node::Literal(v) = rhs.as_ref() {
                if v.is_zero() {
                    return *rhs;
                }
            }
        }
        Node::BinaryOp { operator, lhs, rhs }
    } else {
        node
    }
}

impl<T: MathObject> Node<T> {
    #[must_use]
    pub fn reduce(self, reducers: &[ReduceFn<T>]) -> Box<Self> {
        match self {
            Self::UnaryFunctionCall { func, arg } => Box::new(Self::UnaryFunctionCall {
                func,
                arg: arg.reduce(reducers),
            }),
            Self::BinaryOp { operator, lhs, rhs } => {
                let lhs = lhs.reduce(reducers);
                let rhs = rhs.reduce(reducers);
                Box::new(Self::BinaryOp { operator, lhs, rhs }.reduce_self(reducers))
            }
            _ => Box::new(self),
        }
    }

    fn reduce_self(self, reducers: &[ReduceFn<T>]) -> Self {
        let mut new = self;
        for r in reducers {
            new = r(new)
        }
        new
    }
}
