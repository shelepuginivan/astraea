use astraea::prelude::*;

use super::node::{BinaryOp, Node};

pub type ReduceFn<T> = fn(Node<T>) -> Node<T>;

pub fn reduce_zero_add<T>(node: Node<T>) -> Node<T>
where
    T: MathObject + Pretty + AddWithIdentity<T>,
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

pub fn reduce_one_mul<T>(node: Node<T>) -> Node<T>
where
    T: MathObject + Pretty + MulWithIdentity<T>,
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

impl<T: MathObject + Pretty> Node<T> {
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
