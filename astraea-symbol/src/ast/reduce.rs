use std::{
    collections::VecDeque,
    ops::{Add, Div, Mul, Sub},
};

use astraea::prelude::*;

use crate::MultiFunction;

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

fn bin_to_multi<T>(node: Node<T>, binop: BinaryOp, multi: MultiFunction) -> Node<T>
where
    T: MathObject,
{
    if let Node::BinaryOp { operator, lhs, rhs } = node {
        if operator == binop {
            Node::MultiFunctionCall {
                func: multi,
                args: vec![lhs, rhs],
            }
        } else {
            Node::BinaryOp { operator, lhs, rhs }
        }
    } else {
        node
    }
}

fn flat_args_of<T>(node: Node<T>, binop: BinaryOp, multi: MultiFunction) -> Vec<Box<Node<T>>>
where
    T: MathObject,
{
    let (func, args) = match node {
        Node::MultiFunctionCall { func, args } => (func, args),
        Node::BinaryOp { operator, lhs, rhs } => {
            if operator == binop {
                return vec![lhs, rhs];
            } else {
                return vec![Box::new(Node::BinaryOp { operator, lhs, rhs })];
            }
        }
        _ => return vec![Box::new(node)],
    };

    if func != multi {
        return vec![Box::new(Node::MultiFunctionCall { func, args })];
    }

    return args;
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

pub fn reduce_structural_cancellation<T>(node: Node<T>) -> Node<T>
where
    T: MathObject + AddWithIdentity<T> + PartialEq,
{
    if let Node::BinaryOp { operator, lhs, rhs } = node {
        if operator == BinaryOp::Sub && lhs == rhs {
            Node::Literal(T::zero())
        } else {
            Node::BinaryOp { operator, lhs, rhs }
        }
    } else {
        node
    }
}

pub fn reduce_add_to_sum<T>(node: Node<T>) -> Node<T>
where
    T: MathObject,
{
    bin_to_multi(node, BinaryOp::Add, MultiFunction::Sum)
}

pub fn reduce_empty_sum<T>(node: Node<T>) -> Node<T>
where
    T: MathObject + AddWithIdentity<T>,
{
    if let Node::MultiFunctionCall { func, ref args } = node {
        if func == MultiFunction::Sum && args.is_empty() {
            Node::Literal(T::zero())
        } else {
            node
        }
    } else {
        node
    }
}

pub fn reduce_sum_with_one_arg<T>(node: Node<T>) -> Node<T>
where
    T: MathObject,
{
    if let Node::MultiFunctionCall { func, mut args } = node {
        if func == MultiFunction::Sum && args.len() == 1 {
            *args.pop().take().unwrap()
        } else {
            Node::MultiFunctionCall { func, args }
        }
    } else {
        node
    }
}

pub fn reduce_sum_with_two_args<T>(node: Node<T>) -> Node<T>
where
    T: MathObject,
{
    if let Node::MultiFunctionCall { func, mut args } = node {
        if func == MultiFunction::Sum && args.len() == 2 {
            let rhs = Box::new(*args.pop().take().unwrap());
            let lhs = Box::new(*args.pop().take().unwrap());

            Node::BinaryOp {
                operator: BinaryOp::Add,
                lhs,
                rhs,
            }
        } else {
            Node::MultiFunctionCall { func, args }
        }
    } else {
        node
    }
}

pub fn reduce_sum_to_flat<T>(node: Node<T>) -> Node<T>
where
    T: MathObject + AddAssociative<T>,
{
    let (func, mut self_args) = match node {
        Node::MultiFunctionCall { func, args } => (func, args),
        _ => return node,
    };

    if func != MultiFunction::Sum {
        return Node::MultiFunctionCall {
            func,
            args: self_args,
        };
    }

    let mut new_args = VecDeque::with_capacity(self_args.len());

    while let Some(self_arg) = self_args.pop() {
        for arg in flat_args_of(*self_arg, BinaryOp::Add, MultiFunction::Sum)
            .into_iter()
            .rev()
        {
            new_args.push_front(arg);
        }
    }

    Node::MultiFunctionCall {
        func,
        args: new_args.into(),
    }
}

pub fn reduce_sum_associative<T>(node: Node<T>) -> Node<T>
where
    T: MathObject + Add<Output = T> + AddAssociative<T> + AddWithIdentity<T>,
{
    let (func, mut args) = match node {
        Node::MultiFunctionCall { func, args } => (func, args),
        _ => return node,
    };

    if func != MultiFunction::Sum {
        return Node::MultiFunctionCall { func, args };
    }

    let mut new_args = VecDeque::with_capacity(args.len());
    let mut acc = T::zero();

    while let Some(arg) = args.pop() {
        if let Node::Literal(v) = *arg {
            acc = acc + v
        } else {
            if !acc.is_zero() {
                new_args.push_front(Node::literal(acc));
                acc = T::zero();
            }
            new_args.push_front(arg);
        }
    }

    if !acc.is_zero() {
        new_args.push_front(Node::literal(acc));
    }

    Node::MultiFunctionCall {
        func,
        args: new_args.into(),
    }
}

pub fn reduce_sum_commutative<T>(node: Node<T>) -> Node<T>
where
    T: MathObject + Add<Output = T> + AddWithIdentity<T> + AddCommutative<T>,
{
    let (func, mut args) = match node {
        Node::MultiFunctionCall { func, args } => (func, args),
        _ => return node,
    };

    if func != MultiFunction::Sum {
        return Node::MultiFunctionCall { func, args };
    }

    let mut new_args = VecDeque::with_capacity(args.len());
    let mut acc = T::zero();

    while let Some(arg) = args.pop() {
        if let Node::Literal(v) = *arg {
            acc = acc + v
        } else {
            if !acc.is_zero() {
                new_args.push_front(Node::literal(acc));
                acc = T::zero();
            }
            new_args.push_front(arg);
        }
    }

    if !acc.is_zero() {
        new_args.push_front(Node::literal(acc));
    }

    Node::MultiFunctionCall {
        func,
        args: new_args.into(),
    }
}

pub fn reduce_mul_to_product<T>(node: Node<T>) -> Node<T>
where
    T: MathObject,
{
    bin_to_multi(node, BinaryOp::Mul, MultiFunction::Product)
}

pub fn reduce_empty_product<T>(node: Node<T>) -> Node<T>
where
    T: MathObject + MulWithIdentity<T>,
{
    if let Node::MultiFunctionCall { func, ref args } = node {
        if func == MultiFunction::Product && args.is_empty() {
            Node::Literal(T::one())
        } else {
            node
        }
    } else {
        node
    }
}

pub fn reduce_product_with_one_arg<T>(node: Node<T>) -> Node<T>
where
    T: MathObject,
{
    if let Node::MultiFunctionCall { func, mut args } = node {
        if func == MultiFunction::Product && args.len() == 1 {
            *args.pop().take().unwrap()
        } else {
            Node::MultiFunctionCall { func, args }
        }
    } else {
        node
    }
}

pub fn reduce_product_with_two_args<T>(node: Node<T>) -> Node<T>
where
    T: MathObject,
{
    if let Node::MultiFunctionCall { func, mut args } = node {
        if func == MultiFunction::Product && args.len() == 2 {
            let rhs = Box::new(*args.pop().take().unwrap());
            let lhs = Box::new(*args.pop().take().unwrap());

            Node::BinaryOp {
                operator: BinaryOp::Mul,
                lhs,
                rhs,
            }
        } else {
            Node::MultiFunctionCall { func, args }
        }
    } else {
        node
    }
}

pub fn reduce_product_to_flat<T>(node: Node<T>) -> Node<T>
where
    T: MathObject + MulAssociative<T>,
{
    let (func, mut self_args) = match node {
        Node::MultiFunctionCall { func, args } => (func, args),
        _ => return node,
    };

    if func != MultiFunction::Product {
        return Node::MultiFunctionCall {
            func,
            args: self_args,
        };
    }

    let mut new_args = VecDeque::with_capacity(self_args.len());

    while let Some(self_arg) = self_args.pop() {
        for arg in flat_args_of(*self_arg, BinaryOp::Mul, MultiFunction::Product)
            .into_iter()
            .rev()
        {
            new_args.push_front(arg);
        }
    }

    Node::MultiFunctionCall {
        func,
        args: new_args.into(),
    }
}

pub fn reduce_product_associative<T>(node: Node<T>) -> Node<T>
where
    T: MathObject + Mul<Output = T> + MulAssociative<T> + MulWithIdentity<T>,
{
    let (func, mut args) = match node {
        Node::MultiFunctionCall { func, args } => (func, args),
        _ => return node,
    };

    if func != MultiFunction::Product {
        return Node::MultiFunctionCall { func, args };
    }

    let mut new_args = VecDeque::with_capacity(args.len());
    let mut acc = T::one();

    while let Some(arg) = args.pop() {
        if let Node::Literal(v) = *arg {
            acc = acc * v
        } else {
            if !acc.is_one() {
                new_args.push_front(Node::literal(acc));
                acc = T::one();
            }
            new_args.push_front(arg);
        }
    }

    if !acc.is_one() {
        new_args.push_front(Node::literal(acc));
    }

    Node::MultiFunctionCall {
        func,
        args: new_args.into(),
    }
}

pub fn reduce_product_commutative<T>(node: Node<T>) -> Node<T>
where
    T: MathObject + Mul<Output = T> + MulWithIdentity<T> + MulCommutative<T>,
{
    let (func, mut args) = match node {
        Node::MultiFunctionCall { func, args } => (func, args),
        _ => return node,
    };

    if func != MultiFunction::Product {
        return Node::MultiFunctionCall { func, args };
    }

    let mut new_args = VecDeque::with_capacity(args.len());
    let mut acc = T::one();

    while let Some(arg) = args.pop() {
        if let Node::Literal(v) = *arg {
            acc = acc * v
        } else {
            new_args.push_front(arg);
        }
    }

    if !acc.is_one() {
        new_args.push_front(Node::literal(acc));
    }

    Node::MultiFunctionCall {
        func,
        args: new_args.into(),
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
            Self::MultiFunctionCall { func, args } => {
                let args = args.into_iter().map(|arg| arg.reduce(reducers)).collect();
                Box::new(Self::MultiFunctionCall { func, args }.reduce_self(reducers))
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
