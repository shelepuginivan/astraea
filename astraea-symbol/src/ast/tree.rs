use std::fmt::{self, Display};
use std::str::FromStr;

use astraea::error::ParseError;
use astraea::prelude::{Field, MathObject, Pretty};

use crate::{ReduceFn, parse_postfix_notation, parse_prefix_notation};

use super::dfs::{PostOrderDFS, PreOrderDFS};
use super::node::Node;

#[derive(Clone, Default)]
pub struct AST<T: MathObject>(pub Option<Box<Node<T>>>);

impl<T: MathObject> AST<T> {
    #[must_use]
    pub fn reduce(self, reducers: &[ReduceFn<T>]) -> Self {
        Self(self.0.map(|r| r.reduce(reducers)))
    }
}

impl<T: MathObject + Field> AST<T> {
    #[must_use]
    pub fn field_reduce(self) -> Self {
        Self(self.0.map(|r| r.field_reduce()))
    }

    pub fn derivative(&self, var: &str) -> Self {
        Self(self.0.as_ref().map(|n| n.derivative(var)))
    }
}

impl<T: MathObject> FromStr for AST<T> {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if let Ok(ast) = parse_prefix_notation(s) {
            return Ok(ast);
        }

        if let Ok(ast) = parse_postfix_notation(s) {
            return Ok(ast);
        }

        Err(ParseError::new("cannot parse AST"))
    }
}

impl<T: MathObject + Pretty> AST<T> {
    pub fn prefix_notation(&self) -> String {
        let mut result = String::new();

        let pre_order_dfs = match self.0.as_ref() {
            Some(root) => PreOrderDFS::<T>::new(&root),
            None => return result,
        };

        for (i, node) in pre_order_dfs.enumerate() {
            if i > 0 {
                result.push(' ');
            }

            let s = match node {
                Node::Literal(value) => &value.prettify(),
                Node::Variable(name) => name,
                Node::UnaryFunctionCall { func, .. } => &func.to_string(),
                Node::BinaryOp { operator, .. } => &operator.to_string(),
            };

            result.push_str(s);
        }

        result
    }

    pub fn postfix_notation(&self) -> String {
        let mut result = String::new();

        let post_order_dfs = match self.0.as_ref() {
            Some(root) => PostOrderDFS::new(&root),
            None => return result,
        };

        for (i, node) in post_order_dfs.enumerate() {
            if i > 0 {
                result.push(' ');
            }

            let s = match node {
                Node::Literal(value) => &value.prettify(),
                Node::Variable(name) => name,
                Node::UnaryFunctionCall { func, .. } => &func.to_string(),
                Node::BinaryOp { operator, .. } => &operator.to_string(),
            };

            result.push_str(s);
        }

        result
    }

    pub fn full_notation(&self) -> String {
        self.0
            .as_ref()
            .map(|n| n.full_notation())
            .unwrap_or_default()
    }
}

impl<T: MathObject + Pretty> Display for AST<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.0 {
            Some(root) => root.fmt(f),
            None => write!(f, ""),
        }
    }
}

impl<T: MathObject + Pretty> Pretty for AST<T> {
    fn prettify(&self) -> String {
        self.to_string()
    }
}
