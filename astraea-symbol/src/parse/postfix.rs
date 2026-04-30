use std::collections::LinkedList;
use std::str::FromStr;

use astraea::prelude::{MathObject, Pretty};

use crate::node::{BinaryOp, Node, UnaryFunction};
use crate::token::{SyntaxError, TokenStream};
use crate::tree::AST;

pub fn parse_postfix_notation<'a, T: MathObject + Pretty>(
    s: &'a str,
) -> Result<AST<T>, SyntaxError<'a>> {
    let tokens = TokenStream::new(s);
    let mut stack = LinkedList::new();

    for token in tokens {
        // Variable node.
        if let Some(name) = token.value.strip_prefix("@") {
            if name.trim() == "" {
                return Err(SyntaxError::new("Variable name must not be empty", token));
            }

            let node = Node::var(name);
            stack.push_back((token, node));
            continue;
        }

        // Binary operators.
        if let Ok(operator) = BinaryOp::from_str(token.value) {
            let rhs = match stack.pop_back() {
                Some(node) => node.1,
                None => {
                    return Err(SyntaxError::new("Expected 2 arguments, got 0", token));
                }
            };

            let lhs = match stack.pop_back() {
                Some(node) => node.1,
                None => {
                    return Err(SyntaxError::new("Expected 2 arguments, got 1", token));
                }
            };

            let node = Box::new(Node::BinaryOp { operator, lhs, rhs });
            stack.push_back((token, node));
            continue;
        }

        // Unary functions.
        if let Ok(func) = UnaryFunction::from_str(token.value) {
            let arg = match stack.pop_back() {
                Some(node) => node.1,
                None => {
                    return Err(SyntaxError::new("Expected 1 argument, got 0", token));
                }
            };

            let node = Box::new(Node::UnaryFunctionCall { func, arg });
            stack.push_back((token, node));
            continue;
        }

        // Literals.
        if let Ok(literal) = T::from_str(token.value) {
            let node = Box::new(Node::Literal(literal));
            stack.push_back((token, node));
            continue;
        }

        return Err(SyntaxError::new("Unknown token", token));
    }

    let root = match stack.pop_back() {
        Some(root) => root.1,
        None => return Ok(AST(None)),
    };

    if let Some((token, _)) = stack.pop_back() {
        return Err(SyntaxError::new("Extra value", token));
    }

    return Ok(AST(Some(root)));
}
