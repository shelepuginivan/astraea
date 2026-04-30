use std::str::FromStr;

use astraea::prelude::{MathObject, Pretty};

use crate::UnaryFunction;
use crate::node::{BinaryOp, Node};
use crate::token::{SyntaxError, TokenStream};
use crate::tree::AST;

pub fn parse_prefix_notation<'a, T: MathObject + Pretty>(
    s: &'a str,
) -> Result<AST<T>, SyntaxError<'a>> {
    let mut tokens = TokenStream::new(s);
    let root = parse_token_stream_prefix(&mut tokens)?;

    if let Some(token) = tokens.next() {
        return Err(SyntaxError::new("Extra value", token));
    }

    Ok(AST(root))
}

fn parse_token_stream_prefix<'a, T: MathObject + Pretty>(
    stream: &mut TokenStream<'a>,
) -> Result<Option<Box<Node<T>>>, SyntaxError<'a>> {
    let root_token = match stream.next() {
        Some(token) => token,
        None => return Ok(None),
    };

    // Variable node.
    if let Some(name) = root_token.value.strip_prefix("@") {
        if name.trim() == "" {
            return Err(SyntaxError::new(
                "Variable name must not be empty",
                root_token,
            ));
        }

        return Ok(Some(Node::var(name)));
    }

    // Binary operators.
    if let Ok(operator) = BinaryOp::from_str(root_token.value) {
        let lhs = match parse_token_stream_prefix(stream)? {
            Some(node) => node,
            None => {
                return Err(SyntaxError::new("Expected 2 arguments, got 0", root_token));
            }
        };

        let rhs = match parse_token_stream_prefix(stream)? {
            Some(node) => node,
            None => {
                return Err(SyntaxError::new("Expected 2 arguments, got 1", root_token));
            }
        };

        return Ok(Some(Box::new(Node::BinaryOp { operator, lhs, rhs })));
    }

    // Unary functions.
    if let Ok(func) = UnaryFunction::from_str(root_token.value) {
        let arg = match parse_token_stream_prefix(stream)? {
            Some(node) => node,
            None => {
                return Err(SyntaxError::new("Expected 1 argument, got 0", root_token));
            }
        };

        return Ok(Some(Box::new(Node::UnaryFunctionCall { func, arg })));
    }

    // Literals.
    if let Ok(literal) = T::from_str(root_token.value) {
        return Ok(Some(Box::new(Node::Literal(literal))));
    }

    Err(SyntaxError::new("unknown token", root_token))
}
