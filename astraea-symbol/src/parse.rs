use std::str::FromStr;

use crate::node::{BinaryOp, Node};
use crate::token::{SyntaxError, TokenStream};
use crate::tree::AST;

pub fn parse_prefix_notation<'a>(s: &'a str) -> Result<AST, SyntaxError<'a>> {
    let mut tokens = TokenStream::new(s);
    let root = parse_token_stream_prefix(&mut tokens)?;

    if let Some(token) = tokens.next() {
        return Err(SyntaxError::new("extra token", token));
    }

    Ok(AST(root))
}

fn parse_token_stream_prefix<'a>(
    stream: &mut TokenStream<'a>,
) -> Result<Option<Box<Node>>, SyntaxError<'a>> {
    let root_token = match stream.next() {
        Some(token) => token,
        None => return Ok(None),
    };

    // Variable node.
    if let Some(name) = root_token.value.strip_prefix("@") {
        return Ok(Some(Node::var(name)));
    }

    match root_token.value {
        "+" | "-" | "*" | "/" | "^" => {
            let operator = BinaryOp::from_str(root_token.value).unwrap();

            let rhs = match parse_token_stream_prefix(stream)? {
                Some(node) => node,
                None => {
                    return Err(SyntaxError::new(
                        "no matching right-hand side operand",
                        root_token,
                    ));
                }
            };

            let lhs = match parse_token_stream_prefix(stream)? {
                Some(node) => node,
                None => {
                    return Err(SyntaxError::new(
                        "no matching left-hand side operand",
                        root_token,
                    ));
                }
            };

            return Ok(Some(Box::new(Node::BinaryOp { operator, lhs, rhs })));
        }

        // TODO: functions and literals.
        _ => return Err(SyntaxError::new("unknown token", root_token)),
    }
}
