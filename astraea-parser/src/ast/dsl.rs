use crate::{AST, ASTNode, BinaryOp};

#[macro_export]
macro_rules! ast_node {
    ($val:literal) => {
        ASTNode::Literal {
            value: stringify!($val).to_string(),
        }
    };

    (add {$lhs:expr,$rhs:expr $(,)?}) => {
        ASTNode::BinaryOp {
            operator: BinaryOp::Add,
            lhs: Box::new(ast_node!($lhs)),
            rhs: Box::new(ast_node!($rhs)),
        }
    };
}

#[macro_export]
macro_rules! ast {
    ($($tokens:tt)*) => {
        AST::new(ast_node!($($tokens)*))
    };
}
