use crate::{AST, ASTNode, BinaryOp};

#[macro_export]
macro_rules! ast_node {
    ($val:literal) => {
        ASTNode::Literal($val as f64)
    };

    // operator::<binary operator name> { <lhs>, <rhs> }
    (operator :: $op:tt {$lhs:expr, $rhs:expr $(,)?}) => {
        ASTNode::BinaryOp {
            operator: ast_node!(@op $op),
            lhs: Box::new(ast_node!($lhs)),
            rhs: Box::new(ast_node!($rhs)),
        }
    };

    // Binary operators.
    (@op +) => { BinaryOp::Add };
    (@op -) => { BinaryOp::Sub };
    (@op *) => { BinaryOp::Mul };
    (@op /) => { BinaryOp::Div };
    (@op add) => { BinaryOp::Add };
    (@op sub) => { BinaryOp::Sub };
    (@op mul) => { BinaryOp::Mul };
    (@op div) => { BinaryOp::Div };
}

#[macro_export]
macro_rules! ast {
    ($($tokens:tt)*) => {
        AST::new(ast_node!($($tokens)*))
    };
}
