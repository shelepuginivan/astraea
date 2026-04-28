pub enum BinaryOp {
    Add,
    Sub,
    Mul,
    Div,
}

pub enum ASTNode {
    Literal {
        value: String,
    },
    Variable {
        name: String,
    },
    BinaryOp {
        operator: BinaryOp,
        lhs: Box<ASTNode>,
        rhs: Box<ASTNode>,
    },
    Function {
        name: String,
        args: Vec<ASTNode>,
    },
}

#[derive(Default)]
pub struct AST {
    root: Option<ASTNode>,
}
