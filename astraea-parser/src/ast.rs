use std::collections::VecDeque;

#[derive(Debug)]
pub enum BinaryOp {
    Add,
    Sub,
    Mul,
    Div,
}

#[derive(Debug)]
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

pub struct PreOrderDFS<'a> {
    stack: VecDeque<&'a ASTNode>,
}

impl<'a> PreOrderDFS<'a> {
    pub fn new(root: &'a ASTNode) -> Self {
        let mut stack = VecDeque::new();
        stack.push_back(root);

        Self { stack }
    }
}

impl<'a> Iterator for PreOrderDFS<'a> {
    type Item = &'a ASTNode;

    fn next(&mut self) -> Option<Self::Item> {
        let current = self.stack.pop_back()?;

        match current {
            ASTNode::BinaryOp { lhs, rhs, .. } => {
                self.stack.push_back(&rhs);
                self.stack.push_back(&lhs);
            }
            ASTNode::Function { args, .. } => {
                self.stack.extend(args.iter().rev());
            }
            _ => {}
        }

        Some(current)
    }
}

#[derive(Default)]
pub struct AST {
    root: Option<ASTNode>,
}

impl AST {
    pub fn new(root: ASTNode) -> Self {
        Self { root: Some(root) }
    }

    pub fn prefix_notation(&self) -> String {
        let result = String::new();

        let pre_order_dfs = match self.root.as_ref() {
            Some(root) => PreOrderDFS::new(&root),
            None => return result,
        };

        for node in pre_order_dfs {
            println!("{node:?}");
        }

        result
    }
}
