use std::collections::VecDeque;

use super::node::ASTNode;

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
