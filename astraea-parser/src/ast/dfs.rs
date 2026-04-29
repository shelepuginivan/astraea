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

pub struct PostOrderDFS<'a> {
    output: VecDeque<&'a ASTNode>,
}

impl<'a> PostOrderDFS<'a> {
    pub fn new(root: &'a ASTNode) -> Self {
        let mut stack = VecDeque::new();
        let mut output = VecDeque::new();

        stack.push_back(root);

        while let Some(cur) = stack.pop_back() {
            output.push_back(cur);

            match cur {
                ASTNode::BinaryOp { lhs, rhs, .. } => {
                    stack.push_back(&lhs);
                    stack.push_back(&rhs);
                }
                ASTNode::Function { args, .. } => {
                    stack.extend(args.iter().rev());
                }
                _ => {}
            }
        }

        Self { output }
    }
}

impl<'a> Iterator for PostOrderDFS<'a> {
    type Item = &'a ASTNode;

    fn next(&mut self) -> Option<Self::Item> {
        self.output.pop_back()
    }
}
