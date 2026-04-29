use std::collections::VecDeque;

use super::node::Node;

pub struct PreOrderDFS<'a> {
    stack: VecDeque<&'a Node>,
}

impl<'a> PreOrderDFS<'a> {
    pub fn new(root: &'a Node) -> Self {
        let mut stack = VecDeque::new();
        stack.push_back(root);

        Self { stack }
    }
}

impl<'a> Iterator for PreOrderDFS<'a> {
    type Item = &'a Node;

    fn next(&mut self) -> Option<Self::Item> {
        let current = self.stack.pop_back()?;

        match current {
            Node::BinaryOp { lhs, rhs, .. } => {
                self.stack.push_back(&rhs);
                self.stack.push_back(&lhs);
            }
            Node::Function(func) => {
                self.stack.extend(func.args().iter().rev());
            }
            _ => {}
        }

        Some(current)
    }
}

pub struct PostOrderDFS<'a> {
    output: VecDeque<&'a Node>,
}

impl<'a> PostOrderDFS<'a> {
    pub fn new(root: &'a Node) -> Self {
        let mut stack = VecDeque::new();
        let mut output = VecDeque::new();

        stack.push_back(root);

        while let Some(cur) = stack.pop_back() {
            output.push_back(cur);

            match cur {
                Node::BinaryOp { lhs, rhs, .. } => {
                    stack.push_back(&lhs);
                    stack.push_back(&rhs);
                }
                Node::Function(func) => {
                    stack.extend(func.args().iter().rev());
                }
                _ => {}
            }
        }

        Self { output }
    }
}

impl<'a> Iterator for PostOrderDFS<'a> {
    type Item = &'a Node;

    fn next(&mut self) -> Option<Self::Item> {
        self.output.pop_back()
    }
}
