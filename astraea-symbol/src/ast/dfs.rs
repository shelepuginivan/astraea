use std::collections::LinkedList;

use astraea::prelude::MathObject;

use super::node::Node;

pub struct PreOrderDFS<'a, T: MathObject> {
    stack: LinkedList<&'a Node<T>>,
}

impl<'a, T: MathObject> PreOrderDFS<'a, T> {
    pub fn new(root: &'a Node<T>) -> Self {
        let mut stack = LinkedList::new();
        stack.push_back(root);

        Self { stack }
    }
}

impl<'a, T: MathObject> Iterator for PreOrderDFS<'a, T> {
    type Item = &'a Node<T>;

    fn next(&mut self) -> Option<Self::Item> {
        let current = self.stack.pop_back()?;

        match current {
            Node::BinaryOp { lhs, rhs, .. } => {
                self.stack.push_back(&rhs);
                self.stack.push_back(&lhs);
            }
            Node::UnaryFunctionCall { arg, .. } => {
                self.stack.push_back(&arg);
            }
            _ => {}
        }

        Some(current)
    }
}

pub struct PostOrderDFS<'a, T: MathObject> {
    output: LinkedList<&'a Node<T>>,
}

impl<'a, T: MathObject> PostOrderDFS<'a, T> {
    pub fn new(root: &'a Node<T>) -> Self {
        let mut stack = LinkedList::new();
        let mut output = LinkedList::new();

        stack.push_back(root);

        while let Some(cur) = stack.pop_back() {
            output.push_back(cur);

            match cur {
                Node::BinaryOp { lhs, rhs, .. } => {
                    stack.push_back(&lhs);
                    stack.push_back(&rhs);
                }
                Node::UnaryFunctionCall { arg, .. } => {
                    stack.push_back(&arg);
                }
                _ => {}
            }
        }

        Self { output }
    }
}

impl<'a, T: MathObject> Iterator for PostOrderDFS<'a, T> {
    type Item = &'a Node<T>;

    fn next(&mut self) -> Option<Self::Item> {
        self.output.pop_back()
    }
}
