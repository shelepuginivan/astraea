use super::dfs::{PostOrderDFS, PreOrderDFS};
use super::node::ASTNode;

#[derive(Default)]
pub struct AST {
    root: Option<ASTNode>,
}

impl AST {
    pub fn new(root: ASTNode) -> Self {
        Self { root: Some(root) }
    }

    pub fn prefix_notation(&self) -> String {
        let mut result = String::new();

        let pre_order_dfs = match self.root.as_ref() {
            Some(root) => PreOrderDFS::new(&root),
            None => return result,
        };

        for (i, node) in pre_order_dfs.enumerate() {
            if i > 0 {
                result.push(' ');
            }

            let s = match node {
                ASTNode::Literal(value) => &value.to_string(),
                ASTNode::Variable(name) => name,
                ASTNode::Function(func) => &func.name(),
                ASTNode::BinaryOp { operator, .. } => &operator.to_string(),
            };

            result.push_str(s);
        }

        result
    }

    pub fn postfix_notation(&self) -> String {
        let mut result = String::new();

        let post_order_dfs = match self.root.as_ref() {
            Some(root) => PostOrderDFS::new(&root),
            None => return result,
        };

        for (i, node) in post_order_dfs.enumerate() {
            if i > 0 {
                result.push(' ');
            }

            let s = match node {
                ASTNode::Literal(value) => &value.to_string(),
                ASTNode::Variable(name) => name,
                ASTNode::Function(func) => &func.name(),
                ASTNode::BinaryOp { operator, .. } => &operator.to_string(),
            };

            result.push_str(s);
        }

        result
    }

    pub fn full_notation(&self) -> String {
        self.root
            .as_ref()
            .map(|n| n.full_notation())
            .unwrap_or_default()
    }

    pub fn derivative(&self, var: &str) -> Self {
        Self {
            root: self.root.as_ref().map(|n| n.derivative(var)),
        }
    }
}
