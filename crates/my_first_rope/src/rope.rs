use std::sync::Arc;

use crate::node;

pub struct Rope<'a> {
    root: Arc<node::Node<'a>>,
}

impl Rope<'_> {
    pub fn new() -> Self {
        Self {
            root: Arc::new(node::Node::new()),
        }
    }

    pub fn len(&self) -> usize {
        self.root.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty() -> anyhow::Result<()> {
        let rope = Rope::new();
        assert_eq!(rope.len(), 0);
        Ok(())
    }
}
