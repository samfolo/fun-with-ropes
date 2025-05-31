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
}
