use std::sync::Arc;

pub enum Node<'a> {
    Internal {
        left: Arc<Node<'a>>,
        right: Arc<Node<'a>>,
        weight: usize,
    },
    Leaf {
        data: &'a str,
    },
}

impl<'a> Node<'a> {
    pub fn new() -> Self {
        Self::Leaf { data: "" }
    }
}
