use std::sync::Arc;

pub struct Node<'a> {
    parent: Option<Arc<Node<'a>>>,
    body: Body<'a>,
}

pub enum Body<'a> {
    Internal {
        left: Arc<Node<'a>>,
        right: Arc<Node<'a>>,
        weight: usize,
    },
    Leaf(&'a str),
}

impl<'a> Node<'a> {
    pub fn new() -> Self {
        Self {
            parent: None,
            body: Body::Leaf(""),
        }
    }

    pub fn len(&self) -> usize {
        match &self.body {
            Body::Internal { weight, right, .. } => weight + right.len(),
            Body::Leaf(substr) => substr.len(),
        }
    }
}
