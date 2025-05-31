use std::{
    str::FromStr,
    sync::{Arc, Weak},
};

pub struct Node {
    parent: Option<Weak<Node>>,
    body: Body,
}

pub enum Body {
    Internal {
        left: Arc<Node>,
        right: Arc<Node>,
        weight: usize,
    },
    Leaf(String),
}

impl Node {
    pub fn new() -> Self {
        Self {
            parent: None,
            body: Body::Leaf("".into()),
        }
    }

    pub fn len(&self) -> usize {
        match &self.body {
            Body::Internal { weight, right, .. } => weight + right.len(),
            Body::Leaf(substr) => substr.len(),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl FromStr for Node {
    type Err = anyhow::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(Self {
            parent: None,
            body: Body::Leaf(s.into()),
        })
    }
}
