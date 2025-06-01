use std::{
    fmt::Display,
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
        match &self.body {
            Body::Internal { weight, .. } => *weight == 0,
            Body::Leaf(substr) => substr.is_empty(),
        }
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

impl Display for Node {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.body {
            Body::Internal { left, right, .. } => {
                write!(f, "{}{}", left, right)
            }
            Body::Leaf(substr) => {
                write!(f, "{substr}")
            }
        }
    }
}
