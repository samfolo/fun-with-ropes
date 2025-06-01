use std::{fmt::Display, str::FromStr, sync::Arc};

#[derive(Debug)]
pub enum Node {
    Internal {
        left: Arc<Node>,
        right: Arc<Node>,
        weight: usize,
    },
    Leaf(String),
}

impl Node {
    pub fn new() -> Self {
        Self::Leaf("".into())
    }

    pub fn new_internal(left: Arc<Node>, right: Arc<Node>) -> Self {
        Self::Internal {
            weight: left.len(),
            left,
            right,
        }
    }

    pub fn len(&self) -> usize {
        match self {
            Node::Internal { weight, right, .. } => weight + right.len(),
            Node::Leaf(substr) => substr.len(),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl FromStr for Node {
    type Err = anyhow::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(Self::Leaf(s.into()))
    }
}

impl Display for Node {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Node::Internal { left, right, .. } => {
                write!(f, "{left}{right}")
            }
            Node::Leaf(substr) => {
                write!(f, "{substr}")
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // --------------------------------------------
    fn run_len(values: &[&str]) -> anyhow::Result<()> {
        assert!(!values.is_empty());

        let mut node = None;
        let mut len = 0;

        for value in values {
            len += value.len();

            match node.take() {
                Some(n) => {
                    let temp = Node::new_internal(Arc::new(n), Arc::new(value.parse()?));
                    node = Some(temp);
                }
                None => node = Some(value.parse()?),
            }
        }

        assert_eq!(node.unwrap().len(), len);
        Ok(())
    }

    #[test]
    fn test_len() -> anyhow::Result<()> {
        run_len(&[""])?;
        run_len(&["", "hello"])?;
        run_len(&["", "hello", "", "world", ""])?;
        run_len(&["hello"])?;
        run_len(&["goodbye"])?;
        run_len(&["hello", "world", "goodbye", "mars"])?;

        Ok(())
    }
}
