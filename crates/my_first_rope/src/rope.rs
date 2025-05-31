use std::{str::FromStr, sync::Arc};

use crate::node;

pub struct Rope {
    root: Arc<node::Node>,
}

impl Default for Rope {
    fn default() -> Self {
        Self::new()
    }
}

impl Rope {
    pub fn new() -> Self {
        Self {
            root: Arc::new(node::Node::new()),
        }
    }

    pub fn len(&self) -> usize {
        self.root.len()
    }

    pub fn is_empty(&self) -> bool {
        self.root.is_empty()
    }
}

impl FromStr for Rope {
    type Err = anyhow::Error;
    fn from_str(s: &str) -> anyhow::Result<Self> {
        let mut rope = Self::new();
        let node = node::Node::from_str(s)?;
        rope.root = Arc::new(node);
        Ok(rope)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // --------------------------------------------
    #[test]
    fn test_empty() -> anyhow::Result<()> {
        let rope = Rope::new();
        assert_eq!(rope.len(), 0);
        Ok(())
    }

    // --------------------------------------------
    fn run_init_from_str(s: &str) -> anyhow::Result<()> {
        let rope = s.parse::<Rope>()?;
        assert_eq!(rope.len(), s.len());
        // TODO: assert_eq!(rope.to_string(), s.into());
        Ok(())
    }
    #[test]
    fn test_init_from_str() -> anyhow::Result<()> {
        run_init_from_str("x")?;
        run_init_from_str("hello world")?;
        run_init_from_str("")?;
        run_init_from_str("café")?;
        run_init_from_str("line1\nline2")?;

        Ok(())
    }
}
