use std::{fmt::Display, str::FromStr, sync::Arc};

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
        let node = s.parse::<node::Node>()?;
        rope.root = Arc::new(node);
        Ok(rope)
    }
}

impl Display for Rope {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.root)
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

    // --------------------------------------------
    fn run_extract_string(s: &str) -> anyhow::Result<()> {
        let rope = s.parse::<Rope>()?;
        assert_eq!(format!("{rope}"), s.to_string());
        Ok(())
    }

    #[test]
    fn test_extract_string() -> anyhow::Result<()> {
        run_extract_string("hello")?;
        run_extract_string("")?;
        run_extract_string("hello world")?;
        run_extract_string("café")?;
        run_extract_string("  spaces  ")?;
        run_extract_string("line1\nline2\ttab")?;

        Ok(())
    }
}
