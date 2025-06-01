use std::{cmp::Ordering, fmt::Display, str::FromStr, sync::Arc};

#[derive(Debug, PartialEq)]
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

    pub fn char_at(&self, index: usize) -> Option<char> {
        match self {
            Node::Leaf(substr) => substr.chars().nth(index),
            Node::Internal {
                left,
                right,
                weight,
            } => match index.cmp(weight) {
                Ordering::Less => left.char_at(index),
                _ => right.char_at(index - weight),
            },
        }
    }

    pub fn split_at(&self, index: usize) -> (Self, Self) {
        match self {
            Node::Leaf(substr) => {
                if substr.is_empty() {
                    return (Self::new(), Self::new());
                }

                if index > substr.len() - 1 {
                    return (substr.parse().unwrap(), Self::new());
                }

                let left = &substr[..index];
                let right = &substr[index..];
                (left.parse().unwrap(), right.parse().unwrap())
            }
            Node::Internal { left, right, .. } => {
                //
                (Self::new(), Self::new())
            }
        }
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
    fn build_node(values: &[&str]) -> anyhow::Result<(Option<Node>, usize)> {
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

        Ok((node, len))
    }

    // --------------------------------------------
    fn run_len(values: &[&str]) -> anyhow::Result<()> {
        let (node, len) = build_node(values)?;
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

    // --------------------------------------------
    fn run_char_at(values: &[&str], index: usize, expected: Option<char>) -> anyhow::Result<()> {
        let (node, _) = build_node(values)?;
        assert_eq!(node.unwrap().char_at(index), expected);

        Ok(())
    }

    #[test]
    fn test_char_at() -> anyhow::Result<()> {
        run_char_at(&["abc"], 0, Some('a'))?;
        run_char_at(&["abc"], 2, Some('c'))?;
        run_char_at(&["café"], 3, Some('é'))?;
        run_char_at(&["a", "b", "c"], 0, Some('a'))?;
        run_char_at(&["a", "b", "c"], 2, Some('c'))?;
        run_char_at(&["a", "bc"], 1, Some('b'))?;
        run_char_at(&["a", "bc"], 2, Some('c'))?;
        run_char_at(&["hello", "world", "goodbye", "mars"], 13, Some('d'))?;
        run_char_at(&["hello", "", "goodbye", "mars"], 9, Some('b'))?;
        run_char_at(&["", "", "goodbye", "", "mars"], 8, Some('a'))?;
        run_char_at(&["hello", "", "world", ""], 6, Some('o'))?;

        run_char_at(&[""], 1, None)?;
        run_char_at(&["hello"], 10, None)?;
        run_char_at(&["hello", "world", "goodbye", "mars"], 25, None)?;

        Ok(())
    }

    // --------------------------------------------
    fn run_leaf_split_at(
        values: &[&str],
        index: usize,
        expected: (&str, &str),
    ) -> anyhow::Result<()> {
        let (node, _) = build_node(values)?;
        assert_eq!(
            node.unwrap().split_at(index),
            (expected.0.parse()?, expected.1.parse()?)
        );

        Ok(())
    }

    fn run_internal_split_at(
        values: &[&str],
        index: usize,
        expected: (Node, Node),
    ) -> anyhow::Result<()> {
        Ok(())
    }

    #[test]
    fn test_split_at() -> anyhow::Result<()> {
        run_leaf_split_at(&["abc"], 1, ("a", "bc"))?;
        run_leaf_split_at(&["0123456"], 3, ("012", "3456"))?;
        run_leaf_split_at(&["hello world"], 4, ("hell", "o world"))?;

        run_internal_split_at(&["abc"], 1, (Node::new(), Node::new()))?;
        Ok(())
    }
}
