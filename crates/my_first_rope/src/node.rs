use std::{cmp::Ordering, fmt::Display, str::FromStr, sync::Arc};

#[derive(Debug, PartialEq, Clone)]
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

                if index >= substr.len() {
                    return (substr.parse().unwrap(), Self::new());
                }

                let left = &substr[..index];
                let right = &substr[index..];
                (left.parse().unwrap(), right.parse().unwrap())
            }
            Node::Internal {
                left,
                right,
                weight,
            } => {
                let left = Node::clone(left);
                let right = Node::clone(right);

                match index.cmp(weight) {
                    Ordering::Less => {
                        let (left_left, left_right) = left.split_at(index);
                        let rest = Node::new_internal(Arc::new(left_right), Arc::new(right));
                        (left_left, rest)
                    }
                    Ordering::Greater => {
                        let (right_left, right_right) = right.split_at(index - weight);
                        let rest = Node::new_internal(Arc::new(left), Arc::new(right_left));
                        (rest, right_right)
                    }
                    Ordering::Equal => (left, right),
                }
            }
        }
    }

    pub fn substring(&self, start: usize, end: usize) -> String {
        match self {
            Node::Leaf(substr) => {
                if substr.is_empty() || start >= substr.len() {
                    return Default::default();
                }

                if end >= substr.len() {
                    return substr.to_owned();
                }

                String::from(&substr[start..end])
            }
            Node::Internal {
                left,
                right,
                weight,
            } => match start.cmp(weight) {
                Ordering::Less | Ordering::Equal => {
                    let left_string = left.substring(start, *weight);
                    let right_string = right.substring(*weight, end);
                    left_string + &right_string
                }
                Ordering::Greater => right.substring(start, end),
            },
        }
    }
}

impl Default for Node {
    fn default() -> Self {
        Self::new()
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
impl TryFrom<&[&[&str]]> for Node {
    type Error = anyhow::Error;

    fn try_from(input: &[&[&str]]) -> anyhow::Result<Self> {
        let mut node = None;

        for values in input {
            let mut child_node = None;

            for value in values.iter() {
                match child_node.take() {
                    Some(cn) => {
                        let temp = Node::new_internal(Arc::new(cn), Arc::new(value.parse()?));
                        child_node = Some(temp);
                    }
                    None => child_node = Some(value.parse()?),
                }
            }

            if let Some(cn) = child_node {
                match node.take() {
                    Some(n) => {
                        let temp = Node::new_internal(Arc::new(n), Arc::new(cn));
                        node = Some(temp);
                    }
                    None => node = Some(cn),
                }
            }
        }

        Ok(node.unwrap_or_default())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // --------------------------------------------
    // TODO: Refactor away in favour of the test-only From<&[&[&str]]> implementation
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
    fn run_split_at(
        values: &[&[&str]],
        index: usize,
        expected: (&str, &str),
    ) -> anyhow::Result<()> {
        let node: Node = values.try_into()?;

        let (left, right) = node.split_at(index);
        let (expected_left, expected_right) = expected;

        assert_eq!(left.to_string(), expected_left.to_string());
        assert_eq!(right.to_string(), expected_right.to_string());

        Ok(())
    }

    #[test]
    fn test_split_at() -> anyhow::Result<()> {
        run_split_at(&[&[""]], 0, ("", ""))?;
        run_split_at(&[&[""]], 1, ("", ""))?;
        run_split_at(&[&["abc"]], 1, ("a", "bc"))?;
        run_split_at(&[&["abc"]], 7, ("abc", ""))?;
        run_split_at(&[&["0123456"]], 3, ("012", "3456"))?;
        run_split_at(&[&["0123456"]], 0, ("", "0123456"))?;
        run_split_at(&[&["hello world"]], 4, ("hell", "o world"))?;
        run_split_at(&[&["a", "b", "c"]], 2, ("ab", "c"))?;
        run_split_at(
            &[&["hello", "world", "goodbye", "mars"]],
            7,
            ("hellowo", "rldgoodbyemars"),
        )?;
        run_split_at(&[&["", "hello", "", "", "world"]], 9, ("helloworl", "d"))?;
        run_split_at(
            &[&["goodbye", "", "ma", "rs", "", ""]],
            9,
            ("goodbyema", "rs"),
        )?;

        let alphabet_tree: &[&[&str]] = &[
            &["abc", "defg", "", "hi"],
            &["", "j", "kl"],
            &["mno", "p"],
            &["qrst", "uv", "w", ""],
            &[],
            &["x", "yz"],
        ];

        run_split_at(alphabet_tree, 5, ("abcde", "fghijklmnopqrstuvwxyz"))?;
        run_split_at(alphabet_tree, 7, ("abcdefg", "hijklmnopqrstuvwxyz"))?;
        run_split_at(alphabet_tree, 16, ("abcdefghijklmnop", "qrstuvwxyz"))?;
        run_split_at(alphabet_tree, 36, ("abcdefghijklmnopqrstuvwxyz", ""))?;
        run_split_at(alphabet_tree, 0, ("", "abcdefghijklmnopqrstuvwxyz"))?;

        Ok(())
    }

    // --------------------------------------------
    fn run_substring(
        values: &[&[&str]],
        start: usize,
        end: usize,
        expected: &str,
    ) -> anyhow::Result<()> {
        let node: Node = values.try_into()?;
        let substring = node.substring(start, end);
        assert_eq!(substring, expected.to_string());

        Ok(())
    }

    #[test]
    fn test_substring() -> anyhow::Result<()> {
        run_substring(&[&[""]], 0, 0, "")?;
        run_substring(&[&[""]], 0, 5, "")?;
        run_substring(&[&["ohellothere"]], 1, 6, "hello")?;
        run_substring(&[&["loremipsumdolorsitamet"]], 15, 18, "sit")?;

        Ok(())
    }
}
