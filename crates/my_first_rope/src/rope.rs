use crate::node;
use std::{fmt::Display, str::FromStr, sync::Arc};

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

    pub fn concat(&mut self, other: Rope) {
        let left = self.root.clone();
        let right = other.root;
        let temp = node::Node::new_internal(left, right);
        self.root = Arc::new(temp);
    }

    pub fn char_at(&self, index: usize) -> Option<char> {
        self.root.char_at(index)
    }

    pub fn split_at(&self, index: usize) -> (Rope, Rope) {
        let (left, right) = self.root.split_at(index);
        (left.into(), right.into())
    }
}

impl From<node::Node> for Rope {
    fn from(node: node::Node) -> Self {
        Self {
            root: Arc::new(node),
        }
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
impl TryFrom<&[&[&str]]> for Rope {
    type Error = anyhow::Error;

    fn try_from(value: &[&[&str]]) -> Result<Self, Self::Error> {
        Ok(Self {
            root: Arc::new(value.try_into()?),
        })
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
        run_init_from_str("")?;
        run_init_from_str("x")?;
        run_init_from_str("hello world")?;
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

    // --------------------------------------------
    fn run_concat(s: &str, concat_list: &[&str], expected: &str) -> anyhow::Result<()> {
        let mut rope = s.parse::<Rope>()?;

        for other in concat_list {
            rope.concat(other.parse::<Rope>()?);
        }

        assert_eq!(rope.len(), expected.len());
        assert_eq!(format!("{rope}"), expected.to_string());

        Ok(())
    }

    #[test]
    fn test_concat() -> anyhow::Result<()> {
        run_concat("hello ", &["world"], "hello world")?;
        run_concat("hello", &["world"], "helloworld")?;
        run_concat("a", &["b", "c"], "abc")?;
        run_concat("", &["hello"], "hello")?;
        run_concat("hello", &[""], "hello")?;
        Ok(())
    }

    // --------------------------------------------
    fn run_char_at(
        concat_list: &[&str],
        index: usize,
        expected: Option<char>,
    ) -> anyhow::Result<()> {
        let mut rope: Option<Rope> = None;

        for other in concat_list {
            let other_rope = other.parse()?;

            match rope.take() {
                Some(mut r) => {
                    r.concat(other_rope);
                    rope = Some(r)
                }
                None => {
                    rope = Some(other_rope);
                }
            }
        }

        assert_eq!(rope.unwrap().char_at(index), expected);

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
        let node: Rope = values.try_into()?;

        let (left, right) = node.split_at(index);
        let (expected_left, expected_right) = expected;

        assert_eq!(left.to_string(), expected_left.to_string());
        assert_eq!(right.to_string(), expected_right.to_string());

        Ok(())
    }

    #[test]
    fn test_split_at() -> anyhow::Result<()> {
        run_split_at(&[&[""]], 0, ("", ""))?;
        run_split_at(&[&[""]], 5, ("", ""))?;
        run_split_at(&[&["ab", "cd"], &["ef", "gh"]], 3, ("abc", "defgh"))?;
        run_split_at(&[&["ab", "cd"], &["ef", "gh"]], 1, ("a", "bcdefgh"))?;
        run_split_at(&[&["ab", "cd"], &["ef", "gh"]], 6, ("abcdef", "gh"))?;
        run_split_at(&[&["ab", "cd"], &["ef", "gh"]], 7, ("abcdefg", "h"))?;
        run_split_at(&[&["ab", "cd"], &["ef", "gh"]], 0, ("", "abcdefgh"))?;

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
}
