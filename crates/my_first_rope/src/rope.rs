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

    pub fn concat(&mut self, other: Rope) -> &mut Self {
        let left = self.root.clone();
        let right = other.root;
        let temp = node::Node::new_internal(left, right);
        self.root = Arc::new(temp);
        self
    }

    pub fn char_at(&self, index: usize) -> Option<char> {
        self.root.char_at(index)
    }

    pub fn split_at(&self, index: usize) -> (Rope, Rope) {
        let (left, right) = self.root.split_at(index);
        (left.into(), right.into())
    }

    pub fn insert_at(&mut self, index: usize, value: &str) -> anyhow::Result<&mut Self> {
        let (mut left, right) = self.split_at(index);
        left.concat(value.parse()?).concat(right);
        self.root = left.root;
        Ok(self)
    }

    pub fn delete_range(&mut self, start: usize, end: usize) -> &mut Self {
        assert!(start <= end);
        let (mut left, right) = self.split_at(start);
        let (_, right_right) = right.split_at(end - start);
        left.concat(right_right);
        self.root = left.root;
        self
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
        let rope: Rope = values.try_into()?;

        let (left, right) = rope.split_at(index);
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

    // --------------------------------------------
    fn run_insert_at(
        values: &[&[&str]],
        index: usize,
        to_insert: &str,
        expected: &str,
    ) -> anyhow::Result<()> {
        let mut rope: Rope = values.try_into()?;
        rope.insert_at(index, to_insert)?;
        assert_eq!(rope.to_string(), expected.to_string());

        Ok(())
    }

    #[test]
    fn test_insert_at() -> anyhow::Result<()> {
        run_insert_at(&[&[""]], 0, "hi", "hi")?;
        run_insert_at(&[&[""]], 5, "hi", "hi")?;
        run_insert_at(&[&["hello"]], 2, "XX", "heXXllo")?;
        run_insert_at(&[&["hello"]], 0, "XX", "XXhello")?;
        run_insert_at(&[&["hello"]], 5, "XX", "helloXX")?;
        run_insert_at(&[&["nochange"]], 3, "", "nochange")?;
        run_insert_at(
            &[&["hello ", "world"], &[" moon"]],
            11,
            " goodbye",
            "hello world goodbye moon",
        )?;

        let alphabet_tree: &[&[&str]] = &[
            &["abc", "defg", "", "hi"],
            &["", "j", "kl"],
            &["mno", "p"],
            &["qrst", "uv", "w", ""],
            &[],
            &["x", "yz"],
        ];

        run_insert_at(alphabet_tree, 1, "_", "a_bcdefghijklmnopqrstuvwxyz")?;
        run_insert_at(alphabet_tree, 11, "@", "abcdefghijk@lmnopqrstuvwxyz")?;

        Ok(())
    }

    // --------------------------------------------
    fn run_delete_range(
        values: &[&[&str]],
        (start, end): (usize, usize),
        expected: &str,
    ) -> anyhow::Result<()> {
        let mut rope: Rope = values.try_into()?;
        rope.delete_range(start, end);
        assert_eq!(rope.to_string(), expected.to_string());

        Ok(())
    }

    #[test]
    fn test_delete_range() -> anyhow::Result<()> {
        run_delete_range(&[&[""]], (0, 0), "")?;
        run_delete_range(&[&["nochange"]], (2, 2), "nochange")?;
        run_delete_range(&[&["hello woorld"]], (7, 8), "hello world")?;
        run_delete_range(&[&["0123456789"]], (3, 8), "01289")?;
        run_delete_range(&[&["hello"]], (1, 4), "ho")?;
        run_delete_range(&[&["hello"]], (3, 5), "hel")?;
        run_delete_range(&[&["hello"]], (0, 5), "")?;
        run_delete_range(&[&["hello"]], (3, 10), "hel")?;
        run_delete_range(&[&["hello"]], (7, 10), "hello")?;
        run_delete_range(&[&["hello"]], (0, 2), "llo")?;

        let alphabet_tree: &[&[&str]] = &[
            &["abc", "defg", "", "hi"],
            &["", "j", "kl"],
            &["mno", "p"],
            &["qrst", "uv", "w", ""],
            &[],
            &["x", "yz"],
        ];

        run_delete_range(alphabet_tree, (11, 16), "abcdefghijkqrstuvwxyz")?;
        run_delete_range(alphabet_tree, (1, 25), "az")?;
        run_delete_range(alphabet_tree, (0, 26), "")?;

        Ok(())
    }
}
