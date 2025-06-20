use std::{
    cmp::{Ordering, PartialEq},
    fmt::Display,
    str::FromStr,
    sync::Arc,
};

#[derive(Debug, PartialEq, Clone)]
pub struct NodeWeight {
    len: usize,
    newline_count: usize,
    ends_with_newline: bool,
}

pub trait CharLocation {
    fn line(&self) -> usize;
    fn col(&self) -> usize;
}

#[derive(Debug, Clone)]
pub struct LineCol {
    line: usize,
    col: usize,
}

impl CharLocation for LineCol {
    fn line(&self) -> usize {
        self.line
    }

    fn col(&self) -> usize {
        self.col
    }
}

impl<Loc> PartialEq<Loc> for LineCol
where
    Loc: CharLocation,
{
    fn eq(&self, other: &Loc) -> bool {
        self.line() == other.line() && self.col() == other.col()
    }
}

impl From<(usize, usize)> for LineCol {
    fn from((line, col): (usize, usize)) -> Self {
        Self { line, col }
    }
}

impl CharLocation for (usize, usize) {
    fn line(&self) -> usize {
        self.0
    }

    fn col(&self) -> usize {
        self.1
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum Node {
    Internal {
        left: Arc<Node>,
        right: Arc<Node>,
        weight: NodeWeight,
    },
    Leaf(String),
}

impl Node {
    pub fn new() -> Self {
        Self::Leaf("".into())
    }

    pub fn new_internal(left: Arc<Node>, right: Arc<Node>) -> Self {
        Self::Internal {
            weight: NodeWeight {
                len: left.len(),
                newline_count: left.newline_count(),
                ends_with_newline: left.ends_with_newline(),
            },
            left,
            right,
        }
    }

    fn ends_with_newline(&self) -> bool {
        match self {
            Self::Leaf(substr) => substr.ends_with('\n'),
            Self::Internal { left, right, .. } => {
                if right.is_empty() {
                    left.ends_with_newline()
                } else {
                    right.ends_with_newline()
                }
            }
        }
    }

    fn newline_count(&self) -> usize {
        match self {
            Self::Leaf(substr) => substr.chars().filter(|&c| c == '\n').count(),
            Self::Internal { right, weight, .. } => weight.newline_count + right.newline_count(),
        }
    }

    pub fn len(&self) -> usize {
        match self {
            Node::Leaf(substr) => substr.len(),
            Node::Internal { weight, right, .. } => weight.len + right.len(),
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
            } => match index.cmp(&weight.len) {
                Ordering::Less => left.char_at(index),
                _ => right.char_at(index - weight.len),
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

                match index.cmp(&weight.len) {
                    Ordering::Less => {
                        let (left_left, left_right) = left.split_at(index);
                        let rest = Node::new_internal(Arc::new(left_right), Arc::new(right));
                        (left_left, rest)
                    }
                    Ordering::Greater => {
                        let (right_left, right_right) = right.split_at(index - weight.len);
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

                if start == 0 && end >= substr.len() {
                    return substr.to_owned();
                }

                String::from(&substr[start..end.min(substr.len())])
            }
            Node::Internal {
                left,
                right,
                weight,
            } => {
                if start <= weight.len && end > weight.len {
                    left.substring(start, weight.len) + &right.substring(0, end - weight.len)
                } else if start > weight.len {
                    right.substring(start - weight.len, end - weight.len)
                } else {
                    left.substring(start, end)
                }
            }
        }
    }

    pub fn line_count(&self) -> usize {
        match self {
            Self::Leaf(substr) => {
                if substr.is_empty() {
                    0
                } else {
                    let newlines = substr.chars().filter(|&c| c == '\n').count();
                    if substr.ends_with('\n') {
                        newlines.max(1) // A way to exclude the '\n' unless it's the only
                    // character.
                    } else {
                        newlines + 1 // Else the '\n' characters are interspersed, and we can just
                        // add 1 to represent the rest of the chunks
                    }
                }
            }
            Self::Internal {
                left,
                right,
                weight,
            } => {
                let left_lines = left.line_count();
                let right_lines = right.line_count();

                if weight.ends_with_newline {
                    left_lines + right_lines
                } else if weight.len == 0 {
                    right_lines
                } else {
                    left_lines + right_lines.saturating_sub(1) // right node carries on the line of
                    // the left node.
                }
            }
        }
    }

    pub fn char_to_line_col(&self, char_index: usize) -> LineCol {
        self.char_to_line_col_with_offset(char_index, 1, 0)
    }

    fn char_to_line_col_with_offset(
        &self,
        char_index: usize,
        line_offset: usize,
        col_offset: usize,
    ) -> LineCol {
        match self {
            Self::Leaf(substr) => {
                let mut line = line_offset;
                let mut col = col_offset;

                for c in substr.chars().take(char_index) {
                    match c {
                        '\n' => {
                            line += 1;
                            col = 0;
                        }
                        _ => col += 1,
                    };
                }
                LineCol { line, col }
            }
            Self::Internal {
                left,
                right,
                weight,
            } => match char_index.cmp(&weight.len) {
                Ordering::Greater => {
                    let LineCol { line, col } =
                        left.char_to_line_col_with_offset(weight.len, line_offset, col_offset);
                    let remaining_char_index = char_index.saturating_sub(weight.len);
                    right.char_to_line_col_with_offset(remaining_char_index, line, col)
                }
                _ => left.char_to_line_col_with_offset(char_index, line_offset, col_offset),
            },
        }
    }

    pub fn line_col_to_char(&self, location: impl CharLocation) -> Option<char> {
        let text = self.to_string();

        if !text.is_empty() {
            for (i, line) in text.split_inclusive('\n').enumerate() {
                if location.line() == i + 1 {
                    for (char_index, ch) in line.char_indices() {
                        if location.col() == char_index {
                            return Some(ch);
                        }
                    }

                    return None;
                }
            }
        }

        None
    }

    pub fn line_col_to_char_index(&self, location: impl CharLocation) -> usize {
        let text = self.to_string();

        if !text.is_empty() {
            let mut global_char_index = 0usize;

            for (i, line) in text.split_inclusive('\n').enumerate() {
                if location.line() == i + 1 {
                    for (char_index, _) in line.char_indices() {
                        if location.col() == char_index {
                            return global_char_index + char_index;
                        }
                    }

                    return global_char_index + line.len();
                }

                global_char_index += line.chars().count();
            }

            return global_char_index;
        }

        0
    }

    pub fn line_at(&self, line_number: usize) -> Option<String> {
        assert!(line_number > 0, "line_number must be above zero");
        self.to_string()
            .lines()
            .nth(line_number - 1)
            .map(ToString::to_string)
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
        run_substring(&[&["prefix"]], 3, 6, "fix")?;
        run_substring(&[&["postfix"]], 0, 4, "post")?;
        run_substring(&[&["hello"]], 0, 5, "hello")?;
        run_substring(&[&["hello"]], 2, 2, "")?;

        let alphabet_tree: &[&[&str]] = &[
            &["abc", "defg", "", "hi"],
            &["", "j", "kl"],
            &["mno", "p"],
            &["qrst", "uv", "w", ""],
            &[],
            &["x", "yz"],
        ];

        run_substring(alphabet_tree, 2, 8, "cdefgh")?;
        run_substring(alphabet_tree, 0, 26, "abcdefghijklmnopqrstuvwxyz")?;
        run_substring(alphabet_tree, 10, 18, "klmnopqr")?;

        Ok(())
    }

    // --------------------------------------------
    fn run_line_count(values: &[&[&str]], expected: usize) -> anyhow::Result<()> {
        let node: Node = values.try_into()?;
        assert_eq!(node.line_count(), expected);

        Ok(())
    }

    #[test]
    pub fn test_line_count() -> anyhow::Result<()> {
        run_line_count(&[&[""]], 0)?;
        run_line_count(&[&["hello"]], 1)?;
        run_line_count(&[&["hello\nworld"]], 2)?;
        run_line_count(&[&["hello\nworld\ntest"]], 3)?;
        run_line_count(&[&["hello\nwo"], &["rld"]], 2)?;
        run_line_count(&[&["\nhello\nwo"], &["rld"]], 3)?;
        run_line_count(&[&["a\nb\n\ncde"], &["f\ngh"]], 5)?;
        run_line_count(&[&["\n"]], 1)?;
        run_line_count(&[&["\n\n"]], 2)?;

        let alphabet_tree_with_newlines: &[&[&str]] = &[
            &["ab\nc", "defg\n", "", "\nhi"],
            &["\n", "j", "kl"],
            &["mn\n\no", "\n\np"],
            &["qrst\n\n", "uv", "w", ""],
            &[],
            &["x", "yz"],
        ];

        run_line_count(alphabet_tree_with_newlines, 11)?;

        Ok(())
    }

    // --------------------------------------------
    pub fn run_char_to_line_col(
        values: &[&[&str]],
        char_index: usize,
        expected: (usize, usize),
    ) -> anyhow::Result<()> {
        let node: Node = values.try_into()?;
        let expected: LineCol = expected.into();
        assert_eq!(node.char_to_line_col(char_index), expected);
        Ok(())
    }

    #[test]
    fn test_char_to_line_col() -> anyhow::Result<()> {
        run_char_to_line_col(&[&[""]], 0, (1, 0))?;
        run_char_to_line_col(&[&[""]], 4, (1, 0))?;
        run_char_to_line_col(&[&["café"]], 0, (1, 0))?;
        run_char_to_line_col(&[&["café"]], 2, (1, 2))?;
        run_char_to_line_col(&[&["café"]], 8, (1, 4))?;
        run_char_to_line_col(&[&["hello\nthere"]], 7, (2, 1))?;
        run_char_to_line_col(&[&["\nhello"]], 0, (1, 0))?;
        run_char_to_line_col(&[&["\nhello"]], 1, (2, 0))?;
        run_char_to_line_col(&[&["\nhello\nfriends\n"]], 9, (3, 2))?;
        run_char_to_line_col(&[&["\nhello\nfriends\n"]], 13, (3, 6))?;
        run_char_to_line_col(&[&["\nhello\nfriends\n"]], 14, (3, 7))?;

        let alphabet_tree_with_newlines: &[&[&str]] = &[
            &["ab\nc", "defg\n", "", "\nhi"],
            &["\n", "j", "kl"],
            &["mn\n\no", "\n\np"],
            &["qrst\n\n", "uv", "w", ""],
            &[],
            &["x", "yz"],
        ];

        run_char_to_line_col(alphabet_tree_with_newlines, 5, (2, 2))?;
        run_char_to_line_col(alphabet_tree_with_newlines, 19, (6, 0))?;
        run_char_to_line_col(alphabet_tree_with_newlines, 20, (7, 0))?;
        run_char_to_line_col(alphabet_tree_with_newlines, 35, (11, 5))?;

        Ok(())
    }

    // --------------------------------------------
    fn run_line_col_to_char(
        values: &[&[&str]],
        location: (usize, usize),
        expected: Option<char>,
    ) -> anyhow::Result<()> {
        let node: Node = values.try_into()?;
        assert_eq!(node.line_col_to_char(location), expected);
        Ok(())
    }

    #[test]
    fn test_line_col_to_char() -> anyhow::Result<()> {
        run_line_col_to_char(&[&[""]], (0, 0), None)?;
        run_line_col_to_char(&[&[""]], (1, 0), None)?;
        run_line_col_to_char(&[&["café"]], (1, 0), Some('c'))?;
        run_line_col_to_char(&[&["café"]], (1, 3), Some('é'))?;
        run_line_col_to_char(&[&["café"]], (2, 0), None)?;
        run_line_col_to_char(&[&["hello\nthere"]], (1, 3), Some('l'))?;
        run_line_col_to_char(&[&["hello\nthere"]], (1, 5), Some('\n'))?;
        run_line_col_to_char(&[&["hello\nthere"]], (2, 1), Some('h'))?;
        run_line_col_to_char(&[&["\nhello\nthere"]], (3, 0), Some('t'))?;
        run_line_col_to_char(&[&["\n\n\n\n"]], (3, 0), Some('\n'))?;

        let alphabet_tree_with_newlines: &[&[&str]] = &[
            &["ab\nc", "defg\n", "", "\nhi"],
            &["n", "j", "kl"],
            &["mn\n\no", "\n\np"],
            &["qrst\n\n", "uv", "w", ""],
            &[],
            &["x", "yz"],
        ];

        run_line_col_to_char(alphabet_tree_with_newlines, (2, 1), Some('d'))?;
        run_line_col_to_char(alphabet_tree_with_newlines, (4, 3), Some('j'))?;
        run_line_col_to_char(alphabet_tree_with_newlines, (10, 2), Some('w'))?;
        run_line_col_to_char(alphabet_tree_with_newlines, (6, 0), Some('o'))?;
        run_line_col_to_char(alphabet_tree_with_newlines, (6, 1), Some('\n'))?;
        run_line_col_to_char(alphabet_tree_with_newlines, (6, 2), None)?;

        Ok(())
    }

    // --------------------------------------------
    fn run_line_col_to_char_index(
        values: &[&[&str]],
        location: (usize, usize),
        expected: usize,
    ) -> anyhow::Result<()> {
        let node: Node = values.try_into()?;
        assert_eq!(node.line_col_to_char_index(location), expected);
        Ok(())
    }

    #[test]
    fn test_line_col_to_char_index() -> anyhow::Result<()> {
        run_line_col_to_char_index(&[&[""]], (0, 0), 0)?;
        run_line_col_to_char_index(&[&[""]], (1, 0), 0)?;
        run_line_col_to_char_index(&[&["café"]], (1, 0), 0)?;
        run_line_col_to_char_index(&[&["café"]], (1, 3), 3)?;
        run_line_col_to_char_index(&[&["café"]], (2, 0), 4)?;
        run_line_col_to_char_index(&[&["hello\nthere"]], (1, 3), 3)?;
        run_line_col_to_char_index(&[&["hello\nthere"]], (1, 5), 5)?;
        run_line_col_to_char_index(&[&["hello\nthere"]], (2, 1), 7)?;
        run_line_col_to_char_index(&[&["\nhello\nthere"]], (3, 0), 7)?;
        run_line_col_to_char_index(&[&["\n\n\n\n"]], (3, 0), 2)?;

        let alphabet_tree_with_newlines: &[&[&str]] = &[
            &["ab\nc", "defg\n", "", "\nhi"],
            &["n", "j", "kl"],
            &["mn\n\no", "\n\np"],
            &["qrst\n\n", "uv", "w", ""],
            &[],
            &["x", "yz"],
        ];

        run_line_col_to_char_index(alphabet_tree_with_newlines, (2, 1), 4)?;
        run_line_col_to_char_index(alphabet_tree_with_newlines, (4, 3), 13)?;
        run_line_col_to_char_index(alphabet_tree_with_newlines, (10, 2), 32)?;
        run_line_col_to_char_index(alphabet_tree_with_newlines, (6, 0), 20)?;
        run_line_col_to_char_index(alphabet_tree_with_newlines, (6, 1), 21)?;
        run_line_col_to_char_index(alphabet_tree_with_newlines, (6, 2), 22)?;

        Ok(())
    }

    // --------------------------------------------
    fn run_line_at(
        values: &[&[&str]],
        line_number: usize,
        expected: Option<String>,
    ) -> anyhow::Result<()> {
        let node: Node = values.try_into()?;
        assert_eq!(node.line_at(line_number), expected);
        Ok(())
    }

    #[test]
    #[should_panic]
    fn test_line_at_panics_when_line_number_is_zero() {
        let node = "irrelevant value".parse::<Node>();
        assert!(node.is_ok());
        node.unwrap().line_at(0);
    }

    #[test]
    fn test_line_at() -> anyhow::Result<()> {
        run_line_at(&[&[""]], 1, None)?;
        run_line_at(&[&["test"]], 1, Some("test".into()))?;
        run_line_at(&[&["café"]], 1, Some("café".into()))?;
        run_line_at(&[&["hello\nwords"]], 1, Some("hello".into()))?;
        run_line_at(&[&["hello\nwords"]], 2, Some("words".into()))?;
        run_line_at(&[&["\nhello\nwords\n"]], 2, Some("hello".into()))?;
        run_line_at(&[&["\nhello\nwords\n"]], 1, Some("".into()))?;
        run_line_at(&[&["\nhello\nwords"]], 4, None)?;
        run_line_at(&[&["\nhello\nwords\n"]], 4, None)?;
        run_line_at(&[&["\nhello\nwords\n\n"]], 4, Some("".into()))?;

        let alphabet_tree_with_newlines: &[&[&str]] = &[
            &["ab\nc", "defg\n", "", "\nhi"],
            &["\n", "j", "kl"],
            &["mn\n\no", "\n\np"],
            &["qrst\n\n", "uv", "w", ""],
            &[],
            &["x", "yz"],
        ];

        run_line_at(alphabet_tree_with_newlines, 1, Some("ab".into()))?;
        run_line_at(alphabet_tree_with_newlines, 2, Some("cdefg".into()))?;
        run_line_at(alphabet_tree_with_newlines, 3, Some("".into()))?;
        run_line_at(alphabet_tree_with_newlines, 5, Some("jklmn".into()))?;
        run_line_at(alphabet_tree_with_newlines, 20, None)?;

        Ok(())
    }
}
