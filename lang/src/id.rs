use share::{DocAllocator, DocBuilder, Pretty, Set};
use std::fmt;

use crate::parser::*;
use from_pest::{ConversionError, FromPest};
use pest::iterators::Pairs;

/// Generate a new identifier not in the set
pub trait Fresh: Ord + Sized {
    fn fresh(root: &str, s: &mut Set<Self>) -> Self;
}

/// Type variable identifier
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub struct Tid(pub String);

/// Traverse TIDs
pub trait TidSubst: Sized {
    fn tid_subst(&mut self, from: &Tid, to: &Tid);
}

impl<'a, D, A> Pretty<'a, D, A> for Tid
where
    D: DocAllocator<'a, A>,
    D::Doc: Clone,
    A: 'a + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        allocator.text(self.0.to_string())
    }

    fn is_nil(&self) -> bool {
        self.0.is_empty()
    }
}

impl fmt::Display for Tid {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl From<&str> for Tid {
    fn from(s: &str) -> Self {
        Tid(s.to_string())
    }
}

impl From<String> for Tid {
    fn from(s: String) -> Self {
        Tid(s)
    }
}

impl Default for Tid {
    fn default() -> Self {
        Tid("".to_string())
    }
}

/// Fresh type variable generator
impl Fresh for Tid {
    fn fresh(root: &str, s: &mut Set<Self>) -> Self {
        let (root, mut i) = split_alphanumeric(root);
        loop {
            i += 1;
            let id = Tid(format!("{}{}", root, i));
            if !s.contains(&id) {
                s.insert(id.clone());
                return id;
            }
        }
    }
}

/// Fresh variable generator
impl Fresh for Vid {
    fn fresh(root: &str, s: &mut Set<Self>) -> Self {
        let (root, mut i) = split_alphanumeric(root);
        loop {
            i += 1;
            let id = Vid(format!("{}{}", root, i));
            if !s.contains(&id) {
                s.insert(id.clone());
                return id;
            }
        }
    }
}
/// Arbitrary instance for Tid
#[cfg(test)]
use arbitrary::{Arbitrary, Unstructured};
#[cfg(test)]
impl<'a> Arbitrary<'a> for Tid {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let c = u.int_in_range(0..=25)?;
        Ok(Tid(format!("{}", (b'A' + c) as char)))
    }
}

impl Tid {
    pub fn new(s: &str) -> Self {
        Tid(s.to_string())
    }
}

/// Expression variable identifier
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub struct Vid(pub String);

impl<'a, D, A> Pretty<'a, D, A> for Vid
where
    D: DocAllocator<'a, A>,
    D::Doc: Clone,
    A: 'a + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        allocator.text(self.0.to_string())
    }
    fn is_nil(&self) -> bool {
        self.0.is_empty()
    }
}

impl fmt::Display for Vid {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl From<&str> for Vid {
    fn from(s: &str) -> Self {
        Vid(s.to_string())
    }
}

impl From<String> for Vid {
    fn from(s: String) -> Self {
        Vid(s)
    }
}

impl Default for Vid {
    fn default() -> Self {
        Vid("".to_string())
    }
}

/// Arbitrary instance for Vid
#[cfg(test)]
impl<'a> Arbitrary<'a> for Vid {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let c = u.int_in_range(0..=25)?;
        Ok(Vid(format!("{}", (b'a' + c) as char)))
    }
}

impl Vid {
    pub fn new(s: &str) -> Self {
        Vid(s.to_string())
    }
}

impl<'pest> FromPest<'pest> for Vid {
    type Rule = Rule;
    type FatalError = InputError<'pest>;

    fn from_pest(
        pest: &mut Pairs<'pest, Self::Rule>,
    ) -> Result<Self, ConversionError<Self::FatalError>> {
        let pair = pest.next().ok_or(ConversionError::NoMatch)?;
        match pair.as_rule() {
            Rule::id => {
                let s = pair.as_str();
                Ok(Vid::from(s))
            }
            _ => unreachable!(),
        }
    }
}

impl<'pest> FromPest<'pest> for Tid {
    type Rule = Rule;
    type FatalError = InputError<'pest>;

    fn from_pest(
        pest: &mut Pairs<'pest, Self::Rule>,
    ) -> Result<Self, ConversionError<Self::FatalError>> {
        let pair = pest.next().ok_or(ConversionError::NoMatch)?;
        match pair.as_rule() {
            Rule::id => {
                let s = pair.as_str();
                Ok(Tid::from(s))
            }
            _ => unreachable!(),
        }
    }
}

fn split_alphanumeric(input: &str) -> (String, i32) {
    // Find the last non-digit character
    let chars: Vec<char> = input.chars().collect();
    let last_non_digit_pos = chars.iter().rposition(|c| !c.is_numeric());

    match last_non_digit_pos {
        Some(pos) => {
            // There is at least one non-digit, check if there are digits after it
            if pos < input.len() - 1 {
                // There are trailing digits after the last non-digit
                let alpha_part = &input[..=pos];
                let numeric_part = input[pos + 1..].parse::<i32>().unwrap_or(0);
                (alpha_part.to_string(), numeric_part)
            } else {
                // The string ends with a non-digit
                (input.to_string(), 0)
            }
        }
        None => {
            // The entire string is digits
            if !input.is_empty() {
                ("".to_string(), input.parse::<i32>().unwrap_or(0))
            } else {
                ("".to_string(), 0)
            }
        }
    }
}

#[test]
fn test_simple_alphanumeric() {
    assert_eq!(split_alphanumeric("a32"), ("a".to_string(), 32));
}

#[test]
fn test_only_alpha() {
    assert_eq!(split_alphanumeric("abc"), ("abc".to_string(), 0));
}

#[test]
fn test_only_numeric() {
    assert_eq!(split_alphanumeric("123"), ("".to_string(), 123));
}

#[test]
fn test_alpha_numeric_alpha() {
    assert_eq!(split_alphanumeric("a3a"), ("a3a".to_string(), 0));
}

#[test]
fn test_complex_pattern() {
    assert_eq!(
        split_alphanumeric("abc123def"),
        ("abc123def".to_string(), 0)
    );
}

#[test]
fn test_alpha_ending_with_numeric() {
    assert_eq!(split_alphanumeric("abc123"), ("abc".to_string(), 123));
}

#[test]
fn test_empty_string() {
    assert_eq!(split_alphanumeric(""), ("".to_string(), 0));
}

#[test]
fn test_special_characters_with_trailing_number() {
    assert_eq!(split_alphanumeric("a-_!@#123"), ("a-_!@#".to_string(), 123));
}

#[test]
fn tid_fresh() {
    let mut bound = Set::from(vec![Tid("T0".to_string()), Tid("T1".to_string())]);
    let t = Tid::fresh("T", &mut bound);
    assert_eq!(t, Tid("T2".to_string()));
}

#[test]
fn vid_fresh() {
    let mut bound = Set::from(vec![Tid("v".to_string()), Tid("v1".to_string())]);
    let t = Tid::fresh("v", &mut bound);
    assert_eq!(t, Tid("v2".to_string()));
}

////////////////////////////////////////////////////////////////////////////////////////
/// Parser tests
////////////////////////////////////////////////////////////////////////////////////////
#[cfg(test)]
use pest::Parser;
#[test]
fn id_parser() {
    let mut pairs = ZippelParser::parse(Rule::id, "N").unwrap();
    assert_eq!(Tid::from_pest(&mut pairs).unwrap(), Tid::new("N"));

    pairs = ZippelParser::parse(Rule::id, "foo").unwrap();
    assert_eq!(Tid::from_pest(&mut pairs).unwrap(), Tid::new("foo"));

    pairs = ZippelParser::parse(Rule::id, "Foo").unwrap();
    assert_eq!(Tid::from_pest(&mut pairs).unwrap(), Tid::new("Foo"));

    pairs = ZippelParser::parse(Rule::id, "Foo").unwrap();
    assert_eq!(Vid::from_pest(&mut pairs).unwrap(), Vid::new("Foo"));
}
