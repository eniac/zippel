use from_pest::{ConversionError, FromPest};
use pest::iterators::Pairs;
use std::cmp::Ordering;
use std::fmt;

use share::{Pretty, DocAllocator, DocBuilder, BoxAllocator};
use crate::parser::*;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Qualifier {
    Private,
    Public
}

impl Qualifier {
    pub fn is_private(&self) -> bool {
        matches!(self, Qualifier::Private)
    }
    pub fn is_public(&self) -> bool {
        matches!(self, Qualifier::Public)
    }
}

/// Secret <= Private <= Public
impl PartialOrd for Qualifier {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match (self, other) {
            (Qualifier::Private, Qualifier::Private) => Some(Ordering::Equal),
            (Qualifier::Private, Qualifier::Public) => Some(Ordering::Less),
            (Qualifier::Public, Qualifier::Private) => Some(Ordering::Greater),
            (Qualifier::Public, Qualifier::Public) => Some(Ordering::Equal),
        }
    }
}

impl Ord for Qualifier {
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap()
    }
}

////////////////////////////////////////////////////////////////////////////////////////
/* Pretty Formatting & Display */
////////////////////////////////////////////////////////////////////////////////////////
impl<'a, D, A> Pretty<'a, D, A> for Qualifier
where
    D: DocAllocator<'a, A>,
    D::Doc: Clone,
    A: 'a + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        match self {
            Qualifier::Private => allocator.text("private "),
            Qualifier::Public => allocator.text("public "),
        }
    }
    fn is_nil(&self) -> bool {
        false
    }
}

impl<'a> fmt::Display for Qualifier {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <Qualifier as Pretty<'_, BoxAllocator, ()>>::pretty(self.clone(), &BoxAllocator)
            .1
            .render_fmt(20, f)
    }
}


impl<'pest> FromPest<'pest> for Qualifier {
    type Rule = Rule;
    type FatalError = InputError<'pest>;

    fn from_pest(
        pest: &mut Pairs<'pest, Self::Rule>,
    ) -> Result<Self, ConversionError<Self::FatalError>> {
        let pair = pest.next().ok_or(ConversionError::NoMatch)?;
        match pair.as_rule() {
            Rule::qualifier => Qualifier::from_pest(&mut pair.into_inner()),
            Rule::private => Ok(Qualifier::Private),
            Rule::public => Ok(Qualifier::Public),
            _ => unreachable!()
        }
    }
}

#[cfg(test)] use pest::Parser;
#[test]
fn qualifier_parser() {
    let mut pairs = ZippelParser::parse(Rule::qualifier, "private").unwrap();
    let qual = Qualifier::from_pest(&mut pairs).unwrap();
    assert_eq!(qual, Qualifier::Private);

    let input = "public";
    let mut pairs = ZippelParser::parse(Rule::qualifier, input).unwrap();
    let qual = Qualifier::from_pest(&mut pairs).unwrap();
    assert_eq!(qual, Qualifier::Public);
}

