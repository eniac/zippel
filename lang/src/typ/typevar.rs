use crate::id::Tid;
use crate::typ::kind::Kind;
use crate::parser::*;
use from_pest::{ConversionError, FromPest};
use pest::{Parser, iterators::Pairs};
use share::{Pretty, DocAllocator, DocBuilder, BoxAllocator};
use std::fmt;

/// A type variable with an associated kind
#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone)]
pub struct TypeVar { pub id: Tid, pub kind: Kind }
impl TypeVar {
    pub fn new<'a>(id: &'a str, kind: Kind) -> Self {
        TypeVar { id: Tid::new(id), kind }
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone)]
pub struct TypeVars(Vec<TypeVar>);

impl<'pest> FromPest<'pest> for TypeVar {
    type Rule = Rule;
    type FatalError = InputError<'pest>;

    fn from_pest(
        pest: &mut Pairs<'pest, Self::Rule>,
    ) -> Result<Self, ConversionError<Self::FatalError>> {
        let pair = pest.next().ok_or(ConversionError::NoMatch)?;
        match pair.as_rule() {
            Rule::tvar => {
                let mut inner = pair.into_inner();
                let id = Tid::from_pest(&mut Pairs::single(inner.next().unwrap()))?;
                let kind = Kind::from_pest(&mut Pairs::single(inner.next().unwrap()))?;
                Ok(TypeVar { id, kind })
            },
            _ => Err(ConversionError::Malformed(InputError::UnexpectedExp(pair))),
        }
    }
}

impl<'pest> FromPest<'pest> for TypeVars {
    type Rule = Rule;
    type FatalError = InputError<'pest>;

    fn from_pest(
        pest: &mut Pairs<'pest, Self::Rule>,
    ) -> Result<Self, ConversionError<Self::FatalError>> {
        let pair = pest.next().ok_or(ConversionError::NoMatch)?;
        match pair.as_rule() {
            Rule::tvars => {
                let mut tvars = Vec::new();
                for pair in pair.into_inner() {
                    tvars.push(TypeVar::from_pest(&mut Pairs::single(pair))?);
                }
                Ok(TypeVars(tvars))
            },
            _ => Err(ConversionError::Malformed(InputError::UnexpectedExp(pair))),
        }
    }
}

/// Pretty printer instance
impl<'a, D, A> Pretty<'a, D, A> for TypeVar
where
    D: DocAllocator<'a, A>,
    D::Doc: Clone,
    A: 'a + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        allocator.concat([
            self.id.pretty(allocator),
            allocator.text(": "),
            self.kind.pretty(allocator),
        ])
    }

    fn is_nil(&self) -> bool {
        false
    }
}

impl fmt::Display for TypeVar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <TypeVar as Pretty<'_, BoxAllocator, ()>>::pretty(self.clone(), &BoxAllocator)
            .1
            .render_fmt(100, f)
    }
}

impl<'a, D, A> Pretty<'a, D, A> for TypeVars
where
    D: DocAllocator<'a, A>,
    D::Doc: Clone,
    A: 'a + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        allocator.intersperse(
            self.0.into_iter().map(|tvar| tvar.pretty(allocator)), ", ")
    }

    fn is_nil(&self) -> bool {
        self.0.is_empty()
    }
}

impl fmt::Display for TypeVars {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <TypeVars as Pretty<'_, BoxAllocator, ()>>::pretty(self.clone(), &BoxAllocator)
            .1
            .render_fmt(100, f)
    }
}

#[test]
fn typevars_parser() {
    let ex = "A: Field, B: Group, C: Scalar<A>, D: Multiplicative<B>, E: Pairing<A, B>, F: 0..10";
    let mut pairs = ZippelParser::parse(Rule::tvars, ex).unwrap();
    assert_eq!(
        TypeVars::from_pest(&mut pairs),
        Ok(TypeVars(vec![
            TypeVar::new("A", Kind::Field),
            TypeVar::new("B", Kind::Group),
            TypeVar::new("C", Kind::scalar("A")),
            TypeVar::new("D", Kind::multiplicative("B")),
            TypeVar::new("E", Kind::pairing("A", "B")),
            TypeVar::new("F", Kind::range(0, 1, 10))
        ]))
    );
}
