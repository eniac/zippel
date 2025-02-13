use from_pest::{ConversionError, FromPest};
use pest::iterators::Pairs;
use pest::Parser;
use std::fmt;

use share::{Traversable1, Pretty, DocAllocator, DocBuilder, BoxAllocator};
use crate::id::Vid;
use crate::typ::{Size, Typ, Qualifier};
use crate::parser::*;

/// `Arg` represents an argument in the Zippel language, including its identifier, type, and principals.
///
///     **Zippel Code:**
///     ```zippel
///     fn foo<Verifier>(a: F  & Verifier) { ... }
///     ```
///
///     In this example, `a` is the identifier of the argument, `F` is the type and `Verifier` is
///     the principal.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct Arg<N> {
    pub qualifier: Qualifier,
    pub id: Vid,
    pub typ: Typ<N>,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct Args<N>(Vec<Arg<N>>);

impl<N> Arg<N> {
    pub fn new<'a>(qualifier: Qualifier, id: &'a str, typ: Typ<N>) -> Self {
        Arg { qualifier, id: Vid::new(id), typ }
    }
}

/// Traversable1 instance for Arg
impl<N> Traversable1<N> for Arg<N> {
    type Output<Z> = Arg<Z>;
    fn traverse1<Z, E>(
        self,
        f: &mut dyn FnMut(N) -> Result<Z, E>,
    ) -> Result<Arg<Z>, E> {
        let Arg { qualifier, id, typ } = self;
        Ok(Arg { qualifier, id, typ: typ.traverse1(f)? })
    }
}

/// Traversable1 instance for Args
impl<N> Traversable1<N> for Args<N> {
    type Output<Z> = Args<Z>;
    fn traverse1<Z, E>(
        self,
        f: &mut dyn FnMut(N) -> Result<Z, E>,
    ) -> Result<Args<Z>, E> {
        Ok(Args(self.0.traverse1(&mut |x| x.traverse1(f))?))
    }
}

/// Pretty printer instance
impl<'a, D, N, A> Pretty<'a, D, A> for Arg<N>
where
    D: DocAllocator<'a, A>,
    N: 'a + Clone + Pretty<'a, D, A>,
    D::Doc: Clone,
    A: 'a + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        let Arg { qualifier, id, typ } = self;
        allocator.concat([
            qualifier.pretty(allocator),
            allocator.space(),
            id.pretty(allocator),
            allocator.text(": "),
            typ.pretty(allocator),
        ])
    }

    fn is_nil(&self) -> bool {
        false
    }
}

/// Display instance calls the pretty printer
impl<'a, N> fmt::Display for Arg<N>
where
    N: Clone + Pretty<'a, BoxAllocator, ()> + 'a
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <Arg<N> as Pretty<'_, BoxAllocator, ()>>::pretty(self.clone(), &BoxAllocator)
            .1
            .render_fmt(60, f)
    }
}

/// Pretty printer instance
impl<'a, D, N, A> Pretty<'a, D, A> for Args<N>
where
    D: DocAllocator<'a, A>,
    N: 'a + Clone + Pretty<'a, D, A>,
    D::Doc: Clone,
    A: 'a + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        allocator.intersperse(
            self.0.into_iter().map(|arg| arg.pretty(allocator)), ", ")
    }

    fn is_nil(&self) -> bool {
        self.0.is_empty()
    }
}

/// Display instance calls the pretty printer
impl<'a, N> fmt::Display for Args<N>
where
    N: Clone + Pretty<'a, BoxAllocator, ()> + 'a
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <Args<N> as Pretty<'_, BoxAllocator, ()>>::pretty(self.clone(), &BoxAllocator)
            .1
            .render_fmt(140, f)
    }
}

/// Parser instances
impl<'pest> FromPest<'pest> for Arg<Size> {
    type Rule = Rule;
    type FatalError = InputError<'pest>;

    fn from_pest(
        pest: &mut Pairs<'pest, Self::Rule>,
    ) -> Result<Self, ConversionError<Self::FatalError>> {
        let pair = pest.next().ok_or(ConversionError::NoMatch)?;
        match pair.as_rule() {
            Rule::arg => {
                let mut inner = pair.into_inner();
                let qualifier = Qualifier::from_pest(&mut inner)?;
                let id = Vid::from_pest(&mut inner)?;
                let typ = Typ::from_pest(&mut inner)?;
                Ok(Arg { qualifier, id, typ })
            }
            _ => Err(ConversionError::Malformed(InputError::UnexpectedExp(pair))),
        }
    }
}

impl<'pest> FromPest<'pest> for Args<Size> {
    type Rule = Rule;
    type FatalError = InputError<'pest>;

    fn from_pest(
        pest: &mut Pairs<'pest, Self::Rule>,
    ) -> Result<Self, ConversionError<Self::FatalError>> {
        let pair = pest.next().ok_or(ConversionError::NoMatch)?;
        match pair.as_rule() {
            Rule::args => {
                let mut args = Vec::new();
                for pair in pair.into_inner() {
                    let mut p = Pairs::single(pair);
                    args.push(Arg::from_pest(&mut p)?);
                }
                Ok(Args(args))
            },
            _ => Err(ConversionError::Malformed(InputError::UnexpectedExp(pair))),
        }
    }
}

#[test]
fn arg_parser() {
    let ex = "public a: F, private foo: X";
    let mut pairs = ZippelParser::parse(Rule::args, ex).unwrap();
    assert_eq!(
        Args::from_pest(&mut pairs),
        Ok(Args(vec![
            Arg::new(Qualifier::Public, "a", Typ::varstr("F")),
            Arg::new(Qualifier::Private, "foo", Typ::varstr("X"))
        ]))
    );

    let ex3 = "a: F";
    assert!(ZippelParser::parse(Rule::arg, ex3).is_err());
}
