use from_pest::{ConversionError, FromPest};
use pest::iterators::Pairs;
use std::fmt;

use share::traversal::VecTraversal;
use share::{Traversal, Pretty, DocAllocator, DocBuilder, BoxAllocator};
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
pub struct Args<N>(pub Vec<Arg<N>>);

impl<N> Arg<N> {
    pub fn new<'a>(qualifier: Qualifier, id: &'a str, typ: Typ<N>) -> Self {
        Arg { qualifier, id: Vid::new(id), typ }
    }
    pub fn public<'a>(id: &'a str, typ: Typ<N>) -> Self {
        Arg { qualifier: Qualifier::Public, id: Vid::new(id), typ }
    }
    pub fn private<'a>(id: &'a str, typ: Typ<N>) -> Self {
        Arg { qualifier: Qualifier::Private, id: Vid::new(id), typ }
    }
    pub fn get_traversal1() -> ArgTraversal1<N> {
        ArgTraversal1(std::marker::PhantomData)
    }
    pub fn get_traversal_type() -> ArgTraversalType<N> {
        ArgTraversalType(std::marker::PhantomData)
    }
}

impl<N> Args<N> {
    pub fn get_traversal1() -> ArgsTraversal1<N> {
        ArgsTraversal1(std::marker::PhantomData)
    }
    pub fn get_traversal_type() -> ArgsTraversalType<N> {
        ArgsTraversalType(std::marker::PhantomData)
    }
}

/// Traversal instance for Arg
pub struct ArgTraversal1<N>(std::marker::PhantomData<N>);
impl<N, M> Traversal<N, M> for ArgTraversal1<N> {
    type Domain = Arg<N>;
    type Codomain = Arg<M>;
    fn traverse<E>(
        on: Self::Domain,
        f: &mut dyn FnMut(N) -> Result<M, E>,
    ) -> Result<Self::Codomain, E> {
        let Arg { qualifier, id, typ } = on;
        Ok(Arg { qualifier, id, typ: Typ::get_traversal::traverse(typ, f)? })
    }
}

/// Traversal instance for Arg types
pub struct ArgTraversalType<N>(std::marker::PhantomData<N>);
impl<N> Traversal<Typ<N>> for ArgTraversalType<N> {
    type Domain = Arg<N>;
    type Codomain = Arg<N>;
    fn traverse<E>(
        on: Self::Domain,
        f: &mut dyn FnMut(Typ<N>) -> Result<Typ<N>, E>,
    ) -> Result<Self::Codomain, E> {
        let Arg { qualifier, id, typ } = on;
        Ok(Arg { qualifier, id, typ: f(typ)? })
    }
}

/// Traversal instance for Args
pub struct ArgsTraversal1<N>(std::marker::PhantomData<N>);
impl<N, M> Traversal<N, M> for ArgsTraversal1<N> {
    type Domain = Args<N>;
    type Codomain = Args<M>;
    fn traverse<E>(
        on: Self::Domain,
        f: &mut dyn FnMut(N) -> Result<M, E>,
    ) -> Result<Self::Codomain, E> {
        VecTraversal::traverse(on.0, &mut |x| ArgTraversal1::traverse(x, f)).map(Args)
    }
}

/// Traversal instance for Args types
pub struct ArgsTraversalType<N>(std::marker::PhantomData<N>);
impl<N> Traversal<Typ<N>> for ArgsTraversalType<N> {
    type Domain = Args<N>;
    type Codomain = Args<N>;
    fn traverse<E>(
        on: Self::Domain,
        f: &mut dyn FnMut(Typ<N>) -> Result<Typ<N>, E>,
    ) -> Result<Self::Codomain, E> {
        VecTraversal::traverse(on.0, &mut |arg| ArgTraversalType::traverse(arg, f)).map(Args)
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

#[cfg(test)] use pest::Parser;
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

#[test]
fn arg_traversal() {
    let arg = Arg::new(Qualifier::Public, "a", Typ::fin(Size::from(2)));
    assert_eq!(Arg::get_traversal1::traverse(arg.clone(), &mut |x| Ok(x + 1)).unwrap(),
       Arg::new(Qualifier::Public, "a", Typ::fin(Size::from(3)))); // 2 + 1 = 3
}
