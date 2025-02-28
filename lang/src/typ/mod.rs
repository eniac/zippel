mod kind;
mod typevar;
mod size;
mod qualifier;
mod nothing;
pub mod infer;
pub mod unify;
pub mod lub;
pub mod subst;

use crate::id::{Tid, TidTraversal};
use crate::range::{Range, RangeTraversal};

pub use kind::Kind;
pub use size::{Size, EvalError};
pub use qualifier::Qualifier;
pub use typevar::{TypeVar, TypeVars};
pub use nothing::Nothing;
pub use subst::{SizeSubsts, AliasSubsts};

use share::{Ctx, Pretty, Traversal, BoxAllocator, DocAllocator, DocBuilder};
use share::traversal::ToTraversal1;
use crate::parser::*;
use from_pest::{ConversionError, FromPest};
use pest::iterators::Pairs;
use std::fmt;

/// The types of expressions, [N] is the size parameter
#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone)]
pub enum Typ<N> {
    /// Univariate polynomial of degree [Size] and base type [Tid]
    Uni(Tid, N),
    /// Multilinear polynomial of arity [Size] and base type [Tid]
    Mle(Tid, N),
    /// Vector of size [N] and base type [Typ]
    Vec(Box<Typ<N>>, N),
    /// Tid type [Tid]
    Base(Tid),
    /// Fin within range
    Fin(Range<N>),
    /// Boolean (BExp)
    Bool
}

/// Many types
#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone)]
pub struct Typs<N>(pub Vec<Typ<N>>);

impl<N> TidTraversal for Typ<N> {
    fn tid_traverse<E>(self, f: &mut dyn FnMut(Tid) -> Result<Tid, E>) -> Result<Self, E> {
        match self {
            Typ::Uni(b, n) => Ok(Typ::Uni(f(b)?, n)),
            Typ::Mle(b, n) => Ok(Typ::Mle(f(b)?, n)),
            Typ::Base(b) => Ok(Typ::Base(f(b)?)),
            Typ::Vec(box b, n) =>
                Ok(Typ::Vec(Box::new(b.tid_traverse(f)?), n)),
            Typ::Fin(r) => Ok(Typ::Fin(r)),
            Typ::Bool => Ok(Typ::Bool)
        }
    }
}

impl<N> IntoIterator for Typs<N> {
    type Item = Typ<N>;
    type IntoIter = std::vec::IntoIter<Typ<N>>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<N> FromIterator<Typ<N>> for Typs<N> {
    fn from_iter<I: IntoIterator<Item=Typ<N>>>(iter: I) -> Self {
        Typs(iter.into_iter().collect())
    }
}

impl<N> TidTraversal for Typs<N> {
    fn tid_traverse<E>(self, f: &mut dyn FnMut(Tid) -> Result<Tid, E>) -> Result<Self, E> {
        Ok(Typs(self.0.into_iter().map(|t| t.tid_traverse(f)).collect::<Result<Vec<_>, _>>()?))
    }
}

/// Symbolically sized type
pub type UTyp = Typ<Size>;

/// Symbolically sized types
pub type UTyps = Typ<Size>;

/// Concrete size type
pub type CTyp = Typ<usize>;

/// Concrete size types
pub type CTyps = Typs<usize>;

impl<N> Typ<N> {
    pub fn varstr<'a>(b: &'a str) -> Self {
        Typ::Base(Tid::new(b))
    }
    pub fn var(b: Tid) -> Self {
        Typ::Base(b)
    }
    pub fn uni(b: Tid, n: N) -> Self {
        Typ::Uni(b, n)
    }
    pub fn mle(b: Tid, n: N) -> Self {
        Typ::Mle(b, n)
    }
    pub fn vec(b: Typ<N>, n: N) -> Self {
        Typ::Vec(Box::new(b), n)
    }
    pub fn fin(range: Range<N>) -> Self {
        Typ::Fin(range)
    }
    pub fn bool() -> Self {
        Typ::Bool
    }
    pub fn get_base(&self) -> Option<&Tid> {
        match self {
            Typ::Base(b) => Some(b),
            _ => None
        }
    }
    pub fn to_field(self, ctx: &Ctx<Tid, Kind>) -> Option<Tid> {
        match self {
            Typ::Base(b) => {
                let k = ctx.get(&b)?;
                if k.is_field() {
                    Some(b)
                } else {
                    None
                }
            },
            Typ::Fin(_) =>
                // Find the first field and return It
                ctx.iter().find(|(_, k)| k.is_field())
                    .map(|(b, _)| b.clone()),

            _ => None
        }
    }
}

impl<N> Typs<N> {
    pub fn len(&self) -> usize {
        self.0.len()
    }
    pub fn iter(&self) -> std::slice::Iter<Typ<N>> {
        self.0.iter()
    }
}

struct TypTraversal1<N>(std::marker::PhantomData<N>);
impl<A, B> Traversal<A, B> for TypTraversal1<A> {
    type Domain = Typ<A>;
    type Codomain = Typ<B>;
    fn traverse<E>(
        on: Self::Domain,
        f: &mut dyn FnMut(A) -> Result<B, E>,
    ) -> Result<Self::Codomain, E> {
        match on {
            Typ::Uni(b, n) => Ok(Typ::Uni(b, f(n)?)),
            Typ::Mle(b, n) => Ok(Typ::Mle(b, f(n)?)),
            Typ::Base(b) => Ok(Typ::Base(b)),
            Typ::Vec(box b, n) =>
                Ok(Typ::vec(Self::traverse(b, f)?, f(n)?)),
            Typ::Fin(r) => Ok(Typ::Fin(r.traverse1(f)?)),
            Typ::Bool => Ok(Typ::Bool)
        }
    }
}

struct TypTraversalRange<N>(std::marker::PhantomData<N>);
impl<A> Traversal<Range<A>> for TypTraversalRange<A> {
    type Domain = Typ<A>;
    type Codomain = Typ<A>;
    fn traverse<E>(
        on: Self::Domain,
        f: &mut dyn FnMut(Range<A>) -> Result<Range<A>, E>,
    ) -> Result<Self::Codomain, E> {
        match on {
            Typ::Fin(r) => Ok(Typ::Fin(f(r)?)),
            _ => Ok(on)
        }
    }
}

impl<N> ToTraversal1<N> for Typ<N> {
    type Output<Z> = Typ<Z>;
    fn traverse1<Z, E>(self, f: &mut dyn FnMut(N) -> Result<Z, E>) -> Result<Self::Output<Z>, E> {
        TypTraversal1::traverse(self, f)
    }
}

impl<N> RangeTraversal<N> for Typ<N> {
    fn range_traverse<E>(self, f: &mut dyn FnMut(Range<N>) -> Result<Range<N>, E>) -> Result<Self, E> {
        TypTraversalRange::traverse(self, f)
    }
}

impl<N> ToTraversal1<N> for Typs<N> {
    type Output<Z> = Typs<Z>;
    fn traverse1<Z, E>(self, f: &mut dyn FnMut(N) -> Result<Z, E>) -> Result<Self::Output<Z>, E> {
        Ok(Typs(self.0.into_iter().map(|t| t.traverse1(f)).collect::<Result<Vec<_>, _>>()?))
    }
}

impl<N> RangeTraversal<N> for Typs<N> {
    fn range_traverse<E>(self, f: &mut dyn FnMut(Range<N>) -> Result<Range<N>, E>) -> Result<Self, E> {
        Ok(Typs(self.0.into_iter().map(|t| t.range_traverse(f)).collect::<Result<Vec<_>, _>>()?))
    }
}

/// Pretty-printer for zippel types.
impl<'a, D, A, N> Pretty<'a, D, A> for Typ<N>
where
    D: DocAllocator<'a, A>,
    N: Pretty<'a, D, A>,
    D::Doc: Clone,
    A: 'a + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        match self {
            Typ::Uni(b, n) => allocator.concat([
                allocator.text("Uni<"),
                b.pretty(allocator),
                allocator.text(", "),
                n.pretty(allocator),
                allocator.text(">")
            ]),
            Typ::Mle(b, n) => allocator.concat([
                allocator.text("Mle<"),
                b.pretty(allocator),
                allocator.text(", "),
                n.pretty(allocator),
                allocator.text(">")
            ]),
            Typ::Base(base) => allocator.text(base.to_string()),
            Typ::Vec(box t, n) => allocator.concat([
                allocator.text("["),
                t.pretty(allocator),
                allocator.text("; "),
                n.pretty(allocator),
                allocator.text("]")
            ]),
            Typ::Fin(r) => allocator.concat([
                allocator.text("Fin<"),
                r.pretty(allocator),
                allocator.text(">")
            ]),
            Typ::Bool => allocator.text("Bool")
        }
    }

    fn is_nil(&self) -> bool {
        false
    }
}

impl<'a, D, A, N> Pretty<'a, D, A> for Typs<N>
where
    D: DocAllocator<'a, A>,
    N: Pretty<'a, D, A>,
    D::Doc: Clone,
    A: 'a + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        allocator.intersperse(self.0.into_iter().map(|t| t.pretty(allocator)), ", ")
    }

    fn is_nil(&self) -> bool {
        self.0.is_empty()
    }
}

impl<'a, N: Pretty<'a, BoxAllocator, ()> + Clone> fmt::Display for Typ<N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <Typ<N> as Pretty<'a, BoxAllocator, ()>>::pretty(self.clone(), &BoxAllocator)
            .1
            .render_fmt(100, f)
    }
}

impl<'a, N: Pretty<'a, BoxAllocator, ()> + Clone> fmt::Display for Typs<N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <Typs<N> as Pretty<'a, BoxAllocator, ()>>::pretty(self.clone(), &BoxAllocator)
            .1
            .render_fmt(100, f)
    }
}

/// Parser for zippel types.
impl<'pest> FromPest<'pest> for Typ<Size> {
    type Rule = Rule;
    type FatalError = InputError<'pest>;

    fn from_pest(
        pest: &mut Pairs<'pest, Self::Rule>,
    ) -> Result<Self, ConversionError<Self::FatalError>> {
        let pair = pest.next().ok_or(ConversionError::NoMatch)?;
        match pair.as_rule() {
            Rule::typ => Typ::from_pest(&mut pair.into_inner()), // Go into typ here
            Rule::base_ty => Ok(Typ::Base(Tid::from_pest(&mut pair.into_inner())?)),
            Rule::uni_ty => {
                let mut inner = pair.into_inner();
                let id = Tid::from_pest(&mut inner)?;
                let size = Size::from_pest(&mut inner)?;
                Ok(Typ::uni(id, size))
            }
            Rule::mle_ty => {
                let mut inner = pair.into_inner();
                let id = Tid::from_pest(&mut inner)?;
                let size = Size::from_pest(&mut inner)?;
                Ok(Typ::mle(id, size))
            }
            Rule::fin_ty =>
                Ok(Typ::fin(Range::from_pest(&mut pair.into_inner())?)),
            Rule::vec_ty => {
                let mut inner = pair.into_inner();
                let id = Typ::from_pest(&mut inner)?;
                let size = Size::from_pest(&mut inner)?;
                Ok(Typ::vec(id, size))
            }
            _ => unreachable!(),
        }
    }
}

#[cfg(test)] use pest::Parser;

#[test]
fn typ_parser() {
    let mut pairs = ZippelParser::parse(Rule::typ, "A").unwrap();
    assert_eq!(Typ::from_pest(&mut pairs).unwrap(), Typ::varstr("A"));

    pairs = ZippelParser::parse(Rule::typ, "Uni<X, 2^N>").unwrap();
    assert_eq!(Typ::from_pest(&mut pairs).unwrap(), Typ::uni(Tid::from("X"), Size::from(2) ^ Size::from("N")));

    pairs = ZippelParser::parse(Rule::typ, "Mle<X, 2>").unwrap();
    assert_eq!(Typ::from_pest(&mut pairs).unwrap(), Typ::mle(Tid::from("X"), Size::from(2)));

    pairs = ZippelParser::parse(Rule::typ, "[A; N]").unwrap();
    assert_eq!(Typ::from_pest(&mut pairs).unwrap(), Typ::vec(Typ::varstr("A"), Size::from("N")));

    pairs = ZippelParser::parse(Rule::typ, "Fin<0..N>").unwrap();
    assert_eq!(Typ::from_pest(&mut pairs).unwrap(), Typ::fin(Range { start: Size::zero(), step: Size::one(), end: Size::from("N") }));
}
