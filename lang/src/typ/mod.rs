mod kind;
mod typevar;
mod size;
mod qualifier;
mod nothing;
mod infer;
mod lub;

pub use crate::id::Tid;
pub use crate::range::{Range, RangeTraversal1};
pub use kind::Kind;
pub use size::{Size, EvalError};
pub use qualifier::Qualifier;
pub use typevar::{TypeVar, TypeVars};
pub use nothing::Nothing;
pub use lub::Lub;

use share::{Pretty, Traversal, BoxAllocator, DocAllocator, DocBuilder};
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

/// Sybolic size types
pub type STyp = Typ<Size>;

/// Concrete size types
pub type CTyp = Typ<usize>;

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
}

pub struct TypTraversal1<N>(std::marker::PhantomData<N>);
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
            Typ::Fin(r) => Ok(Typ::Fin(RangeTraversal1::traverse(r, f)?)),
            Typ::Bool => Ok(Typ::Bool)
        }
    }
}

pub struct TypTraversalRange<N>(std::marker::PhantomData<N>);
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

impl<'a, N: Pretty<'a, BoxAllocator, ()> + Clone> fmt::Display for Typ<N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <Typ<N> as Pretty<'_, BoxAllocator, ()>>::pretty(self.clone(), &BoxAllocator)
            .1
            .render_fmt(100, f)
    }
}

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
