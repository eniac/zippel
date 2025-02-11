mod kind;
mod typevar;
mod size;
mod qualifier;
mod nothing;

pub use crate::id::Tid;
pub use crate::range::Range;
pub use kind::Kind;
pub use size::Size;
pub use qualifier::Qualifier;
pub use typevar::TypeVar;
pub use nothing::Nothing;

use share::{Pretty, BoxAllocator, DocAllocator, DocBuilder};
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
    /// Index within range
    Index(Range<N>),
}

impl<N> Typ<N> {
    pub fn varstr<'a>(b: &'a str) -> Self {
        Typ::Base(Tid::new(b.clone()))
    }
    pub fn var(b: Tid) -> Self {
        Typ::Base(b)
    }
    pub fn uni(b: Tid, n: Size) -> Self {
        Typ::Uni(b.clone(), n.clone())
    }
    pub fn mle(b: Tid, n: Size) -> Self {
        Typ::Mle(b.clone(), n.clone())
    }
    pub fn vec(b: Typ<N>, n: N) -> Self {
        Typ::Vec(Box::new(b.clone()), n.clone())
    }
    pub fn index(range: Range<N>) -> Self {
        Typ::Index(range)
    }
    pub fn get_base(&self) -> Option<&Tid> {
        match self {
            Typ::Base(b) => Some(b),
            _ => None
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
            Typ::Vec(t, n) => allocator.concat([
                allocator.text(format!("[{}; ", t)),
                n.pretty(allocator),
                allocator.text("]")
            ]),
            Typ::Index(r) => allocator.concat([
                allocator.text("["),
                r.pretty(allocator),
                allocator.text("]")
            ]),
        }
    }

    fn is_nil(&self) -> bool {
        false
    }
}

impl<'a, N: Pretty<'a, BoxAllocator, ()>> fmt::Display for Typ<N> {
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
            Rule::tid => Ok(Typ::Base(Tid::from_pest(&mut pair.into_inner())?)),
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
                Ok(Typ::index(Range::from_pest(&mut pair.into_inner())?)),
            Rule::vec_ty => {
                let mut inner = pair.into_inner();
                let id = Tid::from_pest(&mut inner)?;
                let size = Size::from_pest(&mut inner)?;
                Ok(Typ::vec(id, size))
            }
            _ => unreachable!(),
        }
    }
}
