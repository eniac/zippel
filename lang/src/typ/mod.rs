mod kind;
mod typevar;
mod size;
mod qualifier;

pub use crate::id::Tid;
pub use crate::range::Range;
pub use kind::Kind;
pub use size::Size;
pub use qualifier::Qualifier;

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
    pub fn base<'a>(b: &'a str) -> Self {
        Typ::Base(Tid::new(b.clone()))
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
    pub fn index(from: N, to: N, step: N) -> Self {
        Typ::Index(Range::new(from, to, step))
    }
    pub fn get_base(&self) -> Option<&Tid> {
        match self {
            Typ::Base(b) => Some(b),
            _ => None
        }
    }
}
