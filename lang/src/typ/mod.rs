mod kind;
mod typevar;
mod size;

pub use crate::id::Tid;
pub use crate::range::Range;
pub use kind::Kind;
pub use typevar::TypeVar;
pub use size::Size;

/// The types of expressions, [N] is the size parameter
#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone)]
pub enum Typ<N> {
    /// Univariate polynomial of degree [Size] and base type [Tid]
    Uni(Tid, N),
    /// Multilinear polynomial of arity [Size] and base type [Tid]
    Mle(Tid, N),
    /// Vector of size [Size] and base type [Typ]
    Vec(Box<Typ<N>>, N),
    /// Tid type [Tid]
    Base(Tid),
    /// Size within integer range
    Index(Range<N>),
}
