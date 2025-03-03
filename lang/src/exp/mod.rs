mod aexp;
mod bexp;

pub use aexp::{AExp, UAExp, AExps, UAExps, CAExp, CAExps, AExpTraversal, BinOp};
pub use bexp::{BExp, UBExp, CBExp};

use share::{Pretty, DocAllocator, DocBuilder, BoxAllocator};
use share::traversal::ToTraversal1;

use crate::typ::{Size, Range, RangeTraversal};
use crate::id::{Tid, TidTraversal};
use std::fmt;

/// Combine BExp and AExp into one sum type for graph traversal
#[derive(Eq, PartialEq, Clone, PartialOrd, Ord, Debug)]
pub enum Exp<N> {
    A(AExp<N>),
    B(BExp<N>),
}

/// Untyped AST node with symbolic sizes
pub type UExp = Exp<Size>;

/// Concrete size AST node
pub type CExp = Exp<usize>;

/// Cast [AExp], [BExp] to [Exp]
impl<N> Into<Exp<N>> for AExp<N> {
    fn into(self) -> Exp<N> {
        Exp::A(self)
    }
}

impl<N> Into<Exp<N>> for BExp<N> {
    fn into(self) -> Exp<N> {
        Exp::B(self)
    }
}

impl<N: Clone> Into<Exp<N>> for &AExp<N> {
    fn into(self) -> Exp<N> {
        Exp::A(self.clone())
    }
}

impl<N: Clone> Into<Exp<N>> for &BExp<N> {
    fn into(self) -> Exp<N> {
        Exp::B(self.clone())
    }
}

/// How to traverse the first type parameter [N]
impl<N> ToTraversal1<N> for Exp<N> {
    type Output<Z> = Exp<Z>;
    fn traverse1<Z, E>(self, f: &mut dyn FnMut(N) -> Result<Z, E>) -> Result<Exp<Z>, E> {
        match self {
            Exp::A(aexp) => aexp.traverse1(f).map(Exp::A),
            Exp::B(bexp) => bexp.traverse1(f).map(Exp::B),
        }
    }
}

/// Traverse [Tid] inside [CExp]
impl TidTraversal for CExp {
    fn tid_traverse<E>(self, f: &mut dyn FnMut(Tid) -> Result<Tid, E>) -> Result<Self, E> {
        match self {
            Exp::A(aexp) => aexp.tid_traverse(f).map(Exp::A),
            Exp::B(bexp) => bexp.tid_traverse(f).map(Exp::B),
        }
    }
}

/// Traverse [Range<N>] inside [Exp<N>]
impl<N> RangeTraversal<N> for Exp<N> {
    fn range_traverse<E>(self, f: &mut dyn FnMut(Range<N>) -> Result<Range<N>, E>) -> Result<Self, E> {
        match self {
            Exp::A(aexp) => aexp.range_traverse(f).map(Exp::A),
            Exp::B(bexp) => bexp.range_traverse(f).map(Exp::B),
        }
    }
}

/// Pretty printer instance for Exp
impl<'a, D, A, N> Pretty<'a, D, A> for Exp<N>
where
    N: Pretty<'a, D, A> + Clone,
    D: DocAllocator<'a, A>,
    D::Doc: Clone,
    A: 'a + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        match self {
            Exp::A(aexp) => aexp.pretty(allocator),
            Exp::B(bexp) => bexp.pretty(allocator),
        }
    }

    fn is_nil(&self) -> bool {
        false
    }
}

/// Display instance calls the pretty printer
impl<'a, N> fmt::Display for Exp<N>
where
    N: Clone + Pretty<'a, BoxAllocator, ()>,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <Exp<N> as Pretty<'_, BoxAllocator, ()>>::pretty(self.clone(), &BoxAllocator)
            .1
            .render_fmt(30, f)
    }
}
