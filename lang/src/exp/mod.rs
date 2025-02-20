mod aexp;
mod bexp;

pub use aexp::{AExp, TAExp, UAExp, AExps, TAExps, UAExps, CAExp, CAExps, AExpTraversal, BinOp};
pub use bexp::{BExp, TBExp, UBExp, CBExp, BExpTraversal};

use share::{Pretty, DocAllocator, DocBuilder, BoxAllocator, Traversal};
use share::traversal::{ToTraversal1, ToTraversal2};

use crate::typ::{Nothing, Typ, Size};
use std::fmt;

/// Combine BExp and AExp into one sum type for graph traversal
#[derive(Eq, PartialEq, Clone, PartialOrd, Ord, Debug)]
pub enum Exp<N, T> {
    A(AExp<N, T>),
    B(BExp<N, T>),
}

/// Typed AST node
pub type TExp = Exp<usize, Typ<usize>>;

/// Untyped AST node with symbolic sizes
pub type UExp = Exp<Size, Nothing>;

/// Concrete size AST node
pub type CExp = Exp<usize, Nothing>;

/// Modular get/set acccess to type parameters using [Traversal]
struct ExpTraversal1<N, T>(std::marker::PhantomData<(N, T)>);
impl<N, T, Z> Traversal<N, Z> for ExpTraversal1<N, T> {
    type Domain = Exp<N, T>;
    type Codomain = Exp<Z, T>;

    fn traverse<E>(on: Self::Domain, f: &mut dyn FnMut(N) -> Result<Z, E>) -> Result<Self::Codomain, E> {
        match on {
            Exp::A(aexp) => aexp.traverse1(f).map(Exp::A),
            Exp::B(bexp) => bexp.traverse1(f).map(Exp::B),
        }
    }
}

struct ExpTraversal2<N, T>(std::marker::PhantomData<(N, T)>);
impl<N, T, Z> Traversal<T, Z> for ExpTraversal2<N, T> {
    type Domain = Exp<N, T>;
    type Codomain = Exp<N, Z>;

    fn traverse<E>(on: Self::Domain, f: &mut dyn FnMut(T) -> Result<Z, E>) -> Result<Self::Codomain, E> {
        match on {
            Exp::A(aexp) => aexp.traverse2(f).map(Exp::A),
            Exp::B(bexp) => bexp.traverse2(f).map(Exp::B),
        }
    }
}

/// How to traverse the first type parameter [N]
impl<N, T> ToTraversal1<N> for Exp<N, T> {
    type Output<Z> = Exp<Z, T>;
    fn traverse1<Z, E>(self, f: &mut dyn FnMut(N) -> Result<Z, E>) -> Result<Exp<Z, T>, E> {
        ExpTraversal1::traverse(self, f)
    }
}

/// How to traverse the second type parameter [T]
impl<N, T> ToTraversal2<T> for Exp<N, T> {
    type Output<Z> = Exp<N, Z>;
    fn traverse2<Z, E>(self, f: &mut dyn FnMut(T) -> Result<Z, E>) -> Result<Exp<N, Z>, E> {
        ExpTraversal2::traverse(self, f)
    }
}

/// Pretty printer instance for Exp
impl<'a, D, A, N, T> Pretty<'a, D, A> for Exp<N, T>
where
    N: Pretty<'a, D, A> + Clone,
    T: Pretty<'a, D, A> + Clone,
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
impl<'a, N, T> fmt::Display for Exp<N, T>
where
    N: Clone + Pretty<'a, BoxAllocator, ()>,
    T: Clone + Pretty<'a, BoxAllocator, ()>,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <Exp<N, T> as Pretty<'_, BoxAllocator, ()>>::pretty(self.clone(), &BoxAllocator)
            .1
            .render_fmt(30, f)
    }
}

