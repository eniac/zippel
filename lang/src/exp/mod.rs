mod aexp;
mod bexp;

pub use aexp::{AExp, TAExp, UAExp, AExps, TAExps, UAExps};
pub use bexp::{BExp, TBExp, UBExp};

use share::{Pretty, DocAllocator, DocBuilder, BoxAllocator, Traversable1, Traversable2, Proj1, Proj2};

use crate::typ::{Nothing, Typ, Size};
use std::fmt;

/// Combine BExp and AExp into one sum type for graph traversal
#[derive(Eq, PartialEq, Clone, PartialOrd, Ord, Debug)]
pub enum Exp<N, T> {
    A(AExp<N, T>),
    B(BExp<N, T>),
}

/// Typed AST node
pub type TExp<N, A> = Exp<N, (A, Typ<N>)>;

/// Untyped AST node with symbolic sizes
pub type UExp = Exp<Size, Nothing>;

/// Modular get/set acccess to type parameters using [Traversable1] and [Traversable2]
impl<N, T> Traversable1<N> for Exp<N, T> {
    type Output<Z> = Exp<Z, T>;

    fn traverse1<Z, E>(self, f: &mut dyn FnMut(N) -> Result<Z, E>) -> Result<Exp<Z, T>, E> {
        match self {
            Exp::A(aexp) => aexp.traverse1(f).map(Exp::A),
            Exp::B(bexp) => bexp.traverse1(f).map(Exp::B),
        }
    }
}

impl<N, T> Traversable2<T> for Exp<N, T> {
    type Output<Z> = Exp<N, Z>;

    fn traverse2<Z, E>(self, f: &mut dyn FnMut(T) -> Result<Z, E>) -> Result<Exp<N, Z>, E> {
        match self {
            Exp::A(aexp) => aexp.traverse2(f).map(Exp::A),
            Exp::B(bexp) => bexp.traverse2(f).map(Exp::B),
        }
    }
}

impl<N, A, B> Proj1<A> for Exp<N, (A, B)> {
    type Output<Z> = Exp<N, (Z, B)>;

    fn get_proj1(&self) -> &A {
        match self {
            Exp::A(aexp) => aexp.get_proj1(),
            Exp::B(bexp) => bexp.get_proj1(),
        }
    }

    fn map_proj1<Z>(self, f: &mut dyn FnMut(A)->Z) -> Self::Output<Z> {
        match self {
            Exp::A(aexp) => Exp::A(aexp.map_proj1(f)),
            Exp::B(bexp) => Exp::B(bexp.map_proj1(f)),
        }
    }

    fn modify_proj1(&mut self, f: &mut dyn FnMut(&mut A)) {
        match self {
            Exp::A(aexp) => aexp.modify_proj1(f),
            Exp::B(bexp) => bexp.modify_proj1(f),
        }
    }
}

impl<N, A, B> Proj2<B> for Exp<N, (A, B)> {
    type Output<Z> = Exp<N, (A, Z)>;

    fn get_proj2(&self) -> &B {
        match self {
            Exp::A(aexp) => aexp.get_proj2(),
            Exp::B(bexp) => bexp.get_proj2(),
        }
    }

    fn map_proj2<Z>(self, f: &mut dyn FnMut(B)->Z) -> Self::Output<Z> {
        match self {
            Exp::A(aexp) => Exp::A(aexp.map_proj2(f)),
            Exp::B(bexp) => Exp::B(bexp.map_proj2(f)),
        }
    }

    fn modify_proj2(&mut self, f: &mut dyn FnMut(&mut B)) {
        match self {
            Exp::A(aexp) => aexp.modify_proj2(f),
            Exp::B(bexp) => bexp.modify_proj2(f),
        }
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

