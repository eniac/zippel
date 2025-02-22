use std::ops::{Add, Div, Mul, Sub, BitXor};
use crate::parser::*;
use from_pest::{ConversionError, FromPest};
use lazy_static::lazy_static;
use std::fmt;
use pest::iterators::Pairs;
use pest::pratt_parser::{Assoc, Op, PrattParser};

use share::traversal::{BoxTraversal, ToTraversal1, ToTraversal2, VecTraversal};

use share::{Traversal, BoxAllocator, Pretty, DocAllocator, DocBuilder};
use crate::typ::{Typ, CTyp, TypTraversal, Size, Nothing};
use crate::exp::{BExp, UBExp, BExpTraversal};
use crate::id::{Tid, Fid, Vid};
use crate::range::{Range, RangeTraversal};

/// Represents binary operations in the Zippel language.
/// Each variant corresponds to a different kind of binary operation that can be performed on arithmetic expressions.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash)]
pub enum BinOp {
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let sum = 2 + 3;
    ///     ```
    Add,

    ///     **Zippel Code:**
    ///     ```zippel
    ///     let difference = 5 - 3;
    ///     ```
    Sub,

    ///     **Zippel Code:**
    ///     ```zippel
    ///     let product = 2 * 3;
    ///     ```
    Mul,

    ///     **Zippel Code:**
    ///     ```zippel
    ///     let quotient = 6 / 2;
    ///     ```
    Div,

    ///     **Zippel Code:**
    ///     ```zippel
    ///     let result = 2 ^ 3;
    ///     ```
    Pow,

    ///     **Zippel Code:**
    ///     ```zippel
    ///     let inner: F = [1,2,3] . [2,4,6];
    ///     ```
    Dot,

    ///     **Zippel Code:**
    ///     ```zippel
    ///     let inner: F = [1,2] ++ [2,4];
    ///     ```
    Concat
}

/// Represents arithmetic expressions in the Zippel language.
/// It is parameterized by types `N` representing the sizes of ranges, indices etc, and
/// `A` that represents the generic annotations that can be attached to expressions.
#[derive(Debug, PartialEq, Eq, Clone, PartialOrd, Ord)]
pub enum AExp<N, A> {
    ///     Numeric literal
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let a = 5;
    ///     ```
    Lit(N, A),

    ///     Generator of a group [Tid]
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let g = gen<G>;
    ///     ```
    Gen(Tid, A),

    ///     Variable reference
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let b = a;
    ///     ```
    Var(Vid, A),

    ///     Function application
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let result1 = f(x + 2, x)
    ///     ```
    App(Fid, AExps<N,A>, A),

    ///     Coefficients of a univariate vector
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let v = coef [1,2,1]; // 1 + 2x + x^2
    ///     ```
    Coef(Box<AExp<N, A>>, A),

    ///     Multilinear extension of a matrix, polynomial, etc.
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let g = mle x;
    ///     ```
    Mle(Box<AExp<N, A>>, A),

    ///     A vector of elements
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let v = [1, 2*x, x+y];
    ///     ```
    Vec(AExps<N, A>, A),

    ///     Binary operation
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let sum = 2 + 3;
    ///     ```
    Bin(BinOp, Box<AExp<N, A>>, Box<AExp<N, A>>, A),

    ///     **Zippel Code:**
    ///     ```zippel
    ///     let r = 0..5;
    ///     ```
    Range(Range<N>, A),

    ///     Map comprehension
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let squares = [x^2 for x in 0,2..10];
    ///     ```
    Map(Box<AExp<N, A>>, Vid, Box<AExp<N, A>>, A),

    ///     Random access or slice a vector
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let first = v[0]
    ///     ```
    Ram(Box<AExp<N, A>>, Box<AExp<N, A>>, A),

    ///     Sample pseudo-random number generator
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let r := random<F>();
    ///     ```
    Random(Typ<N>, A),

    ///     Random oracle challenge.
    ///     **Zippel Code:**
    ///     ```zippel
    ///     r <- challenge<F>();
    ///     ```
    Challenge(Typ<N>, A),

    ///     Convert from evaluation domain to lagrange domain.
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let p = interpolate([1, 2], [0, 3]);
    ///     ```
    Interpolate(Box<AExp<N, A>>, Box<AExp<N, A>>, A),

    ///     Represents a let-expression, which binds a value to an identifier.
    ///
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let x = 5 + 3;
    ///     ```
    Let(Vid, Box<AExp<N, A>>, A),

    ///     Represents a log-let expression with transcript dependency.
    ///     This variant is used to bind a value to an identifier while logging the operation.
    ///     **Zippel Code:**
    ///     ```zippel
    ///     p <- interpolate(v, [0,1,2])
    ///     ```
    Log(Vid, Box<AExp<N, A>>, A),

    ///     Prover assertion followed by expression.
    ///     **Zippel Code:**
    ///     ```zippel
    ///     assert(1 == 1);
    ///     ...
    ///     ```
    Assert(Box<BExp<N, A>>, A),

    ///     Verifier check followed by expression.
    ///     **Zippel Code:**
    ///     ```zippel
    ///     verify(a == a);
    ///     ...
    ///     ```
    Verify(Box<BExp<N, A>>, A)
}

/// Represents a sequence of arithmetic expressions in the Zippel language
#[derive(Debug, PartialEq, Eq, Clone, PartialOrd, Ord)]
pub struct AExps<N, A>(pub Vec<AExp<N, A>>);

/// How to traverse structures of arithmetic expressions (AExp)
pub trait AExpTraversal<N, A>: Sized {
    fn aexp_traverse<E>(self, f: &mut dyn FnMut(AExp<N, A>) -> Result<AExp<N, A>, E>) -> Result<Self, E>;
}

/// Untyped AST node, as parsed from input
pub type UAExp = AExp<Size, Nothing>;

/// Concrete size untyped AST node
pub type CAExp = AExp<usize, Nothing>;

/// Typed AST node
pub type TAExp = AExp<usize, Typ<usize>>;

/// Untyped AST sequence, as parsed from input
pub type UAExps = AExps<Size, Nothing>;

/// Concrete size untyped AST node
pub type CAExps = AExps<usize, Nothing>;

/// Typed AST sequence
pub type TAExps = AExps<usize, Typ<usize>>;

/// Modular get/set acccess to type parameters using [Traversal]
struct AExpTraversal1<N, T>(std::marker::PhantomData<(N, T)>);
impl<N, T, Z> Traversal<N, Z> for AExpTraversal1<N, T> {
    type Domain = AExp<N, T>;
    type Codomain = AExp<Z, T>;

    fn traverse<E>(on: Self::Domain, f: &mut dyn FnMut(N) -> Result<Z, E>) -> Result<Self::Codomain, E> {
        match on {
            AExp::Lit(x, a) => Ok(AExp::Lit(f(x)?, a)),
            AExp::Var(v, a) => Ok(AExp::Var(v, a)),
            AExp::Coef(box p, a) => Ok(AExp::Coef(Box::new(p.traverse1(f)?), a)),
            AExp::Mle(box p, a) => Ok(AExp::Mle(Box::new(p.traverse1(f)?), a)),
            AExp::Vec(v, a) =>
                Ok(AExp::Vec(v.aexps_traverse(&mut |x| x.traverse1(f))?, a)),
            AExp::App(x, ts, a) =>
                Ok(AExp::App(x, ts.aexps_traverse(&mut |x| x.traverse1(f))?, a)),
            AExp::Bin(op, box x, box y, a) =>
                Ok(AExp::Bin(
                    op,
                    Box::new(x.traverse1(f)?),
                    Box::new(y.traverse1(f)?),
                    a
                )),
            AExp::Map(box x, id, box r, a) =>
                Ok(AExp::Map(Box::new(x.traverse1(f)?), id, Box::new(r.traverse1(f)?), a)),
            AExp::Challenge(t, a) => Ok(AExp::Challenge(t.traverse1(f)?, a)),
            AExp::Random(t, a) => Ok(AExp::Random(t.traverse1(f)?, a)),
            AExp::Gen(t, a) => Ok(AExp::Gen(t, a)),
            AExp::Range(r, a) => Ok(AExp::Range(r.traverse1(f)?, a)),
            AExp::Interpolate(box x, box y, a) =>
                Ok(AExp::Interpolate(
                    Box::new(x.traverse1(f)?),
                    Box::new(y.traverse1(f)?),
                    a
                )),
            AExp::Ram(box x, box i, a) =>
                Ok(AExp::Ram(
                        Box::new(x.traverse1(f)?),
                        Box::new(i.traverse1(f)?),
                        a
                )),
            AExp::Let(x, box a, t) =>
                Ok(AExp::Let(x, Box::new(a.traverse1(f)?), t)),
            AExp::Log(x, box a, t) =>
                Ok(AExp::Log(x, Box::new(a.traverse1(f)?), t)),
            AExp::Assert(box x,  t) =>
                Ok(AExp::Assert(Box::new(x.traverse1(f)?), t)),
            AExp::Verify(box x, t) =>
                Ok(AExp::Verify(Box::new(x.traverse1(f)?), t))
        }
    }
}

/// Traverse the first free type parameter [N]
struct AExpsTraversal1<N, T>(std::marker::PhantomData<(N, T)>);
impl<N, T, Z> Traversal<N, Z> for AExpsTraversal1<N, T> {
    type Domain = AExps<N, T>;
    type Codomain = AExps<Z, T>;

    fn traverse<E>(on: Self::Domain, f: &mut dyn FnMut(N) -> Result<Z, E>) -> Result<AExps<Z, T>, E> {
        Ok(AExps(VecTraversal::traverse(on.0, &mut |x| AExpTraversal1::traverse(x, f))?))
    }
}

/// Traverse the second free type parameter [T]
struct AExpTraversal2<N, T>(std::marker::PhantomData<(N, T)>);
impl<N, T, Z> Traversal<T, Z> for AExpTraversal2<N, T> {
    type Domain = AExp<N, T>;
    type Codomain = AExp<N, Z>;

    fn traverse<E>(on: Self::Domain, f: &mut dyn FnMut(T) -> Result<Z, E>) -> Result<Self::Codomain, E> {
        match on {
            AExp::Lit(x, a) => Ok(AExp::Lit(x, f(a)?)),
            AExp::Var(v, a) => Ok(AExp::Var(v, f(a)?)),
            AExp::Coef(box p, a) => Ok(AExp::Coef(Box::new(p.traverse2(f)?), f(a)?)),
            AExp::Mle(box p, a) => Ok(AExp::Mle(Box::new(p.traverse2(f)?), f(a)?)),
            AExp::Vec(v, a) =>
                Ok(AExp::Vec(v.aexps_traverse(&mut |x| x.traverse2(f))?, f(a)?)),
            AExp::App(x, ts, a) =>
                Ok(AExp::App(x, ts.aexps_traverse(&mut |x| x.traverse2(f))?, f(a)?)),
            AExp::Bin(op, box x, box y, a) =>
                Ok(AExp::Bin(
                    op,
                    Box::new(x.traverse2(f)?),
                    Box::new(y.traverse2(f)?),
                    f(a)?
                )),
            AExp::Map(box x, id, box r, a) =>
                Ok(AExp::Map(Box::new(x.traverse2(f)?), id, Box::new(r.traverse2(f)?), f(a)?)),
            AExp::Challenge(t, a) => Ok(AExp::Challenge(t, f(a)?)),
            AExp::Random(t, a) => Ok(AExp::Random(t, f(a)?)),
            AExp::Gen(t, a) => Ok(AExp::Gen(t, f(a)?)),
            AExp::Range(r, a) => Ok(AExp::Range(r, f(a)?)),
            AExp::Interpolate(box x, box y, a) =>
                Ok(AExp::Interpolate(
                    Box::new(x.traverse2(f)?),
                    Box::new(y.traverse2(f)?),
                    f(a)?
                )),
            AExp::Ram(box x, box i, a) =>
                Ok(AExp::Ram(
                        Box::new(x.traverse2(f)?),
                        Box::new(i.traverse2(f)?),
                        f(a)?
                )),
            AExp::Let(x, box a,t) =>
                Ok(AExp::Let(x, Box::new(a.traverse2(f)?), f(t)?)),
            AExp::Log(x, box a, t) =>
                Ok(AExp::Log(x, Box::new(a.traverse2(f)?), f(t)?)),
            AExp::Assert(box x, a) =>
                Ok(AExp::Assert(Box::new(x.traverse2(f)?), f(a)?)),
            AExp::Verify(box x, a) =>
                Ok(AExp::Verify(Box::new(x.traverse2(f)?), f(a)?))
        }
    }
}

struct AExpsTraversal2<N, T>(std::marker::PhantomData<(N, T)>);
impl<N, T, Z> Traversal<T, Z> for AExpsTraversal2<N, T> {
    type Domain = AExps<N, T>;
    type Codomain = AExps<N, Z>;

    fn traverse<E>(on: Self::Domain, f: &mut dyn FnMut(T) -> Result<Z, E>) -> Result<Self::Codomain, E> {
        Ok(AExps(on.0.traverse1(&mut |x| AExpTraversal2::traverse(x, f))?))
    }
}

/// Traverse [Range] inside a [UAExp]
struct UAExpTraversalRange();
impl Traversal<Range<Size>> for UAExpTraversalRange {
    type Domain = UAExp;
    type Codomain = UAExp;

    fn traverse<E>(on: Self::Domain, f: &mut dyn FnMut(Range<Size>) -> Result<Range<Size>, E>) -> Result<Self::Codomain, E> {
        match on {
            AExp::Range(r, a) => Ok(AExp::Range(f(r)?, a)),
            AExp::Lit(x, a) => Ok(AExp::Lit(x, a)),
            AExp::Var(v, a) => Ok(AExp::Var(v, a)),
            AExp::Gen(t, a) => Ok(AExp::Gen(t, a)),
            AExp::Challenge(t, a) => Ok(AExp::Challenge(t.range_traverse(f)?, a)),
            AExp::Random(t, a) => Ok(AExp::Random(t.range_traverse(f)?, a)),
            AExp::Coef(p, a) => Ok(AExp::Coef(p.traverse1(
                        &mut |x| x.range_traverse(f))?, a)),
            AExp::Mle(p, a) => Ok(AExp::Mle(BoxTraversal::traverse(p,
                        &mut |x| x.range_traverse(f))?, a)),
            AExp::Vec(v, a) =>
                Ok(AExp::Vec(v.aexps_traverse(&mut |x| x.range_traverse(f))?, a)),
            AExp::Bin(op, x, y, a) => Ok(AExp::Bin(op,
                    BoxTraversal::traverse(x, &mut |x| x.range_traverse(f))?,
                    BoxTraversal::traverse(y, &mut |x| x.range_traverse(f))?, a)),
            AExp::Map(x, id, r, a) => Ok(AExp::Map(
                    BoxTraversal::traverse(x, &mut |x| x.range_traverse(f))?, id,
                    BoxTraversal::traverse(r, &mut |x| x.range_traverse(f))?, a)),
            AExp::Ram(x, i, a) => Ok(AExp::Ram(
                    BoxTraversal::traverse(x, &mut |x| x.range_traverse(f))?,
                    BoxTraversal::traverse(i, &mut |x| x.range_traverse(f))?, a)),
            AExp::Interpolate(x, y, a) => Ok(AExp::Interpolate(
                    BoxTraversal::traverse(x, &mut |x| x.range_traverse(f))?,
                    BoxTraversal::traverse(y, &mut |x| x.range_traverse(f))?, a)),
            AExp::Let(x, a, t) => Ok(AExp::Let(x,
                    BoxTraversal::traverse(a, &mut |x| x.range_traverse(f))?, t)),
            AExp::Log(x, a, t) => Ok(AExp::Log(x,
                    BoxTraversal::traverse(a, &mut |x| x.range_traverse(f))?, t)),
            AExp::Assert(x, t) => Ok(AExp::Assert(
                    BoxTraversal::traverse(x,&mut |x| x.range_traverse(f))?, t)),
            AExp::Verify(x, t) => Ok(AExp::Verify(
                    BoxTraversal::traverse(x,&mut |x| x.range_traverse(f))?, t)),
            AExp::App(x, ts, t) => Ok(AExp::App(x,
                    ts.aexps_traverse(&mut |x| x.range_traverse(f))?, t))
        }
    }
}

/// Traverse [AExp] inside [AExps]
struct AExpsTraversalAExp<N, T>(std::marker::PhantomData<(N, T)>);
impl <N1, T1, N2, T2> Traversal<AExp<N1, T1>, AExp<N2, T2>> for AExpsTraversalAExp<N1, T1> {
    type Domain = AExps<N1, T1>;
    type Codomain = AExps<N2, T2>;

    fn traverse<E>(on: Self::Domain, f: &mut dyn FnMut(AExp<N1, T1>) -> Result<AExp<N2, T2>, E>) -> Result<Self::Codomain, E> {
        Ok(AExps(VecTraversal::traverse(on.0, f)?))
    }
}

/// Traverse [AExp] inside [AExp]
struct AExpTraversalAExp<N, T>(std::marker::PhantomData<(N, T)>);
impl<N, T> Traversal<AExp<N, T>> for AExpTraversalAExp<N, T> {
    type Domain = AExp<N, T>;
    type Codomain = AExp<N, T>;

    fn traverse<E>(on: Self::Domain, f: &mut dyn FnMut(AExp<N, T>) -> Result<AExp<N, T>, E>) -> Result<Self::Codomain, E> {
        match on {
            AExp::Lit(x, a) => Ok(AExp::Lit(x, a)),
            AExp::Var(v, a) => Ok(AExp::Var(v, a)),
            AExp::Coef(p, a) => Ok(AExp::Coef(p.traverse1(&mut |x| f(x)?.aexp_traverse(f))?, a)),
            AExp::Mle(p, a) => Ok(AExp::Mle(p.traverse1(&mut |x| f(x)?.aexp_traverse(f))?, a)),
            AExp::Vec(v, a) => Ok(AExp::Vec(v.aexps_traverse(&mut |x| f(x)?.aexp_traverse(f))?, a)),
            AExp::Bin(op, x, y, a) => Ok(AExp::Bin(op,
                    x.traverse1(&mut |x| f(x)?.aexp_traverse(f))?,
                    y.traverse1(&mut |x| f(x)?.aexp_traverse(f))?, a
            )),
            AExp::Map(x, id, r, a) => Ok(AExp::Map(
                    x.traverse1(&mut |x| f(x)?.aexp_traverse(f))?, id,
                    r.traverse1(&mut |x| f(x)?.aexp_traverse(f))?, a
            )),
            AExp::Challenge(t, a) => Ok(AExp::Challenge(t, a)),
            AExp::Random(t, a) => Ok(AExp::Random(t, a)),
            AExp::Gen(t, a) => Ok(AExp::Gen(t, a)),
            AExp::Range(r, a) => Ok(AExp::Range(r, a)),
            AExp::Interpolate(x, y, a) => Ok(AExp::Interpolate(
                    x.traverse1(&mut |x| f(x)?.aexp_traverse(f))?,
                    y.traverse1(&mut |x| f(x)?.aexp_traverse(f))?, a
            )),
            AExp::Ram(x, i, a) => Ok(AExp::Ram(
                    x.traverse1(&mut |x| f(x)?.aexp_traverse(f))?,
                    i.traverse1(&mut |x| f(x)?.aexp_traverse(f))?, a
            )),
            AExp::Let(x, a, t) => Ok(AExp::Let(x,
                    a.traverse1(&mut |x| f(x)?.aexp_traverse(f))?, t)),
            AExp::Log(x, a, t) => Ok(AExp::Log(x,
                    a.traverse1(&mut |x| f(x)?.aexp_traverse(f))?, t)),
            AExp::Assert(x, t) => Ok(AExp::Assert(
                    x.traverse1(&mut |x| x.aexp_traverse(f))?, t)),
            AExp::Verify(x, t) => Ok(AExp::Verify(
                    x.traverse1(&mut |x| x.aexp_traverse(f))?, t)),
            AExp::App(x, ts, t) => Ok(AExp::App(x,
                    ts.aexps_traverse(&mut |x| f(x)?.aexp_traverse(f))?, t))
        }
    }
}

/// Traverse [BExp] inside [AExp]
struct AExpTraversalBExp<N, T>(std::marker::PhantomData<(N, T)>);
impl<N, T> Traversal<BExp<N, T>> for AExpTraversalBExp<N, T> {
    type Domain = AExp<N, T>;
    type Codomain = AExp<N, T>;

    fn traverse<E>(on: Self::Domain, f: &mut dyn FnMut(BExp<N, T>) -> Result<BExp<N, T>, E>) -> Result<Self::Codomain, E> {
        match on {
            AExp::Lit(x, a) => Ok(AExp::Lit(x, a)),
            AExp::Var(v, a) => Ok(AExp::Var(v, a)),
            AExp::Coef(p, a) =>
                Ok(AExp::Coef(p.traverse1(&mut |x| x.bexp_traverse(f))?, a)),
            AExp::Mle(p, a) =>
                Ok(AExp::Mle(p.traverse1(&mut |x| x.bexp_traverse(f))?, a)),
            AExp::Vec(v, a) =>
                Ok(AExp::Vec(v.aexps_traverse(&mut |x| x.bexp_traverse(f))?, a)),
            AExp::Bin(op, x, y, a) => Ok(AExp::Bin(op,
                    x.traverse1(&mut |x| x.bexp_traverse(f))?,
                    y.traverse1(&mut |x| x.bexp_traverse(f))?, a
            )),
            AExp::Map(x, id, r, a) => Ok(AExp::Map(
                    x.traverse1(&mut |x| x.bexp_traverse(f))?, id,
                    r.traverse1(&mut |x| x.bexp_traverse(f))?, a
            )),
            AExp::Challenge(t, a) => Ok(AExp::Challenge(t, a)),
            AExp::Random(t, a) => Ok(AExp::Random(t, a)),
            AExp::Gen(t, a) => Ok(AExp::Gen(t, a)),
            AExp::Range(r, a) => Ok(AExp::Range(r, a)),
            AExp::Interpolate(x, y, a) => Ok(AExp::Interpolate(
                    x.traverse1(&mut |x| x.bexp_traverse(f))?,
                    y.traverse1(&mut |x| x.bexp_traverse(f))?, a
            )),
            AExp::Ram(x, i, a) => Ok(AExp::Ram(
                    x.traverse1(&mut |x| x.bexp_traverse(f))?,
                    i.traverse1(&mut |x| x.bexp_traverse(f))?, a
            )),
            AExp::Let(x, a, t) => Ok(AExp::Let(x,
                    a.traverse1(&mut |x| x.bexp_traverse(f))?, t)),
            AExp::Log(x, a, t) => Ok(AExp::Log(x,
                    a.traverse1(&mut |x| x.bexp_traverse(f))?, t)),
            AExp::Assert(x, t) => Ok(AExp::Assert(
                    x.traverse1(&mut |x| f(x)?.bexp_traverse(f))?, t)),
            AExp::Verify(x, t) => Ok(AExp::Verify(
                    x.traverse1(&mut |x| f(x)?.bexp_traverse(f))?, t)),
            AExp::App(x, ts, t) => Ok(AExp::App(x,
                    ts.aexps_traverse(&mut |x| x.bexp_traverse(f))?, t))
        }
    }
}

/// How to traverse the first type parameter [N] for AExp<N, T>
impl<N, T> ToTraversal1<N> for AExp<N, T> {
    type Output<Z> = AExp<Z, T>;
    fn traverse1<Z, E>(self, f: &mut dyn FnMut(N) -> Result<Z, E>) -> Result<AExp<Z, T>, E> {
        AExpTraversal1::traverse(self, f)
    }
}

/// How to traverse the second type parameter [T] for AExp<N, T>
impl<N, T> ToTraversal2<T> for AExp<N, T> {
    type Output<Z> = AExp<N, Z>;
    fn traverse2<Z, E>(self, f: &mut dyn FnMut(T) -> Result<Z, E>) -> Result<AExp<N, Z>, E> {
        AExpTraversal2::traverse(self, f)
    }
}
/// How to traverse the first type parameter [N] for AExps<N, T>
impl<N, T> ToTraversal1<N> for AExps<N, T> {
    type Output<Z> = AExps<Z, T>;
    fn traverse1<Z, E>(self, f: &mut dyn FnMut(N) -> Result<Z, E>) -> Result<AExps<Z, T>, E> {
        AExpsTraversal1::traverse(self, f)
    }
}

/// How to traverse the second type parameter [T] for AExps<N, T>
impl<N, T> ToTraversal2<T> for AExps<N, T> {
    type Output<Z> = AExps<N, Z>;
    fn traverse2<Z, E>(self, f: &mut dyn FnMut(T) -> Result<Z, E>) -> Result<AExps<N, Z>, E> {
        AExpsTraversal2::traverse(self, f)
    }
}

impl<N, T> AExpTraversal<N, T> for AExp<N, T> {
    fn aexp_traverse<E>(self, f: &mut dyn FnMut(AExp<N, T>) -> Result<AExp<N, T>, E>) -> Result<AExp<N, T>, E> {
        AExpTraversalAExp::traverse(self, f)
    }
}

/// How to traverse [BExp] inside an [AExp]
impl<N, T> BExpTraversal<N, T> for AExp<N, T> {
    fn bexp_traverse<E>(self, f: &mut dyn FnMut(BExp<N, T>) -> Result<BExp<N, T>, E>) -> Result<AExp<N, T>, E> {
        AExpTraversalBExp::traverse(self, f)
    }
}

/// How to traverse [Range] inside an [AExp]
impl RangeTraversal<Size> for UAExp {
    fn range_traverse<E>(self, f: &mut dyn FnMut(Range<Size>) -> Result<Range<Size>, E>) -> Result<Self, E> {
        UAExpTraversalRange::traverse(self, f)
    }
}

impl<N, A> AExps<N, A> {
    pub fn aexps_traverse<E, Z, T>(self, f: &mut dyn FnMut(AExp<N, A>) -> Result<AExp<Z, T>, E>) -> Result<AExps<Z, T>, E> {
        Ok(AExps(VecTraversal::traverse(self.0, f)?))
    }
}

impl<N, T> IntoIterator for AExps<N, T> {
    type Item = AExp<N, T>;
    type IntoIter = std::vec::IntoIter<AExp<N, T>>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<N, T> FromIterator<AExp<N, T>> for AExps<N, T> {
    fn from_iter<I: IntoIterator<Item = AExp<N, T>>>(iter: I) -> Self {
        AExps(iter.into_iter().collect())
    }
}

impl TAExp {
    pub fn typ(self) -> Typ<usize> {
        match self {
            AExp::Lit(_, a) => a,
            AExp::Var(_, a) => a,
            AExp::Coef(_, a) => a,
            AExp::Mle(_, a) => a,
            AExp::Vec(_, a) => a,
            AExp::Bin(_, _, _, a) => a,
            AExp::Map(_, _, _, a) => a,
            AExp::Challenge(_, a) => a,
            AExp::Random(_, a) => a,
            AExp::Gen(_, a) => a,
            AExp::Range(_, a) => a,
            AExp::Interpolate(_, _, a) => a,
            AExp::Ram(_, _, a) => a,
            AExp::Let(_, _, a) => a,
            AExp::Log(_, _, a) => a,
            AExp::Assert(_, a) => a,
            AExp::Verify(_, a) => a,
            AExp::App(_, _, a) => a,
        }
    }
}

/// Construct untyped expressions and type infer later [types/infer.rs]
impl UAExp {
    /// Annotated constructors
    pub fn lit(v: Size) -> Self {
        AExp::Lit(v, Nothing)
    }
    pub fn bin(op: BinOp, l: Self, r: Self) -> Self {
        AExp::Bin(op, Box::new(l), Box::new(r), Nothing)
    }
    pub fn gen(t: Tid) -> Self {
        AExp::Gen(t, Nothing)
    }
    pub fn coef(a: Self) -> Self {
        AExp::Coef(Box::new(a), Nothing)
    }
    pub fn mle(a: Self) -> Self {
        AExp::Mle(Box::new(a), Nothing)
    }
    pub fn interpolate(e: Self, d: Self) -> Self {
        AExp::Interpolate(Box::new(e), Box::new(d), Nothing)
    }
    pub fn challenge(t: Typ<Size>) -> Self {
        AExp::Challenge(t, Nothing)
    }
    pub fn random(t: Typ<Size>) -> Self {
        AExp::Random(t, Nothing)
    }
    pub fn vec(v: Vec<Self>) -> Self {
        AExp::Vec(AExps(v), Nothing)
    }
    pub fn map(l: Self, x: Vid, range: Self) -> Self {
        AExp::Map(Box::new(l), x, Box::new(range), Nothing)
    }
    pub fn ram(v: Self, i: Self) -> Self {
        AExp::Ram(Box::new(v), Box::new(i), Nothing)
    }
    pub fn range(r: Range<Size>) -> Self {
        AExp::Range(r, Nothing)
    }
    pub fn add(l: Self, r: Self) -> Self {
        AExp::Bin(BinOp::Add, Box::new(l), Box::new(r), Nothing)
    }
    pub fn sub(l: Self, r: Self) -> Self {
        AExp::Bin(BinOp::Sub, Box::new(l), Box::new(r), Nothing)
    }
    pub fn mul(l: Self, r: Self) -> Self {
        AExp::Bin(BinOp::Mul, Box::new(l), Box::new(r), Nothing)
    }
    pub fn div(l: Self, r: Self) -> Self {
        AExp::Bin(BinOp::Div, Box::new(l), Box::new(r), Nothing)
    }
    pub fn pow(l: Self, r: Self) -> Self {
        AExp::Bin(BinOp::Pow, Box::new(l), Box::new(r), Nothing)
    }
    pub fn dot(l: Self, r: Self) -> Self {
        AExp::Bin(BinOp::Dot, Box::new(l), Box::new(r), Nothing)
    }
    pub fn concat(l: Self, r: Self) -> Self {
        AExp::Bin(BinOp::Concat, Box::new(l), Box::new(r), Nothing)
    }
    pub fn var(x: Vid) -> Self {
        AExp::Var(x, Nothing)
    }
    pub fn varstr<'a>(x: &'a str) -> Self {
        AExp::var(Vid::from(x))
    }
    pub fn app(e: Fid, d: UAExps) -> Self {
        AExp::App(e, d, Nothing)
    }
    pub fn assert(b: UBExp) -> Self {
        AExp::Assert(Box::new(b), Nothing)
    }
    pub fn verify(b: UBExp) -> Self {
        AExp::Verify(Box::new(b), Nothing)
    }
    pub fn letx(a: Vid, d: Self) -> Self {
        AExp::Let(a, Box::new(d), Nothing)
    }
    pub fn logx(a: Vid, d: Self) -> Self {
        AExp::Log(a, Box::new(d), Nothing)
    }
}

/// Pretty printer instance
impl<'a, D, A> Pretty<'a, D, A> for BinOp
where
    D: DocAllocator<'a, A>,
    D::Doc: Clone,
    A: 'a + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        match self {
            BinOp::Add => allocator.text(" + "),
            BinOp::Sub => allocator.text(" - "),
            BinOp::Mul => allocator.text(" * "),
            BinOp::Div => allocator.text(" / "),
            BinOp::Pow => allocator.text(" ^ "),
            BinOp::Dot => allocator.text(" . "),
            BinOp::Concat => allocator.text(" ++ "),
        }
    }

    fn is_nil(&self) -> bool {
        false
    }
}

/// Pretty printer instance for typed AExp
impl<'a, D, A, N, T> Pretty<'a, D, A> for AExp<N, T>
where
    D: DocAllocator<'a, A>,
    D::Doc: Clone,
    T: Pretty<'a, D, A>,
    N: Pretty<'a, D, A>,
    A: 'a + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        match self {
            AExp::Lit(p, t) => allocator.concat([
                p.pretty(allocator),
                if t.is_nil() {
                    allocator.nil()
                } else {
                    allocator.text(" ⇝ ").append(t.pretty(allocator))
                }]),
            AExp::Coef(p, t) => allocator.concat([
                allocator.text("coef "),
                p.pretty(allocator),
                if t.is_nil() {
                    allocator.nil()
                } else {
                    allocator.text(" ⇝ ").append(t.pretty(allocator))
                }]),
            AExp::Mle(p, t) => allocator.concat([
                allocator.text("mle "),
                p.pretty(allocator),
                if t.is_nil() {
                    allocator.nil()
                } else {
                    allocator.text("⇝").append(t.pretty(allocator))
                }]),
            AExp::Vec(ts, t) => allocator.concat([
                allocator.text("["),
                allocator.intersperse(ts.into_iter().map(|x| x.pretty(allocator)), ", "),
                allocator.text("]"),
                if t.is_nil() {
                    allocator.nil()
                } else {
                    allocator.text(" ⇝ ").append(t.pretty(allocator))
                }]),
            AExp::Bin(op, a, b, t) => allocator.concat([
                (*a).pretty(allocator),
                op.pretty(allocator),
                (*b).pretty(allocator),
                if t.is_nil() {
                    allocator.nil()
                } else {
                    allocator.text("⇝").append(t.pretty(allocator))
                }]),
            AExp::Map(x, id, range, t) => allocator.concat([
                allocator.text("["),
                x.pretty(allocator),
                allocator.text(format!(" for {} in ", id)),
                range.pretty(allocator),
                allocator.text("] ⇝ "),
                t.pretty(allocator)
            ]),
            AExp::Var(x, t) => allocator.concat([
                x.pretty(allocator),
                if t.is_nil() {
                    allocator.nil()
                } else {
                    allocator.text("⇝").append(t.pretty(allocator))
                }]),
            AExp::Challenge(t, t2) => allocator.concat([
                allocator.text("challenge<"),
                t.pretty(allocator),
                allocator.text(">"),
                if t2.is_nil() {
                    allocator.nil()
                } else {
                    allocator.text(" ⇝ ").append(t2.pretty(allocator))
                }]),
            AExp::Random(t, t2) => allocator.concat([
                allocator.text("random<"),
                t.pretty(allocator),
                allocator.text(">"),
                if t2.is_nil() {
                    allocator.nil()
                } else {
                    allocator.text(" ⇝ ").append(t2.pretty(allocator))
                }]),
            AExp::Gen(t, t2) => allocator.concat([
                allocator.text("gen<"),
                t.pretty(allocator),
                allocator.text(">"),
                if t2.is_nil() {
                    allocator.nil()
                } else {
                    allocator.text(" ⇝ ").append(t2.pretty(allocator))
                }]),
            AExp::Range(r, t2) => allocator.concat([
                r.pretty(allocator),
                if t2.is_nil() {
                    allocator.nil()
                } else {
                    allocator.text(" ⇝ ").append(t2.pretty(allocator))
                }]),
            AExp::App(x, d, t) => allocator.concat([
                x.pretty(allocator),
                allocator.text("("),
                d.pretty(allocator),
                allocator.text(")"),
                if t.is_nil() {
                    allocator.nil()
                } else {
                    allocator.text("⇝").append(t.pretty(allocator))
                }]),
            AExp::Interpolate(b, d, t) => allocator.concat([
                allocator.text("interpolate("),
                (*b).pretty(allocator),
                allocator.text(", "),
                (*d).pretty(allocator),
                allocator.text(")"),
                if t.is_nil() {
                    allocator.nil()
                } else {
                    allocator.text("⇝").append(t.pretty(allocator))
                }]),
            AExp::Ram(x, i, t) => allocator.concat([
                (*x).pretty(allocator),
                allocator.text("["),
                (*i).pretty(allocator),
                allocator.text("]"),
                if t.is_nil() {
                    allocator.nil()
                } else {
                    allocator.text("⇝").append(t.pretty(allocator))
                }]),
            AExp::Let(x, a, t) => allocator.concat([
                allocator.text("let "),
                x.pretty(allocator),
                allocator.text(" = "),
                (*a).pretty(allocator),
                allocator.text(" in "),
                if t.is_nil() {
                    allocator.nil()
                } else {
                    allocator.text("⇝").append(t.pretty(allocator))
                },
            ]),
            AExp::Log(x, a, t) => allocator.concat([
                x.pretty(allocator),
                allocator.text(" <- "),
                (*a).pretty(allocator),
                if t.is_nil() {
                    allocator.nil()
                } else {
                    allocator.text("⇝").append(t.pretty(allocator))
                },
            ]),
            AExp::Assert(c, t) => allocator.concat([
                allocator.text("assert("),
                (*c).pretty(allocator),
                allocator.text(")"),
                if t.is_nil() {
                    allocator.nil()
                } else {
                    allocator.text("⇝").append(t.pretty(allocator))
                },
            ]),
            AExp::Verify(c, t) => allocator.concat([
                allocator.text("verify("),
                (*c).pretty(allocator),
                allocator.text(")"),
                if t.is_nil() {
                    allocator.nil()
                } else {
                    allocator.text("⇝").append(t.pretty(allocator))
                },
            ])
        }
    }

    fn is_nil(&self) -> bool {
        false
    }
}

impl<'a, D, A, N, T> Pretty<'a, D, A> for AExps<N, T>
where
    D: DocAllocator<'a, A>,
    D::Doc: Clone,
    T: Pretty<'a, D, A>,
    N: Pretty<'a, D, A>,
    A: 'a + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        allocator.intersperse(
            self.0.into_iter().map(|x| x.pretty(allocator)), ";\n")
    }
    fn is_nil(&self) -> bool {
        self.0.is_empty()
    }
}

impl Add for UAExp {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        UAExp::add(self, rhs)
    }
}

impl Sub for UAExp {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self {
        UAExp::sub(self, rhs)
    }
}

impl Mul for UAExp {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self {
        UAExp::mul(self, rhs)
    }
}

impl Div for UAExp {
    type Output = Self;

    fn div(self, rhs: Self) -> Self {
        UAExp::div(self, rhs)
    }
}

impl BitXor for UAExp {
    type Output = Self;

    fn bitxor(self, rhs: Self) -> Self {
        UAExp::pow(self, rhs)
    }
}

impl From<u32> for UAExp {
    fn from(x: u32) -> Self {
        UAExp::lit(Size::from(x))
    }
}

impl From<Vid> for UAExp {
    fn from(x: Vid) -> Self {
        UAExp::var(x)
    }
}

impl From<&str> for UAExp {
    fn from(x: &str) -> Self {
        UAExp::varstr(x)
    }
}

/// Display instance calls the pretty printer
impl fmt::Display for BinOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <BinOp as Pretty<'_, BoxAllocator, ()>>::pretty(self.clone(), &BoxAllocator)
            .1
            .render_fmt(100, f)
    }
}

impl<'a, N, T> fmt::Display for AExp<N, T>
where
    T: Clone + Pretty<'a, BoxAllocator, ()>,
    N: Clone + Pretty<'a, BoxAllocator, ()>,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <AExp<N, T> as Pretty<'_, BoxAllocator, ()>>::pretty(self.clone(), &BoxAllocator)
            .1
            .render_fmt(100, f)
    }
}

impl<'a, N, T> fmt::Display for AExps<N, T>
where
    T: Clone + Pretty<'a, BoxAllocator, ()>,
    N: Clone + Pretty<'a, BoxAllocator, ()>,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <AExps<N, T> as Pretty<'_, BoxAllocator, ()>>::pretty(self.clone(), &BoxAllocator)
            .1
            .render_fmt(100, f)
    }
}

lazy_static! {
    pub static ref AEXP_PARSER: PrattParser<Rule> = {
        use Assoc::*;
        use Rule::*;

        PrattParser::new()
            .op(Op::infix(add_op, Left) | Op::infix(sub_op, Left))
            .op(Op::infix(mul_op, Left) | Op::infix(dot_op, Left) | Op::infix(div_op, Left))
            .op(Op::infix(concat_op, Left))
            .op(Op::infix(pow_op, Right))
    };
}

impl<'pest> FromPest<'pest> for BinOp {
    type Rule = Rule;
    type FatalError = InputError<'pest>;

    fn from_pest(
        pest: &mut Pairs<'pest, Self::Rule>,
    ) -> Result<Self, ConversionError<Self::FatalError>> {
        let pair = pest.next().ok_or(ConversionError::NoMatch)?;
        match pair.as_rule() {
            Rule::add_op => Ok(BinOp::Add),
            Rule::sub_op => Ok(BinOp::Sub),
            Rule::mul_op => Ok(BinOp::Mul),
            Rule::div_op => Ok(BinOp::Div),
            Rule::pow_op => Ok(BinOp::Pow),
            Rule::dot_op => Ok(BinOp::Dot),
            Rule::concat_op => Ok(BinOp::Concat),
            _ => unreachable!()
        }
    }
}

impl<'pest> FromPest<'pest> for UAExp {
    type Rule = Rule;
    type FatalError = InputError<'pest>;

    fn from_pest(
        expression: &mut Pairs<'pest, Self::Rule>,
    ) -> Result<Self, ConversionError<Self::FatalError>> {
        AEXP_PARSER
            .map_primary(|pair| match pair.as_rule() {
                Rule::id => Ok(AExp::var(Vid(pair.as_str().to_string()))),
                Rule::positive => Ok(AExp::lit(Size::from_pest(&mut Pairs::single(pair))?)),
                Rule::gen_exp => Ok(AExp::gen(Tid::from_pest(&mut pair.into_inner())?)),
                Rule::coef_exp => Ok(AExp::coef(AExp::from_pest(&mut pair.into_inner())?)),
                Rule::mle_exp => Ok(AExp::mle(AExp::from_pest(&mut pair.into_inner())?)),
                Rule::interp_exp => {
                    let mut inner = pair.into_inner();
                    Ok(AExp::interpolate(
                        AExp::from_pest(&mut Pairs::single(inner.next().unwrap()))?,
                        AExp::from_pest(&mut Pairs::single(inner.next().unwrap()))?
                    ))
                },
                Rule::challenge_exp =>
                    Ok(AExp::challenge(Typ::from_pest(&mut pair.into_inner())?)),
                Rule::random_exp =>
                    Ok(AExp::random(Typ::from_pest(&mut pair.into_inner())?)),
                Rule::vec_exp => {
                    let inner = pair.into_inner();
                    let mut ve = Vec::new();
                    for x in inner {
                        ve.push(AExp::from_pest(&mut Pairs::single(x))?);
                    }
                    Ok(AExp::vec(ve))
                },
                Rule::map_exp => {
                    let mut inner = pair.into_inner();
                    Ok(AExp::map(
                        AExp::from_pest(&mut Pairs::single(inner.next().unwrap()))?,
                        Vid::from_pest(&mut Pairs::single(inner.next().unwrap()))?,
                        AExp::from_pest(&mut Pairs::single(inner.next().unwrap()))?
                    ))
                },
                Rule::ram_exp => {
                    let mut inner = pair.into_inner();
                    Ok(AExp::ram(
                        AExp::var(Vid::from_pest(&mut Pairs::single(inner.next().unwrap()))?),
                        AExp::from_pest(&mut Pairs::single(inner.next().unwrap()))?
                    ))
                },
                Rule::app_exp => {
                    let mut inner = pair.into_inner();
                    // Call a function
                    let func = Fid::from_pest(&mut inner)?;
                    // Arguments
                    let params = AExps::from_pest(&mut inner)?;
                    Ok(AExp::app(func, params))
                },
                Rule::assert_exp => {
                    let mut inner = pair.into_inner();
                    Ok(AExp::assert(UBExp::from_pest(&mut Pairs::single(inner.next().unwrap()))?))
                },
                Rule::verify_exp => {
                    let mut inner = pair.into_inner();
                    dbg!(&inner);
                    Ok(AExp::verify(
                        UBExp::from_pest(&mut Pairs::single(inner.next().unwrap()))?,
                    ))
                },
                Rule::let_exp => {
                    let mut inner = pair.into_inner();
                    Ok(AExp::letx(
                        Vid::from_pest(&mut Pairs::single(inner.next().unwrap()))?,
                        AExp::from_pest(&mut Pairs::single(inner.next().unwrap()))?
                    ))
                },
                Rule::log_exp => {
                    let mut inner = pair.into_inner();
                    Ok(AExp::logx(
                        Vid::from_pest(&mut Pairs::single(inner.next().unwrap()))?,
                        AExp::from_pest(&mut Pairs::single(inner.next().unwrap()))?
                    ))
                },
                Rule::aexp => AExp::from_pest(&mut pair.into_inner()),
                Rule::range_exp => Ok(AExp::range(Range::from_pest(&mut pair.into_inner())?)),
                _ => Err(ConversionError::Malformed(InputError::UnexpectedExp(pair)))
            })
            .map_infix(|lhs, op, rhs|
                match op.clone().as_rule() {
                    Rule::add_op => Ok(AExp::add(lhs?, rhs?)),
                    Rule::sub_op => Ok(AExp::sub(lhs?, rhs?)),
                    Rule::mul_op => Ok(AExp::mul(lhs?, rhs?)),
                    Rule::div_op => Ok(AExp::div(lhs?, rhs?)),
                    Rule::pow_op => Ok(AExp::pow(lhs?, rhs?)),
                    Rule::dot_op => Ok(AExp::dot(lhs?, rhs?)),
                    Rule::concat_op => Ok(AExp::concat(lhs?, rhs?)),
                    _ => unreachable!(),
                })
            .parse(expression)
    }
}

impl<'pest> FromPest<'pest> for UAExps {
    type Rule = Rule;
    type FatalError = InputError<'pest>;

    fn from_pest(
        pest: &mut Pairs<'pest, Self::Rule>,
    ) -> Result<Self, ConversionError<Self::FatalError>> {
        let pair = pest.next().ok_or(ConversionError::NoMatch)?;
        match pair.as_rule() {
            Rule::aexps => {
                let mut aexps = Vec::new();
                for pair in pair.into_inner() {
                    aexps.push(UAExp::from_pest(&mut Pairs::single(pair))?);
                }
                Ok(AExps(aexps))
            },
            _ => Err(ConversionError::Malformed(InputError::UnexpectedExp(pair))),
        }
    }
}

////////////////////////////////////////////////////////////////////////
/// Parser tests
////////////////////////////////////////////////////////////////////////
#[cfg(test)] use pest::Parser;
#[test]
fn parser_lit() {
    let ex = "2";
    let mut pairs = ZippelParser::parse(Rule::aexp, ex).unwrap();
    assert_eq!(UAExp::from_pest(&mut pairs), Ok(AExp::from(2)));
}

#[test]
fn parser_var() {
    let ex = "x";
    let mut pairs = ZippelParser::parse(Rule::aexp, ex).unwrap();
    assert_eq!(UAExp::from_pest(&mut pairs), Ok(AExp::varstr("x")));
}

#[test]
fn parser_bin() {
    // Add
    let ex1 = "x + 2";
    let mut pairs = ZippelParser::parse(Rule::aexp, ex1).unwrap();
    assert_eq!(
        UAExp::from_pest(&mut pairs),
        Ok(AExp::varstr("x") + AExp::from(2))
    );

    // Sub
    let ex2 = "x - 2";
    let mut pairs = ZippelParser::parse(Rule::aexp, ex2).unwrap();
    assert_eq!(
        UAExp::from_pest(&mut pairs),
        Ok(AExp::varstr("x") - AExp::from(2))
    );

    // Mul
    let ex3 = "x * 2";
    let mut pairs = ZippelParser::parse(Rule::aexp, ex3).unwrap();
    assert_eq!(
        AExp::from_pest(&mut pairs),
        Ok(AExp::varstr("x") * AExp::from(2))
    );

    // Div
    let ex4 = "x / 2";
    let mut pairs = ZippelParser::parse(Rule::aexp, ex4).unwrap();
    assert_eq!(
        UAExp::from_pest(&mut pairs),
        Ok(AExp::varstr("x") / AExp::from(2))
    );

    // Pow
    let ex6 = "x ^ 2";
    let mut pairs = ZippelParser::parse(Rule::aexp, ex6).unwrap();
    assert_eq!(
        UAExp::from_pest(&mut pairs),
        Ok(AExp::pow(AExp::varstr("x"), AExp::from(2)))
    );
}

#[test]
fn parser_interpolate() {
    let ex = "interpolate(x + 2, 4*x)";
    let mut pairs = ZippelParser::parse(Rule::aexp, ex).unwrap();
    assert_eq!(
        UAExp::from_pest(&mut pairs),
        Ok(AExp::interpolate(
            AExp::varstr("x") + AExp::from(2),
            AExp::from(4) * AExp::varstr("x")
        ))
    );
}

#[test]
fn parser_call_two() {
    let ex = "f(x + 2, x)";
    let mut pairs = ZippelParser::parse(Rule::aexp, ex).unwrap();
    assert_eq!(
        UAExp::from_pest(&mut pairs),
        Ok(AExp::app(
            Fid::from("f"),
            AExps(vec![AExp::varstr("x") + AExp::from(2), AExp::varstr("x")])
        ))
    );
}

#[test]
fn parser_range() {
    let ex = "0..N";
    let mut pairs = ZippelParser::parse(Rule::aexp, ex).unwrap();
    assert_eq!(
        UAExp::from_pest(&mut pairs),
        Ok(AExp::range(Range { start: Size::from(0), step: Size::from(1), end: Size::from("N") }))
    );
}

#[test]
fn parser_for() {
    let ex = "[ 3^i for i in 0..N ]";
    let mut pairs = ZippelParser::parse(Rule::aexp, ex).unwrap();
    assert_eq!(
        UAExp::from_pest(&mut pairs),
        Ok(AExp::map(
            AExp::pow(AExp::from(3), AExp::varstr("i")),
            Vid::from("i"),
            AExp::range(Range { start: Size::from(0), step: Size::from(1), end: Size::from("N") }))
        ));
}

#[test]
fn parser_random() {
    let ex = "random<Uni<A, 2>>";
    let mut pairs = ZippelParser::parse(Rule::aexp, ex).unwrap();
    assert_eq!(
        UAExp::from_pest(&mut pairs),
        Ok(AExp::random(Typ::uni(Tid::from("A"), Size::from(2))))
    );
}

#[test]
fn parser_challenge() {
    let ex = "challenge<F>";
    let mut pairs = ZippelParser::parse(Rule::aexp, ex).unwrap();
    assert_eq!(UAExp::from_pest(&mut pairs), Ok(AExp::challenge(Typ::varstr("F"))));
}

#[test]
fn parser_concat() {
    let ex = "(x + 2) ++ x";
    let mut pairs = ZippelParser::parse(Rule::aexp, ex).unwrap();
    assert_eq!(
        UAExp::from_pest(&mut pairs),
        Ok(AExp::concat(
            AExp::varstr("x") + AExp::from(2),
            AExp::varstr("x")
        ))
    );
}

#[test]
fn parser_let() {
    let ex = "let x = 2";
    let mut pairs = ZippelParser::parse(Rule::aexp, ex).unwrap();
    assert_eq!(
        UAExp::from_pest(&mut pairs),
        Ok(AExp::letx(
            Vid::from("x"),
            AExp::from(2)
        ))
    );
}

#[test]
fn parser_log() {
    let ex = "x <- 2";
    let mut pairs = ZippelParser::parse(Rule::aexp, ex).unwrap();
    assert_eq!(
        UAExp::from_pest(&mut pairs),
        Ok(AExp::logx(
            Vid::from("x"),
            AExp::from(2),
        ))
    );
}

#[test]
fn parser_assert() {
    let ex = "assert(x == 2)";
    let mut pairs = ZippelParser::parse(Rule::aexp, ex).unwrap();
    assert_eq!(
        UAExp::from_pest(&mut pairs),
        Ok(AExp::assert(
            BExp::equ(AExp::varstr("x"), AExp::from(2)),
        ))
    );
}

#[test]
fn parser_verify() {
    let ex = "verify(x == 2)";
    let mut pairs = ZippelParser::parse(Rule::aexp, ex).unwrap();
    assert_eq!(
        UAExp::from_pest(&mut pairs),
        Ok(AExp::verify(
            BExp::equ(AExp::varstr("x"), AExp::from(2)),
        ))
    );
}

#[test]
fn parser_seq() {
    let ex = "x <- 2; y <- 3; let x = 2 * 4";
    let mut pairs = ZippelParser::parse(Rule::aexps, ex).unwrap();
    assert_eq!(
        UAExps::from_pest(&mut pairs),
        Ok(AExps(vec![
            AExp::logx(Vid::from("x"), AExp::from(2)),
            AExp::logx(Vid::from("y"), AExp::from(3)),
            AExp::letx(Vid::from("x"), AExp::from(2) * AExp::from(4))
        ]))
    );
}
