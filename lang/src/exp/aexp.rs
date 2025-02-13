use std::ops::{Add, Div, Mul, Sub};
use crate::parser::*;
use from_pest::{ConversionError, FromPest};
use lazy_static::lazy_static;
use std::fmt;
use pest::iterators::Pairs;
use pest::pratt_parser::{Assoc, Op, PrattParser};

use share::{Proj1, Proj2, Traversable2, Traversable1, BoxAllocator, Pretty, DocAllocator, DocBuilder};
use crate::typ::{Typ, Size, Nothing};
use crate::exp::BExp;
use crate::id::{Tid, Fid, Vid};
use crate::range::Range;

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
    Lit(i32, A),

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

    ///     Fold over non-empty vector
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let sum = reduce(+, v)
    ///     ```
    Reduce(BinOp, Box<AExp<N, A>>, A),

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
    Vec(Vec<AExp<N, A>>, A),

    ///     Binary operation
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let sum = 2 + 3;
    ///     ```
    Bin(BinOp, Box<AExp<N, A>>, Box<AExp<N, A>>, A),

    ///     **Zippel Code:**
    ///     ```zippel
    ///     let r = [0..5];
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

/// Typed AST node
pub type TAExp<N, A> = AExp<N, (A, Typ<N>)>;

/// Untyped AST node, as parsed from input
pub type UAExp = AExp<Size, Nothing>;

/// Typed AST sequence
pub type TAExps<N, A> = AExps<N, (A, Typ<N>)>;

/// Untyped AST sequence, as parsed from input
pub type UAExps = AExps<Size, Nothing>;

/// Modular get/set acccess to expression annotations using [Proj1] and [Proj2]
impl<N, A, B> Proj1<A> for AExp<N, (A, B)> {
    type Output<Z> = AExp<N, (Z, B)>;

    fn get_proj1(&self) -> &A {
        match self {
            AExp::Lit(_, t) => &t.0,
            AExp::Var(_, t) => &t.0,
            AExp::Coef(_, t) => &t.0,
            AExp::Mle(_, t) => &t.0,
            AExp::Vec(_, t) => &t.0,
            AExp::Bin(_, _, _, t) => &t.0,
            AExp::Map(_, _, _, t) => &t.0,
            AExp::Challenge(_, t) => &t.0,
            AExp::Random(_, t) => &t.0,
            AExp::Verify(_, t) => &t.0,
            AExp::App(_, _, t) => &t.0,
            AExp::Reduce(_, _, t) => &t.0,
            AExp::Interpolate(_, _, t) => &t.0,
            AExp::Ram(_, _, t) => &t.0,
            AExp::Range(_, t) => &t.0,
            AExp::Let(_, _, t) => &t.0,
            AExp::Log(_, _, t) => &t.0,
            AExp::Assert(_, t) => &t.0,
            AExp::Gen(_, t) => &t.0
        }
    }

    fn map_proj1<Z>(self, f: &mut dyn FnMut(A)->Z) -> Self::Output<Z> {
        match self {
            AExp::Lit(a, (x, y)) => AExp::Lit(a, (f(x), y)),
            AExp::Var(a, (x, y)) => AExp::Var(a, (f(x), y)),
            AExp::Coef(box a, (x, y)) => AExp::coef(a.map_proj1(f), (f(x), y)),
            AExp::Mle(box a, (x, y)) => AExp::mle(a.map_proj1(f), (f(x), y)),
            AExp::Vec(a, (x, y)) =>
                AExp::Vec(a.into_iter().map(|x| x.map_proj1(f)).collect(), (f(x), y)),
            AExp::App(a, b, (x, y)) =>
                AExp::App(a, AExps(b.0.into_iter().map(|x| x.map_proj1(f)).collect()), (f(x), y)),
            AExp::Reduce(op, box d, (x, y)) =>
                AExp::reduce(op, d.map_proj1(f), (f(x), y)),
            AExp::Bin(op, box x, box z, (y, w)) =>
                AExp::bin(op, x.map_proj1(f), z.map_proj1(f), (f(y), w)),
            AExp::Map(box x, id, box r, (y, z)) =>
                AExp::map(x.map_proj1(f), id, r.map_proj1(f), (f(y), z)),
            AExp::Challenge(t, (x, y)) => AExp::challenge(t, (f(x), y)),
            AExp::Random(t, (x, y)) => AExp::random(t, (f(x), y)),
            AExp::Gen(t, (x, y)) => AExp::gen(t, (f(x), y)),
            AExp::Range(r, (x, y)) => AExp::range(r, (f(x), y)),
            AExp::Interpolate(box x, box y, (z, w)) =>
                AExp::interpolate(x.map_proj1(f), y.map_proj1(f), (f(z), w)),
            AExp::Ram(box x, box i, (y, z)) =>
                AExp::ram(x.map_proj1(f), i.map_proj1(f), (f(y), z)),
            AExp::Let(x, box a,  (y, z)) =>
                AExp::letx(x, a.map_proj1(f), (f(y), z)),
            AExp::Log(x, box a, (y, z)) =>
                AExp::logx(x, a.map_proj1(f), (f(y), z)),
            AExp::Assert(box x, (y, z)) =>
                AExp::assert(x.map_proj1(f), (f(y), z)),
            AExp::Verify(box x, (y, z)) =>
                AExp::verify(x.map_proj1(f), (f(y), z))
        }
    }

    fn modify_proj1(&mut self, f: &mut dyn FnMut(&mut A)) {
        match self {
            AExp::Lit(_, (x, _)) => f(x),
            AExp::Var(_, (x, _)) => f(x),
            AExp::Coef(box a, (x, _)) => { a.modify_proj1(f); f(x) },
            AExp::Mle(box a, (x, _)) => { a.modify_proj1(f); f(x) },
            AExp::Vec(v, (x, _)) => {
                for e in v.iter_mut() {
                    e.modify_proj1(f);
                }
                f(x)
            },
            AExp::Bin(_, box a, box b, (x, _)) => {
                a.modify_proj1(f);
                b.modify_proj1(f);
                f(x)
            },
            AExp::Map(box a, _, box b, (x, _)) => {
                a.modify_proj1(f);
                b.modify_proj1(f);
                f(x)
            },
            AExp::Challenge(_, (x, _)) => f(x),
            AExp::Random(_, (x, _)) => f(x),
            AExp::Verify(box a, (x, _)) => {
                a.modify_proj1(f);
                f(x)
            },
            AExp::App(_, b, (x, _)) => {
                for e in b.0.iter_mut() {
                    e.modify_proj1(f);
                }
                f(x)
            },
            AExp::Reduce(_, box a, (x, _)) => {
                a.modify_proj1(f);
                f(x)
            },
            AExp::Interpolate(box a, box b, (x, _)) => {
                a.modify_proj1(f);
                b.modify_proj1(f);
                f(x)
            },
            AExp::Ram(box a, box b, (x, _)) => {
                a.modify_proj1(f);
                b.modify_proj1(f);
                f(x)
            },
            AExp::Range(_, (x, _)) => f(x),
            AExp::Let(_, box a, (x, _)) => {
                a.modify_proj1(f);
                f(x)
            },
            AExp::Log(_, box a, (x, _)) => {
                a.modify_proj1(f);
                f(x)
            },
            AExp::Assert(box a, (x, _)) => {
                a.modify_proj1(f);
                f(x)
            },
            AExp::Gen(_, (x, _)) => f(x)
        }
    }
}

impl<N, A, B> Proj2<B> for AExp<N, (A, B)> {
    type Output<Z> = AExp<N, (A, Z)>;

    fn get_proj2(&self) -> &B {
        match self {
            AExp::Lit(_, t) => &t.1,
            AExp::Var(_, t) => &t.1,
            AExp::Coef(_, t) => &t.1,
            AExp::Mle(_, t) => &t.1,
            AExp::Vec(_, t) => &t.1,
            AExp::Bin(_, _, _, t) => &t.1,
            AExp::Map(_, _, _, t) => &t.1,
            AExp::Challenge(_, t) => &t.1,
            AExp::Random(_, t) => &t.1,
            AExp::Verify(_, t) => &t.1,
            AExp::App(_, _, t) => &t.1,
            AExp::Reduce(_, _, t) => &t.1,
            AExp::Interpolate(_, _, t) => &t.1,
            AExp::Ram(_, _, t) => &t.1,
            AExp::Range(_, t) => &t.1,
            AExp::Let(_, _, t) => &t.1,
            AExp::Log(_, _, t) => &t.1,
            AExp::Assert(_, t) => &t.1,
            AExp::Gen(_, t) => &t.1
        }
    }

    fn map_proj2<Z>(self, f: &mut dyn FnMut(B)->Z) -> Self::Output<Z> {
        match self {
            AExp::Lit(a, (x, y)) => AExp::Lit(a, (x, f(y))),
            AExp::Var(a, (x, y)) => AExp::Var(a, (x, f(y))),
            AExp::Coef(box a, (x, y)) => AExp::coef(a.map_proj2(f), (x, f(y))),
            AExp::Mle(box a, (x, y)) => AExp::mle(a.map_proj2(f), (x, f(y))),
            AExp::Vec(a, (x, y)) =>
                AExp::Vec(a.into_iter().map(|x| x.map_proj2(f)).collect(), (x, f(y))),
            AExp::App(a, b, (x, y)) =>
                AExp::App(a, AExps(b.0.into_iter().map(|x| x.map_proj2(f)).collect()), (x, f(y))),
            AExp::Reduce(op, box d, (x, y)) =>
                AExp::reduce(op, d.map_proj2(f), (x, f(y))),
            AExp::Bin(op, box x, box z, (y, w)) =>
                AExp::bin(op, x.map_proj2(f), z.map_proj2(f), (y, f(w))),
            AExp::Map(box x, id, box r, (y, z)) =>
                AExp::map(x.map_proj2(f), id, r.map_proj2(f), (y, f(z))),
            AExp::Challenge(t, (x, y)) => AExp::challenge(t, (x, f(y))),
            AExp::Random(t, (x, y)) => AExp::random(t, (x, f(y))),
            AExp::Gen(t, (x, y)) => AExp::gen(t, (x, f(y))),
            AExp::Range(r, (x, y)) => AExp::range(r, (x, f(y))),
            AExp::Interpolate(box x, box y, (z, w)) =>
                AExp::interpolate(x.map_proj2(f), y.map_proj2(f), (z, f(w))),
            AExp::Ram(box x, box i, (y, z)) =>
                AExp::ram(x.map_proj2(f), i.map_proj2(f), (y, f(z))),
            AExp::Let(x, box a, (y, z)) =>
                AExp::letx(x, a.map_proj2(f), (y, f(z))),
            AExp::Log(x, box a, (y, z)) =>
                AExp::logx(x, a.map_proj2(f), (y, f(z))),
            AExp::Assert(box a, (x, y)) =>
                AExp::assert(a.map_proj2(f), (x, f(y))),
            AExp::Verify(box a, (x, y)) =>
                AExp::verify(a.map_proj2(f), (x, f(y)))
        }
    }

    fn modify_proj2(&mut self, f: &mut dyn FnMut(&mut B)) {
        match self {
            AExp::Lit(_, (_, y)) => f(y),
            AExp::Var(_, (_, y)) => f(y),
            AExp::Coef(box a, (_, y)) => { a.modify_proj2(f); f(y) },
            AExp::Mle(box a, (_, y)) => { a.modify_proj2(f); f(y) },
            AExp::Vec(v, (_, y)) => {
                for e in v.iter_mut() {
                    e.modify_proj2(f);
                }
                f(y)
            },
            AExp::Bin(_, box a, box b, (_, y)) => {
                a.modify_proj2(f);
                b.modify_proj2(f);
                f(y)
            },
            AExp::Map(box a, _, box b, (_, y)) => {
                a.modify_proj2(f);
                b.modify_proj2(f);
                f(y)
            },
            AExp::Challenge(_, (_, y)) => f(y),
            AExp::Random(_, (_, y)) => f(y),
            AExp::Verify(box a, (_, y)) => {
                a.modify_proj2(f);
                f(y)
            },
            AExp::App(_, b, (_, y)) => {
                for e in b.0.iter_mut() {
                    e.modify_proj2(f);
                }
                f(y)
            },
            AExp::Reduce(_, box a, (_, y)) => {
                a.modify_proj2(f);
                f(y)
            },
            AExp::Interpolate(box a, box b, (_, y)) => {
                a.modify_proj2(f);
                b.modify_proj2(f);
                f(y)
            },
            AExp::Ram(_, box a, (_, y)) => {
                a.modify_proj2(f);
                f(y)
            },
            AExp::Range(_, (_, y)) => f(y),
            AExp::Let(_, box a, (_, y)) => {
                a.modify_proj2(f);
                f(y)
            },
            AExp::Log(_, box a, (_, y)) => {
                a.modify_proj2(f);
                f(y)
            },
            AExp::Assert(box a, (_, y)) => {
                a.modify_proj2(f);
                f(y)
            },
            AExp::Gen(_, (_, y)) => f(y)
        }
    }
}

/// Modular get/set acccess to type parameters using [Traversable1] and [Traversable2]
impl<N, T> Traversable1<N> for AExp<N, T> {
    type Output<Z> = AExp<Z, T>;

    fn traverse1<Z, E>(self, f: &mut dyn FnMut(N) -> Result<Z, E>) -> Result<AExp<Z, T>, E> {
        match self {
            AExp::Lit(x, a) => Ok(AExp::Lit(x, a)),
            AExp::Var(v, a) => Ok(AExp::Var(v, a)),
            AExp::Coef(box p, a) => Ok(AExp::coef(p.traverse1(f)?, a)),
            AExp::Mle(box p, a) => Ok(AExp::mle(p.traverse1(f)?, a)),
            AExp::Vec(v, a) =>
                Ok(AExp::Vec(v.traverse1(&mut |x| x.traverse1(f))?, a)),
            AExp::App(x, ts, a) =>
                Ok(AExp::App(x, ts.traverse1(f)?, a)),
            AExp::Bin(op, box x, box y, a) =>
                Ok(AExp::bin(
                    op,
                    x.traverse1(f)?,
                    y.traverse1(f)?,
                    a
                )),
            AExp::Map(box x, id, box r, a) =>
                Ok(AExp::map(x.traverse1(f)?, id, r.traverse1(f)?, a)),
            AExp::Challenge(t, a) => Ok(AExp::challenge(t.traverse1(f)?, a)),
            AExp::Random(t, a) => Ok(AExp::random(t.traverse1(f)?, a)),
            AExp::Gen(t, a) => Ok(AExp::gen(t, a)),
            AExp::Range(r, a) => Ok(AExp::range(r.traverse1(f)?, a)),
            AExp::Interpolate(box x, box y, a) =>
                Ok(AExp::interpolate(
                    x.traverse1(f)?,
                    y.traverse1(f)?,
                    a
                )),
            AExp::Reduce(op, box x, a) =>
                Ok(AExp::reduce(op,
                    x.traverse1(f)?,
                    a
                )),
            AExp::Ram(box x, box i, a) =>
                Ok(AExp::ram(
                        x.traverse1(f)?,
                        i.traverse1(f)?,
                        a
                )),
            AExp::Let(x, box a, t) =>
                Ok(AExp::letx(x, a.traverse1(f)?, t)),
            AExp::Log(x, box a, t) =>
                Ok(AExp::logx(x, a.traverse1(f)?, t)),
            AExp::Assert(box x,  t) =>
                Ok(AExp::assert(x.traverse1(f)?, t)),
            AExp::Verify(box x, t) =>
                Ok(AExp::verify(x.traverse1(f)?, t))
        }
    }
}

impl<N, T> Traversable1<N> for AExps<N, T> {
    type Output<Z> = AExps<Z, T>;

    fn traverse1<Z, E>(self, f: &mut dyn FnMut(N) -> Result<Z, E>) -> Result<AExps<Z, T>, E> {
        Ok(AExps(self.0.traverse1(&mut |x| x.traverse1(f))?))
    }
}

impl<N, T> Traversable2<T> for AExp<N, T> {
    type Output<Z> = AExp<N, Z>;

    fn traverse2<Z, E>(self, f: &mut dyn FnMut(T) -> Result<Z, E>) -> Result<AExp<N, Z>, E> {
        match self {
            AExp::Lit(x, a) => Ok(AExp::Lit(x, f(a)?)),
            AExp::Var(v, a) => Ok(AExp::Var(v, f(a)?)),
            AExp::Coef(box p, a) => Ok(AExp::coef(p.traverse2(f)?, f(a)?)),
            AExp::Mle(box p, a) => Ok(AExp::mle(p.traverse2(f)?, f(a)?)),
            AExp::Vec(v, a) =>
                Ok(AExp::Vec(v.traverse1(&mut |x| x.traverse2(f))?, f(a)?)),
            AExp::App(x, ts, a) =>
                Ok(AExp::App(x, ts.traverse2(f)?, f(a)?)),
            AExp::Bin(op, box x, box y, a) =>
                Ok(AExp::bin(
                    op,
                    x.traverse2(f)?,
                    y.traverse2(f)?,
                    f(a)?
                )),
            AExp::Map(box x, id, box r, a) => {
                Ok(AExp::map(x.traverse2(f)?, id, r.traverse2(f)?, f(a)?))
            }
            AExp::Challenge(t, a) => Ok(AExp::challenge(t, f(a)?)),
            AExp::Random(t, a) => Ok(AExp::random(t, f(a)?)),
            AExp::Gen(t, a) => Ok(AExp::gen(t, f(a)?)),
            AExp::Range(r, a) => Ok(AExp::range(r, f(a)?)),
            AExp::Interpolate(box x, box y, a) =>
                Ok(AExp::interpolate(
                    x.traverse2(f)?,
                    y.traverse2(f)?,
                    f(a)?
                )),
            AExp::Reduce(op, box x, a) =>
                Ok(AExp::reduce(op,
                    x.traverse2(f)?,
                    f(a)?
                )),
            AExp::Ram(box x, box i, a) =>
                Ok(AExp::ram(
                        x.traverse2(f)?,
                        i.traverse2(f)?,
                        f(a)?
                )),
            AExp::Let(x, box a,t) =>
                Ok(AExp::letx(x, a.traverse2(f)?, f(t)?)),
            AExp::Log(x, box a, t) =>
                Ok(AExp::logx(x, a.traverse2(f)?, f(t)?)),
            AExp::Assert(box x, a) =>
                Ok(AExp::assert(x.traverse2(f)?, f(a)?)),
            AExp::Verify(box x, a) =>
                Ok(AExp::verify(x.traverse2(f)?, f(a)?))
        }
    }
}

impl<N, T> Traversable2<T> for AExps<N, T> {
    type Output<Z> = AExps<N, Z>;

    fn traverse2<Z, E>(self, f: &mut dyn FnMut(T) -> Result<Z, E>) -> Result<AExps<N, Z>, E> {
        Ok(AExps(self.0.traverse1(&mut |x| x.traverse2(f))?))
    }
}

/// Construct untyped expressions and type infer later [types/infer.rs]
impl<N, T> AExp<N, T> {
    /// Annotated constructors
    pub fn lit(v: i32, ann: T) -> Self {
        AExp::Lit(v, ann)
    }
    pub fn bin(op: BinOp, l: Self, r: Self, ann: T) -> Self {
        AExp::Bin(op, Box::new(l), Box::new(r), ann)
    }
    pub fn gen(t: Tid, ann: T) -> Self {
        AExp::Gen(t, ann)
    }
    pub fn coef(a: Self, ann: T) -> Self {
        AExp::Coef(Box::new(a), ann)
    }
    pub fn mle(a: Self, ann: T) -> Self {
        AExp::Mle(Box::new(a), ann)
    }
    pub fn interpolate(e: Self, d: Self, ann: T) -> Self {
        AExp::Interpolate(Box::new(e), Box::new(d), ann)
    }
    pub fn challenge(t: Typ<N>, ann: T) -> Self {
        AExp::Challenge(t, ann)
    }
    pub fn random(t: Typ<N>, ann: T) -> Self {
        AExp::Random(t, ann)
    }
    pub fn vec(v: Vec<Self>, ann: T) -> Self {
        AExp::Vec(v, ann)
    }
    pub fn map(l: Self, x: Vid, range: Self, ann: T) -> Self {
        AExp::Map(Box::new(l), x, Box::new(range), ann)
    }
    pub fn ram(v: Self, i: Self, ann: T) -> Self {
        AExp::Ram(Box::new(v), Box::new(i), ann)
    }
    pub fn range(r: Range<N>, ann: T) -> Self {
        AExp::Range(r, ann)
    }
    pub fn add(l: Self, r: Self, ann: T) -> Self {
        AExp::Bin(BinOp::Add, Box::new(l), Box::new(r), ann)
    }
    pub fn sub(l: Self, r: Self, ann: T) -> Self {
        AExp::Bin(BinOp::Sub, Box::new(l), Box::new(r), ann)
    }
    pub fn mul(l: Self, r: Self, ann: T) -> Self {
        AExp::Bin(BinOp::Mul, Box::new(l), Box::new(r), ann)
    }
    pub fn div(l: Self, r: Self, ann: T) -> Self {
        AExp::Bin(BinOp::Div, Box::new(l), Box::new(r), ann)
    }
    pub fn pow(l: Self, r: Self, ann: T) -> Self {
        AExp::Bin(BinOp::Pow, Box::new(l), Box::new(r), ann)
    }
    pub fn dot(l: Self, r: Self, ann: T) -> Self {
        AExp::Bin(BinOp::Dot, Box::new(l), Box::new(r), ann)
    }
    pub fn concat(l: Self, r: Self, ann: T) -> Self {
        AExp::Bin(BinOp::Concat, Box::new(l), Box::new(r), ann)
    }
    pub fn var(x: Vid, ann: T) -> Self {
        AExp::Var(x, ann)
    }
    pub fn varstr<'a>(x: &'a str, ann: T) -> Self {
        AExp::var(Vid::from(x), ann)
    }
    pub fn app(e: Fid, d: AExps<N, T>, ann: T) -> Self {
        AExp::App(e, d, ann)
    }
    pub fn reduce(op: BinOp, d: Self, ann: T) -> Self {
        AExp::Reduce(op, Box::new(d), ann)
    }
    pub fn assert(b: BExp<N, T>, ann: T) -> Self {
        AExp::Assert(Box::new(b), ann)
    }
    pub fn verify(b: BExp<N, T>, ann: T) -> Self {
        AExp::Verify(Box::new(b), ann)
    }
    pub fn letx(a: Vid, d: Self, ann: T) -> Self {
        AExp::Let(a, Box::new(d), ann)
    }
    pub fn logx(a: Vid, d: Self, ann: T) -> Self {
        AExp::Log(a, Box::new(d), ann)
    }
}

/// Constructors for un-annotated, untyped expressions with symbolic sizes
impl UAExp {
    /// Unannotated constructors
    pub fn ulit(v: i32) -> Self {
        AExp::Lit(v, Nothing)
    }
    pub fn ubin(op: BinOp, l: Self, r: Self) -> Self {
        AExp::bin(op, l, r, Nothing)
    }
    pub fn ugen(t: Tid) -> Self {
        AExp::gen(t, Nothing)
    }
    pub fn ucoef(a: Self) -> Self {
        AExp::coef(a, Nothing)
    }
    pub fn umle(a: Self) -> Self {
        AExp::mle(a, Nothing)
    }
    pub fn uinterpolate(e: Self, d: Self) -> Self {
        AExp::interpolate(e, d, Nothing)
    }
    pub fn uchallenge(t: Typ<Size>) -> Self {
        AExp::challenge(t, Nothing)
    }
    pub fn urandom(t: Typ<Size>) -> Self {
        AExp::random(t, Nothing)
    }
    pub fn uvec(v: Vec<Self>) -> Self {
        AExp::Vec(v, Nothing)
    }
    pub fn uconcat(a: Self, b: Self) -> Self {
        AExp::concat(a, b, Nothing)
    }
    pub fn umap(l: Self, id: Vid, r: Self) -> Self {
        AExp::map(l, id,  r, Nothing)
    }
    pub fn uram(v: Self, i: Self) -> Self {
        AExp::ram(v, i, Nothing)
    }
    pub fn urange(r: Range<Size>) -> Self {
        AExp::Range(r, Nothing)
    }
    pub fn uadd(l: Self, r: Self) -> Self {
        AExp::Bin(BinOp::Add, Box::new(l), Box::new(r), Nothing)
    }
    pub fn usub(l: Self, r: Self) -> Self {
        AExp::Bin(BinOp::Sub, Box::new(l), Box::new(r), Nothing)
    }
    pub fn umul(l: Self, r: Self) -> Self {
        AExp::Bin(BinOp::Mul, Box::new(l), Box::new(r), Nothing)
    }
    pub fn udiv(l: Self, r: Self) -> Self {
        AExp::Bin(BinOp::Div, Box::new(l), Box::new(r), Nothing)
    }
    pub fn upow(l: Self, r: Self) -> Self {
        AExp::Bin(BinOp::Pow, Box::new(l), Box::new(r), Nothing)
    }
    pub fn udot(l: Self, r: Self) -> Self {
        AExp::Bin(BinOp::Dot, Box::new(l), Box::new(r), Nothing)
    }
    pub fn uvar(x: Vid) -> Self {
        AExp::Var(x, Nothing)
    }
    pub fn uvarstr<'a>(x: &'a str) -> Self {
        AExp::uvar(Vid::from(x))
    }
    pub fn uapp(e: Fid, d: UAExps) -> Self {
        AExp::App(e, d, Nothing)
    }
    pub fn ureduce(op: BinOp, d: Self) -> Self {
        AExp::Reduce(op, Box::new(d), Nothing)
    }
    pub fn uassert(b: BExp<Size, Nothing>) -> Self {
        AExp::Assert(Box::new(b), Nothing)
    }
    pub fn uverify(b: BExp<Size, Nothing>) -> Self {
        AExp::Verify(Box::new(b), Nothing)
    }
    pub fn uletx(a: Vid, d: Self) -> Self {
        AExp::Let(a, Box::new(d), Nothing)
    }
    pub fn ulogx(a: Vid, d: Self)  -> Self {
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
            AExp::Lit(p, t) =>
                allocator.text(p.to_string())
                .append(" ⇝ ")
                .append(t.pretty(allocator)),
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
            AExp::Reduce(op, d, t) => allocator.concat([
                allocator.text("reduce("),
                op.pretty(allocator),
                allocator.text(", "),
                (*d).pretty(allocator),
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
        UAExp::uadd(self, rhs)
    }
}

impl Sub for UAExp {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self {
        UAExp::usub(self, rhs)
    }
}

impl Mul for UAExp {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self {
        UAExp::umul(self, rhs)
    }
}

impl Div for UAExp {
    type Output = Self;

    fn div(self, rhs: Self) -> Self {
        UAExp::udiv(self, rhs)
    }
}

impl From<i32> for UAExp {
    fn from(x: i32) -> Self {
        UAExp::ulit(x)
    }
}

impl From<Vid> for UAExp {
    fn from(x: Vid) -> Self {
        UAExp::uvar(x)
    }
}

impl From<&str> for UAExp {
    fn from(x: &str) -> Self {
        UAExp::uvarstr(x)
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
                Rule::id => Ok(AExp::uvar(Vid(pair.as_str().to_string()))),
                Rule::positive => Ok(AExp::ulit(pair.as_str().parse().unwrap())),
                Rule::gen_exp => Ok(AExp::ugen(Tid::from_pest(&mut pair.into_inner())?)),
                Rule::coef_exp => Ok(AExp::ucoef(AExp::from_pest(&mut pair.into_inner())?)),
                Rule::mle_exp => Ok(AExp::umle(AExp::from_pest(&mut pair.into_inner())?)),
                Rule::interp_exp => {
                    let mut inner = pair.into_inner();
                    Ok(AExp::uinterpolate(
                        AExp::from_pest(&mut Pairs::single(inner.next().unwrap()))?,
                        AExp::from_pest(&mut Pairs::single(inner.next().unwrap()))?
                    ))
                },
                Rule::challenge_exp =>
                    Ok(AExp::uchallenge(Typ::from_pest(&mut pair.into_inner())?)),
                Rule::random_exp =>
                    Ok(AExp::urandom(Typ::from_pest(&mut pair.into_inner())?)),
                Rule::vec_exp => {
                    let inner = pair.into_inner();
                    let mut ve = Vec::new();
                    for x in inner {
                        ve.push(AExp::from_pest(&mut Pairs::single(x))?);
                    }
                    Ok(AExp::uvec(ve))
                },
                Rule::map_exp => {
                    let mut inner = pair.into_inner();
                    Ok(AExp::umap(
                        AExp::from_pest(&mut Pairs::single(inner.next().unwrap()))?,
                        Vid::from_pest(&mut Pairs::single(inner.next().unwrap()))?,
                        AExp::from_pest(&mut Pairs::single(inner.next().unwrap()))?
                    ))
                },
                Rule::ram_exp => {
                    let mut inner = pair.into_inner();
                    Ok(AExp::uram(
                        AExp::uvar(Vid::from_pest(&mut Pairs::single(inner.next().unwrap()))?),
                        AExp::from_pest(&mut Pairs::single(inner.next().unwrap()))?
                    ))
                },
                Rule::app_exp => {
                    let mut inner = pair.into_inner();
                    // Call a function
                    let func = Fid::from_pest(&mut inner)?;
                    // Arguments
                    let params = AExps::from_pest(&mut inner)?;
                    Ok(AExp::uapp(func, params))
                },
                Rule::reduce_exp => {
                    let mut inner = pair.into_inner();
                    Ok(AExp::ureduce(
                        BinOp::from_pest(&mut Pairs::single(inner.next().unwrap()))?,
                        AExp::from_pest(&mut Pairs::single(inner.next().unwrap()))?
                    ))
                },
                Rule::assert_exp => {
                    let mut inner = pair.into_inner();
                    Ok(AExp::uassert(BExp::from_pest(&mut Pairs::single(inner.next().unwrap()))?))
                },
                Rule::verify_exp => {
                    let mut inner = pair.into_inner();
                    dbg!(&inner);
                    Ok(AExp::uverify(
                        BExp::from_pest(&mut Pairs::single(inner.next().unwrap()))?,
                    ))
                },
                Rule::let_exp => {
                    let mut inner = pair.into_inner();
                    Ok(AExp::uletx(
                        Vid::from_pest(&mut Pairs::single(inner.next().unwrap()))?,
                        AExp::from_pest(&mut Pairs::single(inner.next().unwrap()))?
                    ))
                },
                Rule::log_exp => {
                    let mut inner = pair.into_inner();
                    Ok(AExp::ulogx(
                        Vid::from_pest(&mut Pairs::single(inner.next().unwrap()))?,
                        AExp::from_pest(&mut Pairs::single(inner.next().unwrap()))?
                    ))
                },
                Rule::aexp => AExp::from_pest(&mut pair.into_inner()),
                Rule::range_exp => Ok(AExp::urange(Range::from_pest(&mut pair.into_inner())?)),
                _ => Err(ConversionError::Malformed(InputError::UnexpectedExp(pair)))
            })
            .map_infix(|lhs, op, rhs|
                match op.clone().as_rule() {
                    Rule::add_op => Ok(AExp::uadd(lhs?, rhs?)),
                    Rule::sub_op => Ok(AExp::usub(lhs?, rhs?)),
                    Rule::mul_op => Ok(AExp::umul(lhs?, rhs?)),
                    Rule::div_op => Ok(AExp::udiv(lhs?, rhs?)),
                    Rule::pow_op => Ok(AExp::upow(lhs?, rhs?)),
                    Rule::dot_op => Ok(AExp::udot(lhs?, rhs?)),
                    Rule::concat_op => Ok(AExp::uconcat(lhs?, rhs?)),
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
    assert_eq!(UAExp::from_pest(&mut pairs), Ok(AExp::ulit(2)));
}

#[test]
fn parser_var() {
    let ex = "x";
    let mut pairs = ZippelParser::parse(Rule::aexp, ex).unwrap();
    assert_eq!(UAExp::from_pest(&mut pairs), Ok(AExp::uvarstr("x")));
}

#[test]
fn parser_bin() {
    // Add
    let ex1 = "x + 2";
    let mut pairs = ZippelParser::parse(Rule::aexp, ex1).unwrap();
    assert_eq!(
        UAExp::from_pest(&mut pairs),
        Ok(AExp::uvarstr("x") + AExp::ulit(2))
    );

    // Sub
    let ex2 = "x - 2";
    let mut pairs = ZippelParser::parse(Rule::aexp, ex2).unwrap();
    assert_eq!(
        UAExp::from_pest(&mut pairs),
        Ok(AExp::uvarstr("x") - AExp::ulit(2))
    );

    // Mul
    let ex3 = "x * 2";
    let mut pairs = ZippelParser::parse(Rule::aexp, ex3).unwrap();
    assert_eq!(
        AExp::from_pest(&mut pairs),
        Ok(AExp::uvarstr("x") * AExp::ulit(2))
    );

    // Div
    let ex4 = "x / 2";
    let mut pairs = ZippelParser::parse(Rule::aexp, ex4).unwrap();
    assert_eq!(
        UAExp::from_pest(&mut pairs),
        Ok(AExp::uvarstr("x") / AExp::ulit(2))
    );

    // Pow
    let ex6 = "x ^ 2";
    let mut pairs = ZippelParser::parse(Rule::aexp, ex6).unwrap();
    assert_eq!(
        UAExp::from_pest(&mut pairs),
        Ok(AExp::upow(AExp::uvarstr("x"), AExp::ulit(2)))
    );
}

#[test]
fn parser_interpolate() {
    let ex = "interpolate(x + 2, 4*x)";
    let mut pairs = ZippelParser::parse(Rule::aexp, ex).unwrap();
    assert_eq!(
        UAExp::from_pest(&mut pairs),
        Ok(AExp::uinterpolate(
            AExp::uvarstr("x") + AExp::ulit(2),
            AExp::ulit(4) * AExp::uvarstr("x")
        ))
    );
}

#[test]
fn parser_call_two() {
    let ex = "f(x + 2, x)";
    let mut pairs = ZippelParser::parse(Rule::aexp, ex).unwrap();
    assert_eq!(
        UAExp::from_pest(&mut pairs),
        Ok(AExp::uapp(
            Fid::from("f"),
            AExps(vec![AExp::uvarstr("x") + AExp::ulit(2), AExp::uvarstr("x")])
        ))
    );
}

#[test]
fn parser_range() {
    let ex = "0..N";
    let mut pairs = ZippelParser::parse(Rule::aexp, ex).unwrap();
    assert_eq!(
        UAExp::from_pest(&mut pairs),
        Ok(AExp::urange(Range::new(Size::from(0), Size::from(1), Size::from("N"))))
    );
}

#[test]
fn parser_for() {
    let ex = "[ 3^i for i in 0..N ]";
    let mut pairs = ZippelParser::parse(Rule::aexp, ex).unwrap();
    assert_eq!(
        UAExp::from_pest(&mut pairs),
        Ok(AExp::umap(
            AExp::upow(AExp::ulit(3), AExp::uvarstr("i")),
            Vid::from("i"),
            AExp::urange(Range::new(Size::from(0), Size::from(1), Size::from("N")))
        ))
    );
}

#[test]
fn parser_random() {
    let ex = "random<Uni<A, 2>>";
    let mut pairs = ZippelParser::parse(Rule::aexp, ex).unwrap();
    assert_eq!(
        UAExp::from_pest(&mut pairs),
        Ok(AExp::urandom(Typ::uni(Tid::from("A"), Size::from(2))))
    );
}

#[test]
fn parser_challenge() {
    let ex = "challenge<F>";
    let mut pairs = ZippelParser::parse(Rule::aexp, ex).unwrap();
    assert_eq!(UAExp::from_pest(&mut pairs), Ok(AExp::uchallenge(Typ::varstr("F"))));
}

#[test]
fn parser_concat() {
    let ex = "(x + 2) ++ x";
    let mut pairs = ZippelParser::parse(Rule::aexp, ex).unwrap();
    assert_eq!(
        UAExp::from_pest(&mut pairs),
        Ok(AExp::uconcat(
            AExp::uvarstr("x") + AExp::ulit(2),
            AExp::uvarstr("x")
        ))
    );
}

#[test]
fn parser_reduce() {
    let ex = "reduce(+, [1,2,3])";
    let mut pairs = ZippelParser::parse(Rule::aexp, ex).unwrap();
    assert_eq!(
        UAExp::from_pest(&mut pairs),
        Ok(AExp::ureduce(
            BinOp::Add,
            AExp::uvec(vec![AExp::ulit(1), AExp::ulit(2), AExp::ulit(3)])
        ))
    );
}

#[test]
fn parser_let() {
    let ex = "let x = 2";
    let mut pairs = ZippelParser::parse(Rule::aexp, ex).unwrap();
    assert_eq!(
        UAExp::from_pest(&mut pairs),
        Ok(AExp::uletx(
            Vid::from("x"),
            AExp::ulit(2)
        ))
    );
}

#[test]
fn parser_log() {
    let ex = "x <- 2";
    let mut pairs = ZippelParser::parse(Rule::aexp, ex).unwrap();
    assert_eq!(
        UAExp::from_pest(&mut pairs),
        Ok(AExp::ulogx(
            Vid::from("x"),
            AExp::ulit(2),
        ))
    );
}

#[test]
fn parser_assert() {
    let ex = "assert(x == 2)";
    let mut pairs = ZippelParser::parse(Rule::aexp, ex).unwrap();
    assert_eq!(
        UAExp::from_pest(&mut pairs),
        Ok(AExp::uassert(
            BExp::ueq(AExp::uvarstr("x"), AExp::ulit(2)),
        ))
    );
}

#[test]
fn parser_verify() {
    let ex = "verify(x == 2)";
    let mut pairs = ZippelParser::parse(Rule::aexp, ex).unwrap();
    assert_eq!(
        UAExp::from_pest(&mut pairs),
        Ok(AExp::uverify(
            BExp::ueq(AExp::uvarstr("x"), AExp::ulit(2)),
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
            AExp::ulogx(Vid::from("x"), AExp::ulit(2)),
            AExp::ulogx(Vid::from("y"), AExp::ulit(3)),
            AExp::uletx(Vid::from("x"), AExp::ulit(2) * AExp::ulit(4))
        ]))
    );
}
