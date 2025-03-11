use std::ops::{Add, Div, Mul, Sub, BitXor};
use crate::parser::*;
use from_pest::{ConversionError, FromPest};
use lazy_static::lazy_static;
use std::fmt;
use pest::iterators::Pairs;
use pest::pratt_parser::{Assoc, Op, PrattParser};

use share::traversal::ToTraversal1;

use share::{Set, BoxAllocator, Pretty, DocAllocator, DocBuilder};
use crate::typ::Size;
use crate::typ::range::{Range, RangeTraversal};
use crate::id::{Gen, Tid, TidSubst, Fid, Vid};

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
/// It is parameterized by types `N` representing the sizes of ranges, indices etc
#[derive(Debug, PartialEq, Eq, Clone, PartialOrd, Ord)]
pub enum Exp<N> {
    ///     Numeric literal
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let a = 5;
    ///     ```
    Lit(N),

    ///     Generator of a group [Tid]
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let g = gen<G>;
    ///     ```
    Gen(Tid),

    ///     Variable reference
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let b = a;
    ///     ```
    Var(Vid),

    ///     Function application
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let result1 = f(x + 2, x)
    ///     ```
    App(Fid, Exps<N>),

    ///     Coefficients of a univariate vector
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let v = coef [1,2,1]; // 1 + 2x + x^2
    ///     ```
    Coef(Box<Exp<N>>),

    ///     Multilinear extension of a matrix, polynomial, etc.
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let g = mle x;
    ///     ```
    Mle(Box<Exp<N>>),

    ///     A vector of elements
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let v = [1, 2*x, x+y];
    ///     ```
    Vec(Exps<N>),

    ///     Binary operation
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let sum = 2 + 3;
    ///     ```
    Bin(BinOp, Box<Exp<N>>, Box<Exp<N>>),

    ///     **Zippel Code:**
    ///     ```zippel
    ///     let r = 0..5;
    ///     ```
    Range(Range<N>),

    ///     Map comprehension
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let squares = [x^2 for x in 0,2..10];
    ///     ```
    Map(Box<Exp<N>>, Vid, Box<Exp<N>>),

    ///     Random access or slice a vector
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let first = v[0]
    ///     ```
    Ram(Box<Exp<N>>, Box<Exp<N>>),

    ///     Sample pseudo-random number generator
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let r := random<F>();
    ///     ```
    Random(Tid),

    ///     Random oracle challenge.
    ///     **Zippel Code:**
    ///     ```zippel
    ///     r <- challenge<F>();
    ///     ```
    Challenge(Tid),

    ///     Convert from evaluation domain to lagrange domain.
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let p = interpolate([1, 2], [0, 3]);
    ///     ```
    Interpolate(Box<Exp<N>>, Box<Exp<N>>),

    ///     Represents inclusion of an element in a vector
    ///
    ///     **Zippel Code:**
    ///     ```zippel
    ///     assert(x in v);
    ///     ```
    Contains(Box<Exp<N>>, Box<Exp<N>>),

    ///     Represents the equality comparison between two arithmetic expressions.
    ///
    ///     **Zippel Code:**
    ///     ```zippel
    ///     verify(5 == 5);
    ///     ```
    Equ(Box<Exp<N>>, Box<Exp<N>>),

    ///     Represents the logical AND of two boolean expressions.
    ///
    ///     **Zippel Code:**
    ///     ```zippel
    ///     assert(true && false);
    ///     ```
    And(Box<Exp<N>>, Box<Exp<N>>),

    ///     Represents the logical OR of two boolean expressions.
    ///
    ///     **Zippel Code:**
    ///     ```zippel
    ///     verify(true || false);
    ///     ```
    Or(Box<Exp<N>>, Box<Exp<N>>),

    ///     Represents the negation of a boolean expression.
    ///
    ///     **Zippel Code:**
    ///     ```zippel
    ///     assert(!true);
    ///     ```
    Not(Box<Exp<N>>),

    ///     Represents a let-expression, which binds a value to an identifier.
    ///
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let x = 5 + 3;
    ///     assert(5 == 3);
    ///     ```
    Let(Option<Vid>, Box<Exp<N>>, Box<Exp<N>>),

    ///     Represents a log-let expression with transcript dependency.
    ///     This variant is used to bind a value to an identifier while logging the operation.
    ///     **Zippel Code:**
    ///     ```zippel
    ///     p <- interpolate(v, [0,1,2])
    ///     ```
    Log(Vid, Box<Exp<N>>, Box<Exp<N>>),

    ///     Prover assertion followed by expression.
    ///     **Zippel Code:**
    ///     ```zippel
    ///     assert(1 == 1);
    ///     ...
    ///     ```
    Assert(Box<Exp<N>>),

    ///     Verifier check followed by expression.
    ///     **Zippel Code:**
    ///     ```zippel
    ///     verify(a == a);
    ///     ...
    ///     ```
    Verify(Box<Exp<N>>)
}

/// Free variables
pub trait FreeVars {
    fn freevars(&self) -> Set<Vid>;
}

/// Traverse VIDs
pub trait ExpSubst : FreeVars + Sized {
    fn subst(&mut self, from: &Vid, to: &CExp, ctx: &mut Set<Vid>);
    fn shift(&mut self, from: &Vid, ctx: &mut Set<Vid>) {
        self.subst(from, &CExp::Var(Vid::gen(from, ctx)), ctx);
    }
}

#[derive(Debug, PartialEq, Eq, Clone, PartialOrd, Ord)]
pub struct Exps<N>(pub Vec<Exp<N>>);

/// Symbolic sized AST node, as parsed from input
pub type UExp = Exp<Size>;

/// Concrete size untyped AST node
pub type CExp = Exp<usize>;

/// Symbolic sized AST sequence, as parsed from input
pub type UExps = Exps<Size>;

/// Concrete size untyped AST node
pub type CExps = Exps<usize>;

/// How to traverse the first type parameter [N] for Exp<N>
impl<N> ToTraversal1<N> for Exp<N> {
    type Output<Z> = Exp<Z>;
    fn traverse1<Z, E>(self, f: &mut dyn FnMut(N) -> Result<Z, E>) -> Result<Exp<Z>, E> {
        match self {
            Exp::Lit(x) => Ok(Exp::Lit(f(x)?)),
            Exp::Var(v) => Ok(Exp::Var(v)),
            Exp::Coef(box p) => Ok(Exp::Coef(Box::new(p.traverse1(f)?))),
            Exp::Mle(box p) => Ok(Exp::Mle(Box::new(p.traverse1(f)?))),
            Exp::Vec(v) =>
                Ok(Exp::Vec(v.traverse1(f)?)),
            Exp::App(x, ts) =>
                Ok(Exp::App(x, ts.traverse1(f)?)),
            Exp::Bin(op, box x, box y) =>
                Ok(Exp::Bin(
                    op,
                    Box::new(x.traverse1(f)?),
                    Box::new(y.traverse1(f)?),
                )),
            Exp::Map(box x, id, box r) =>
                Ok(Exp::Map(Box::new(x.traverse1(f)?), id, Box::new(r.traverse1(f)?))),
            Exp::Challenge(t) => Ok(Exp::Challenge(t)),
            Exp::Random(t) => Ok(Exp::Random(t)),
            Exp::Gen(t) => Ok(Exp::Gen(t)),
            Exp::Range(r) => Ok(Exp::Range(r.traverse1(f)?)),
            Exp::Interpolate(box x, box y) =>
                Ok(Exp::Interpolate(
                    Box::new(x.traverse1(f)?),
                    Box::new(y.traverse1(f)?)
                )),
            Exp::Ram(box x, box i) =>
                Ok(Exp::Ram(
                        Box::new(x.traverse1(f)?),
                        Box::new(i.traverse1(f)?)
                )),
            Exp::Equ(a, b) =>
                Ok(Exp::Equ(a.traverse1(&mut |x| x.traverse1(f))?, b.traverse1(&mut |x| x.traverse1(f))?)),
            Exp::Contains(a, b) =>
                Ok(Exp::Contains(a.traverse1(&mut |x| x.traverse1(f))?, b.traverse1(&mut |x| x.traverse1(f))?)),
            Exp::And(a, b) =>
                Ok(Exp::And(a.traverse1(&mut |x| x.traverse1(f))?, b.traverse1(&mut |x| x.traverse1(f))?)),
            Exp::Or(a, b) =>
                Ok(Exp::Or(a.traverse1(&mut |x| x.traverse1(f))?, b.traverse1(&mut |x| x.traverse1(f))?)),
            Exp::Not(a) => Ok(Exp::Not(a.traverse1(&mut |x| x.traverse1(f))?)),
            Exp::Let(x, box a, box b) =>
                Ok(Exp::Let(x, Box::new(a.traverse1(f)?), Box::new(b.traverse1(f)?))),
            Exp::Log(x, box a, box b) =>
                Ok(Exp::Log(x, Box::new(a.traverse1(f)?), Box::new(b.traverse1(f)?))),
            Exp::Assert(box x) =>
                Ok(Exp::Assert(Box::new(x.traverse1(f)?))),
            Exp::Verify(box x) =>
                Ok(Exp::Verify(Box::new(x.traverse1(f)?)))
        }
    }
}

/// How to traverse the first type parameter [N] for Exps<N>
impl<N> ToTraversal1<N> for Exps<N> {
    type Output<Z> = Exps<Z>;
    fn traverse1<Z, E>(self, f: &mut dyn FnMut(N) -> Result<Z, E>) -> Result<Exps<Z>, E> {
        Ok(Exps(self.0.into_iter().map(|x| x.traverse1(f)).collect::<Result<_, _>>()?))
    }
}

/// Traverse [Tid] inside [TExp]
impl TidSubst for CExp {
    fn tid_subst(&mut self, from: &Tid, to: &Tid) {
        match self {
            Exp::Challenge(t) if t == from => *t = to.clone(),
            Exp::Random(t) if t == from => *t = to.clone(),
            Exp::Gen(t) if t == from => *t = to.clone(),
            Exp::Coef(box p)
            | Exp::Mle(box p)
            | Exp::Assert(box p)
            | Exp::Verify(box p)
            | Exp::Not(box p) => p.tid_subst(from, to),
            Exp::Vec(v)
            | Exp::App(_, v) => v.tid_subst(from, to),
            Exp::Bin(_, box a, box b)
            | Exp::Map(box a, _, box b)
            | Exp::Interpolate(box a, box b)
            | Exp::Ram(box a, box b)
            | Exp::Equ(box a, box b)
            | Exp::And(box a, box b)
            | Exp::Or(box a, box b)
            | Exp::Contains(box a, box b)
            | Exp::Let(_, box a, box b)
            | Exp::Log(_, box a, box b) => {
                a.tid_subst(from, to);
                b.tid_subst(from, to);
            },
            Exp::Lit(_) | Exp::Var(_) | Exp::Range(_)
            | Exp::Challenge(_) | Exp::Random(_) | Exp::Gen(_) => {}
        }
    }
}

impl TidSubst for CExps {
    fn tid_subst(&mut self, from: &Tid, to: &Tid) {
        self.0.iter_mut().for_each(|x| x.tid_subst(from, to))
    }
}

impl FreeVars for CExp {
    fn freevars(&self) -> Set<Vid> {
        match self {
            Exp::Var(id) => Set::singleton(id.clone()),
            Exp::Challenge(_) | Exp::Random(_) | Exp::Gen(_) | Exp::Lit(_) | Exp::Range(_) => Set::new(),
            Exp::Coef(box p) | Exp::Mle(box p) | Exp::Assert(box p) | Exp::Verify(box p) | Exp::Not(box p) => p.freevars(),
            Exp::Vec(v) | Exp::App(_, v) => v.freevars(),
            Exp::Bin(_, box a, box b)
                | Exp::Interpolate(box a, box b)
                | Exp::Ram(box a, box b)
                | Exp::Equ(box a, box b)
                | Exp::And(box a, box b)
                | Exp::Or(box a, box b)
                | Exp::Contains(box a, box b)
                | Exp::Map(box a, _, box b)
                | Exp::Let(_, box a, box b)
                | Exp::Log(_, box a, box b) => a.freevars().union(b.freevars()),
        }
    }
}

impl ExpSubst for CExp {
    fn subst(&mut self, from: &Vid, to: &CExp, ctx: &mut Set<Vid>) {
        match self {
            Exp::Var(id) if id == from => *self = to.clone(),
            Exp::Var(_) | Exp::Challenge(_) | Exp::Random(_)
            | Exp::Gen(_) | Exp::Lit(_) | Exp::Range(_) => {},
            Exp::Coef(box p)
            | Exp::Mle(box p)
            | Exp::Assert(box p)
            | Exp::Verify(box p)
            | Exp::Not(box p) => p.subst(from, to, ctx),
            Exp::Vec(v)
            | Exp::App(_, v) => v.subst(from, to, ctx),
            Exp::Bin(_, box a, box b)
            | Exp::Interpolate(box a, box b)
            | Exp::Ram(box a, box b)
            | Exp::Equ(box a, box b)
            | Exp::And(box a, box b)
            | Exp::Or(box a, box b)
            | Exp::Let(None, box a, box b)
            | Exp::Contains(box a, box b) => {
                a.subst(from, to, ctx);
                b.subst(from, to, ctx);
            },
            Exp::Map(box l, id, box r) =>
                if id == from {
                    // Shadowing
                    r.subst(from, to, ctx);
                } else if to.freevars().contains(id) {
                    // Capturing, shift [id] in [l]
                    r.subst(from, to, ctx);
                    let nid = Vid::gen(&id, ctx);
                    l.subst(&id, &CExp::var(&nid), ctx);
                    ctx.insert(nid.clone());
                    l.subst(from, to, ctx);
                } else {
                    // No shadowing or capturing
                    r.subst(from, to, ctx);
                    ctx.insert(id.clone());
                    l.subst(from, to, ctx);
                }
            Exp::Let(Some(id), box a, box b)
            | Exp::Log(id, box a, box b) =>
                if id == from {
                    // Shadowing
                    a.subst(from, to, ctx);
                } else if to.freevars().contains(id) {
                    // Capturing, shift [x] in [a]
                    a.subst(from, to, ctx);
                    let nid = Vid::gen(&id, ctx);
                    b.subst(&id, &CExp::var(&nid), ctx);
                    ctx.insert(nid.clone());
                    b.subst(from, to, ctx);
                } else {
                    // No shadowing or capturing
                    a.subst(from, to, ctx);
                    ctx.insert(id.clone());
                    b.subst(from, to, ctx);
                }
        }
    }
}

impl ExpSubst for CExps {
    fn subst(&mut self, from: &Vid, to: &CExp, ctx: &mut Set<Vid>) {
        self.0.iter_mut().for_each(|x| x.subst(from, to, ctx))
    }
}

impl FreeVars for CExps {
    fn freevars(&self) -> Set<Vid> {
        self.0.iter().map(|x| x.freevars()).fold(Set::new(), |acc, x| acc.union(x))
    }
}

/// How to traverse [Range] inside an [Exp]
impl<N> RangeTraversal<N> for Exp<N> {
    fn range_traverse<E>(self, f: &mut dyn FnMut(Range<N>) -> Result<Range<N>, E>) -> Result<Self, E> {
        match self {
            Exp::Range(r) => Ok(Exp::Range(f(r)?)),
            Exp::Coef(box p) => Ok(Exp::coef(p.range_traverse(f)?)),
            Exp::Mle(box p) => Ok(Exp::mle(p.range_traverse(f)?)),
            Exp::Vec(v) =>
                Ok(Exp::Vec(v.range_traverse(f)?)),
            Exp::Bin(op, box x, box y) =>
                Ok(Exp::bin(op, x.range_traverse(f)?, y.range_traverse(f)?)),
            Exp::Map(box x, id, box r) =>
                Ok(Exp::map(x.range_traverse(f)?, id,r.range_traverse(f)?)),
            Exp::Ram(box x, box i) =>
                Ok(Exp::ram(x.range_traverse(f)?, i.range_traverse(f)?)),
            Exp::Interpolate(box x, box y) =>
                Ok(Exp::interpolate(x.range_traverse(f)?, y.range_traverse(f)?)),
            Exp::Equ(box a, box b) =>
                Ok(Exp::equ(a.range_traverse(f)?, b.range_traverse(f)?)),
            Exp::Contains(box a, box b) =>
                Ok(Exp::contains(a.range_traverse(f)?, b.range_traverse(f)?)),
            Exp::And(box a, box b) =>
                Ok(Exp::and(a.range_traverse(f)?, b.range_traverse(f)?)),
            Exp::Or(box a, box b) =>
                Ok(Exp::or(a.range_traverse(f)?, b.range_traverse(f)?)),
            Exp::Not(box a) =>
                Ok(Exp::not(a.range_traverse(f)?)),
            Exp::Let(Some(x), box t, box e) => Ok(Exp::letx(x, t.range_traverse(f)?, e.range_traverse(f)?)),
            Exp::Log(x, box t, box e) => Ok(Exp::logx(x, t.range_traverse(f)?, e.range_traverse(f)?)),
            Exp::Let(None, box t, box e) => Ok(Exp::seq(t.range_traverse(f)?, e.range_traverse(f)?)),
            Exp::Assert(box x) => Ok(Exp::assert(x.range_traverse(f)?)),
            Exp::Verify(box x) => Ok(Exp::verify(x.range_traverse(f)?)),
            Exp::App(x, ts) => Ok(Exp::app(x, ts.range_traverse(f)?)),
            other => Ok(other)
        }
    }
}

impl<N> RangeTraversal<N> for Exps<N> {
    fn range_traverse<E>(self, f: &mut dyn FnMut(Range<N>) -> Result<Range<N>, E>) -> Result<Self, E> {
        Ok(Exps(self.0.traverse1(&mut |x| x.range_traverse(f))?))
    }
}

impl<N> Exps<N> {
    pub fn iter(&self) -> std::slice::Iter<Exp<N>> {
        self.0.iter()
    }
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
    pub fn len(&self) -> usize {
        self.0.len()
    }
    // Parser guarantees that the vector is non-empty
    pub fn last(&self) -> &Exp<N> {
        self.0.last().unwrap()
    }
}

impl<N> IntoIterator for Exps<N> {
    type Item = Exp<N>;
    type IntoIter = std::vec::IntoIter<Exp<N>>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<N> FromIterator<Exp<N>> for Exps<N> {
    fn from_iter<I: IntoIterator<Item = Exp<N>>>(iter: I) -> Self {
        Exps(iter.into_iter().collect())
    }
}

impl<const N: usize, T> From<[Exp<T>; N]> for Exps<T> {
    fn from(arr: [Exp<T>; N]) -> Self {
        Exps(arr.into())
    }
}

/// Construct untyped expressions
impl<N> Exp<N> {
    pub fn from_vec(a: Self, ts: &[Self]) -> Self where N: Clone {
        ts.into_iter().fold(a, |acc, a| Exp::seq(acc, a.clone()))
    }
    /// Annotated constructors
    pub fn lit(v: N) -> Self {
        Exp::Lit(v)
    }
    pub fn bin(op: BinOp, l: Self, r: Self) -> Self {
        Exp::Bin(op, Box::new(l), Box::new(r))
    }
    pub fn gen(t: Tid) -> Self {
        Exp::Gen(t)
    }
    pub fn coef(a: Self) -> Self {
        Exp::Coef(Box::new(a))
    }
    pub fn mle(a: Self) -> Self {
        Exp::Mle(Box::new(a))
    }
    pub fn interpolate(e: Self, d: Self) -> Self {
        Exp::Interpolate(Box::new(e), Box::new(d))
    }
    pub fn challenge(t: Tid) -> Self {
        Exp::Challenge(t)
    }
    pub fn random(t: Tid) -> Self {
        Exp::Random(t)
    }
    pub fn vec(v: Vec<Self>) -> Self {
        Exp::Vec(Exps(v))
    }
    pub fn map(l: Self, x: Vid, range: Self) -> Self {
        Exp::Map(Box::new(l), x, Box::new(range))
    }
    pub fn ram(v: Self, i: Self) -> Self {
        Exp::Ram(Box::new(v), Box::new(i))
    }
    pub fn range(r: Range<N>) -> Self {
        Exp::Range(r)
    }
    pub fn add(l: Self, r: Self) -> Self {
        Exp::Bin(BinOp::Add, Box::new(l), Box::new(r))
    }
    pub fn sub(l: Self, r: Self) -> Self {
        Exp::Bin(BinOp::Sub, Box::new(l), Box::new(r))
    }
    pub fn mul(l: Self, r: Self) -> Self {
        Exp::Bin(BinOp::Mul, Box::new(l), Box::new(r))
    }
    pub fn div(l: Self, r: Self) -> Self {
        Exp::Bin(BinOp::Div, Box::new(l), Box::new(r))
    }
    pub fn pow(l: Self, r: Self) -> Self {
        Exp::Bin(BinOp::Pow, Box::new(l), Box::new(r))
    }
    pub fn dot(l: Self, r: Self) -> Self {
        Exp::Bin(BinOp::Dot, Box::new(l), Box::new(r))
    }
    pub fn concat(l: Self, r: Self) -> Self {
        Exp::Bin(BinOp::Concat, Box::new(l), Box::new(r))
    }
    pub fn var(x: &Vid) -> Self {
        Exp::Var(x.clone())
    }
    pub fn varstr<'a>(x: &'a str) -> Self {
        Exp::Var(Vid::from(x))
    }
    pub fn assert(b: Exp<N>) -> Self {
        Exp::Assert(Box::new(b))
    }
    pub fn verify(b: Exp<N>) -> Self {
        Exp::Verify(Box::new(b))
    }
    pub fn letx(a: Vid, d: Self, e: Self) -> Self {
        Exp::Let(Some(a), Box::new(d), Box::new(e))
    }
    pub fn logx(a: Vid, d: Self, e: Self) -> Self {
        Exp::Log(a, Box::new(d), Box::new(e))
    }
    pub fn seq(a: Self, b: Self) -> Self {
        Exp::Let(None, Box::new(a), Box::new(b))
    }
    pub fn and(l: Self, r: Self) -> Self {
        Exp::And(Box::new(l), Box::new(r))
    }
    pub fn or(l: Self, r: Self) -> Self {
        Exp::Or(Box::new(l), Box::new(r))
    }
    pub fn equ(l: Exp<N>, r: Exp<N>) -> Self {
        Exp::Equ(Box::new(l), Box::new(r))
    }
    pub fn app(id: Fid, args: Exps<N>) -> Self {
        Exp::App(id, args)
    }
    pub fn contains(a: Exp<N>, b: Exp<N>) -> Self {
        Exp::Contains(Box::new(a), Box::new(b))
    }
    pub fn not(a: Self) -> Self {
        Exp::Not(Box::new(a))
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

/// Pretty printer instance for typed Exp
impl<'a, D, A, N> Pretty<'a, D, A> for Exp<N>
where
    D: DocAllocator<'a, A>,
    D::Doc: Clone,
    N: Pretty<'a, D, A>,
    A: 'a + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        match self {
            Exp::Lit(p) => p.pretty(allocator),
            Exp::Coef(p) => allocator.concat([
                allocator.text("coef "),
                p.pretty(allocator),
            ]),
            Exp::Mle(p) => allocator.concat([
                allocator.text("mle "),
                p.pretty(allocator),
            ]),
            Exp::Vec(ts) => allocator.concat([
                allocator.text("["),
                allocator.intersperse(ts.into_iter().map(|x| x.pretty(allocator)), ", "),
                allocator.text("]"),
            ]),
            Exp::Bin(op, a, b) => allocator.concat([
                (*a).pretty(allocator),
                op.pretty(allocator),
                (*b).pretty(allocator),
            ]),
            Exp::Map(x, id, range) => allocator.concat([
                allocator.text("["),
                x.pretty(allocator),
                allocator.text(format!(" for {} in ", id)),
                range.pretty(allocator),
                allocator.text("]"),
            ]),
            Exp::Var(x) => allocator.concat([
                x.pretty(allocator),
            ]),
            Exp::Challenge(t) => allocator.concat([
                allocator.text("challenge<"),
                t.pretty(allocator),
                allocator.text(">"),
            ]),
            Exp::Random(t) => allocator.concat([
                allocator.text("random<"),
                t.pretty(allocator),
                allocator.text(">"),
            ]),
            Exp::Gen(t) => allocator.concat([
                allocator.text("gen<"),
                t.pretty(allocator),
                allocator.text(">"),
            ]),
            Exp::Range(r) => allocator.concat([
                r.pretty(allocator),
            ]),
            Exp::App(x, d) => allocator.concat([
                x.pretty(allocator),
                allocator.text("("),
                d.pretty(allocator),
                allocator.text(")"),
            ]),
            Exp::Interpolate(b, d) => allocator.concat([
                allocator.text("interpolate("),
                (*b).pretty(allocator),
                allocator.text(", "),
                (*d).pretty(allocator),
                allocator.text(")")
            ]),
            Exp::Ram(x, i) => allocator.concat([
                (*x).pretty(allocator),
                allocator.text("["),
                (*i).pretty(allocator),
                allocator.text("]"),
            ]),
            Exp::Equ(a, b) => allocator.concat([
                a.pretty(allocator),
                allocator.text(" == "),
                b.pretty(allocator),
            ]),
            Exp::And(a, b) => allocator.concat([
                (*a).pretty(allocator),
                allocator.text(" && "),
                (*b).pretty(allocator),
            ]),
            Exp::Or(a, b) => allocator.concat([
                (*a).pretty(allocator),
                allocator.text(" || "),
                (*b).pretty(allocator),
            ]),
            Exp::Contains(a, b) => allocator.concat([
                a.pretty(allocator),
                allocator.text(" in "),
                b.pretty(allocator),
            ]),
            Exp::Not(a) => allocator.concat([
                allocator.text("!"),
                (*a).pretty(allocator),
            ]),
            Exp::Let(Some(x), t, e) => allocator.concat([
                allocator.text("let "),
                x.pretty(allocator),
                allocator.text(" = "),
                (*t).pretty(allocator),
                allocator.text(";"),
                (*e).pretty(allocator),
            ]),
            Exp::Let(None, t, e) => allocator.concat([
                (*t).pretty(allocator),
                allocator.text(";"),
                (*e).pretty(allocator),
            ]),
            Exp::Log(x, t, e) => allocator.concat([
                x.pretty(allocator),
                allocator.text(" <- "),
                (*t).pretty(allocator),
                allocator.text(";"),
                (*e).pretty(allocator),
            ]),
            Exp::Assert(c) => allocator.concat([
                allocator.text("assert("),
                (*c).pretty(allocator),
                allocator.text(")"),
            ]),
            Exp::Verify(c) => allocator.concat([
                allocator.text("verify("),
                (*c).pretty(allocator),
                allocator.text(")"),
            ])
        }
    }

    fn is_nil(&self) -> bool {
        false
    }
}

impl<'a, D, A, N> Pretty<'a, D, A> for Exps<N>
where
    D: DocAllocator<'a, A>,
    D::Doc: Clone,
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

impl Add for UExp {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        UExp::add(self, rhs)
    }
}

impl Sub for UExp {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self {
        UExp::sub(self, rhs)
    }
}

impl Mul for UExp {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self {
        UExp::mul(self, rhs)
    }
}

impl Div for UExp {
    type Output = Self;

    fn div(self, rhs: Self) -> Self {
        UExp::div(self, rhs)
    }
}

impl BitXor for UExp {
    type Output = Self;

    fn bitxor(self, rhs: Self) -> Self {
        UExp::pow(self, rhs)
    }
}

impl From<u32> for UExp {
    fn from(x: u32) -> Self {
        UExp::lit(Size::from(x))
    }
}

impl From<Vid> for UExp {
    fn from(x: Vid) -> Self {
        UExp::Var(x)
    }
}

impl From<&str> for UExp {
    fn from(x: &str) -> Self {
        UExp::varstr(x)
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

impl<'a, N> fmt::Display for Exp<N>
where
    N: Clone + Pretty<'a, BoxAllocator, ()>,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <Exp<N> as Pretty<'_, BoxAllocator, ()>>::pretty(self.clone(), &BoxAllocator)
            .1
            .render_fmt(100, f)
    }
}

impl<'a, N> fmt::Display for Exps<N>
where
    N: Clone + Pretty<'a, BoxAllocator, ()>,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <Exps<N> as Pretty<'_, BoxAllocator, ()>>::pretty(self.clone(), &BoxAllocator)
            .1
            .render_fmt(100, f)
    }
}

lazy_static! {
    pub static ref AEXP_PARSER: PrattParser<Rule> = {
        use Assoc::*;
        use Rule::*;

        PrattParser::new()
            .op(Op::infix(and_op, Left))
            .op(Op::infix(or_op, Left))
            .op(Op::infix(add_op, Left) | Op::infix(sub_op, Left))
            .op(Op::infix(mul_op, Left) | Op::infix(dot_op, Left) | Op::infix(div_op, Left))
            .op(Op::infix(concat_op, Left))
            .op(Op::infix(pow_op, Right))
    };
}

impl<'pest> FromPest<'pest> for UExp {
    type Rule = Rule;
    type FatalError = InputError<'pest>;

    fn from_pest(
        expression: &mut Pairs<'pest, Self::Rule>,
    ) -> Result<Self, ConversionError<Self::FatalError>> {
        AEXP_PARSER
            .map_primary(|pair| match pair.as_rule() {
                Rule::id => Ok(Exp::Var(Vid(pair.as_str().to_string()))),
                Rule::positive => Ok(Exp::lit(Size::from_pest(&mut Pairs::single(pair))?)),
                Rule::gen_exp => Ok(Exp::gen(Tid::from_pest(&mut pair.into_inner())?)),
                Rule::coef_exp => Ok(Exp::coef(Exp::from_pest(&mut pair.into_inner())?)),
                Rule::mle_exp => Ok(Exp::mle(Exp::from_pest(&mut pair.into_inner())?)),
                Rule::interp_exp => {
                    let mut inner = pair.into_inner();
                    Ok(Exp::interpolate(
                        Exp::from_pest(&mut Pairs::single(inner.next().unwrap()))?,
                        Exp::from_pest(&mut Pairs::single(inner.next().unwrap()))?
                    ))
                },
                Rule::range_exp => Ok(Exp::range(Range::from_pest(&mut pair.into_inner())?)),
                Rule::challenge_exp =>
                    Ok(Exp::challenge(Tid::from_pest(&mut pair.into_inner())?)),
                Rule::random_exp =>
                    Ok(Exp::random(Tid::from_pest(&mut pair.into_inner())?)),
                Rule::vec_exp => {
                    let inner = pair.into_inner();
                    let mut ve = Vec::new();
                    for x in inner {
                        ve.push(Exp::from_pest(&mut Pairs::single(x))?);
                    }
                    Ok(Exp::vec(ve))
                },
                Rule::map_exp => {
                    let mut inner = pair.into_inner();
                    Ok(Exp::map(
                        Exp::from_pest(&mut Pairs::single(inner.next().unwrap()))?,
                        Vid::from_pest(&mut Pairs::single(inner.next().unwrap()))?,
                        Exp::from_pest(&mut Pairs::single(inner.next().unwrap()))?
                    ))
                },
                Rule::ram_exp => {
                    let mut inner = pair.into_inner();
                    Ok(Exp::ram(
                        Exp::Var(Vid::from_pest(&mut Pairs::single(inner.next().unwrap()))?),
                        Exp::from_pest(&mut Pairs::single(inner.next().unwrap()))?
                    ))
                },
                Rule::app_exp => {
                    let mut inner = pair.into_inner();
                    // Call a function
                    let func = Fid::from_pest(&mut inner)?;
                    // Arguments
                    let params = Exps::from_pest(&mut inner)?;
                    Ok(Exp::app(func, params))
                },
                Rule::eq_bexp => {
                    let mut inner = pair.into_inner();
                    Ok(Exp::equ(
                        UExp::from_pest(&mut Pairs::single(inner.next().unwrap()))?,
                        UExp::from_pest(&mut Pairs::single(inner.next().unwrap()))?
                    ))
                },
                Rule::contains_bexp => {
                    let mut inner = pair.into_inner();
                    Ok(Exp::contains(
                        UExp::from_pest(&mut Pairs::single(inner.next().unwrap()))?,
                        UExp::from_pest(&mut Pairs::single(inner.next().unwrap()))?
                    ))
                },
                Rule::not_bexp => {
                    let mut inner = pair.into_inner();
                    Ok(Exp::not(UExp::from_pest(&mut inner)?))
                },
                Rule::assert_exp => {
                    let mut inner = pair.into_inner();
                    Ok(Exp::assert(UExp::from_pest(&mut Pairs::single(inner.next().unwrap()))?))
                },
                Rule::verify_exp => {
                    let mut inner = pair.into_inner();
                    dbg!(&inner);
                    Ok(Exp::verify(
                        UExp::from_pest(&mut Pairs::single(inner.next().unwrap()))?,
                    ))
                },
                Rule::let_exp => {
                    let mut inner = pair.into_inner();
                    Ok(Exp::letx(
                        Vid::from_pest(&mut Pairs::single(inner.next().unwrap()))?,
                        Exp::from_pest(&mut Pairs::single(inner.next().unwrap()))?,
                        Exp::from_pest(&mut Pairs::single(inner.next().unwrap()))?
                    ))
                },
                Rule::log_exp => {
                    let mut inner = pair.into_inner();
                    Ok(Exp::logx(
                        Vid::from_pest(&mut Pairs::single(inner.next().unwrap()))?,
                        Exp::from_pest(&mut Pairs::single(inner.next().unwrap()))?,
                        Exp::from_pest(&mut Pairs::single(inner.next().unwrap()))?
                    ))
                },
                Rule::aexp => Exp::from_pest(&mut pair.into_inner()),
                Rule::bexp => Exp::from_pest(&mut pair.into_inner()),
                _ => Err(ConversionError::Malformed(InputError::UnexpectedExp(pair)))
            })
            .map_infix(|lhs, op, rhs|
                match op.clone().as_rule() {
                    Rule::and_op => Ok(Exp::and(lhs?, rhs?)),
                    Rule::or_op => Ok(Exp::or(lhs?, rhs?)),
                    Rule::add_op => Ok(Exp::add(lhs?, rhs?)),
                    Rule::sub_op => Ok(Exp::sub(lhs?, rhs?)),
                    Rule::mul_op => Ok(Exp::mul(lhs?, rhs?)),
                    Rule::div_op => Ok(Exp::div(lhs?, rhs?)),
                    Rule::pow_op => Ok(Exp::pow(lhs?, rhs?)),
                    Rule::dot_op => Ok(Exp::dot(lhs?, rhs?)),
                    Rule::concat_op => Ok(Exp::concat(lhs?, rhs?)),
                    _ => unreachable!(),
                })
            .parse(expression)
    }
}

impl<'pest> FromPest<'pest> for UExps {
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
                    aexps.push(UExp::from_pest(&mut Pairs::single(pair))?);
                }
                Ok(Exps(aexps))
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
    assert_eq!(UExp::from_pest(&mut pairs), Ok(Exp::from(2)));
}

#[test]
fn parser_var() {
    let ex = "x";
    let mut pairs = ZippelParser::parse(Rule::aexp, ex).unwrap();
    assert_eq!(UExp::from_pest(&mut pairs), Ok(Exp::varstr("x")));
}

#[test]
fn parser_bin() {
    // Add
    let ex1 = "x + 2";
    let mut pairs = ZippelParser::parse(Rule::aexp, ex1).unwrap();
    assert_eq!(
        UExp::from_pest(&mut pairs),
        Ok(Exp::varstr("x") + Exp::from(2))
    );

    // Sub
    let ex2 = "x - 2";
    let mut pairs = ZippelParser::parse(Rule::aexp, ex2).unwrap();
    assert_eq!(
        UExp::from_pest(&mut pairs),
        Ok(Exp::varstr("x") - Exp::from(2))
    );

    // Mul
    let ex3 = "x * 2";
    let mut pairs = ZippelParser::parse(Rule::aexp, ex3).unwrap();
    assert_eq!(
        Exp::from_pest(&mut pairs),
        Ok(Exp::varstr("x") * Exp::from(2))
    );

    // Div
    let ex4 = "x / 2";
    let mut pairs = ZippelParser::parse(Rule::aexp, ex4).unwrap();
    assert_eq!(
        UExp::from_pest(&mut pairs),
        Ok(Exp::varstr("x") / Exp::from(2))
    );

    // Pow
    let ex6 = "x ^ 2";
    let mut pairs = ZippelParser::parse(Rule::aexp, ex6).unwrap();
    assert_eq!(
        UExp::from_pest(&mut pairs),
        Ok(Exp::pow(Exp::varstr("x"), Exp::from(2)))
    );
}

#[test]
fn parser_interpolate() {
    let ex = "interpolate(x + 2, 4*x)";
    let mut pairs = ZippelParser::parse(Rule::aexp, ex).unwrap();
    assert_eq!(
        UExp::from_pest(&mut pairs),
        Ok(Exp::interpolate(
            Exp::varstr("x") + Exp::from(2),
            Exp::from(4) * Exp::varstr("x")
        ))
    );
}

#[test]
fn parser_call_two() {
    let ex = "f(x + 2, x)";
    let mut pairs = ZippelParser::parse(Rule::aexp, ex).unwrap();
    assert_eq!(
        UExp::from_pest(&mut pairs),
        Ok(Exp::app(
            Fid::from("f"),
            Exps(vec![Exp::varstr("x") + Exp::from(2), Exp::varstr("x")])
        ))
    );
}

#[test]
fn parser_range() {
    let ex = "0..N";
    let mut pairs = ZippelParser::parse(Rule::aexp, ex).unwrap();
    assert_eq!(
        UExp::from_pest(&mut pairs),
        Ok(Exp::range(Range { start: Size::from(0), step: Size::from(1), end: Size::from("N") }))
    );
}

#[test]
fn parser_for() {
    let ex = "[ 3^i for i in 0..N ]";
    let mut pairs = ZippelParser::parse(Rule::aexp, ex).unwrap();
    assert_eq!(
        UExp::from_pest(&mut pairs),
        Ok(Exp::map(
            Exp::pow(Exp::from(3), Exp::varstr("i")),
            Vid::from("i"),
            Exp::range(Range { start: Size::from(0), step: Size::from(1), end: Size::from("N") }))
        ));
}

#[test]
fn parser_random() {
    let ex = "random<A>";
    let mut pairs = ZippelParser::parse(Rule::aexp, ex).unwrap();
    assert_eq!(
        UExp::from_pest(&mut pairs),
        Ok(Exp::random(Tid::from("A")))
    );
}

#[test]
fn parser_challenge() {
    let ex = "challenge<F>";
    let mut pairs = ZippelParser::parse(Rule::aexp, ex).unwrap();
    assert_eq!(UExp::from_pest(&mut pairs), Ok(Exp::challenge(Tid::from("F"))));
}

#[test]
fn parser_concat() {
    let ex = "(x + 2) ++ x";
    let mut pairs = ZippelParser::parse(Rule::aexp, ex).unwrap();
    assert_eq!(
        UExp::from_pest(&mut pairs),
        Ok(Exp::concat(
            Exp::varstr("x") + Exp::from(2),
            Exp::varstr("x")
        ))
    );
}

#[test]
fn parser_let() {
    let ex = "let x = 2; 3";
    let mut pairs = ZippelParser::parse(Rule::aexp, ex).unwrap();
    dbg!(&pairs);
    assert_eq!(
        UExp::from_pest(&mut pairs),
        Ok(Exp::letx(
            Vid::from("x"),
            Exp::from(2),
            Exp::from(3)
        ))
    );
}

#[test]
fn parser_log() {
    let ex = "x <- 2; 4";
    let mut pairs = ZippelParser::parse(Rule::aexp, ex).unwrap();
    assert_eq!(
        UExp::from_pest(&mut pairs),
        Ok(Exp::logx(
            Vid::from("x"),
            Exp::from(2),
            Exp::from(4)
        ))
    );
}

#[test]
fn parser_assert() {
    let ex = "assert(x == 2)";
    let mut pairs = ZippelParser::parse(Rule::aexp, ex).unwrap();
    assert_eq!(
        UExp::from_pest(&mut pairs),
        Ok(Exp::assert(
            Exp::equ(Exp::varstr("x"), Exp::from(2)),
        ))
    );
}

#[test]
fn parser_verify() {
    let ex = "verify(x == 2)";
    let mut pairs = ZippelParser::parse(Rule::aexp, ex).unwrap();
    assert_eq!(
        UExp::from_pest(&mut pairs),
        Ok(Exp::verify(
            Exp::equ(Exp::varstr("x"), Exp::from(2)),
        ))
    );
}

#[test]
fn parser_seq() {
    let ex = "x <- 2; y <- 3; let x = 2 * 4; 2";
    let mut pairs = ZippelParser::parse(Rule::aexps, ex).unwrap();
    assert_eq!(
        UExps::from_pest(&mut pairs),
        Ok(Exps(vec![
            Exp::logx(Vid::from("x"), Exp::from(2),
                Exp::logx(Vid::from("y"), Exp::from(3),
                    Exp::letx(Vid::from("x"), Exp::from(2) * Exp::from(4),
                        Exp::from(2))))
        ]))
    );
}
