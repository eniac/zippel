use std::ops::{Add, Div, Mul, Sub, BitXor};
use crate::parser::*;
use from_pest::{ConversionError, FromPest};
use lazy_static::lazy_static;
use std::fmt;
use pest::iterators::Pairs;
use pest::pratt_parser::{Assoc, Op, PrattParser};

use share::traversal::{BoxTraversal, ToTraversal1, ToTraversal2};

use share::{Traversal, BoxAllocator, Pretty, DocAllocator, DocBuilder};
use crate::typ::{Typ, Size};
use crate::exp::{BExp, UBExp};
use crate::id::{Tid, TidTraversal, Fid, Vid};
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
/// It is parameterized by types `N` representing the sizes of ranges, indices etc
#[derive(Debug, PartialEq, Eq, Clone, PartialOrd, Ord)]
pub enum AExp<N> {
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
    App(Fid, AExps<N>),

    ///     Coefficients of a univariate vector
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let v = coef [1,2,1]; // 1 + 2x + x^2
    ///     ```
    Coef(Box<AExp<N>>),

    ///     Multilinear extension of a matrix, polynomial, etc.
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let g = mle x;
    ///     ```
    Mle(Box<AExp<N>>),

    ///     A vector of elements
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let v = [1, 2*x, x+y];
    ///     ```
    Vec(AExps<N>),

    ///     Binary operation
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let sum = 2 + 3;
    ///     ```
    Bin(BinOp, Box<AExp<N>>, Box<AExp<N>>),

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
    Map(Box<AExp<N>>, Vid, Box<AExp<N>>),

    ///     Random access or slice a vector
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let first = v[0]
    ///     ```
    Ram(Box<AExp<N>>, Box<AExp<N>>),

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
    Interpolate(Box<AExp<N>>, Box<AExp<N>>),

    ///     Represents a let-expression, which binds a value to an identifier.
    ///
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let x = 5 + 3;
    ///     ```
    Let(Vid, Box<AExp<N>>),

    ///     Represents a log-let expression with transcript dependency.
    ///     This variant is used to bind a value to an identifier while logging the operation.
    ///     **Zippel Code:**
    ///     ```zippel
    ///     p <- interpolate(v, [0,1,2])
    ///     ```
    Log(Vid, Box<AExp<N>>),

    ///     Prover assertion followed by expression.
    ///     **Zippel Code:**
    ///     ```zippel
    ///     assert(1 == 1);
    ///     ...
    ///     ```
    Assert(Box<BExp<N>>),

    ///     Verifier check followed by expression.
    ///     **Zippel Code:**
    ///     ```zippel
    ///     verify(a == a);
    ///     ...
    ///     ```
    Verify(Box<BExp<N>>)
}

/// Represents a sequence of arithmetic expressions in the Zippel language
#[derive(Debug, PartialEq, Eq, Clone, PartialOrd, Ord)]
pub struct AExps<N>(pub Vec<AExp<N>>);

/// How to traverse structures of arithmetic expressions (AExp)
pub trait AExpTraversal<N>: Sized {
    type Output<Z>;
    fn aexp_traverse<E, Z>(self, f: &mut dyn FnMut(AExp<N>) -> Result<AExp<Z>, E>) -> Result<Self::Output<Z>, E>;
}

impl<N> AExpTraversal<N> for AExps<N> {
    type Output<Z> = AExps<Z>;
    fn aexp_traverse<E, Z>(self, f: &mut dyn FnMut(AExp<N>) -> Result<AExp<Z>, E>) -> Result<AExps<Z>, E> {
        self.0.into_iter().map(|x| f(x)).collect()
    }
}
/// Symbolic sized AST node, as parsed from input
pub type UAExp = AExp<Size>;

/// Concrete size untyped AST node
pub type CAExp = AExp<usize>;

/// Symbolic sized AST sequence, as parsed from input
pub type UAExps = AExps<Size>;

/// Concrete size untyped AST node
pub type CAExps = AExps<usize>;

/// How to traverse the first type parameter [N] for AExp<N>
impl<N> ToTraversal1<N> for AExp<N> {
    type Output<Z> = AExp<Z>;
    fn traverse1<Z, E>(self, f: &mut dyn FnMut(N) -> Result<Z, E>) -> Result<AExp<Z>, E> {
        match self {
            AExp::Lit(x) => Ok(AExp::Lit(f(x)?)),
            AExp::Var(v) => Ok(AExp::Var(v)),
            AExp::Coef(box p) => Ok(AExp::Coef(Box::new(p.traverse1(f)?))),
            AExp::Mle(box p) => Ok(AExp::Mle(Box::new(p.traverse1(f)?))),
            AExp::Vec(v) =>
                Ok(AExp::Vec(v.aexp_traverse(&mut |x| x.traverse1(f))?)),
            AExp::App(x, ts) =>
                Ok(AExp::App(x, ts.aexp_traverse(&mut |x| x.traverse1(f))?)),
            AExp::Bin(op, box x, box y) =>
                Ok(AExp::Bin(
                    op,
                    Box::new(x.traverse1(f)?),
                    Box::new(y.traverse1(f)?),
                )),
            AExp::Map(box x, id, box r) =>
                Ok(AExp::Map(Box::new(x.traverse1(f)?), id, Box::new(r.traverse1(f)?))),
            AExp::Challenge(t) => Ok(AExp::Challenge(t)),
            AExp::Random(t) => Ok(AExp::Random(t)),
            AExp::Gen(t) => Ok(AExp::Gen(t)),
            AExp::Range(r) => Ok(AExp::Range(r.traverse1(f)?)),
            AExp::Interpolate(box x, box y) =>
                Ok(AExp::Interpolate(
                    Box::new(x.traverse1(f)?),
                    Box::new(y.traverse1(f)?)
                )),
            AExp::Ram(box x, box i) =>
                Ok(AExp::Ram(
                        Box::new(x.traverse1(f)?),
                        Box::new(i.traverse1(f)?)
                )),
            AExp::Let(x, box a) =>
                Ok(AExp::Let(x, Box::new(a.traverse1(f)?))),
            AExp::Log(x, box a) =>
                Ok(AExp::Log(x, Box::new(a.traverse1(f)?))),
            AExp::Assert(box x) =>
                Ok(AExp::Assert(Box::new(x.traverse1(f)?))),
            AExp::Verify(box x) =>
                Ok(AExp::Verify(Box::new(x.traverse1(f)?)))
        }
    }
}

/// How to traverse the first type parameter [N] for AExps<N>
impl<N> ToTraversal1<N> for AExps<N> {
    type Output<Z> = AExps<Z>;
    fn traverse1<Z, E>(self, f: &mut dyn FnMut(N) -> Result<Z, E>) -> Result<AExps<Z>, E> {
        Ok(AExps(self.0.traverse1(&mut |x| x.traverse1(f))?))
    }
}

/// Traverse [Tid] inside [TAExp]
impl TidTraversal for CAExp {
    fn tid_traverse<E>(self, f: &mut dyn FnMut(Tid) -> Result<Tid, E>) -> Result<Self, E> {
        match self {
            AExp::Lit(x) => Ok(AExp::Lit(x)),
            AExp::Var(v) => Ok(AExp::Var(v)),
            AExp::Coef(p) =>
                Ok(AExp::Coef(p.traverse1(&mut |x| x.tid_traverse(f))?)),
            AExp::Mle(p) =>
                Ok(AExp::Mle(p.traverse1(&mut |x| x.tid_traverse(f))?)),
            AExp::Vec(v) =>
                Ok(AExp::Vec(v.aexp_traverse(&mut |x| x.tid_traverse(f))?)),
            AExp::Bin(op, x, y) => Ok(AExp::Bin(op,
                    x.traverse1(&mut |x| x.tid_traverse(f))?,
                    y.traverse1(&mut |x| x.tid_traverse(f))?)),
            AExp::Map(x, id, r) => Ok(AExp::Map(
                    x.traverse1(&mut |x| x.tid_traverse(f))?, id,
                    r.traverse1(&mut |x| x.tid_traverse(f))?)),
            AExp::Challenge(t) => Ok(AExp::Challenge(f(t)?)),
            AExp::Random(t) => Ok(AExp::Random(f(t)?)),
            AExp::Gen(t) => Ok(AExp::Gen(f(t)?)),
            AExp::Range(r) => Ok(AExp::Range(r)),
            AExp::Interpolate(x, y) => Ok(AExp::Interpolate(
                    x.traverse1(&mut |x| x.tid_traverse(f))?,
                    y.traverse1(&mut |x| x.tid_traverse(f))?)),
            AExp::Ram(x, i) => Ok(AExp::Ram(
                    x.traverse1(&mut |x| x.tid_traverse(f))?,
                    i.traverse1(&mut |x| x.tid_traverse(f))?)),
            AExp::Let(x, a) =>
                Ok(AExp::Let(x, a.traverse1(&mut |x| x.tid_traverse(f))?)),
            AExp::Log(x, a) =>
                Ok(AExp::Log(x, a.traverse1(&mut |x| x.tid_traverse(f))?)),
            AExp::Assert(x) =>
                Ok(AExp::Assert(x.traverse1(&mut |x| x.tid_traverse(f))?)),
            AExp::Verify(x) =>
                Ok(AExp::Verify(x.traverse1(&mut |x| x.tid_traverse(f))?)),
            AExp::App(x, ts) => Ok(AExp::App(x, ts.aexp_traverse(&mut |x| x.tid_traverse(f))?))
        }
    }
}

impl TidTraversal for CAExps {
    fn tid_traverse<E>(self, f: &mut dyn FnMut(Tid) -> Result<Tid, E>) -> Result<Self, E> {
        Ok(AExps(self.0.traverse1(&mut |x| x.tid_traverse(f))?))
    }
}

/// How to traverse [Range] inside an [AExp]
impl<N> RangeTraversal<N> for AExp<N> {
    fn range_traverse<E>(self, f: &mut dyn FnMut(Range<N>) -> Result<Range<N>, E>) -> Result<Self, E> {
        match self {
            AExp::Range(r) => Ok(AExp::Range(f(r)?)),
            AExp::Lit(x) => Ok(AExp::Lit(x)),
            AExp::Var(v) => Ok(AExp::Var(v)),
            AExp::Gen(t) => Ok(AExp::Gen(t)),
            AExp::Challenge(t) => Ok(AExp::Challenge(t)),
            AExp::Random(t) => Ok(AExp::Random(t)),
            AExp::Coef(p) => Ok(AExp::Coef(p.traverse1(
                        &mut |x| x.range_traverse(f))?)),
            AExp::Mle(p) => Ok(AExp::Mle(BoxTraversal::traverse(p,
                        &mut |x| x.range_traverse(f))?)),
            AExp::Vec(v) =>
                Ok(AExp::Vec(v.aexp_traverse(&mut |x| x.range_traverse(f))?)),
            AExp::Bin(op, x, y) => Ok(AExp::Bin(op,
                    BoxTraversal::traverse(x, &mut |x| x.range_traverse(f))?,
                    BoxTraversal::traverse(y, &mut |x| x.range_traverse(f))?)),
            AExp::Map(x, id, r) => Ok(AExp::Map(
                    BoxTraversal::traverse(x, &mut |x| x.range_traverse(f))?, id,
                    BoxTraversal::traverse(r, &mut |x| x.range_traverse(f))?)),
            AExp::Ram(x, i) => Ok(AExp::Ram(
                    BoxTraversal::traverse(x, &mut |x| x.range_traverse(f))?,
                    BoxTraversal::traverse(i, &mut |x| x.range_traverse(f))?)),
            AExp::Interpolate(x, y) => Ok(AExp::Interpolate(
                    BoxTraversal::traverse(x, &mut |x| x.range_traverse(f))?,
                    BoxTraversal::traverse(y, &mut |x| x.range_traverse(f))?)),
            AExp::Let(x, t) => Ok(AExp::Let(x, t.traverse1(&mut |x| x.range_traverse(f))?)),
            AExp::Log(x, t) => Ok(AExp::Log(x, t.traverse1(&mut |x| x.range_traverse(f))?)),
            AExp::Assert(x) => Ok(AExp::Assert(x.traverse1(&mut |x| x.range_traverse(f))?)),
            AExp::Verify(x) => Ok(AExp::Verify(x.traverse1(&mut |x| x.range_traverse(f))?)),
            AExp::App(x, ts) => Ok(AExp::App(x,
                    ts.aexp_traverse(&mut |x| x.range_traverse(f))?))
        }
    }
}

impl<N> RangeTraversal<N> for AExps<N> {
    fn range_traverse<E>(self, f: &mut dyn FnMut(Range<N>) -> Result<Range<N>, E>) -> Result<Self, E> {
        Ok(AExps(self.0.traverse1(&mut |x| x.range_traverse(f))?))
    }
}

impl<N> AExps<N> {
    pub fn iter(&self) -> std::slice::Iter<AExp<N>> {
        self.0.iter()
    }
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
    pub fn len(&self) -> usize {
        self.0.len()
    }
    // Parser guarantees that the vector is non-empty
    pub fn last(&self) -> &AExp<N> {
        self.0.last().unwrap()
    }
}

impl<N> IntoIterator for AExps<N> {
    type Item = AExp<N>;
    type IntoIter = std::vec::IntoIter<AExp<N>>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<N> FromIterator<AExp<N>> for AExps<N> {
    fn from_iter<I: IntoIterator<Item = AExp<N>>>(iter: I) -> Self {
        AExps(iter.into_iter().collect())
    }
}

/// Construct untyped expressions
impl<N> AExp<N> {
    /// Annotated constructors
    pub fn lit(v: N) -> Self {
        AExp::Lit(v)
    }
    pub fn bin(op: BinOp, l: Self, r: Self) -> Self {
        AExp::Bin(op, Box::new(l), Box::new(r))
    }
    pub fn gen(t: Tid) -> Self {
        AExp::Gen(t)
    }
    pub fn coef(a: Self) -> Self {
        AExp::Coef(Box::new(a))
    }
    pub fn mle(a: Self) -> Self {
        AExp::Mle(Box::new(a))
    }
    pub fn interpolate(e: Self, d: Self) -> Self {
        AExp::Interpolate(Box::new(e), Box::new(d))
    }
    pub fn challenge(t: Tid) -> Self {
        AExp::Challenge(t)
    }
    pub fn random(t: Tid) -> Self {
        AExp::Random(t)
    }
    pub fn vec(v: Vec<Self>) -> Self {
        AExp::Vec(AExps(v))
    }
    pub fn map(l: Self, x: Vid, range: Self) -> Self {
        AExp::Map(Box::new(l), x, Box::new(range))
    }
    pub fn ram(v: Self, i: Self) -> Self {
        AExp::Ram(Box::new(v), Box::new(i))
    }
    pub fn range(r: Range<N>) -> Self {
        AExp::Range(r)
    }
    pub fn add(l: Self, r: Self) -> Self {
        AExp::Bin(BinOp::Add, Box::new(l), Box::new(r))
    }
    pub fn sub(l: Self, r: Self) -> Self {
        AExp::Bin(BinOp::Sub, Box::new(l), Box::new(r))
    }
    pub fn mul(l: Self, r: Self) -> Self {
        AExp::Bin(BinOp::Mul, Box::new(l), Box::new(r))
    }
    pub fn div(l: Self, r: Self) -> Self {
        AExp::Bin(BinOp::Div, Box::new(l), Box::new(r))
    }
    pub fn pow(l: Self, r: Self) -> Self {
        AExp::Bin(BinOp::Pow, Box::new(l), Box::new(r))
    }
    pub fn dot(l: Self, r: Self) -> Self {
        AExp::Bin(BinOp::Dot, Box::new(l), Box::new(r))
    }
    pub fn concat(l: Self, r: Self) -> Self {
        AExp::Bin(BinOp::Concat, Box::new(l), Box::new(r))
    }
    pub fn var(x: Vid) -> Self {
        AExp::Var(x)
    }
    pub fn varstr<'a>(x: &'a str) -> Self {
        AExp::var(Vid::from(x))
    }
    pub fn app(e: Fid, d: AExps<N>) -> Self {
        AExp::App(e, d)
    }
    pub fn assert(b: BExp<N>) -> Self {
        AExp::Assert(Box::new(b))
    }
    pub fn verify(b: BExp<N>) -> Self {
        AExp::Verify(Box::new(b))
    }
    pub fn letx(a: Vid, d: Self) -> Self {
        AExp::Let(a, Box::new(d))
    }
    pub fn logx(a: Vid, d: Self) -> Self {
        AExp::Log(a, Box::new(d))
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
impl<'a, D, A, N> Pretty<'a, D, A> for AExp<N>
where
    D: DocAllocator<'a, A>,
    D::Doc: Clone,
    N: Pretty<'a, D, A>,
    A: 'a + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        match self {
            AExp::Lit(p) => p.pretty(allocator),
            AExp::Coef(p) => allocator.concat([
                allocator.text("coef "),
                p.pretty(allocator),
            ]),
            AExp::Mle(p) => allocator.concat([
                allocator.text("mle "),
                p.pretty(allocator),
            ]),
            AExp::Vec(ts) => allocator.concat([
                allocator.text("["),
                allocator.intersperse(ts.into_iter().map(|x| x.pretty(allocator)), ", "),
                allocator.text("]"),
            ]),
            AExp::Bin(op, a, b) => allocator.concat([
                (*a).pretty(allocator),
                op.pretty(allocator),
                (*b).pretty(allocator),
            ]),
            AExp::Map(x, id, range) => allocator.concat([
                allocator.text("["),
                x.pretty(allocator),
                allocator.text(format!(" for {} in ", id)),
                range.pretty(allocator),
                allocator.text("]"),
            ]),
            AExp::Var(x) => allocator.concat([
                x.pretty(allocator),
            ]),
            AExp::Challenge(t) => allocator.concat([
                allocator.text("challenge<"),
                t.pretty(allocator),
                allocator.text(">"),
            ]),
            AExp::Random(t) => allocator.concat([
                allocator.text("random<"),
                t.pretty(allocator),
                allocator.text(">"),
            ]),
            AExp::Gen(t) => allocator.concat([
                allocator.text("gen<"),
                t.pretty(allocator),
                allocator.text(">"),
            ]),
            AExp::Range(r) => allocator.concat([
                r.pretty(allocator),
            ]),
            AExp::App(x, d) => allocator.concat([
                x.pretty(allocator),
                allocator.text("("),
                d.pretty(allocator),
                allocator.text(")"),
            ]),
            AExp::Interpolate(b, d) => allocator.concat([
                allocator.text("interpolate("),
                (*b).pretty(allocator),
                allocator.text(", "),
                (*d).pretty(allocator),
                allocator.text(")")
            ]),
            AExp::Ram(x, i) => allocator.concat([
                (*x).pretty(allocator),
                allocator.text("["),
                (*i).pretty(allocator),
                allocator.text("]"),
            ]),
            AExp::Let(x, t) => allocator.concat([
                allocator.text("let "),
                x.pretty(allocator),
                allocator.text(" = "),
                (*t).pretty(allocator),
            ]),
            AExp::Log(x, t) => allocator.concat([
                x.pretty(allocator),
                allocator.text(" <- "),
                (*t).pretty(allocator),
            ]),
            AExp::Assert(c) => allocator.concat([
                allocator.text("assert("),
                (*c).pretty(allocator),
                allocator.text(")"),
            ]),
            AExp::Verify(c) => allocator.concat([
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

impl<'a, D, A, N> Pretty<'a, D, A> for AExps<N>
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

impl<'a, N> fmt::Display for AExp<N>
where
    N: Clone + Pretty<'a, BoxAllocator, ()>,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <AExp<N> as Pretty<'_, BoxAllocator, ()>>::pretty(self.clone(), &BoxAllocator)
            .1
            .render_fmt(100, f)
    }
}

impl<'a, N> fmt::Display for AExps<N>
where
    N: Clone + Pretty<'a, BoxAllocator, ()>,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <AExps<N> as Pretty<'_, BoxAllocator, ()>>::pretty(self.clone(), &BoxAllocator)
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
                    Ok(AExp::challenge(Tid::from_pest(&mut pair.into_inner())?)),
                Rule::random_exp =>
                    Ok(AExp::random(Tid::from_pest(&mut pair.into_inner())?)),
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
    let ex = "random<A>";
    let mut pairs = ZippelParser::parse(Rule::aexp, ex).unwrap();
    assert_eq!(
        UAExp::from_pest(&mut pairs),
        Ok(AExp::random(Tid::from("A")))
    );
}

#[test]
fn parser_challenge() {
    let ex = "challenge<F>";
    let mut pairs = ZippelParser::parse(Rule::aexp, ex).unwrap();
    assert_eq!(UAExp::from_pest(&mut pairs), Ok(AExp::challenge(Tid::from("F"))));
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
