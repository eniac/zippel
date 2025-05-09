use std::ops::{Add, Div, Mul, Sub, Rem, BitXor, BitAnd, Index};
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
use crate::id::{Tid, TidSubst, Vid};

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
    Concat,

    ///     **Zippel Code:**
    ///     ```zippel
    ///     let inner: F = 5 % 2;
    ///     ```
    Rem,

    ///     Represents the equality comparison between two arithmetic expressions.
    ///
    ///     **Zippel Code:**
    ///     ```zippel
    ///     verify(5 == 5);
    ///     ```
    Equ,

    ///     Represents the logical AND of two boolean expressions.
    ///
    ///     **Zippel Code:**
    ///     ```zippel
    ///     assert(true && false);
    ///     ```
    And
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

    ///     Boolean literal
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let b = true;
    ///     ```
    Bool(bool),

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
    App(Vid, Exps<N>),

    ///     Coefficients of a univariate vector
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let v = coef [1,2,1]; // 1 + 2x + x^2
    ///     ```
    Coef(Box<Exp<N>>),

    ///     Convert from lagrange domain to evaluation domain.
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let p = eval(poly);
    ///     ```
    Eval(Box<Exp<N>>),

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

    ///     Reduce a vector with a binary operation
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let sum = reduce(+, [1,2,3]);
    ///     ```
    Reduce(BinOp, Box<Exp<N>>),

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

#[derive(Debug, PartialEq, Eq, Clone, PartialOrd, Ord)]
pub struct Exps<N>(pub Vec<Exp<N>>);

/// Symbolic sized AST node, as parsed from input
pub type UExp = Exp<Size>;
pub type UExps = Exps<Size>;

/// Concrete size untyped AST node
pub type CExp = Exp<usize>;
pub type CExps = Exps<usize>;

/// How to traverse the first type parameter [N] for Exp<N>
impl<N> ToTraversal1<N> for Exp<N> {
    type Output<Z> = Exp<Z>;
    fn traverse1<Z, E>(self, f: &mut dyn FnMut(N) -> Result<Z, E>) -> Result<Exp<Z>, E> {
        match self {
            Exp::Lit(x) => Ok(Exp::Lit(f(x)?)),
            Exp::Bool(b) => Ok(Exp::Bool(b)),
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
            Exp::Reduce(op, box x) =>
                Ok(Exp::Reduce(op, Box::new(x.traverse1(f)?))),
            Exp::Challenge(t) => Ok(Exp::Challenge(t)),
            Exp::Random(t) => Ok(Exp::Random(t)),
            Exp::Range(r) => Ok(Exp::Range(r.traverse1(f)?)),
            Exp::Eval(box x) =>
                Ok(Exp::Eval(Box::new(x.traverse1(f)?))),
            Exp::Ram(box x, box i) =>
                Ok(Exp::Ram(
                        Box::new(x.traverse1(f)?),
                        Box::new(i.traverse1(f)?)
                )),
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
            Exp::Coef(box p)
            | Exp::Mle(box p)
            | Exp::Assert(box p)
            | Exp::Verify(box p)
            | Exp::Reduce(_, box p)
            | Exp::Eval(box p) => p.tid_subst(from, to),
            Exp::Vec(v)
            | Exp::App(_, v) => v.tid_subst(from, to),
            Exp::Bin(_, box a, box b)
            | Exp::Map(box a, _, box b)
            | Exp::Ram(box a, box b)
            | Exp::Let(_, box a, box b)
            | Exp::Log(_, box a, box b) => {
                a.tid_subst(from, to);
                b.tid_subst(from, to);
            },
            Exp::Lit(_) | Exp::Var(_) | Exp::Range(_) | Exp::Bool(_)
            | Exp::Challenge(_) | Exp::Random(_) => {}
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
            Exp::Bool(_) | Exp::Challenge(_) | Exp::Random(_)
            | Exp::Lit(_) | Exp::Range(_) => Set::new(),
            Exp::Coef(box p)
            | Exp::Mle(box p)
            | Exp::Reduce(_, box p)
            | Exp::Assert(box p)
            | Exp::Verify(box p)
            | Exp::Eval(box p) => p.freevars(),
            Exp::Vec(v) | Exp::App(_, v) => v.freevars(),
            Exp::Bin(_, box a, box b)
            | Exp::Ram(box a, box b)
            | Exp::Map(box a, _, box b)
            | Exp::Let(_, box a, box b)
            | Exp::Log(_, box a, box b) => a.freevars().union(b.freevars()),
        }
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
            Exp::Eval(box x) =>
                Ok(Exp::eval(x.range_traverse(f)?)),
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

impl<T> Index<usize> for Exps<T> {
    type Output = Exp<T>;

    fn index(&self, index: usize) -> &Self::Output {
        self.0.index(index)
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
    pub fn bool(b: bool) -> Self {
        Exp::Bool(b)
    }
    pub fn bin(op: BinOp, l: Self, r: Self) -> Self {
        Exp::Bin(op, Box::new(l), Box::new(r))
    }
    pub fn coef(a: Self) -> Self {
        Exp::Coef(Box::new(a))
    }
    pub fn mle(a: Self) -> Self {
        Exp::Mle(Box::new(a))
    }
    pub fn eval(e: Self) -> Self {
        Exp::Eval(Box::new(e))
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
    pub fn reduce(op: BinOp, a: Self) -> Self {
        Exp::Reduce(op, Box::new(a))
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
    pub fn rem(l: Self, r: Self) -> Self {
        Exp::Bin(BinOp::Rem, Box::new(l), Box::new(r))
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
        Exp::Bin(BinOp::And, Box::new(l), Box::new(r))
    }
    pub fn equ(l: Exp<N>, r: Exp<N>) -> Self {
        Exp::Bin(BinOp::Equ, Box::new(l), Box::new(r))
    }
    pub fn app(id: Vid, args: Exps<N>) -> Self {
        Exp::App(id, args)
    }
    pub fn is_pure(&self) -> bool {
        match self {
            Exp::Lit(_) | Exp::Bool(_) | Exp::Var(_) | Exp::Range(_) => true,
            Exp::Coef(box p) => p.is_pure(),
            Exp::Mle(box p) => p.is_pure(),
            Exp::Reduce(_, box p) => p.is_pure(),
            Exp::Vec(v) => v.iter().all(|e| e.is_pure()),
            Exp::Bin(_, box a, box b) => a.is_pure() && b.is_pure(),
            Exp::Map(box a, _, box b) => a.is_pure() && b.is_pure(),
            Exp::Ram(box a, box b) => a.is_pure() && b.is_pure(),
            Exp::Let(_, box a, box b) => a.is_pure() && b.is_pure(),
            Exp::Log(_, box _, box _) => false,
            Exp::Challenge(_) | Exp::Random(_) => false,
            Exp::App(_, args) => args.iter().all(|e| e.is_pure()),
            Exp::Eval(box a) => a.is_pure(),
            Exp::Assert(_) | Exp::Verify(_) => false,
        }
    }
}

impl CExp {
    pub fn zeroes(n: usize) -> Self {
        Exp::map(
            Exp::lit(0),
            Vid::from("_"),
            Exp::range(Range::new(0, n)),
        )
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
            BinOp::Rem => allocator.text(" % "),
            BinOp::Equ => allocator.text(" == "),
            BinOp::And => allocator.text(" && "),
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
            Exp::Bool(b) => allocator.text(b.to_string()),
            Exp::Coef(p) => allocator.concat([
                allocator.text("coef("),
                p.pretty(allocator),
                allocator.text(")"),
            ]),
            Exp::Mle(p) => allocator.concat([
                allocator.text("mle("),
                p.pretty(allocator),
                allocator.text(")"),
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
            Exp::Reduce(op, a) => allocator.concat([
                allocator.text("reduce("),
                op.pretty(allocator),
                allocator.text(", "),
                (*a).pretty(allocator),
                allocator.text(")"),
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
            Exp::Range(r) => allocator.concat([
                r.pretty(allocator),
            ]),
            Exp::App(x, d) => allocator.concat([
                x.pretty(allocator),
                allocator.text("("),
                d.pretty(allocator),
                allocator.text(")"),
            ]),
            Exp::Eval(b) => allocator.concat([
                allocator.text("eval("),
                (*b).pretty(allocator),
                allocator.text(")")
            ]),
            Exp::Ram(x, i) => allocator.concat([
                (*x).pretty(allocator),
                allocator.text("["),
                (*i).pretty(allocator),
                allocator.text("]"),
            ]),
            Exp::Let(Some(x), t, e) => allocator.concat([
                allocator.text("let "),
                x.pretty(allocator),
                allocator.text(" = "),
                (*t).pretty(allocator),
                allocator.text(";"),
                allocator.hardline(),
                (*e).pretty(allocator),
            ]),
            Exp::Let(None, t, e) => allocator.concat([
                (*t).pretty(allocator),
                allocator.text(";"),
                allocator.hardline(),
                (*e).pretty(allocator),
            ]),
            Exp::Log(x, t, e) => allocator.concat([
                x.pretty(allocator),
                allocator.text(" <- "),
                (*t).pretty(allocator),
                allocator.text(";"),
                allocator.hardline(),
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
            self.0.into_iter().map(|x| x.pretty(allocator)), ", ")
    }
    fn is_nil(&self) -> bool {
        self.0.is_empty()
    }
}

impl<N> Add for Exp<N> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        Exp::add(self, rhs)
    }
}

impl<N> Sub for Exp<N> {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self {
        Exp::sub(self, rhs)
    }
}

impl<N> Mul for Exp<N> {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self {
        Exp::mul(self, rhs)
    }
}

impl<N> Div for Exp<N> {
    type Output = Self;

    fn div(self, rhs: Self) -> Self {
        Exp::div(self, rhs)
    }
}

impl<N> Rem for Exp<N> {
    type Output = Self;

    fn rem(self, rhs: Self) -> Self {
        Exp::rem(self, rhs)
    }
}

impl<N> BitXor for Exp<N> {
    type Output = Self;

    fn bitxor(self, rhs: Self) -> Self {
        Exp::pow(self, rhs)
    }
}

impl<N> BitAnd for Exp<N> {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self {
        Exp::and(self, rhs)
    }
}

impl From<u32> for UExp {
    fn from(x: u32) -> Self {
        UExp::lit(Size::from(x))
    }
}

impl From<usize> for CExp {
    fn from(x: usize) -> Self {
        CExp::lit(x)
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

impl From<bool> for UExp {
    fn from(x: bool) -> Self {
        UExp::Bool(x)
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
            .op(Op::infix(eq_op, Left))
            .op(Op::infix(add_op, Left) | Op::infix(sub_op, Left))
            .op(Op::infix(mul_op, Left) | Op::infix(dot_op, Left) | Op::infix(div_op, Left) | Op::infix(rem_op, Left))
            .op(Op::infix(concat_op, Left))
            .op(Op::infix(pow_op, Right))
            .op(Op::prefix(unary_minus))
    };
}

impl<'pest> FromPest<'pest> for BinOp {
    type Rule = Rule;
    type FatalError = InputError<'pest>;

    fn from_pest(
        expression: &mut Pairs<'pest, Self::Rule>,
    ) -> Result<Self, ConversionError<Self::FatalError>> {
        let pair = expression.next().ok_or(ConversionError::NoMatch)?;
        match pair.as_rule() {
            Rule::bin_op => BinOp::from_pest(&mut pair.into_inner()),
            Rule::add_op => Ok(BinOp::Add),
            Rule::sub_op => Ok(BinOp::Sub),
            Rule::mul_op => Ok(BinOp::Mul),
            Rule::div_op => Ok(BinOp::Div),
            Rule::pow_op => Ok(BinOp::Pow),
            Rule::dot_op => Ok(BinOp::Dot),
            Rule::rem_op => Ok(BinOp::Rem),
            Rule::concat_op => Ok(BinOp::Concat),
            Rule::eq_op => Ok(BinOp::Equ),
            Rule::and_op => Ok(BinOp::And),
            _ => Err(ConversionError::Malformed(InputError::UnexpectedExp(pair)))
        }
    }
}

impl<'pest> FromPest<'pest> for UExp {
    type Rule = Rule;
    type FatalError = InputError<'pest>;

    fn from_pest(
        expression: &mut Pairs<'pest, Self::Rule>,
    ) -> Result<Self, ConversionError<Self::FatalError>> {
        AEXP_PARSER
            .map_primary(|pair| match pair.as_rule() {
                Rule::bool_exp => Ok(Exp::Bool(pair.as_str().parse().unwrap())),
                Rule::id => Ok(Exp::Var(Vid(pair.as_str().to_string()))),
                Rule::positive => Ok(Exp::lit(Size::from_pest(&mut Pairs::single(pair))?)),
                Rule::coef_exp => Ok(Exp::coef(Exp::from_pest(&mut pair.into_inner())?)),
                Rule::mle_exp => Ok(Exp::mle(Exp::from_pest(&mut pair.into_inner())?)),
                Rule::eval_exp => Ok(Exp::eval(Exp::from_pest(&mut pair.into_inner())?)),
                Rule::range_exp => Ok(Exp::range(Range::from_pest(&mut pair.into_inner())?)),
                Rule::minus_exp => {
                    let mut inner = pair.into_inner();
                    let op = BinOp::from_pest(&mut Pairs::single(inner.next().unwrap()))?;
                    let exp = Exp::from_pest(&mut Pairs::single(inner.next().unwrap()))?;
                    Ok(Exp::bin(op, Exp::lit(Size::zero()), exp))
                },
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
                Rule::reduce_exp => {
                    let mut inner = pair.into_inner();
                    Ok(Exp::reduce(
                        BinOp::from_pest(&mut Pairs::single(inner.next().unwrap()))?,
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
                    let func = Vid::from_pest(&mut inner)?;
                    // Arguments
                    let params = Exps::from_pest(&mut inner)?;
                    Ok(Exp::app(func, params))
                },
                Rule::assert_exp => {
                    let mut inner = pair.into_inner();
                    Ok(Exp::assert(UExp::from_pest(&mut Pairs::single(inner.next().unwrap()))?))
                },
                Rule::verify_exp => {
                    let mut inner = pair.into_inner();
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
                Rule::exp => Exp::from_pest(&mut pair.into_inner()),
                _ => Err(ConversionError::Malformed(InputError::UnexpectedExp(pair)))
            })
            .map_infix(|lhs, op, rhs|
                match op.clone().as_rule() {
                    Rule::and_op => Ok(Exp::and(lhs?, rhs?)),
                    Rule::add_op => Ok(Exp::add(lhs?, rhs?)),
                    Rule::sub_op => Ok(Exp::sub(lhs?, rhs?)),
                    Rule::mul_op => Ok(Exp::mul(lhs?, rhs?)),
                    Rule::div_op => Ok(Exp::div(lhs?, rhs?)),
                    Rule::pow_op => Ok(Exp::pow(lhs?, rhs?)),
                    Rule::dot_op => Ok(Exp::dot(lhs?, rhs?)),
                    Rule::rem_op => Ok(Exp::rem(lhs?, rhs?)),
                    Rule::concat_op => Ok(Exp::concat(lhs?, rhs?)),
                    Rule::eq_op => Ok(Exp::equ(lhs?, rhs?)),
                    _ => unreachable!(),
                })
            .map_prefix(|op, rhs| match op.as_rule() {
                Rule::unary_minus => Ok(Exp::sub(Exp::lit(Size::zero()), rhs?)),
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
            Rule::exps => {
                let mut exps = Vec::new();
                for pair in pair.into_inner() {
                    exps.push(UExp::from_pest(&mut Pairs::single(pair))?);
                }
                Ok(Exps(exps))
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
    let mut pairs = ZippelParser::parse(Rule::exp, ex).unwrap();
    assert_eq!(UExp::from_pest(&mut pairs), Ok(Exp::from(2)));
}

#[test]
fn parser_var() {
    let ex = "x";
    let mut pairs = ZippelParser::parse(Rule::exp, ex).unwrap();
    assert_eq!(UExp::from_pest(&mut pairs), Ok(Exp::varstr("x")));
}

#[test]
fn parser_bin() {
    // Add
    let ex1 = "x + 2";
    let mut pairs = ZippelParser::parse(Rule::exp, ex1).unwrap();
    assert_eq!(
        UExp::from_pest(&mut pairs),
        Ok(Exp::varstr("x") + Exp::from(2))
    );

    // Sub
    let ex2 = "x - 2";
    let mut pairs = ZippelParser::parse(Rule::exp, ex2).unwrap();
    assert_eq!(
        UExp::from_pest(&mut pairs),
        Ok(Exp::varstr("x") - Exp::from(2))
    );

    // Mul
    let ex3 = "x * 2";
    let mut pairs = ZippelParser::parse(Rule::exp, ex3).unwrap();
    assert_eq!(
        Exp::from_pest(&mut pairs),
        Ok(Exp::varstr("x") * Exp::from(2))
    );

    // Div
    let ex4 = "x / 2";
    let mut pairs = ZippelParser::parse(Rule::exp, ex4).unwrap();
    assert_eq!(
        UExp::from_pest(&mut pairs),
        Ok(Exp::varstr("x") / Exp::from(2))
    );

    // Pow
    let ex6 = "x ^ 2";
    let mut pairs = ZippelParser::parse(Rule::exp, ex6).unwrap();
    assert_eq!(
        UExp::from_pest(&mut pairs),
        Ok(Exp::pow(Exp::varstr("x"), Exp::from(2)))
    );

    // Dot
    let ex7 = "x . 2";
    let mut pairs = ZippelParser::parse(Rule::exp, ex7).unwrap();
    assert_eq!(
        UExp::from_pest(&mut pairs),
        Ok(Exp::dot(Exp::varstr("x"), Exp::from(2)))
    );

    // Rem
    let ex8 = "x % 2";
    let mut pairs = ZippelParser::parse(Rule::exp, ex8).unwrap();
    assert_eq!(
        UExp::from_pest(&mut pairs),
        Ok(Exp::rem(Exp::varstr("x"), Exp::from(2)))
    );
}

#[test]
fn parser_coef() {
    let ex = "coef([1,2,3])";
    let mut pairs = ZippelParser::parse(Rule::exp, ex).unwrap();
    assert_eq!(
        UExp::from_pest(&mut pairs),
        Ok(Exp::coef(Exp::vec(vec![Exp::from(1), Exp::from(2), Exp::from(3)])))
    );
}

#[test]
fn parser_eval() {
    let ex = "eval(x + 2)";
    let mut pairs = ZippelParser::parse(Rule::exp, ex).unwrap();
    assert_eq!(
        UExp::from_pest(&mut pairs),
        Ok(Exp::eval(Exp::varstr("x") + Exp::from(2)))
    );
}

#[test]
fn parser_call_two() {
    let ex = "f(x + 2, x)";
    let mut pairs = ZippelParser::parse(Rule::exp, ex).unwrap();
    assert_eq!(
        UExp::from_pest(&mut pairs),
        Ok(Exp::app(
            Vid::from("f"),
            Exps(vec![Exp::varstr("x") + Exp::from(2), Exp::varstr("x")])
        ))
    );
}

#[test]
fn parser_range() {
    let ex = "0..N";
    let mut pairs = ZippelParser::parse(Rule::exp, ex).unwrap();
    assert_eq!(
        UExp::from_pest(&mut pairs),
        Ok(Exp::range(Range { start: Size::from(0), step: Size::from(1), end: Size::from("N") }))
    );

    let ex = "(N/2)..N";
    let mut pairs = ZippelParser::parse(Rule::exp, ex).unwrap();
    assert_eq!(
        UExp::from_pest(&mut pairs),
        Ok(Exp::range(Range { start: Size::from("N").div(Size::from(2)), step: Size::from(1), end: Size::from("N") }))
    );
}

#[test]
fn parser_for() {
    let ex = "[ 3^i for i in 0..N ]";
    let mut pairs = ZippelParser::parse(Rule::exp, ex).unwrap();
    assert_eq!(
        UExp::from_pest(&mut pairs),
        Ok(Exp::map(
            Exp::pow(Exp::from(3), Exp::varstr("i")),
            Vid::from("i"),
            Exp::range(Range { start: Size::from(0), step: Size::from(1), end: Size::from("N") }))
        ));
}

#[test]
fn parser_reduce() {
    let ex = "reduce(+, [1,2,3])";
    let mut pairs = ZippelParser::parse(Rule::exp, ex).unwrap();
    assert_eq!(
        UExp::from_pest(&mut pairs),
        Ok(Exp::reduce(
            BinOp::Add,
            Exp::vec(vec![Exp::from(1), Exp::from(2), Exp::from(3)])
        ))
    );
}

#[test]
fn parser_random() {
    let ex = "random<A>";
    let mut pairs = ZippelParser::parse(Rule::exp, ex).unwrap();
    assert_eq!(
        UExp::from_pest(&mut pairs),
        Ok(Exp::random(Tid::from("A")))
    );
}

#[test]
fn parser_challenge() {
    let ex = "challenge<F>";
    let mut pairs = ZippelParser::parse(Rule::exp, ex).unwrap();
    assert_eq!(UExp::from_pest(&mut pairs), Ok(Exp::challenge(Tid::from("F"))));
}

#[test]
fn parser_concat() {
    let ex = "(x + 2) ++ x";
    let mut pairs = ZippelParser::parse(Rule::exp, ex).unwrap();
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
    let mut pairs = ZippelParser::parse(Rule::exp, ex).unwrap();
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
    let mut pairs = ZippelParser::parse(Rule::exp, ex).unwrap();
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
    let ex = "assert(x == 2 && false)";
    let mut pairs = ZippelParser::parse(Rule::exp, ex).unwrap();
    assert_eq!(
        UExp::from_pest(&mut pairs),
        Ok(Exp::assert(
            Exp::and(
                Exp::equ(Exp::varstr("x"), Exp::from(2)),
                Exp::bool(false))
        ))
    );
}

#[test]
fn parser_verify() {
    let ex = "verify(x == 2 && 3 == 4)";
    let mut pairs = ZippelParser::parse(Rule::exp, ex).unwrap();
    assert_eq!(
        UExp::from_pest(&mut pairs),
        Ok(Exp::verify(
            Exp::and(
                Exp::equ(Exp::varstr("x"), Exp::from(2)),
                Exp::equ(Exp::from(3), Exp::from(4)))
        ))
    );
}

#[test]
fn parser_map() {
    let ex = "[ss[i] == s^i for i in 0..N]";
    let mut pairs = ZippelParser::parse(Rule::exp, ex).unwrap();
    assert_eq!(
        UExp::from_pest(&mut pairs),
        Ok(Exp::map(
            Exp::equ(
                Exp::ram(Exp::varstr("ss"), Exp::varstr("i")),
                Exp::pow(Exp::varstr("s"), Exp::varstr("i"))
            ),
            Vid::from("i"),
            Exp::range(Range { start: Size::from(0), step: Size::from(1), end: Size::from("N") })
        ))
    );
}

#[test]
fn parser_seq() {
    let ex = "x <- 2; y <- 3; let x = 2 * 4; 2";
    let mut pairs = ZippelParser::parse(Rule::exps, ex).unwrap();
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

#[test]
fn parser_minus() {
    let ex = "[-x, 3]";
    let mut pairs = ZippelParser::parse(Rule::exp, ex).unwrap();
    assert_eq!(
        UExp::from_pest(&mut pairs),
        Ok(Exp::vec(vec![
            Exp::bin(BinOp::Sub, Exp::lit(Size::zero()), Exp::varstr("x")),
            Exp::from(3)
        ]))
    );
}

#[test]
fn parser_app() {
    let ex = "p(a) == q(a)";
    let mut pairs = ZippelParser::parse(Rule::exp, ex).unwrap();
    assert_eq!(
        UExp::from_pest(&mut pairs),
        Ok(Exp::equ(
            Exp::app(Vid::from("p"), Exps(vec![Exp::varstr("a")])),
            Exp::app(Vid::from("q"), Exps(vec![Exp::varstr("a")]))
        ))
    );
}
