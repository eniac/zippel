use std::{
    collections::{BTreeSet, HashSet},
    convert::From,
    fmt::{self, Debug},
    hash::Hash,
    ops::{Add, Div, Mul, Rem, Sub},
    rc::Rc,
};
use ark_ff::Field;
use pretty::{BoxAllocator, DocAllocator, DocBuilder};

use crate::{
    lang::{
        traits::{Pretty, Proj1, Traversable1},
        context::{Set, Ctx},
        id::{Vid, Fid, Tid},
        types::{
            Nothing,
            Typ,
            Range,
            labels::Label,
            sizes::{
                constraints::Constr,
                eval::{Eval, EvalError}
            }
        }
    },
};

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

/// Represents boolean expressions in the Zippel language.
/// It is parameterized by the type `A` of annotations:
#[derive(Debug, PartialEq, Eq, Clone, PartialOrd, Ord)]
pub enum BExp<T> {

    /// Represents an application of a protocol to a list of arguments.
    ///
    /// **Zippel Code:**
    /// ```zippel
    /// assert<P>(sumcheck(a, b, c));
    /// ```
    App(Fid, Vec<AExp<T>>),

    ///     Represents the equality comparison between two arithmetic expressions.
    ///
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let a = (5 == 5);
    ///     ```
    ///
    ///     **Rust Representation:**
    ///     ```rust
    ///     BExp::Eq(AExp::Lit(5), AExp::Lit(5))
    ///     ```
    Eq(AExp<T>, AExp<T>),

    ///     Represents the logical AND of two boolean expressions.
    ///
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let a = (true && false);
    ///     ```
    ///
    ///     **Rust Representation:**
    ///     ```rust
    ///     BExp::And(Box::new(BExp::TrueE), Box::new(BExp::FalseE))
    ///     ```
    And(Box<BExp<T>>, Box<BExp<T>>),

    ///     Represents the logical OR of two boolean expressions.
    ///
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let a = (true || false);
    ///     ```
    ///
    ///     **Rust Representation:**
    ///     ```rust
    ///     BExp::Or(Box::new(BExp::TrueE), Box::new(BExp::FalseE))
    ///     ```
    Or(Box<BExp<T>>, Box<BExp<T>>),
}

/// Represents arithmetic expressions in the Zippel language.
/// It is parameterized by a type `A` that represents the annotations that can be attached to each
/// expression.
#[derive(Debug, PartialEq, Eq, Clone, PartialOrd, Ord)]
pub enum AExp<A> {
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
    App(Fid, Vec<AExp<A>>, A),

    ///     Fold over non-empty vector
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let sum = reduce(+, v)
    ///     ```
    Reduce(BinOp, Box<AExp<A>>, A),

    ///     Coefficients of a univariate vector
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let v = coef [1,2,1]; // 1 + 2x + x^2
    ///     ```
    Coef(Box<AExp<A>>, A),

    ///     Multilinear extension of a matrix, polynomial, etc.
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let g = mle x;
    ///     ```
    Mle(Box<AExp<A>>, A),

    ///     A vector of elements
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let v = [1, 2*x, x+y];
    ///     ```
    Vec(Vec<AExp<A>>, A),

    ///     Binary operation
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let sum = 2 + 3;
    ///     ```
    Bin(BinOp, Box<AExp<A>>, Box<AExp<A>>, A),

    ///     **Zippel Code:**
    ///     ```zippel
    ///     let r = [0..5];
    ///     ```
    Range(Range, A),

    ///     Map comprehension
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let squares = [x^2 for x in 0,2..10];
    ///     ```
    Map(Box<AExp<A>>, Vid, Box<AExp<A>>, A),

    ///     Index or slice a vector
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let first = v[0]
    ///     ```
    Index(Box<AExp<A>>, Box<AExp<A>>, A),

    ///     Sample pseudo-random number generator
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let r := random<F>();
    ///     ```
    Random(Typ, A),

    ///     Random oracle challenge.
    ///     **Zippel Code:**
    ///     ```zippel
    ///     r <- challenge<F>();
    ///     ```
    Challenge(Typ, A),

    ///     Convert from evaluation domain to lagrange domain.
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let p = interpolate([1, 2], [0, 3]);
    ///     ```
    Interpolate(Box<AExp<A>>, Box<AExp<A>>, A),

    ///     Represents a let-expression, which binds a value to an identifier.
    ///
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let x = 5 + 3;
    ///     ```
    Let(Vid, Box<AExp<A>>, Box<AExp<A>>, A),

    ///     Represents a log-let expression with transcript dependency.
    ///     This variant is used to bind a value to an identifier while logging the operation.
    ///     **Zippel Code:**
    ///     ```zippel
    ///     p <- interpolate(v, [0,1,2])
    ///     ```
    Log(Vid, Box<AExp<A>>, Box<AExp<A>>, A),

    ///     Prover assertion followed by expression.
    ///     **Zippel Code:**
    ///     ```zippel
    ///     assert(1 == 1);
    ///     ...
    ///     ```
    Assert(Box<BExp<A>>, Box<AExp<A>>, A),

    ///     Verifier check followed by expression.
    ///     **Zippel Code:**
    ///     ```zippel
    ///     verify(a == a);
    ///     ...
    ///     ```
    Verify(Box<BExp<A>>, Box<AExp<A>>, A)
}

/// Typed AST node
pub type TAExp<A> = AExp<(A, Typ)>;
pub type TBExp<A> = BExp<(A, Typ)>;

/// Cost instance for AExp
impl<A> Cost for AExp<A> {
    fn runtime(&self, num_thread: usize) -> f64 {
        let fnum_thread = num_thread as f64;
        match self {
            AExp::Lit(_, _) => 1.0,
            AExp::Var(_, _) => 2.0,
            AExp::Bin(_, _, _, _) => (30.0 + (50.0 / fnum_thread)),
            AExp::Coef(_, _) => (40.0 + (50.0 / fnum_thread)),
            AExp::Mle(_, _) => (40.0 + (50.0 / fnum_thread)),
            AExp::App(_, _, _) => (50.0 + (50.0 / fnum_thread)),
            AExp::Vec(_, _) => (60.0 + (50.0 / fnum_thread)),
            AExp::Map(_, _, _, _) => (70.0 + (50.0 / fnum_thread)),
            AExp::Concat(_, _, _) => (80.0 + (50.0 / fnum_thread)),
            AExp::Reduce(_, _, _) => (90.0 + (50.0 / fnum_thread)),
            AExp::Random(_, _) => (100.0 + (50.0 / fnum_thread)),
            AExp::Challenge(_, _) => (100.0 + (50.0 / fnum_thread)),
            AExp::Gen(_, _) => (100.0 + (50.0 / fnum_thread)),
            AExp::Interpolate(_, _, _) => (110.0 + (50.0 / fnum_thread)),
            AExp::Index(_, _, _) => (120.0 + (50.0 / fnum_thread)),
            AExp::Let(_, _, _, _) => (130.0 + (50.0 / fnum_thread)),
            AExp::Log(_, _, _, _) => (140.0 + (50.0 / fnum_thread)),
            AExp::Assert(_, _, _) => (150.0 + (50.0 / fnum_thread)),
            AExp::Range(_, _) => (150.0 + (50.0 / fnum_thread)),
        }
    }

    fn memory(&self, num_thread: usize) -> f64 {
        unimplemented!()
    }
}

/// Cost instance for BExp
impl<T> Cost for BExp<T> {
    fn runtime(&self, num_thread: usize) -> f64 {
        let fnum_thread = num_thread as f64;
        match self {
            BExp::And(_, _) => 12.0,
            BExp::Or(_, _) => 13.0,
            BExp::Eq(_, _) => 14.0,
            BExp::App(_, _) => 15.0,
        }
    }
    fn memory(&self, num_thread: usize) -> f64 {
        unimplemented!()
    }
}

/// Take the annotation
impl<N> Proj1<N> for AExp<N> {
    fn proj1(&self) -> &N {
        match self {
            AExp::Lit(_, t) => t,
            AExp::Var(_, t) => t,
            AExp::Coef(_, t) => t,
            AExp::Mle(_, t) => t,
            AExp::Vec(_, t) => t,
            AExp::Bin(_, _, _, t) => t,
            AExp::Map(_, _, _, t) => t,
            AExp::Concat(_, _, t) => t,
            AExp::Challenge(_, t) => t,
            AExp::App(_, _, t) => t,
            AExp::Reduce(_, _, t) => t,
            AExp::Interpolate(_, _, t) => t,
            AExp::Index(_, _, t) => t,
            AExp::Range(_, t) => t,
            AExp::Let(_, _, _, t) => t,
            AExp::Log(_, _, _, t) => t,
            AExp::Assert(_, _, t) => t,
            AExp::Gen(_, t) => t,
        }
    }
}

impl<T> Traversable1<T> for AExp<T> {
    type Output<Z> = AExp<Z>;

    fn traverse1<Z, E>(self, mut f: &mut dyn FnMut(T) -> Result<Z, E>) -> Result<AExp<Z>, E> {
        match self {
            AExp::Lit(x, a) => Ok(AExp::Lit(x, f(a)?)),
            AExp::Var(v, a) => Ok(AExp::Var(v, f(a)?)),
            AExp::Coef(box p, a) => Ok(AExp::coef(p.traverse1(f)?, f(a)?)),
            AExp::Mle(box p, a) => Ok(AExp::mle(p.traverse1(f)?, f(a)?)),
            AExp::Vec(v, a) =>
                Ok(AExp::Vec(v.traverse1(&mut |x| x.traverse1(f))?, f(a)?)),
            AExp::App(x, ts, a) =>
                Ok(AExp::App(x, ts.traverse1(&mut |x| x.traverse1(f))? , f(a)?)),
            AExp::Reduce(op, box d, a) =>
                Ok(AExp::reduce(op, d.traverse1(f)?, f(a)?)),
            AExp::Bin(op, box x, box y, a) =>
                Ok(AExp::bin(
                    op,
                    x.traverse1(f)?,
                    y.traverse1(f)?,
                    f(a)?
                )),
            AExp::Map(box x, id, box r, a) => {
                Ok(AExp::map(x.traverse1(f)?, id, r.traverse1(f)?, f(a)?))
            }
            AExp::Concat(box x, box y, a) =>
                Ok(AExp::concat(
                    x.traverse1(f)?,
                    y.traverse1(f)?,
                    f(a)?
                )),
            AExp::Challenge(t, a) => Ok(AExp::challenge(t, f(a)?)),
            AExp::Gen(t, a) => Ok(AExp::gen(t, f(a)?)),
            AExp::Range(r, a) => Ok(AExp::range(r, f(a)?)),
            AExp::Interpolate(box x, box y, a) =>
                Ok(AExp::interpolate(
                    x.traverse1(f)?,
                    y.traverse1(f)?,
                    f(a)?
                )),
            AExp::Reduce(op, box x, a) =>
                Ok(AExp::reduce(op,
                    x.traverse1(f)?,
                    f(a)?
                )),
            AExp::Index(box x, box i, a) =>
                Ok(AExp::index(
                        x.traverse1(f)?,
                        i.traverse1(f)?,
                        f(a)?
                )),
            AExp::Let(x, box a, box b, t) =>
                Ok(AExp::letx(x, a.traverse1(f)?, b.traverse1(f)?, f(t)?)),
            AExp::Log(x, box a, box b, t) =>
                Ok(AExp::log(x, a.traverse1(f)?, b.traverse1(f)?, f(t)?)),
            AExp::Assert(x, box t, a) =>
                Ok(AExp::assert(x.traverse1(f)?, t.traverse1(f)?, f(a)?))
        }
    }
}

/// Combine BExp and AExp into one sum type for graph traversal
#[derive(Eq, PartialEq, Clone, PartialOrd, Ord, Debug)]
pub enum Exp<T> {
    A(AExp<T>),
    B(BExp<T>),
}

/// Typed AST node
pub type TExp<A> = Exp<(A, Typ)>;

impl BinOp {
    pub fn is_assoc(&self) -> bool {
        self == &BinOp::Add || self == &BinOp::Mul || self == &BinOp::Dot
    }
}

/// Construct untyped expressions and type infer later [types/infer.rs]
impl<N> AExp<N> {
    /// Annotated constructors
    pub fn lit(v: u32, ann: N) -> Self {
        AExp::Lit(v, ann)
    }
    pub fn bin(op: BinOp, l: Self, r: Self, ann: N) -> Self {
        AExp::Bin(op, Box::new(l), Box::new(r), ann)
    }
    pub fn gen(t: Tid, ann: N) -> Self {
        AExp::Gen(t, ann)
    }
    pub fn coef(a: Self, ann: N) -> Self {
        AExp::Coef(Box::new(a), ann)
    }
    pub fn mle(a: Self, ann: N) -> Self {
        AExp::Mle(Box::new(a), ann)
    }
    pub fn interpolate(e: Self, d: Self, ann: N) -> Self {
        AExp::Interpolate(Box::new(e), Box::new(d), ann)
    }
    pub fn challenge(t: Typ, ann: N) -> Self {
        AExp::Challenge(t, ann)
    }
    pub fn vec(v: Vec<Self>, ann: N) -> Self {
        AExp::Vec(v, ann)
    }
    pub fn concat(a: Self, b: Self, ann: N) -> Self {
        AExp::Concat(Box::new(a), Box::new(b), ann)
    }
    pub fn map(l: Self, x: Vid, range: Self, ann: N) -> Self {
        AExp::Map(Box::new(l), x, Box::new(range), ann)
    }
    pub fn index(v: Self, i: Self, ann: N) -> Self {
        AExp::Index(Box::new(v), Box::new(i), ann)
    }
    pub fn range(r: Range, ann: N) -> Self {
        AExp::Range(r, ann)
    }
    pub fn add(l: Self, r: Self, ann: N) -> Self {
        AExp::Bin(BinOp::Add, Box::new(l), Box::new(r), ann)
    }
    pub fn sub(l: Self, r: Self, ann: N) -> Self {
        AExp::Bin(BinOp::Sub, Box::new(l), Box::new(r), ann)
    }
    pub fn mul(l: Self, r: Self, ann: N) -> Self {
        AExp::Bin(BinOp::Mul, Box::new(l), Box::new(r), ann)
    }
    pub fn div(l: Self, r: Self, ann: N) -> Self {
        AExp::Bin(BinOp::Div, Box::new(l), Box::new(r), ann)
    }
    pub fn pow(l: Self, r: Self, ann: N) -> Self {
        AExp::Bin(BinOp::Pow, Box::new(l), Box::new(r), ann)
    }
    pub fn dot(l: Self, r: Self, ann: N) -> Self {
        AExp::Bin(BinOp::Dot, Box::new(l), Box::new(r), ann)
    }
    pub fn var(x: Vid, ann: N) -> Self {
        AExp::Var(x, ann)
    }
    pub fn varstr<'a>(x: &'a str, ann: N) -> Self {
        AExp::var(Vid::from(x), ann)
    }
    pub fn app(e: Fid, d: Vec<Self>, ann: N) -> Self {
        AExp::App(e, d, ann)
    }
    pub fn reduce(op: BinOp, d: Self, ann: N) -> Self {
        AExp::Reduce(op, Box::new(d), ann)
    }
    pub fn assert(b: BExp<N>, d: Self, ann: N) -> Self {
        AExp::Assert(Box::new(b), Box::new(d), ann)
    }
    pub fn verify(b: BExp<N>, d: Self, ann: N) -> Self {
        AExp::Verify(Box::new(b), Box::new(d), ann)
    }
    pub fn letx(a: Vid, d: Self, e: Self, ann: N) -> Self {
        AExp::Let(a, Box::new(d), Box::new(e), ann)
    }
    pub fn log(a: Vid, d: Self, e: Self, ann: N) -> Self {
        AExp::Log(a, Box::new(d), Box::new(e), ann)
    }
}

impl AExp<Nothing> {
    /// Unannotated constructors
    pub fn ulit(v: u32) -> Self {
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
    pub fn uchallenge(t: Typ) -> Self {
        AExp::challenge(t, Nothing)
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
    pub fn uindex(v: Self, i: Self) -> Self {
        AExp::index(v, i, Nothing)
    }
    pub fn urange(r: Range) -> Self {
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
    pub fn uapp(e: Fid, d: Vec<Self>) -> Self {
        AExp::App(e, d, Nothing)
    }
    pub fn ureduce(op: BinOp, d: Self) -> Self {
        AExp::Reduce(op, Box::new(d), Nothing)
    }
    pub fn uassert(b: BExp<Nothing>, d: Self) -> Self {
        AExp::Assert(Box::new(b), Box::new(d), Nothing)
    }
    pub fn uverify(b: BExp<Nothing>, d: Self) -> Self {
        AExp::Verify(Box::new(b), Box::new(d), Nothing)
    }
    pub fn uletx(a: Vid, d: Self, e: Self) -> Self {
        AExp::Let(a, Box::new(d), Box::new(e), Nothing)
    }
    pub fn ulog(a: Vid, d: Self, e: Self) -> Self {
        AExp::Log(a, Box::new(d), Box::new(e), Nothing)
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

/// Pretty printer instance for Arg
impl<'a, D, A> Pretty<'a, D, A> for Arg
where
    D: DocAllocator<'a, A>,
    D::Doc: Clone,
    A: 'a + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        allocator.concat([
            self.label.pretty(allocator),
            allocator.space(),
            self.id.pretty(allocator),
            allocator.text(": "),
            self.typ.pretty(allocator)
        ])
    }

    fn is_nil(&self) -> bool {
        false
    }
}

/// Pretty printer instance for typed AExp
impl<'a, D, A, T> Pretty<'a, D, A> for AExp<T>
where
    D: DocAllocator<'a, A>,
    D::Doc: Clone,
    T: Pretty<'a, D, A>,
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
            AExp::Concat(a, b, t) => allocator.concat([
                allocator.text("("),
                (*a).pretty(allocator),
                allocator.text(" ++ "),
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
                allocator.intersperse(d.into_iter().map(|x| x.pretty(allocator)), ", "),
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
            AExp::Index(x, i, t) => allocator.concat([
                x.pretty(allocator),
                allocator.text("["),
                (*i).pretty(allocator),
                allocator.text("]"),
                if t.is_nil() {
                    allocator.nil()
                } else {
                    allocator.text("⇝").append(t.pretty(allocator))
                }]),
            AExp::Let(x, a, b, t) => allocator.concat([
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
                allocator.line(),
                (*b).pretty(allocator),
            ]),
            AExp::Log(x, a, b, t) => allocator.concat([
                x.pretty(allocator),
                allocator.text(" <- "),
                (*a).pretty(allocator),
                allocator.text("; "),
                if t.is_nil() {
                    allocator.nil()
                } else {
                    allocator.text("⇝").append(t.pretty(allocator))
                },
                allocator.line(),
                (*b).pretty(allocator),
            ]),
            AExp::Assert(c, b, t) => allocator.concat([
                allocator.text("assert("),
                (*c).pretty(allocator),
                allocator.text("); "),
                if t.is_nil() {
                    allocator.nil()
                } else {
                    allocator.text("⇝").append(t.pretty(allocator))
                },
                allocator.line(),
                (*b).pretty(allocator)
            ]),
            AExp::Verify(c, b, t) => allocator.concat([
                allocator.text("verify("),
                (*c).pretty(allocator),
                allocator.text("); "),
                if t.is_nil() {
                    allocator.nil()
                } else {
                    allocator.text("⇝").append(t.pretty(allocator))
                },
                allocator.line(),
                (*b).pretty(allocator)
            ])
        }
    }

    fn is_nil(&self) -> bool {
        false
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

impl fmt::Display for Arg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <Arg as Pretty<'_, BoxAllocator, ()>>::pretty(self.clone(), &BoxAllocator)
            .1
            .render_fmt(100, f)
    }
}

impl<'a, T> fmt::Display for AExp<T>
where
    T: Clone + Pretty<'a, BoxAllocator, ()>,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <AExp<T> as Pretty<'_, BoxAllocator, ()>>::pretty(self.clone(), &BoxAllocator)
            .1
            .render_fmt(100, f)
    }
}

/// BExp is a traversable on the second type parameter
impl<T> Traversable1<T> for BExp<T> {
    type Output<Z> = BExp<Z>;

    fn traverse1<Z, E>(self, mut f: &mut dyn FnMut(T) -> Result<Z, E>) -> Result<BExp<Z>, E> {
        match self {
            BExp::Eq(a, b) => Ok(BExp::Eq(a.traverse1(f)?, b.traverse1(f)?)),
            BExp::App(id, v) =>
                Ok(BExp::App(id, v.traverse1(&mut |e| e.traverse1(f))?)),
            BExp::And(a, b) => Ok(BExp::And(
                a.traverse1(&mut |b| b.traverse1(f))?,
                b.traverse1(&mut |b| b.traverse1(f))?,
            )),
            BExp::Or(a, b) => Ok(BExp::Or(
                a.traverse1(&mut |b| b.traverse1(f))?,
                b.traverse1(&mut |b| b.traverse1(f))?,
            )),
        }
    }
}

/// Constructor for BExp
impl<T> BExp<T> {
    pub fn and(l: Self, r: Self) -> Self {
        BExp::And(Box::new(l), Box::new(r))
    }
    pub fn or(l: Self, r: Self) -> Self {
        BExp::Or(Box::new(l), Box::new(r))
    }
    pub fn eq(l: AExp<T>, r: AExp<T>) -> Self {
        BExp::Eq(l, r)
    }
    pub fn app(id: Fid, args: Vec<AExp<T>>) -> Self {
        BExp::App(id, args)
    }
}

/// Pretty printer instance
impl<'a, D, A, T> Pretty<'a, D, A> for BExp<T>
where
    T: Pretty<'a, D, A>,
    D: DocAllocator<'a, A>,
    D::Doc: Clone,
    A: 'a + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        match self {
            BExp::Eq(a, b) => allocator.concat([
                a.pretty(allocator),
                allocator.text(" == "),
                b.pretty(allocator),
            ]),
            BExp::App(id, args) => allocator.concat([
                id.pretty(allocator),
                allocator.text("("),
                allocator.intersperse(args.into_iter().map(|a| a.pretty(allocator)), ", "),
                allocator.text(")"),
            ]),
            BExp::And(a, b) => allocator.concat([
                (*a).pretty(allocator),
                allocator.text(" && "),
                (*b).pretty(allocator),
            ]),
            BExp::Or(a, b) => allocator.concat([
                (*a).pretty(allocator),
                allocator.text(" || "),
                (*b).pretty(allocator),
            ]),
        }
    }

    fn is_nil(&self) -> bool {
        false
    }
}

/// Display instance calls the pretty printer
impl<'a, T> fmt::Display for BExp<T>
where
    T: Clone + Pretty<'a, BoxAllocator, ()>,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <BExp<T> as Pretty<'_, BoxAllocator, ()>>::pretty(self.clone(), &BoxAllocator)
            .1
            .render_fmt(100, f)
    }
}

/// Pretty printer instance for Exp
impl<'a, D, A, T> Pretty<'a, D, A> for Exp<T>
where
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
impl<'a, T> fmt::Display for Exp<T>
where
    T: Clone + Pretty<'a, BoxAllocator, ()>,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <Exp<T> as Pretty<'_, BoxAllocator, ()>>::pretty(self.clone(), &BoxAllocator)
            .1
            .render_fmt(30, f)
    }
}

impl<T> Cost for Exp<T> {
    fn runtime(&self, num_thread: usize) -> f64 {
        match self {
            Exp::A(aexp) => aexp.runtime(num_thread),
            Exp::B(bexp) => bexp.runtime(num_thread),
        }
    }

    fn memory(&self, num_thread: usize) -> f64 {
        match self {
            Exp::A(aexp) => aexp.memory(num_thread),
            Exp::B(bexp) => bexp.memory(num_thread),
        }
    }
}
