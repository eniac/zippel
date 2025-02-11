mod aexp;
mod bexp;

pub use aexp::{AExp, TAExp, UAExp};
pub use bexp::{BExp, TBExp, UBExp};

use std::{
    convert::From,
    fmt::{self, Debug},
    hash::Hash,
    ops::{Add, Div, Mul, Rem, Sub},
    rc::Rc,
};
use share::Pretty;

/// Combine BExp and AExp into one sum type for graph traversal
#[derive(Eq, PartialEq, Clone, PartialOrd, Ord, Debug)]
pub enum Exp<N, T> {
    A(AExp<N, T>),
    B(BExp<N, T>),
}

/// Typed AST node
pub type TExp<N, A> = Exp<(A, Typ<N>)>;


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
