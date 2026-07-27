use crate::parser::*;
use from_pest::{ConversionError, FromPest};
use lazy_static::lazy_static;
use pest::iterators::{Pair, Pairs};
use pest::pratt_parser::{Assoc, Op, PrattParser};
use share::Ctx;
use std::fmt;
use std::ops::{Add, BitXor, Div, Index, Mul, Rem, Sub};

use share::traversal::ToTraversal1;

use crate::id::{Tid, TidSubst, Vid};
use crate::typ::range::{Range, RangeTraversal};
use crate::typ::GTyp;
use crate::typ::Size;
use share::{BoxAllocator, DocAllocator, DocBuilder, Pretty, Set};

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

    ///     Unit value (the empty value of type Unit)
    Unit,

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

    /// Interpolate to a univariate polynomial: unary `interpolate(v)` uses the FFT
    /// evaluation grid (inverse FFT); binary `interpolate(xs, ys)` uses explicit points.
    ///
    /// **Zippel:**
    /// ```zippel
    /// let p_grid = interpolate(evals_on_fft_domain);
    /// let q = interpolate([0, 1, 2], [a, b, c]);
    /// ```
    Interpolate(Option<Box<Exp<N>>>, Box<Exp<N>>),

    ///     Polynomial from coefficients
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let p = poly(1,2,3);
    ///     ```
    Poly(Box<Exp<N>>),

    /// Evaluate a polynomial. Unary `eval(p)` evaluates on the FFT grid (FFT);
    /// binary `eval(p, points)` evaluates at explicit points (scalar or vector);
    /// selected `eval<range>(p, fixed)` keeps a contiguous range of variables
    /// free and fixes every variable outside that range.
    ///
    /// **Zippel:**
    /// ```zippel
    /// let evs = eval(p);                    // FFT-grid evaluation
    /// let v   = eval(p, point);             // single-point eval
    /// let vs  = eval(p, [x0, x1, x2]);      // batch eval
    /// let g   = eval<0>(p, tail);           // unit-range sugar for eval<0..1>
    /// let h   = eval<1..3>(p, fixed);       // keep variables 1 and 2 free
    /// ```
    Evaluate(Box<Exp<N>>, Option<Range<N>>, Option<Box<Exp<N>>>),

    ///     Get vector of coefficients of polynomial
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let v = coef(poly(1,2,3));
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

    ///     Bilinear pairing
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let g = pair(g1, g2);
    ///     ```
    Pair(Box<Exp<N>>, Box<Exp<N>>),

    ///     Sample pseudo-random number generator
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let r := random<F*>();
    ///     ```
    Random(Tid, bool),

    ///     Random oracle challenge.
    ///     **Zippel Code:**
    ///     ```zippel
    ///     r <- challenge<F>();
    ///     ```
    Challenge(Tid, bool),

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

    ///     Prover assertion: asserts `lhs == rhs`.
    ///     **Zippel Code:**
    ///     ```zippel
    ///     assert(1 == 1)
    ///     ```
    Assert(Box<Exp<N>>, Box<Exp<N>>),

    ///     Verifier check: verifies `lhs == rhs`.
    ///     **Zippel Code:**
    ///     ```zippel
    ///     verify(a == a)
    ///     ```
    Verify(Box<Exp<N>>, Box<Exp<N>>),

    ///     Polynomial function definition
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let p = fun x, y => x^2 + 2*x*y + 3*y^2;
    ///     ```
    Fun(Vec<Vid>, Box<Exp<N>>),

    ///     Record construction
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let a = {| name: "Sydnie", balance: 100 |};
    ///     ```
    Record(Ctx<String, Exp<N>>),

    ///     Field projection
    ///     **Zippel Code:**
    ///     ```zippel
    ///     a.name
    ///     ```
    Proj(Box<Exp<N>>, String),

    ///     Record update: create a new record identical to the given record
    ///     except with the specified field set to the given value.
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let new_record = old_record.set(name, 3);
    ///     ```
    SetRecord(Box<Exp<N>>, String, Box<Exp<N>>),
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
impl<N: Clone> ToTraversal1<N> for Exp<N> {
    type Output<Z> = Exp<Z>;
    fn traverse1<Z: Clone, E>(self, f: &mut dyn FnMut(N) -> Result<Z, E>) -> Result<Exp<Z>, E> {
        match self {
            Exp::Lit(x) => Ok(Exp::Lit(f(x)?)),
            Exp::Unit => Ok(Exp::Unit),
            Exp::Var(v) => Ok(Exp::Var(v)),
            Exp::Interpolate(po, box evals) => Ok(Exp::Interpolate(
                match po {
                    None => None,
                    Some(box p) => Some(Box::new(p.traverse1(f)?)),
                },
                Box::new(evals.traverse1(f)?),
            )),
            Exp::Poly(box p) => Ok(Exp::Poly(Box::new(p.traverse1(f)?))),
            Exp::Evaluate(box p, selector, ox) => Ok(Exp::Evaluate(
                Box::new(p.traverse1(f)?),
                match selector {
                    None => None,
                    Some(r) => Some(r.traverse1(f)?),
                },
                match ox {
                    None => None,
                    Some(box x) => Some(Box::new(x.traverse1(f)?)),
                },
            )),
            Exp::Coef(box p) => Ok(Exp::Coef(Box::new(p.traverse1(f)?))),
            Exp::Mle(box p) => Ok(Exp::Mle(Box::new(p.traverse1(f)?))),
            Exp::Pair(box x, box y) => Ok(Exp::Pair(
                Box::new(x.traverse1(f)?),
                Box::new(y.traverse1(f)?),
            )),
            Exp::Vec(v) => Ok(Exp::Vec(v.traverse1(f)?)),
            Exp::App(x, ts) => Ok(Exp::App(x, ts.traverse1(f)?)),
            Exp::Bin(op, box x, box y) => Ok(Exp::Bin(
                op,
                Box::new(x.traverse1(f)?),
                Box::new(y.traverse1(f)?),
            )),
            Exp::Map(box x, id, box r) => Ok(Exp::Map(
                Box::new(x.traverse1(f)?),
                id,
                Box::new(r.traverse1(f)?),
            )),
            Exp::Reduce(op, box x) => Ok(Exp::Reduce(op, Box::new(x.traverse1(f)?))),
            Exp::Challenge(t, b) => Ok(Exp::Challenge(t, b)),
            Exp::Random(t, b) => Ok(Exp::Random(t, b)),
            Exp::Range(r) => Ok(Exp::Range(r.traverse1(f)?)),
            Exp::Ram(box x, box i) => Ok(Exp::Ram(
                Box::new(x.traverse1(f)?),
                Box::new(i.traverse1(f)?),
            )),
            Exp::Let(x, box a, box b) => Ok(Exp::Let(
                x,
                Box::new(a.traverse1(f)?),
                Box::new(b.traverse1(f)?),
            )),
            Exp::Log(x, box a, box b) => Ok(Exp::Log(
                x,
                Box::new(a.traverse1(f)?),
                Box::new(b.traverse1(f)?),
            )),
            Exp::Assert(box lhs, box rhs) => Ok(Exp::Assert(
                Box::new(lhs.traverse1(f)?),
                Box::new(rhs.traverse1(f)?),
            )),
            Exp::Verify(box lhs, box rhs) => Ok(Exp::Verify(
                Box::new(lhs.traverse1(f)?),
                Box::new(rhs.traverse1(f)?),
            )),
            Exp::Fun(vars, box body) => Ok(Exp::Fun(vars, Box::new(body.traverse1(f)?))),
            Exp::Record(fields) => {
                let pairs: Vec<_> = fields
                    .into_iter()
                    .map(|(name, exp)| exp.traverse1(f).map(|new_exp| (name, new_exp)))
                    .collect::<Result<_, _>>()?;
                Ok(Exp::Record(Ctx::from_iter(pairs)))
            }
            Exp::Proj(box exp, field) => Ok(Exp::Proj(Box::new(exp.traverse1(f)?), field)),
            Exp::SetRecord(box record, field, box value) => Ok(Exp::SetRecord(
                Box::new(record.traverse1(f)?),
                field,
                Box::new(value.traverse1(f)?),
            )),
        }
    }
}

/// How to traverse the first type parameter [N] for Exps<N>
impl<N: Clone> ToTraversal1<N> for Exps<N> {
    type Output<Z> = Exps<Z>;
    fn traverse1<Z: Clone, E>(self, f: &mut dyn FnMut(N) -> Result<Z, E>) -> Result<Exps<Z>, E> {
        Ok(Exps(
            self.0
                .into_iter()
                .map(|x| x.traverse1(f))
                .collect::<Result<_, _>>()?,
        ))
    }
}

/// Traverse [Tid] inside [TExp]
impl TidSubst for CExp {
    fn tid_subst(&mut self, from: &Tid, to: &Tid) {
        match self {
            Exp::Challenge(t, _) if t == from => *t = to.clone(),
            Exp::Random(t, _) if t == from => *t = to.clone(),
            Exp::Interpolate(None, box e) => e.tid_subst(from, to),
            Exp::Interpolate(Some(box p), box e) => {
                p.tid_subst(from, to);
                e.tid_subst(from, to);
            }
            Exp::Evaluate(box p, _, None) => p.tid_subst(from, to),
            Exp::Evaluate(box p, _, Some(box x)) => {
                p.tid_subst(from, to);
                x.tid_subst(from, to);
            }
            Exp::Mle(box p) | Exp::Poly(box p) | Exp::Reduce(_, box p) | Exp::Coef(box p) => {
                p.tid_subst(from, to)
            }
            Exp::Assert(box lhs, box rhs) | Exp::Verify(box lhs, box rhs) => {
                lhs.tid_subst(from, to);
                rhs.tid_subst(from, to);
            }
            Exp::Vec(v) | Exp::App(_, v) => v.tid_subst(from, to),
            Exp::Bin(_, box a, box b)
            | Exp::Map(box a, _, box b)
            | Exp::Ram(box a, box b)
            | Exp::Let(_, box a, box b)
            | Exp::Log(_, box a, box b)
            | Exp::Pair(box a, box b) => {
                a.tid_subst(from, to);
                b.tid_subst(from, to);
            }
            Exp::Fun(_, box body) => body.tid_subst(from, to),
            Exp::Record(fields) => {
                fields.modify(|_, field_exp| {
                    field_exp.tid_subst(from, to);
                });
            }
            Exp::Proj(box exp, _) => exp.tid_subst(from, to),
            Exp::SetRecord(box record, _, box value) => {
                record.tid_subst(from, to);
                value.tid_subst(from, to);
            }
            Exp::Lit(_)
            | Exp::Unit
            | Exp::Var(_)
            | Exp::Range(_)
            | Exp::Challenge(_, _)
            | Exp::Random(_, _) => {}
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
            Exp::Unit | Exp::Challenge(_, _) | Exp::Random(_, _) | Exp::Lit(_) | Exp::Range(_) => {
                Set::new()
            }
            Exp::Interpolate(points, evals) => match points {
                None => evals.freevars(),
                Some(p) => p.freevars().union(evals.freevars()),
            },
            Exp::Evaluate(p, _, points) => match points {
                None => p.freevars(),
                Some(x) => p.freevars().union(x.freevars()),
            },
            Exp::Mle(box p) | Exp::Poly(box p) | Exp::Reduce(_, box p) | Exp::Coef(box p) => {
                p.freevars()
            }
            Exp::Assert(box lhs, box rhs) | Exp::Verify(box lhs, box rhs) => {
                lhs.freevars().union(rhs.freevars())
            }
            Exp::Vec(v) | Exp::App(_, v) => v.freevars(),
            Exp::Bin(_, box a, box b)
            | Exp::Pair(box a, box b)
            | Exp::Ram(box a, box b)
            | Exp::Map(box a, _, box b)
            | Exp::Let(_, box a, box b)
            | Exp::Log(_, box a, box b) => a.freevars().union(b.freevars()),
            Exp::Fun(vars, box body) => {
                let bound_vars: Set<Vid> = vars.iter().cloned().collect();
                body.freevars()
                    .into_iter()
                    .filter(|v| !bound_vars.iter().any(|bv| bv == v))
                    .collect()
            }
            Exp::Record(fields) => fields
                .iter()
                .map(|(_, exp)| exp.freevars())
                .fold(Set::new(), |acc, x| acc.union(x)),
            Exp::Proj(box exp, _) => exp.freevars(),
            Exp::SetRecord(box record, _, box value) => record.freevars().union(value.freevars()),
        }
    }
}

impl FreeVars for CExps {
    fn freevars(&self) -> Set<Vid> {
        self.0
            .iter()
            .map(|x| x.freevars())
            .fold(Set::new(), |acc, x| acc.union(x))
    }
}

/// How to traverse [Range] inside an [Exp]
impl<N: Clone> RangeTraversal<N> for Exp<N> {
    fn range_traverse<E>(
        self,
        f: &mut dyn FnMut(Range<N>) -> Result<Range<N>, E>,
    ) -> Result<Self, E> {
        match self {
            Exp::Range(r) => Ok(Exp::Range(f(r)?)),
            Exp::Interpolate(po, box evals) => Ok(Exp::interpolate(
                match po {
                    None => None,
                    Some(box p) => Some(p.range_traverse(f)?),
                },
                evals.range_traverse(f)?,
            )),
            Exp::Poly(box p) => Ok(Exp::poly(p.range_traverse(f)?)),
            Exp::Mle(box p) => Ok(Exp::mle(p.range_traverse(f)?)),
            Exp::Vec(v) => Ok(Exp::Vec(v.range_traverse(f)?)),
            Exp::Evaluate(box p, selector, ox) => Ok(Exp::evaluate(
                p.range_traverse(f)?,
                match selector {
                    None => None,
                    Some(r) => Some(f(r)?),
                },
                match ox {
                    None => None,
                    Some(box x) => Some(x.range_traverse(f)?),
                },
            )),
            Exp::Bin(op, box x, box y) => {
                Ok(Exp::bin(op, x.range_traverse(f)?, y.range_traverse(f)?))
            }
            Exp::Map(box x, id, box r) => {
                Ok(Exp::map(x.range_traverse(f)?, id, r.range_traverse(f)?))
            }
            Exp::Ram(box x, box i) => Ok(Exp::ram(x.range_traverse(f)?, i.range_traverse(f)?)),
            Exp::Coef(box x) => Ok(Exp::coef(x.range_traverse(f)?)),
            Exp::Let(Some(x), box t, box e) => {
                Ok(Exp::letx(x, t.range_traverse(f)?, e.range_traverse(f)?))
            }
            Exp::Log(x, box t, box e) => {
                Ok(Exp::logx(x, t.range_traverse(f)?, e.range_traverse(f)?))
            }
            Exp::Let(None, box t, box e) => {
                Ok(Exp::seq(t.range_traverse(f)?, e.range_traverse(f)?))
            }
            Exp::Pair(box t, box e) => Ok(Exp::pair(t.range_traverse(f)?, e.range_traverse(f)?)),
            Exp::Assert(box lhs, box rhs) => Ok(Exp::assert_eq(
                lhs.range_traverse(f)?,
                rhs.range_traverse(f)?,
            )),
            Exp::Verify(box lhs, box rhs) => Ok(Exp::verify_eq(
                lhs.range_traverse(f)?,
                rhs.range_traverse(f)?,
            )),
            Exp::App(x, ts) => Ok(Exp::app(x, ts.range_traverse(f)?)),
            Exp::Fun(vars, box body) => Ok(Exp::Fun(vars, Box::new(body.range_traverse(f)?))),
            Exp::Record(fields) => {
                let pairs: Vec<_> = fields
                    .into_iter()
                    .map(|(name, exp)| exp.range_traverse(f).map(|new_exp| (name, new_exp)))
                    .collect::<Result<_, _>>()?;
                Ok(Exp::Record(Ctx::from_iter(pairs)))
            }
            Exp::Proj(box exp, field) => Ok(Exp::Proj(Box::new(exp.range_traverse(f)?), field)),
            Exp::SetRecord(box record, field, box value) => Ok(Exp::SetRecord(
                Box::new(record.range_traverse(f)?),
                field,
                Box::new(value.range_traverse(f)?),
            )),
            other => Ok(other),
        }
    }
}

impl<N: Clone> RangeTraversal<N> for Exps<N> {
    fn range_traverse<E>(
        self,
        f: &mut dyn FnMut(Range<N>) -> Result<Range<N>, E>,
    ) -> Result<Self, E> {
        Ok(Exps(self.0.traverse1(&mut |x| x.range_traverse(f))?))
    }
}

impl<N> Exps<N> {
    pub fn iter(&self) -> std::slice::Iter<'_, Exp<N>> {
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
    pub fn from_vec(a: Self, ts: &[Self]) -> Self
    where
        N: Clone,
    {
        ts.iter().fold(a, |acc, a| Exp::seq(acc, a.clone()))
    }
    /// Annotated constructors
    pub fn lit(v: N) -> Self {
        Exp::Lit(v)
    }
    pub fn bin(op: BinOp, l: Self, r: Self) -> Self {
        Exp::Bin(op, Box::new(l), Box::new(r))
    }
    pub fn interpolate(points: Option<Self>, evals: Self) -> Self {
        Exp::Interpolate(points.map(Box::new), Box::new(evals))
    }
    pub fn interpolate_at(points: Self, evals: Self) -> Self {
        Exp::Interpolate(Some(Box::new(points)), Box::new(evals))
    }
    pub fn interpolate_grid(evals: Self) -> Self {
        Exp::Interpolate(None, Box::new(evals))
    }
    pub fn mle(a: Self) -> Self {
        Exp::Mle(Box::new(a))
    }
    pub fn poly(a: Self) -> Self {
        Exp::Poly(Box::new(a))
    }
    pub fn evaluate(p: Self, selector: Option<Range<N>>, points: Option<Self>) -> Self {
        Exp::Evaluate(Box::new(p), selector, points.map(Box::new))
    }
    pub fn evaluate_at(p: Self, points: Self) -> Self {
        Exp::Evaluate(Box::new(p), None, Some(Box::new(points)))
    }
    pub fn evaluate_grid(p: Self) -> Self {
        Exp::Evaluate(Box::new(p), None, None)
    }
    pub fn evaluate_selected(range: Range<N>, p: Self, fixed: Self) -> Self {
        Exp::Evaluate(Box::new(p), Some(range), Some(Box::new(fixed)))
    }
    pub fn coef(a: Self) -> Self {
        Exp::Coef(Box::new(a))
    }
    pub fn challenge(t: Tid) -> Self {
        Exp::Challenge(t, false)
    }
    pub fn challenge_nz(t: Tid) -> Self {
        Exp::Challenge(t, true)
    }
    pub fn random(t: Tid) -> Self {
        Exp::Random(t, false)
    }
    pub fn random_nz(t: Tid) -> Self {
        Exp::Random(t, true)
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
    pub fn pair(t: Self, e: Self) -> Self {
        Exp::Pair(Box::new(t), Box::new(e))
    }
    pub fn range(r: Range<N>) -> Self {
        Exp::Range(r)
    }
    #[allow(clippy::should_implement_trait)]
    pub fn add(l: Self, r: Self) -> Self {
        Exp::Bin(BinOp::Add, Box::new(l), Box::new(r))
    }
    #[allow(clippy::should_implement_trait)]
    pub fn sub(l: Self, r: Self) -> Self {
        Exp::Bin(BinOp::Sub, Box::new(l), Box::new(r))
    }
    #[allow(clippy::should_implement_trait)]
    pub fn mul(l: Self, r: Self) -> Self {
        Exp::Bin(BinOp::Mul, Box::new(l), Box::new(r))
    }
    #[allow(clippy::should_implement_trait)]
    pub fn div(l: Self, r: Self) -> Self {
        Exp::Bin(BinOp::Div, Box::new(l), Box::new(r))
    }
    pub fn pow(l: Self, r: Self) -> Self {
        Exp::Bin(BinOp::Pow, Box::new(l), Box::new(r))
    }
    pub fn dot(l: Self, r: Self) -> Self {
        Exp::Bin(BinOp::Dot, Box::new(l), Box::new(r))
    }
    #[allow(clippy::should_implement_trait)]
    pub fn rem(l: Self, r: Self) -> Self {
        Exp::Bin(BinOp::Rem, Box::new(l), Box::new(r))
    }
    pub fn concat(l: Self, r: Self) -> Self {
        Exp::Bin(BinOp::Concat, Box::new(l), Box::new(r))
    }
    pub fn var(x: &Vid) -> Self {
        Exp::Var(x.clone())
    }
    pub fn varstr(x: &str) -> Self {
        Exp::Var(Vid::from(x))
    }
    pub fn assert_eq(lhs: Exp<N>, rhs: Exp<N>) -> Self {
        Exp::Assert(Box::new(lhs), Box::new(rhs))
    }
    pub fn verify_eq(lhs: Exp<N>, rhs: Exp<N>) -> Self {
        Exp::Verify(Box::new(lhs), Box::new(rhs))
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
    pub fn app(id: Vid, args: Exps<N>) -> Self {
        Exp::App(id, args)
    }
    pub fn fun(vars: Vec<Vid>, body: Self) -> Self {
        Exp::Fun(vars, Box::new(body))
    }
    pub fn record(fields: Ctx<String, Self>) -> Self {
        Exp::Record(fields)
    }
    pub fn proj(exp: Self, field: String) -> Self {
        Exp::Proj(Box::new(exp), field)
    }
    pub fn set_record(record: Self, field: String, value: Self) -> Self {
        Exp::SetRecord(Box::new(record), field, Box::new(value))
    }
    pub fn is_pure(&self) -> bool {
        match self {
            Exp::Lit(_) | Exp::Unit | Exp::Var(_) | Exp::Range(_) => true,
            Exp::Interpolate(None, box e) => e.is_pure(),
            Exp::Interpolate(Some(box p), box e) => p.is_pure() && e.is_pure(),
            Exp::Coef(box p) => p.is_pure(),
            Exp::Poly(box p) => p.is_pure(),
            Exp::Mle(box p) => p.is_pure(),
            Exp::Reduce(_, box p) => p.is_pure(),
            Exp::Vec(v) => v.iter().all(|e| e.is_pure()),
            Exp::Bin(_, box a, box b) => a.is_pure() && b.is_pure(),
            Exp::Evaluate(box p, _, ox) => p.is_pure() && ox.as_ref().is_none_or(|x| x.is_pure()),
            Exp::Pair(box a, box b) => a.is_pure() && b.is_pure(),
            Exp::Map(box a, _, box b) => a.is_pure() && b.is_pure(),
            Exp::Ram(box a, box b) => a.is_pure() && b.is_pure(),
            Exp::Let(_, box a, box b) => a.is_pure() && b.is_pure(),
            Exp::Log(_, box _, box _) => false,
            Exp::Challenge(_, _) | Exp::Random(_, _) => false,
            Exp::App(_, args) => args.iter().all(|e| e.is_pure()),
            Exp::Assert(_, _) | Exp::Verify(_, _) => false,
            Exp::Fun(_, box body) => body.is_pure(),
            Exp::Record(fields) => fields.iter().all(|(_, e)| e.is_pure()),
            Exp::Proj(box exp, _) => exp.is_pure(),
            Exp::SetRecord(box record, _, box value) => record.is_pure() && value.is_pure(),
        }
    }

    /// Check if an expression is valid in a relation (where clause).
    ///
    /// Allows: `Let`, `Assert`, `Random`, and all pure expressions.
    /// Rejects: `Challenge` (verifier oracle), `Log` (transcript),
    /// `Verify` (verifier-side check).
    pub fn is_relation_pure(&self) -> bool {
        match self {
            // Reject: verifier-only constructs
            Exp::Challenge(_, _) | Exp::Log(_, _, _) | Exp::Verify(_, _) => false,
            // Allow: Random (trusted-setup trapdoors, etc.)
            Exp::Random(_, _) => true,
            // Recurse into all sub-expressions with is_relation_pure
            Exp::Assert(box lhs, box rhs) => lhs.is_relation_pure() && rhs.is_relation_pure(),
            Exp::Let(Some(_), box val, box cont) | Exp::Let(None, box val, box cont) => {
                val.is_relation_pure() && cont.is_relation_pure()
            }
            Exp::Map(box a, _, box b) => a.is_relation_pure() && b.is_relation_pure(),
            Exp::Vec(v) => v.iter().all(|e| e.is_relation_pure()),
            Exp::Bin(_, box a, box b) => a.is_relation_pure() && b.is_relation_pure(),
            Exp::Pair(box a, box b) => a.is_relation_pure() && b.is_relation_pure(),
            Exp::Ram(box a, box b) => a.is_relation_pure() && b.is_relation_pure(),
            Exp::Interpolate(None, box e) => e.is_relation_pure(),
            Exp::Interpolate(Some(box p), box e) => p.is_relation_pure() && e.is_relation_pure(),
            Exp::Coef(box p) => p.is_relation_pure(),
            Exp::Poly(box p) => p.is_relation_pure(),
            Exp::Mle(box p) => p.is_relation_pure(),
            Exp::Reduce(_, box p) => p.is_relation_pure(),
            Exp::Evaluate(box p, _, ox) => {
                p.is_relation_pure() && ox.as_ref().is_none_or(|x| x.is_relation_pure())
            }
            Exp::App(_, args) => args.iter().all(|e| e.is_relation_pure()),
            Exp::Fun(_, box body) => body.is_relation_pure(),
            Exp::Record(fields) => fields.iter().all(|(_, e)| e.is_relation_pure()),
            Exp::Proj(box exp, _) => exp.is_relation_pure(),
            Exp::SetRecord(box record, _, box value) => {
                record.is_relation_pure() && value.is_relation_pure()
            }
            // Leaves: always valid
            Exp::Lit(_) | Exp::Unit | Exp::Var(_) | Exp::Range(_) => true,
        }
    }
}

impl CExp {
    pub fn zeroes(n: usize) -> Self {
        Exp::map(Exp::lit(0), Vid::from("_"), Exp::range(Range::new(0, n)))
    }
}

impl BinOp {
    pub fn precedence(&self) -> usize {
        match self {
            BinOp::Add | BinOp::Sub => 2,
            BinOp::Mul | BinOp::Div => 3,
            BinOp::Pow => 4,
            BinOp::Dot => 5,
            BinOp::Concat => 6,
            BinOp::Rem => 7,
        }
    }

    /// Precedence matching `AEXP_PARSER` (the parser's Pratt table, exp.rs:1219-1233).
    /// Lower binds looser. This is what the pretty printer must use to produce
    /// text that re-parses to the same AST — `precedence()` above gives a
    /// DIFFERENT ordering (Rem=7, Concat=6) that does not match the parser.
    pub fn parser_precedence(&self) -> usize {
        match self {
            BinOp::Add | BinOp::Sub => 1,
            BinOp::Mul | BinOp::Div | BinOp::Rem => 2,
            BinOp::Concat => 3,
            BinOp::Pow => 4,
            BinOp::Dot => 5, // not infix in grammar; programmatic-only
        }
    }

    /// Right-associative? (Only Pow; all other infix binops are left-assoc.)
    pub fn is_right_assoc(&self) -> bool {
        matches!(self, BinOp::Pow)
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
    N: Pretty<'a, D, A> + Clone,
    A: 'a + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        match self {
            Exp::Lit(p) => p.pretty(allocator),
            Exp::Unit => allocator.text("()"),
            Exp::Interpolate(None, ev) => allocator.concat([
                allocator.text("interpolate("),
                ev.pretty(allocator),
                allocator.text(")"),
            ]),
            Exp::Interpolate(Some(points), evals) => allocator.concat([
                allocator.text("interpolate("),
                points.pretty(allocator),
                allocator.text(", "),
                evals.pretty(allocator),
                allocator.text(")"),
            ]),
            Exp::Poly(p) => allocator.concat([
                allocator.text("poly("),
                p.pretty(allocator),
                allocator.text(")"),
            ]),
            Exp::Coef(p) => allocator.concat([
                allocator.text("coef("),
                p.pretty(allocator),
                allocator.text(")"),
            ]),
            Exp::Evaluate(p, None, None) => allocator.concat([
                allocator.text("eval("),
                p.pretty(allocator),
                allocator.text(")"),
            ]),
            Exp::Evaluate(p, None, Some(x)) => allocator.concat([
                allocator.text("eval("),
                p.pretty(allocator),
                allocator.text(", "),
                x.pretty(allocator),
                allocator.text(")"),
            ]),
            Exp::Evaluate(p, Some(range), Some(x)) => allocator.concat([
                allocator.text("eval<"),
                range.pretty(allocator),
                allocator.text(">("),
                p.pretty(allocator),
                allocator.text(", "),
                x.pretty(allocator),
                allocator.text(")"),
            ]),
            Exp::Evaluate(p, Some(range), None) => allocator.concat([
                allocator.text("eval<"),
                range.pretty(allocator),
                allocator.text(">("),
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
            Exp::Bin(op, a, b) => {
                let parent_prec = op.parser_precedence();
                let right_assoc = op.is_right_assoc();
                let lhs_needs_paren = matches!(a.as_ref(),
                    Exp::Bin(child_op, _, _) if child_op.parser_precedence() < parent_prec
                        || (child_op.parser_precedence() == parent_prec && right_assoc));
                let rhs_needs_paren = matches!(b.as_ref(),
                    Exp::Bin(child_op, _, _) if child_op.parser_precedence() < parent_prec
                        || (child_op.parser_precedence() == parent_prec && !right_assoc));
                let lhs = (*a).pretty(allocator);
                let lhs = if lhs_needs_paren {
                    allocator.concat([allocator.text("("), lhs, allocator.text(")")])
                } else {
                    lhs
                };
                let rhs = (*b).pretty(allocator);
                let rhs = if rhs_needs_paren {
                    allocator.concat([allocator.text("("), rhs, allocator.text(")")])
                } else {
                    rhs
                };
                allocator.concat([lhs, op.pretty(allocator), rhs])
            }
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
            Exp::Var(x) => allocator.concat([x.pretty(allocator)]),
            Exp::Challenge(t, b) => allocator.concat([
                allocator.text("challenge<"),
                t.pretty(allocator),
                if b {
                    allocator.text("*")
                } else {
                    allocator.text("")
                },
                allocator.text(">"),
            ]),
            Exp::Random(t, b) => allocator.concat([
                allocator.text("random<"),
                t.pretty(allocator),
                if b {
                    allocator.text("*")
                } else {
                    allocator.text("")
                },
                allocator.text(">"),
            ]),
            Exp::Pair(box t, box e) => allocator.concat([
                allocator.text("pair("),
                t.pretty(allocator),
                allocator.text(", "),
                e.pretty(allocator),
                allocator.text(")"),
            ]),
            Exp::Range(r) => allocator.concat([r.pretty(allocator)]),
            Exp::App(x, d) => allocator.concat([
                x.pretty(allocator),
                allocator.text("("),
                d.pretty(allocator),
                allocator.text(")"),
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
            Exp::Assert(box lhs, box rhs) => allocator.concat([
                allocator.text("assert("),
                lhs.pretty(allocator),
                allocator.text(" == "),
                rhs.pretty(allocator),
                allocator.text(")"),
            ]),
            Exp::Verify(box lhs, box rhs) => allocator.concat([
                allocator.text("verify("),
                lhs.pretty(allocator),
                allocator.text(" == "),
                rhs.pretty(allocator),
                allocator.text(")"),
            ]),
            Exp::Fun(vars, body) => {
                let vars_str = vars
                    .iter()
                    .map(|v| v.0.as_str())
                    .collect::<Vec<_>>()
                    .join(", ");
                allocator.concat([
                    allocator.text("fun "),
                    allocator.text(vars_str),
                    allocator.text(" => "),
                    (*body).pretty(allocator),
                ])
            }
            Exp::Record(fields) => {
                let mut docs = Vec::new();
                docs.push(allocator.text("{|"));
                let field_docs: Vec<_> = fields
                    .into_iter()
                    .map(|(name, exp)| {
                        allocator.concat([
                            allocator.text(name),
                            allocator.text(": "),
                            exp.pretty(allocator),
                        ])
                    })
                    .collect();
                docs.push(allocator.intersperse(field_docs, ", "));
                docs.push(allocator.text("|}"));
                allocator.concat(docs)
            }
            Exp::Proj(box exp, field) => allocator.concat([
                exp.pretty(allocator),
                allocator.text("."),
                allocator.text(field),
            ]),
            Exp::SetRecord(box record, field, box value) => allocator.concat([
                record.pretty(allocator),
                allocator.text(".set("),
                allocator.text(field),
                allocator.text(", "),
                value.pretty(allocator),
                allocator.text(")"),
            ]),
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
    N: Pretty<'a, D, A> + Clone,
    A: 'a + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        allocator.intersperse(self.0.into_iter().map(|x| x.pretty(allocator)), ", ")
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

/// Display instance calls the pretty printer
impl fmt::Display for BinOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <BinOp as Pretty<'_, BoxAllocator, ()>>::pretty(*self, &BoxAllocator)
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
            .op(Op::infix(add_op, Left) | Op::infix(sub_op, Left))
            .op(Op::infix(mul_op, Left) | Op::infix(div_op, Left) | Op::infix(rem_op, Left))
            .op(Op::infix(concat_op, Left))
            .op(Op::infix(pow_op, Right))
            .op(Op::prefix(unary_minus))
            .op(Op::postfix(record_set_op))
            .op(Op::postfix(proj_op))
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
            Rule::rem_op => Ok(BinOp::Rem),
            Rule::concat_op => Ok(BinOp::Concat),
            _ => Err(ConversionError::Malformed(InputError::UnexpectedExp(pair))),
        }
    }
}

impl<'pest> FromPest<'pest> for UExp {
    type Rule = Rule;
    type FatalError = InputError<'pest>;

    fn from_pest(
        expression: &mut Pairs<'pest, Self::Rule>,
    ) -> Result<Self, ConversionError<Self::FatalError>> {
        let pair = expression.next().ok_or(ConversionError::NoMatch)?;
        match pair.as_rule() {
            // exp = { let_exp | log_exp | seq_exp | exp_no_seq }
            // Unwrap to the inner alternative.
            Rule::exp => parse_exp(pair.into_inner().next().unwrap()),
            // where_exp = { where_let | where_eq | exp_no_seq }
            // Unwrap to the inner alternative.
            Rule::where_exp => parse_where_exp(pair.into_inner().next().unwrap()),
            Rule::exp_no_seq => parse_exp_no_seq(pair),
            _ => Err(ConversionError::Malformed(InputError::UnexpectedExp(pair))),
        }
    }
}

/// Dispatch on exp = { let_exp | log_exp | seq_exp | exp_no_seq }
/// `pair` is the inner alternative (let_exp/log_exp/seq_exp/exp_no_seq),
/// not `Rule::exp` itself — callers unwrap.
fn parse_exp<'pest>(pair: Pair<'pest, Rule>) -> Result<UExp, ConversionError<InputError<'pest>>> {
    match pair.as_rule() {
        Rule::let_exp => {
            // let_exp = { "let" ~ id ~ (":" ~ typ)? ~ "=" ~ exp_no_seq ~ ";" ~ exp? }
            let mut inner = pair.into_inner();
            let var = Vid::from_pest(&mut Pairs::single(inner.next().unwrap()))?;
            let next = inner.next().unwrap();
            let (typ_ann, val) = if next.as_rule() == Rule::exp_no_seq {
                (None, parse_exp_no_seq(next)?)
            } else {
                let typ = GTyp::from_pest(&mut Pairs::single(next))?;
                let val = parse_exp_no_seq(inner.next().unwrap())?;
                (Some(typ), val)
            };
            // exp? — optional continuation; trailing `;` → Unit
            let body = match inner.next() {
                Some(cont) => Exp::from_pest(&mut Pairs::single(cont))?,
                None => Exp::Unit,
            };
            let _ = typ_ann;
            Ok(Exp::letx(var, val, body))
        }
        Rule::log_exp => {
            // log_exp = { id ~ "<-" ~ exp_no_seq ~ ";" ~ exp? }
            let mut inner = pair.into_inner();
            let id = Vid::from_pest(&mut Pairs::single(inner.next().unwrap()))?;
            let val = parse_exp_no_seq(inner.next().unwrap())?;
            // exp? — optional continuation; trailing `;` → Unit
            let cont = match inner.next() {
                Some(cont) => Exp::from_pest(&mut Pairs::single(cont))?,
                None => Exp::Unit,
            };
            Ok(Exp::logx(id, val, cont))
        }
        Rule::seq_exp => {
            // seq_exp = { exp_no_seq ~ ";" ~ exp? }
            // ";" is a silent string literal — no pair produced
            let mut inner = pair.into_inner();
            let lhs = parse_exp_no_seq(inner.next().unwrap())?;
            // exp? — optional continuation; trailing `;` → Unit
            let rhs = match inner.next() {
                Some(cont) => Exp::from_pest(&mut Pairs::single(cont))?,
                None => Exp::Unit,
            };
            Ok(Exp::seq(lhs, rhs))
        }
        Rule::exp_no_seq => parse_exp_no_seq(pair),
        _ => unreachable!("unexpected rule in exp: {:?}", pair.as_rule()),
    }
}

/// Dispatch on where_exp = { where_let | where_eq | exp_no_seq }
/// `pair` is the inner alternative (where_let/where_eq/exp_no_seq),
/// not `Rule::where_exp` itself — callers unwrap.
fn parse_where_exp<'pest>(
    pair: Pair<'pest, Rule>,
) -> Result<UExp, ConversionError<InputError<'pest>>> {
    match pair.as_rule() {
        Rule::where_let => parse_where_let(pair),
        Rule::where_eq => parse_where_eq(pair),
        Rule::exp_no_seq => parse_exp_no_seq(pair),
        _ => unreachable!("unexpected rule in where_exp: {:?}", pair.as_rule()),
    }
}

/// where_let = { "let" ~ id ~ (":" ~ typ)? ~ "=" ~ exp_no_seq ~ ";" ~ where_exp? }
fn parse_where_let<'pest>(
    pair: Pair<'pest, Rule>,
) -> Result<UExp, ConversionError<InputError<'pest>>> {
    let mut inner = pair.into_inner();
    let var = Vid::from_pest(&mut Pairs::single(
        inner.next().ok_or(ConversionError::NoMatch)?,
    ))?;
    let next = inner.next().ok_or(ConversionError::NoMatch)?;
    let (val, rest) = if next.as_rule() == Rule::exp_no_seq {
        (parse_exp_no_seq(next)?, inner.next())
    } else {
        let val = parse_exp_no_seq(inner.next().ok_or(ConversionError::NoMatch)?)?;
        (val, inner.next())
    };
    // where_exp? — optional continuation; trailing `;` → Unit
    let cont = match rest {
        Some(cont) => parse_where_exp(cont.into_inner().next().unwrap())?,
        None => Exp::Unit,
    };
    Ok(Exp::letx(var, val, cont))
}

/// where_eq = { exp_no_seq ~ eq_op ~ exp_no_seq ~ (";" ~ where_exp?)? }
fn parse_where_eq<'pest>(
    pair: Pair<'pest, Rule>,
) -> Result<UExp, ConversionError<InputError<'pest>>> {
    let mut inner = pair.into_inner();
    let lhs = parse_exp_no_seq(inner.next().ok_or(ConversionError::NoMatch)?)?;
    inner.next(); // skip eq_op
    let rhs = parse_exp_no_seq(inner.next().ok_or(ConversionError::NoMatch)?)?;
    match inner.next() {
        // cont is Rule::where_exp — unwrap to inner alternative
        Some(cont) => {
            // where_exp? inside — cont may be empty (trailing ;)
            let where_inner = cont.into_inner().next();
            match where_inner {
                Some(actual) => Ok(Exp::seq(Exp::assert_eq(lhs, rhs), parse_where_exp(actual)?)),
                None => Ok(Exp::seq(Exp::assert_eq(lhs, rhs), Exp::Unit)),
            }
        }
        None => Ok(Exp::assert_eq(lhs, rhs)),
    }
}

/// Parse exp_no_seq using the PrattParser on its flat inner pairs.
fn parse_exp_no_seq<'pest>(
    pair: Pair<'pest, Rule>,
) -> Result<UExp, ConversionError<InputError<'pest>>> {
    AEXP_PARSER
        .map_primary(|pair| match pair.as_rule() {
            Rule::unit_exp => Ok(Exp::Unit),
            Rule::id => {
                let name = pair.as_str().to_string();
                if name.starts_with(|c: char| c.is_uppercase()) {
                    // Uppercase-starting identifiers are size type variables
                    Ok(Exp::lit(Size::varstr(&name)))
                } else {
                    Ok(Exp::Var(Vid(name)))
                }
            }
            Rule::positive => Ok(Exp::lit(Size::from_pest(&mut Pairs::single(pair))?)),
            Rule::fun_exp => {
                let mut inner = pair.into_inner();
                let mut vars = Vec::new();
                // Parse variable names until we hit the expression
                loop {
                    let next = inner.next().ok_or(ConversionError::NoMatch)?;
                    if next.as_rule() == Rule::exp {
                        // This is the body expression
                        let body = Exp::from_pest(&mut Pairs::single(next))?;
                        return Ok(Exp::fun(vars, body));
                    } else {
                        // This should be an id
                        vars.push(Vid(next.as_str().to_string()));
                    }
                }
            }
            Rule::mle_exp => Ok(Exp::mle(parse_exp_no_seq(
                pair.into_inner().next().unwrap(),
            )?)),
            Rule::interpolate_exp => {
                let mut inner = pair.into_inner();
                let first = parse_exp_no_seq(inner.next().ok_or(ConversionError::NoMatch)?)?;
                match inner.next() {
                    None => Ok(Exp::interpolate_grid(first)),
                    Some(second) => Ok(Exp::interpolate_at(first, parse_exp_no_seq(second)?)),
                }
            }
            Rule::poly_exp => Ok(Exp::poly(parse_exp_no_seq(
                pair.into_inner().next().unwrap(),
            )?)),
            Rule::coef_exp => Ok(Exp::coef(parse_exp_no_seq(
                pair.into_inner().next().unwrap(),
            )?)),
            Rule::range_exp => Ok(Exp::range(Range::from_pest(&mut pair.into_inner())?)),
            Rule::minus_exp => {
                let mut inner = pair.into_inner();
                let op = BinOp::from_pest(&mut Pairs::single(inner.next().unwrap()))?;
                let exp = parse_exp_no_seq(inner.next().unwrap())?;
                Ok(Exp::bin(op, Exp::lit(Size::zero()), exp))
            }
            Rule::challenge_exp => {
                let mut inner = pair.into_inner();
                let tid = Tid::from_pest(&mut Pairs::single(inner.next().unwrap()))?;
                let b = inner.next().is_some();
                Ok(Exp::Challenge(tid, b))
            }
            Rule::random_exp => {
                let mut inner = pair.into_inner();
                let tid = Tid::from_pest(&mut Pairs::single(inner.next().unwrap()))?;
                let b = inner.next().is_some();
                Ok(Exp::Random(tid, b))
            }
            Rule::vec_exp => {
                let inner = pair.into_inner();
                let mut ve = Vec::new();
                for x in inner {
                    ve.push(parse_exp_no_seq(x)?);
                }
                Ok(Exp::vec(ve))
            }
            Rule::map_exp => {
                let mut inner = pair.into_inner();
                Ok(Exp::map(
                    Exp::from_pest(&mut Pairs::single(inner.next().unwrap()))?,
                    Vid::from_pest(&mut Pairs::single(inner.next().unwrap()))?,
                    parse_exp_no_seq(inner.next().unwrap())?,
                ))
            }
            Rule::reduce_exp => {
                let mut inner = pair.into_inner();
                Ok(Exp::reduce(
                    BinOp::from_pest(&mut Pairs::single(inner.next().unwrap()))?,
                    parse_exp_no_seq(inner.next().unwrap())?,
                ))
            }
            Rule::ram_exp => {
                let mut inner = pair.into_inner();
                Ok(Exp::ram(
                    Exp::Var(Vid::from_pest(&mut Pairs::single(inner.next().unwrap()))?),
                    parse_exp_no_seq(inner.next().unwrap())?,
                ))
            }
            Rule::pair_exp => {
                let mut inner = pair.into_inner();
                Ok(Exp::pair(
                    parse_exp_no_seq(inner.next().unwrap())?,
                    parse_exp_no_seq(inner.next().unwrap())?,
                ))
            }
            Rule::eval_exp => {
                let mut inner = pair.into_inner();
                let first_pair = inner.next().ok_or(ConversionError::NoMatch)?;
                let (selector, selector_pair_for_error, poly_pair) = if first_pair.as_rule()
                    == Rule::eval_selector
                {
                    let selector_pair_for_error = first_pair.clone();
                    let mut selector_inner = first_pair.into_inner();
                    let selector_pair = selector_inner.next().ok_or(ConversionError::NoMatch)?;
                    let range = match selector_pair.as_rule() {
                        Rule::range => Range::from_pest(&mut Pairs::single(selector_pair))?,
                        Rule::size_ty => {
                            let start = Size::from_pest(&mut Pairs::single(selector_pair))?;
                            Range {
                                start: start.clone(),
                                step: Size::one(),
                                end: start + Size::one(),
                            }
                        }
                        _ => return Err(ConversionError::NoMatch),
                    };
                    (
                        Some(range),
                        Some(selector_pair_for_error),
                        inner.next().ok_or(ConversionError::NoMatch)?,
                    )
                } else {
                    (None, None, first_pair)
                };

                let poly = parse_exp_no_seq(poly_pair)?;
                match (selector, inner.next()) {
                    (None, None) => Ok(Exp::evaluate_grid(poly)),
                    (None, Some(second)) => Ok(Exp::evaluate_at(poly, parse_exp_no_seq(second)?)),
                    (Some(range), Some(fixed)) => Ok(Exp::evaluate_selected(
                        range,
                        poly,
                        parse_exp_no_seq(fixed)?,
                    )),
                    (Some(_), None) => Err(ConversionError::Malformed(
                        InputError::EvaluateSelectorWithoutPoints(
                            selector_pair_for_error.ok_or(ConversionError::NoMatch)?,
                        ),
                    )),
                }
            }
            Rule::dot_exp => {
                let mut inner = pair.into_inner();
                Ok(Exp::dot(
                    parse_exp_no_seq(inner.next().unwrap())?,
                    parse_exp_no_seq(inner.next().unwrap())?,
                ))
            }
            Rule::app_exp => {
                let mut inner = pair.into_inner();
                // Call a function
                let func = Vid::from_pest(&mut inner)?;
                // Arguments
                let params = Exps::from_pest(&mut inner)?;
                Ok(Exp::app(func, params))
            }
            Rule::assert_exp => {
                let mut inner = pair.into_inner();
                // constraint = { exp_no_seq ~ eq_op ~ exp_no_seq }
                let constraint_pair = inner.next().unwrap();
                let mut constraint_inner = constraint_pair.into_inner();
                let lhs = parse_exp_no_seq(constraint_inner.next().unwrap())?;
                // skip eq_op
                constraint_inner.next();
                let rhs = parse_exp_no_seq(constraint_inner.next().unwrap())?;
                Ok(Exp::assert_eq(lhs, rhs))
            }
            Rule::verify_exp => {
                let mut inner = pair.into_inner();
                // constraint = { exp_no_seq ~ eq_op ~ exp_no_seq }
                let constraint_pair = inner.next().unwrap();
                let mut constraint_inner = constraint_pair.into_inner();
                let lhs = parse_exp_no_seq(constraint_inner.next().unwrap())?;
                // skip eq_op
                constraint_inner.next();
                let rhs = parse_exp_no_seq(constraint_inner.next().unwrap())?;
                Ok(Exp::verify_eq(lhs, rhs))
            }
            Rule::record_exp => {
                let inner = pair.into_inner();
                let mut fields = Ctx::new();
                for field_pair in inner {
                    if field_pair.as_rule() == Rule::record_field_exp {
                        let mut field_inner = field_pair.into_inner();
                        let field_name = Vid::from_pest(&mut field_inner)?.0;
                        let field_value = parse_exp_no_seq(field_inner.next().unwrap())?;
                        fields.insert(&field_name, &field_value);
                    }
                }
                Ok(Exp::Record(fields))
            }
            // Parenthesized expression: "(" ~ exp ~ ")"
            // exp allows seq, so (a; b) is valid.
            Rule::exp => Exp::from_pest(&mut Pairs::single(pair)),
            // Inner exp_no_seq from silent rules like minus_exp
            Rule::exp_no_seq => parse_exp_no_seq(pair),
            _ => Err(ConversionError::Malformed(InputError::UnexpectedExp(pair))),
        })
        .map_infix(|lhs, op, rhs| match op.clone().as_rule() {
            Rule::add_op => Ok(Exp::add(lhs?, rhs?)),
            Rule::sub_op => Ok(Exp::sub(lhs?, rhs?)),
            Rule::mul_op => Ok(Exp::mul(lhs?, rhs?)),
            Rule::div_op => Ok(Exp::div(lhs?, rhs?)),
            Rule::pow_op => Ok(Exp::pow(lhs?, rhs?)),
            Rule::rem_op => Ok(Exp::rem(lhs?, rhs?)),
            Rule::concat_op => Ok(Exp::concat(lhs?, rhs?)),
            _ => unreachable!(),
        })
        .map_prefix(|op, rhs| match op.as_rule() {
            Rule::unary_minus => Ok(Exp::sub(Exp::lit(Size::zero()), rhs?)),
            _ => unreachable!(),
        })
        .map_postfix(|lhs, op| match op.as_rule() {
            Rule::record_set_op => {
                let mut inner = op.into_inner();
                let field_name = Vid::from_pest(&mut Pairs::single(
                    inner.next().ok_or(ConversionError::NoMatch)?,
                ))?
                .0;
                let value_pair = inner.next().ok_or(ConversionError::NoMatch)?;
                let value = parse_exp_no_seq(value_pair)?;
                Ok(Exp::set_record(lhs?, field_name, value))
            }
            Rule::proj_op => {
                let mut inner = op.into_inner();
                let field_name = Vid::from_pest(&mut inner)?.0;
                Ok(Exp::proj(lhs?, field_name))
            }
            _ => unreachable!(),
        })
        .parse(&mut pair.into_inner())
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
            }
            _ => Err(ConversionError::Malformed(InputError::UnexpectedExp(pair))),
        }
    }
}

////////////////////////////////////////////////////////////////////////
/// Parser tests
////////////////////////////////////////////////////////////////////////
#[cfg(test)]
use pest::Parser;
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

    // Dot (function-style syntax)
    let ex7 = "dot(x, 2)";
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
fn parser_eval() {
    let ex = "eval(p, 3)";
    let mut pairs = ZippelParser::parse(Rule::exp, ex).unwrap();
    assert_eq!(
        UExp::from_pest(&mut pairs),
        Ok(Exp::evaluate_at(Exp::varstr("p"), Exp::from(3)))
    );
}

#[test]
fn parser_eval_selected_unit() {
    let ex = "eval<0>(p, xs)";
    let mut pairs = ZippelParser::parse(Rule::exp, ex).unwrap();
    assert_eq!(
        UExp::from_pest(&mut pairs),
        Ok(Exp::evaluate_selected(
            Range {
                start: Size::from(0),
                step: Size::from(1),
                end: Size::from(0) + Size::one(),
            },
            Exp::varstr("p"),
            Exp::varstr("xs"),
        ))
    );
}

#[test]
fn parser_eval_selected_range() {
    let ex = "eval<0..1>(p, xs)";
    let mut pairs = ZippelParser::parse(Rule::exp, ex).unwrap();
    assert_eq!(
        UExp::from_pest(&mut pairs),
        Ok(Exp::evaluate_selected(
            Range {
                start: Size::from(0),
                step: Size::from(1),
                end: Size::from(1),
            },
            Exp::varstr("p"),
            Exp::varstr("xs"),
        ))
    );
}

#[test]
fn parser_rejects_eval_selected_unit_without_points() {
    let ex = "eval<0>(p)";
    let mut pairs = ZippelParser::parse(Rule::exp, ex).unwrap();
    assert!(matches!(
        UExp::from_pest(&mut pairs),
        Err(ConversionError::Malformed(
            InputError::EvaluateSelectorWithoutPoints(_)
        ))
    ));
}

#[test]
fn parser_rejects_eval_selected_range_without_points() {
    let ex = "eval<0..1>(p)";
    let mut pairs = ZippelParser::parse(Rule::exp, ex).unwrap();
    assert!(matches!(
        UExp::from_pest(&mut pairs),
        Err(ConversionError::Malformed(
            InputError::EvaluateSelectorWithoutPoints(_)
        ))
    ));
}

#[test]
fn parser_eval_grid() {
    let ex = "eval(p)";
    let mut pairs = ZippelParser::parse(Rule::exp, ex).unwrap();
    assert_eq!(
        UExp::from_pest(&mut pairs),
        Ok(Exp::evaluate_grid(Exp::varstr("p")))
    );
}

#[test]
fn parser_coef() {
    let ex = "coef(poly([1,2,3]))";
    let mut pairs = ZippelParser::parse(Rule::exp, ex).unwrap();
    assert_eq!(
        UExp::from_pest(&mut pairs),
        Ok(Exp::coef(Exp::poly(Exp::vec(vec![
            Exp::from(1),
            Exp::from(2),
            Exp::from(3)
        ]))))
    );
}

#[test]
fn parser_interpolate() {
    let ex = "interpolate([0,1,2], [1,2,3])";
    let mut pairs = ZippelParser::parse(Rule::exp, ex).unwrap();
    assert_eq!(
        UExp::from_pest(&mut pairs),
        Ok(Exp::interpolate_at(
            Exp::vec(vec![Exp::from(0), Exp::from(1), Exp::from(2)]),
            Exp::vec(vec![Exp::from(1), Exp::from(2), Exp::from(3)]),
        ))
    );
}

#[test]
fn parser_fft_via_eval() {
    let ex = "eval(x + 2)";
    let mut pairs = ZippelParser::parse(Rule::exp, ex).unwrap();
    assert_eq!(
        UExp::from_pest(&mut pairs),
        Ok(Exp::evaluate_grid(Exp::varstr("x") + Exp::from(2)))
    );
}

#[test]
fn parser_poly() {
    let ex = "poly([1,2,3])";
    let mut pairs = ZippelParser::parse(Rule::exp, ex).unwrap();
    assert_eq!(
        UExp::from_pest(&mut pairs),
        Ok(Exp::poly(Exp::vec(vec![
            Exp::from(1),
            Exp::from(2),
            Exp::from(3)
        ])))
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
        Ok(Exp::range(Range {
            start: Size::from(0),
            step: Size::from(1),
            end: Size::from("N")
        }))
    );

    let ex = "(N/2)..N";
    let mut pairs = ZippelParser::parse(Rule::exp, ex).unwrap();
    assert_eq!(
        UExp::from_pest(&mut pairs),
        Ok(Exp::range(Range {
            start: Size::from("N").div(Size::from(2)),
            step: Size::from(1),
            end: Size::from("N")
        }))
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
            Exp::range(Range {
                start: Size::from(0),
                step: Size::from(1),
                end: Size::from("N")
            })
        ))
    );
}

#[test]
fn parser_pair() {
    let ex = "pair(x, y)";
    let mut pairs = ZippelParser::parse(Rule::exp, ex).unwrap();
    assert_eq!(
        UExp::from_pest(&mut pairs),
        Ok(Exp::pair(Exp::varstr("x"), Exp::varstr("y")))
    );
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
    assert_eq!(UExp::from_pest(&mut pairs), Ok(Exp::random(Tid::from("A"))));
}

#[test]
fn parser_challenge() {
    let ex = "challenge<F>";
    let mut pairs = ZippelParser::parse(Rule::exp, ex).unwrap();
    assert_eq!(
        UExp::from_pest(&mut pairs),
        Ok(Exp::challenge(Tid::from("F")))
    );
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
        Ok(Exp::letx(Vid::from("x"), Exp::from(2), Exp::from(3)))
    );
}

#[test]
fn parser_log() {
    let ex = "x <- 2; 4";
    let mut pairs = ZippelParser::parse(Rule::exp, ex).unwrap();
    assert_eq!(
        UExp::from_pest(&mut pairs),
        Ok(Exp::logx(Vid::from("x"), Exp::from(2), Exp::from(4)))
    );
}

#[test]
fn parser_assert() {
    let ex = "assert(x == 2)";
    let mut pairs = ZippelParser::parse(Rule::exp, ex).unwrap();
    assert_eq!(
        UExp::from_pest(&mut pairs),
        Ok(Exp::assert_eq(Exp::varstr("x"), Exp::from(2)))
    );
}

#[test]
fn parser_verify() {
    let ex = "verify(x == 2)";
    let mut pairs = ZippelParser::parse(Rule::exp, ex).unwrap();
    assert_eq!(
        UExp::from_pest(&mut pairs),
        Ok(Exp::verify_eq(Exp::varstr("x"), Exp::from(2)))
    );
}

#[test]
fn parser_verify_multiple() {
    let ex = "verify(x == 2); verify(3 == 4)";
    let mut pairs = ZippelParser::parse(Rule::exp, ex).unwrap();
    assert_eq!(
        UExp::from_pest(&mut pairs),
        Ok(Exp::seq(
            Exp::verify_eq(Exp::varstr("x"), Exp::from(2)),
            Exp::verify_eq(Exp::from(3), Exp::from(4))
        ))
    );
}

#[test]
fn parser_verify_three() {
    let ex = "verify(a == a); verify(b == b); verify(c == c)";
    let mut pairs = ZippelParser::parse(Rule::exp, ex).unwrap();
    assert_eq!(
        UExp::from_pest(&mut pairs),
        Ok(Exp::seq(
            Exp::verify_eq(Exp::varstr("a"), Exp::varstr("a")),
            Exp::seq(
                Exp::verify_eq(Exp::varstr("b"), Exp::varstr("b")),
                Exp::verify_eq(Exp::varstr("c"), Exp::varstr("c"))
            )
        ))
    );
}

#[test]
fn parser_map() {
    let ex = "[ss[i] + s^i for i in 0..N]";
    let mut pairs = ZippelParser::parse(Rule::exp, ex).unwrap();
    assert_eq!(
        UExp::from_pest(&mut pairs),
        Ok(Exp::map(
            Exp::ram(Exp::varstr("ss"), Exp::varstr("i"))
                + Exp::pow(Exp::varstr("s"), Exp::varstr("i")),
            Vid::from("i"),
            Exp::range(Range {
                start: Size::from(0),
                step: Size::from(1),
                end: Size::from("N")
            })
        ))
    );
}

#[test]
fn parser_seq() {
    let ex = "x <- 2; y <- 3; let x = 2 * 4; 2";
    let mut pairs = ZippelParser::parse(Rule::exp, ex).unwrap();
    assert_eq!(
        UExp::from_pest(&mut pairs),
        Ok(Exp::logx(
            Vid::from("x"),
            Exp::from(2),
            Exp::logx(
                Vid::from("y"),
                Exp::from(3),
                Exp::letx(Vid::from("x"), Exp::from(2) * Exp::from(4), Exp::from(2))
            )
        ))
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
    let ex = "p(a) + q(a)";
    let mut pairs = ZippelParser::parse(Rule::exp, ex).unwrap();
    assert_eq!(
        UExp::from_pest(&mut pairs),
        Ok(Exp::app(Vid::from("p"), Exps(vec![Exp::varstr("a")]))
            + Exp::app(Vid::from("q"), Exps(vec![Exp::varstr("a")])))
    );
}

#[test]
fn parser_fun_univariate() {
    // Test: fun x => x^2 + 2*x + 3
    let ex = "fun x => x^2 + 2*x + 3";
    let mut pairs = ZippelParser::parse(Rule::exp, ex).unwrap();
    let expected = Exp::fun(
        vec![Vid::from("x")],
        (Exp::varstr("x") ^ Exp::from(2)) + (Exp::from(2) * Exp::varstr("x")) + Exp::from(3),
    );
    assert_eq!(UExp::from_pest(&mut pairs), Ok(expected));
}

#[test]
fn parser_fun_multivariate() {
    // Test: fun x, y, z => 3*x + 4*y + 5*x*z
    let ex = "fun x, y, z => 3*x + 4*y + 5*x*z";
    let mut pairs = ZippelParser::parse(Rule::exp, ex).unwrap();
    let expected = Exp::fun(
        vec![Vid::from("x"), Vid::from("y"), Vid::from("z")],
        Exp::from(3) * Exp::varstr("x")
            + Exp::from(4) * Exp::varstr("y")
            + Exp::from(5) * Exp::varstr("x") * Exp::varstr("z"),
    );
    assert_eq!(UExp::from_pest(&mut pairs), Ok(expected));
}

#[test]
fn parser_fun_simple() {
    // Test: fun x => x
    let ex = "fun x => x";
    let mut pairs = ZippelParser::parse(Rule::exp, ex).unwrap();
    let expected = Exp::fun(vec![Vid::from("x")], Exp::varstr("x"));
    assert_eq!(UExp::from_pest(&mut pairs), Ok(expected));
}

#[test]
fn parser_mle() {
    let ex = "mle(x)";
    let mut pairs = ZippelParser::parse(Rule::exp, ex).unwrap();
    assert_eq!(UExp::from_pest(&mut pairs), Ok(Exp::mle(Exp::varstr("x"))));
}

#[test]
fn parser_record() {
    let ex = "{| x: 1, y: f |}";
    let mut pairs = ZippelParser::parse(Rule::exp, ex).unwrap();
    let mut fields = Ctx::new();
    fields.insert(&"x".to_string(), &Exp::from(1));
    fields.insert(&"y".to_string(), &Exp::varstr("f"));
    assert_eq!(UExp::from_pest(&mut pairs), Ok(Exp::record(fields)));
}

#[test]
fn parser_proj() {
    let ex = "r.x";
    let mut pairs = ZippelParser::parse(Rule::exp, ex).unwrap();
    assert_eq!(
        UExp::from_pest(&mut pairs),
        Ok(Exp::proj(Exp::varstr("r"), "x".to_string()))
    );
}

#[test]
fn parser_set_record() {
    let ex = "r.set(x, 2)";
    let mut pairs = ZippelParser::parse(Rule::exp, ex).unwrap();
    assert_eq!(
        UExp::from_pest(&mut pairs),
        Ok(Exp::set_record(
            Exp::varstr("r"),
            "x".to_string(),
            Exp::from(2)
        ))
    );
}

#[test]
fn parser_record_nested() {
    let ex = "{| a: {| b: 1 |}, c: 2 |}";
    let mut pairs = ZippelParser::parse(Rule::exp, ex).unwrap();
    let mut inner_fields = Ctx::new();
    inner_fields.insert(&"b".to_string(), &Exp::from(1));
    let mut fields = Ctx::new();
    fields.insert(&"a".to_string(), &Exp::record(inner_fields));
    fields.insert(&"c".to_string(), &Exp::from(2));
    assert_eq!(UExp::from_pest(&mut pairs), Ok(Exp::record(fields)));
}

#[test]
fn parser_record_set_nested() {
    let ex = "r.set(x, 2).set(y, 3)";
    let mut pairs = ZippelParser::parse(Rule::exp, ex).unwrap();
    assert_eq!(
        UExp::from_pest(&mut pairs),
        Ok(Exp::set_record(
            Exp::set_record(Exp::varstr("r"), "x".to_string(), Exp::from(2)),
            "y".to_string(),
            Exp::from(3)
        ))
    );
}

#[test]
fn parser_let_with_type() {
    let ex = "let x: F = 2; x";
    let mut pairs = ZippelParser::parse(Rule::exp, ex).unwrap();
    assert_eq!(
        UExp::from_pest(&mut pairs),
        Ok(Exp::letx(Vid::from("x"), Exp::from(2), Exp::varstr("x")))
    );
}

#[test]
fn parser_assert_and_verify_chain() {
    let ex = "assert(x == 2); verify(y == 3); z";
    let mut pairs = ZippelParser::parse(Rule::exp, ex).unwrap();
    let expected = Exp::seq(
        Exp::assert_eq(Exp::varstr("x"), Exp::from(2)),
        Exp::seq(
            Exp::verify_eq(Exp::varstr("y"), Exp::from(3)),
            Exp::varstr("z"),
        ),
    );
    assert_eq!(UExp::from_pest(&mut pairs), Ok(expected));
}

#[test]
fn parser_app_seq() {
    // The main motivation for the refactor: foo(); bar now parses.
    let ex = "foo(a); bar(b)";
    let mut pairs = ZippelParser::parse(Rule::exp, ex).unwrap();
    assert_eq!(
        UExp::from_pest(&mut pairs),
        Ok(Exp::seq(
            Exp::app(Vid::from("foo"), Exps::from([Exp::varstr("a")])),
            Exp::app(Vid::from("bar"), Exps::from([Exp::varstr("b")])),
        ))
    );
}

#[test]
fn parser_arith_seq() {
    // Any expression can be sequenced, not just let/log/assert/verify.
    let ex = "1 + 2; x";
    let mut pairs = ZippelParser::parse(Rule::exp, ex).unwrap();
    assert_eq!(
        UExp::from_pest(&mut pairs),
        Ok(Exp::seq(Exp::from(1) + Exp::from(2), Exp::varstr("x"),))
    );
}

#[test]
fn parser_paren_seq() {
    // Sequencing inside parenthesized expressions.
    let ex = "(a; b)";
    let mut pairs = ZippelParser::parse(Rule::exp, ex).unwrap();
    assert_eq!(
        UExp::from_pest(&mut pairs),
        Ok(Exp::seq(Exp::varstr("a"), Exp::varstr("b")))
    );
}

#[test]
fn parser_let_value_no_seq() {
    // Value position uses exp_no_seq — `;` cannot appear in the value.
    // `let x = 1 + 2; x` parses as let(x, 1+2, x), NOT let(x, seq(1, ...)).
    let ex = "let x = 1 + 2; x";
    let mut pairs = ZippelParser::parse(Rule::exp, ex).unwrap();
    assert_eq!(
        UExp::from_pest(&mut pairs),
        Ok(Exp::letx(
            Vid::from("x"),
            Exp::from(1) + Exp::from(2),
            Exp::varstr("x")
        ))
    );
}

#[test]
fn parser_assert_no_cont() {
    // Assert without `;` produces bare Assert(lhs, rhs), no Unit cont.
    let ex = "assert(x == 2)";
    let mut pairs = ZippelParser::parse(Rule::exp, ex).unwrap();
    assert_eq!(
        UExp::from_pest(&mut pairs),
        Ok(Exp::Assert(
            Box::new(Exp::varstr("x")),
            Box::new(Exp::from(2)),
        ))
    );
}

#[test]
fn pretty_bin_parens() {
    // (a + b) * c must print with parens, not as "a + b * c"
    let expr: UExp = Exp::mul(
        Exp::add(Exp::varstr("a"), Exp::varstr("b")),
        Exp::varstr("c"),
    );
    assert_eq!(format!("{}", expr), "(a + b) * c");

    // a * b + c needs no parens (higher prec child on left of lower prec parent)
    let expr: UExp = Exp::add(
        Exp::mul(Exp::varstr("a"), Exp::varstr("b")),
        Exp::varstr("c"),
    );
    assert_eq!(format!("{}", expr), "a * b + c");

    // a - (b - c) needs rhs parens (left-assoc, same prec)
    let expr: UExp = Exp::sub(
        Exp::varstr("a"),
        Exp::sub(Exp::varstr("b"), Exp::varstr("c")),
    );
    assert_eq!(format!("{}", expr), "a - (b - c)");

    // a - b - c needs no parens (left-assoc, left child same prec)
    let expr: UExp = Exp::sub(
        Exp::sub(Exp::varstr("a"), Exp::varstr("b")),
        Exp::varstr("c"),
    );
    assert_eq!(format!("{}", expr), "a - b - c");

    // a ^ b ^ c needs no rhs parens (right-assoc)
    let expr: UExp = Exp::pow(
        Exp::varstr("a"),
        Exp::pow(Exp::varstr("b"), Exp::varstr("c")),
    );
    assert_eq!(format!("{}", expr), "a ^ b ^ c");

    // (a ^ b) ^ c needs lhs parens (right-assoc, left child same prec)
    let expr: UExp = Exp::pow(
        Exp::pow(Exp::varstr("a"), Exp::varstr("b")),
        Exp::varstr("c"),
    );
    assert_eq!(format!("{}", expr), "(a ^ b) ^ c");

    // a % b + c — Rem is same prec as Mul (AEXP_PARSER level 2), higher than Add
    let expr: UExp = Exp::add(
        Exp::rem(Exp::varstr("a"), Exp::varstr("b")),
        Exp::varstr("c"),
    );
    assert_eq!(format!("{}", expr), "a % b + c");

    // (a + b) ++ c — Concat is higher prec than Add
    let expr: UExp = Exp::concat(
        Exp::add(Exp::varstr("a"), Exp::varstr("b")),
        Exp::varstr("c"),
    );
    assert_eq!(format!("{}", expr), "(a + b) ++ c");

    // (a + b) + (c + d) — left-assoc: lhs no parens, rhs parens
    let expr: UExp = Exp::add(
        Exp::add(Exp::varstr("a"), Exp::varstr("b")),
        Exp::add(Exp::varstr("c"), Exp::varstr("d")),
    );
    assert_eq!(format!("{}", expr), "a + b + (c + d)");
}

#[test]
fn pretty_pair() {
    // pair(t, e) not t pair(e)
    let expr: UExp = Exp::pair(Exp::varstr("g1"), Exp::varstr("g2"));
    assert_eq!(format!("{}", expr), "pair(g1, g2)");
}
