use share::Ctx;
use std::fmt;
use std::ops::Index;

use share::traversal::ToTraversal1;

use crate::ast::range::{Range, RangeTraversal};
use crate::ast::spanned::Spanned;
use crate::ast::Size;
use crate::id::{Tid, TidSubst, Vid};
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

    ///     Equality comparison: returns `Bool` (scalar) or `Vec<Bool, N>` (vec).
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let b = x == y;
    ///     ```
    Equ,

    ///     Logical AND: both operands must be `Bool`, result is `Bool`.
    ///     In the GB encoding, `&&` is multiplication (`a * b`), since `Bool`
    ///     values are 0/1 field elements.
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let b = x == y && z == w;
    ///     ```
    And,
}

/// Represents arithmetic expressions in the Zippel language.
/// It is parameterized by types `N` representing the sizes of ranges, indices etc
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
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
    Var(Spanned<Vid>),

    ///     Function application
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let result1 = f(x + 2, x)
    ///     ```
    App(Spanned<Vid>, Exps<N>),

    /// Interpolate to a univariate polynomial: unary `interpolate(v)` uses the FFT
    /// evaluation grid (inverse FFT); binary `interpolate(xs, ys)` uses explicit points.
    ///
    /// **Zippel:**
    /// ```zippel
    /// let p_grid = interpolate(evals_on_fft_domain);
    /// let q = interpolate([0, 1, 2], [a, b, c]);
    /// ```
    Interpolate(Option<Box<Spanned<Exp<N>>>>, Box<Spanned<Exp<N>>>),

    ///     Polynomial from coefficients
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let p = poly(1,2,3);
    ///     ```
    Poly(Box<Spanned<Exp<N>>>),

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
    Evaluate(
        Box<Spanned<Exp<N>>>,
        Option<Range<N>>,
        Option<Box<Spanned<Exp<N>>>>,
    ),

    ///     Get vector of coefficients of polynomial
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let v = coef(poly(1,2,3));
    ///     ```
    Coef(Box<Spanned<Exp<N>>>),

    ///     Multilinear extension of a matrix, polynomial, etc.
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let g = mle x;
    ///     ```
    Mle(Box<Spanned<Exp<N>>>),

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
    Bin(BinOp, Box<Spanned<Exp<N>>>, Box<Spanned<Exp<N>>>),

    ///     Unary negation
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let neg = -x;
    ///     ```
    Neg(Box<Spanned<Exp<N>>>),

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
    Map(Box<Spanned<Exp<N>>>, Spanned<Vid>, Box<Spanned<Exp<N>>>),

    ///     Reduce a vector with a binary operation
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let sum = reduce(+, [1,2,3]);
    ///     ```
    Reduce(BinOp, Box<Spanned<Exp<N>>>),

    ///     Random access or slice a vector
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let first = v[0]
    ///     ```
    Ram(Box<Spanned<Exp<N>>>, Box<Spanned<Exp<N>>>),

    ///     Bilinear pairing
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let g = pair(g1, g2);
    ///     ```
    Pair(Box<Spanned<Exp<N>>>, Box<Spanned<Exp<N>>>),

    ///     Sample pseudo-random number generator
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let r := random<F*>();
    ///     ```
    Random(Spanned<Tid>, bool),

    ///     Random oracle challenge.
    ///     **Zippel Code:**
    ///     ```zippel
    ///     r <- challenge<F>();
    ///     ```
    Challenge(Spanned<Tid>, bool),

    ///     Represents a let-expression, which binds a value to an identifier.
    ///
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let x = 5 + 3;
    ///     assert(5 == 3);
    ///     ```
    Let(
        Option<Spanned<Vid>>,
        Box<Spanned<Exp<N>>>,
        Option<Box<Spanned<Exp<N>>>>,
    ),

    ///     Represents a log-let expression with transcript dependency.
    ///     This variant is used to bind a value to an identifier while logging the operation.
    ///     **Zippel Code:**
    ///     ```zippel
    ///     p <- interpolate(v, [0,1,2])
    ///     ```
    Log(
        Spanned<Vid>,
        Box<Spanned<Exp<N>>>,
        Option<Box<Spanned<Exp<N>>>>,
    ),

    ///     Prover assertion: asserts that the expression is true.
    ///     The expression must be `Bool` or `Vec<Bool, N>`.
    ///     **Zippel Code:**
    ///     ```zippel
    ///     assert(1 == 1)
    ///     ```
    Assert(Box<Spanned<Exp<N>>>),

    ///     Verifier check: verifies that the expression is true.
    ///     The expression must be `Bool` or `Vec<Bool, N>`.
    ///     **Zippel Code:**
    ///     ```zippel
    ///     verify(a == a)
    ///     ```
    Verify(Box<Spanned<Exp<N>>>),

    ///     Polynomial function definition
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let p = fun x, y => x^2 + 2*x*y + 3*y^2;
    ///     ```
    Fun(Vec<Spanned<Vid>>, Box<Spanned<Exp<N>>>),

    ///     Record construction
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let a = {| name: "Sydnie", balance: 100 |};
    ///     ```
    Record(Ctx<Spanned<String>, Spanned<Exp<N>>>),

    ///     Field projection
    ///     **Zippel Code:**
    ///     ```zippel
    ///     a.name
    ///     ```
    Proj(Box<Spanned<Exp<N>>>, Spanned<String>),

    ///     Record update: create a new record identical to the given record
    ///     except with the specified field set to the given value.
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let new_record = old_record.set(name, 3);
    ///     ```
    SetRecord(Box<Spanned<Exp<N>>>, Spanned<String>, Box<Spanned<Exp<N>>>),
}

/// Free variables
pub trait FreeVars {
    fn freevars(&self) -> Set<Vid>;
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Exps<N>(pub Vec<Spanned<Exp<N>>>);

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
            Exp::Neg(box x) => Ok(Exp::Neg(Box::new(x.traverse1(f)?))),
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
            Exp::Let(x, box a, b) => {
                let b = match b {
                    Some(b) => Some(Box::new((*b).traverse1(f)?)),
                    None => None,
                };
                Ok(Exp::Let(x, Box::new(a.traverse1(f)?), b))
            }
            Exp::Log(x, box a, b) => {
                let b = match b {
                    Some(b) => Some(Box::new((*b).traverse1(f)?)),
                    None => None,
                };
                Ok(Exp::Log(x, Box::new(a.traverse1(f)?), b))
            }
            Exp::Assert(box exp) => Ok(Exp::Assert(Box::new(exp.traverse1(f)?))),
            Exp::Verify(box exp) => Ok(Exp::Verify(Box::new(exp.traverse1(f)?))),
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
            Exp::Challenge(t, _) if &t.node == from => t.node = to.clone(),
            Exp::Random(t, _) if &t.node == from => t.node = to.clone(),
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
            Exp::Mle(box p)
            | Exp::Poly(box p)
            | Exp::Reduce(_, box p)
            | Exp::Coef(box p)
            | Exp::Neg(box p) => p.tid_subst(from, to),
            Exp::Assert(box exp) | Exp::Verify(box exp) => {
                exp.tid_subst(from, to);
            }
            Exp::Vec(v) | Exp::App(_, v) => v.tid_subst(from, to),
            Exp::Bin(_, box a, box b)
            | Exp::Map(box a, _, box b)
            | Exp::Ram(box a, box b)
            | Exp::Pair(box a, box b) => {
                a.tid_subst(from, to);
                b.tid_subst(from, to);
            }
            Exp::Let(_, box a, b) => {
                a.tid_subst(from, to);
                if let Some(box b) = b {
                    b.tid_subst(from, to);
                }
            }
            Exp::Log(_, box a, b) => {
                a.tid_subst(from, to);
                if let Some(box b) = b {
                    b.tid_subst(from, to);
                }
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
            Exp::Var(id) => Set::singleton(id.node.clone()),
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
            Exp::Mle(box p)
            | Exp::Poly(box p)
            | Exp::Reduce(_, box p)
            | Exp::Coef(box p)
            | Exp::Neg(box p) => p.freevars(),
            Exp::Assert(box exp) | Exp::Verify(box exp) => exp.freevars(),
            Exp::Vec(v) | Exp::App(_, v) => v.freevars(),
            Exp::Bin(_, box a, box b)
            | Exp::Pair(box a, box b)
            | Exp::Ram(box a, box b)
            | Exp::Map(box a, _, box b) => a.freevars().union(b.freevars()),
            Exp::Let(_, box a, b) => {
                let mut fv = a.freevars();
                if let Some(box b) = b {
                    fv = fv.union(b.freevars());
                }
                fv
            }
            Exp::Log(_, box a, b) => {
                let mut fv = a.freevars();
                if let Some(box b) = b {
                    fv = fv.union(b.freevars());
                }
                fv
            }
            Exp::Fun(vars, box body) => {
                let bound_vars: Set<Vid> = vars.iter().map(|v| v.node.clone()).collect();
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
            Exp::Interpolate(po, box evals) => Ok(Exp::Interpolate(
                match po {
                    None => None,
                    Some(box p) => Some(Box::new(p.range_traverse(f)?)),
                },
                Box::new(evals.range_traverse(f)?),
            )),
            Exp::Poly(box p) => Ok(Exp::Poly(Box::new(p.range_traverse(f)?))),
            Exp::Mle(box p) => Ok(Exp::Mle(Box::new(p.range_traverse(f)?))),
            Exp::Vec(v) => Ok(Exp::Vec(v.range_traverse(f)?)),
            Exp::Evaluate(box p, selector, ox) => Ok(Exp::Evaluate(
                Box::new(p.range_traverse(f)?),
                match selector {
                    None => None,
                    Some(r) => Some(f(r)?),
                },
                match ox {
                    None => None,
                    Some(box x) => Some(Box::new(x.range_traverse(f)?)),
                },
            )),
            Exp::Bin(op, box x, box y) => Ok(Exp::Bin(
                op,
                Box::new(x.range_traverse(f)?),
                Box::new(y.range_traverse(f)?),
            )),
            Exp::Neg(box x) => Ok(Exp::Neg(Box::new(x.range_traverse(f)?))),
            Exp::Map(box x, id, box r) => Ok(Exp::Map(
                Box::new(x.range_traverse(f)?),
                id,
                Box::new(r.range_traverse(f)?),
            )),
            Exp::Ram(box x, box i) => Ok(Exp::Ram(
                Box::new(x.range_traverse(f)?),
                Box::new(i.range_traverse(f)?),
            )),
            Exp::Coef(box x) => Ok(Exp::Coef(Box::new(x.range_traverse(f)?))),
            Exp::Let(x, box t, e) => {
                let e = match e {
                    Some(e) => Some(Box::new((*e).range_traverse(f)?)),
                    None => None,
                };
                Ok(Exp::Let(x, Box::new(t.range_traverse(f)?), e))
            }
            Exp::Log(x, box t, e) => {
                let e = match e {
                    Some(e) => Some(Box::new((*e).range_traverse(f)?)),
                    None => None,
                };
                Ok(Exp::Log(x, Box::new(t.range_traverse(f)?), e))
            }
            Exp::Pair(box t, box e) => Ok(Exp::Pair(
                Box::new(t.range_traverse(f)?),
                Box::new(e.range_traverse(f)?),
            )),
            Exp::Assert(box exp) => Ok(Exp::Assert(Box::new(exp.range_traverse(f)?))),
            Exp::Verify(box exp) => Ok(Exp::Verify(Box::new(exp.range_traverse(f)?))),
            Exp::App(x, ts) => Ok(Exp::App(x, ts.range_traverse(f)?)),
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
    pub fn iter(&self) -> std::slice::Iter<'_, Spanned<Exp<N>>> {
        self.0.iter()
    }
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
    pub fn len(&self) -> usize {
        self.0.len()
    }
    // Parser guarantees that the vector is non-empty
    pub fn last(&self) -> &Spanned<Exp<N>> {
        self.0.last().unwrap()
    }
}

impl<N> IntoIterator for Exps<N> {
    type Item = Spanned<Exp<N>>;
    type IntoIter = std::vec::IntoIter<Spanned<Exp<N>>>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<N> FromIterator<Spanned<Exp<N>>> for Exps<N> {
    fn from_iter<I: IntoIterator<Item = Spanned<Exp<N>>>>(iter: I) -> Self {
        Exps(iter.into_iter().collect())
    }
}

impl<const N: usize, T> From<[Spanned<Exp<T>>; N]> for Exps<T> {
    fn from(arr: [Spanned<Exp<T>>; N]) -> Self {
        Exps(arr.into())
    }
}

impl<T> Index<usize> for Exps<T> {
    type Output = Spanned<Exp<T>>;

    fn index(&self, index: usize) -> &Self::Output {
        self.0.index(index)
    }
}

impl<N> Exp<N> {
    pub fn is_pure(&self) -> bool {
        match self {
            Exp::Lit(_) | Exp::Unit | Exp::Var(_) | Exp::Range(_) => true,
            Exp::Interpolate(None, box e) => e.is_pure(),
            Exp::Interpolate(Some(box p), box e) => p.is_pure() && e.is_pure(),
            Exp::Coef(box p) => p.is_pure(),
            Exp::Poly(box p) => p.is_pure(),
            Exp::Mle(box p) => p.is_pure(),
            Exp::Reduce(_, box p) => p.is_pure(),
            Exp::Vec(v) => v.iter().all(|e| e.node.is_pure()),
            Exp::Bin(_, box a, box b) => a.is_pure() && b.is_pure(),
            Exp::Neg(box a) => a.is_pure(),
            Exp::Evaluate(box p, _, ox) => p.is_pure() && ox.as_ref().is_none_or(|x| x.is_pure()),
            Exp::Pair(box a, box b) => a.is_pure() && b.is_pure(),
            Exp::Map(box a, _, box b) => a.is_pure() && b.is_pure(),
            Exp::Ram(box a, box b) => a.is_pure() && b.is_pure(),
            Exp::Let(_, box a, b) => a.is_pure() && b.as_ref().is_none_or(|b| b.is_pure()),
            Exp::Log(_, box _, _) => false,
            Exp::Challenge(_, _) | Exp::Random(_, _) => false,
            Exp::App(_, args) => args.iter().all(|e| e.node.is_pure()),
            Exp::Assert(_) | Exp::Verify(_) => false,
            Exp::Fun(_, box body) => body.is_pure(),
            Exp::Record(fields) => fields.iter().all(|(_, e)| e.node.is_pure()),
            Exp::Proj(box exp, _) => exp.is_pure(),
            Exp::SetRecord(box record, _, box value) => record.is_pure() && value.is_pure(),
        }
    }

    /// Check if an expression is valid in a relation (where clause).
    ///
    /// Allows: `Let`, `Random`, and all pure expressions.
    /// Rejects: `Challenge` (verifier oracle), `Log` (transcript),
    /// `Verify` (verifier-side check), `Assert` (returns `Unit`, not
    /// `Bool` — the relation IS the assertion, auto-wrapped by the graph).
    pub fn is_relation_pure(&self) -> bool {
        match self {
            // Reject: verifier-only constructs and Assert (returns Unit)
            Exp::Challenge(_, _) | Exp::Log(_, _, _) | Exp::Verify(_) | Exp::Assert(_) => false,
            // Allow: Random (trusted-setup trapdoors, etc.)
            Exp::Random(_, _) => true,
            Exp::Let(_, box val, cont) => {
                val.is_relation_pure() && cont.as_ref().is_none_or(|c| c.is_relation_pure())
            }
            Exp::Map(box a, _, box b) => a.is_relation_pure() && b.is_relation_pure(),
            Exp::Vec(v) => v.iter().all(|e| e.node.is_relation_pure()),
            Exp::Bin(_, box a, box b) => a.is_relation_pure() && b.is_relation_pure(),
            Exp::Neg(box a) => a.is_relation_pure(),
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
            Exp::App(_, args) => args.iter().all(|e| e.node.is_relation_pure()),
            Exp::Fun(_, box body) => body.is_relation_pure(),
            Exp::Record(fields) => fields.iter().all(|(_, e)| e.node.is_relation_pure()),
            Exp::Proj(box exp, _) => exp.is_relation_pure(),
            Exp::SetRecord(box record, _, box value) => {
                record.is_relation_pure() && value.is_relation_pure()
            }
            // Leaves: always valid
            Exp::Lit(_) | Exp::Unit | Exp::Var(_) | Exp::Range(_) => true,
        }
    }
}

impl BinOp {
    /// Precedence matching the parser's Pratt table.
    /// Lower binds looser. Used by the formatter to produce text that
    /// re-parses to the same AST.
    pub fn precedence(&self) -> usize {
        match self {
            BinOp::And => 0, // lowest precedence
            BinOp::Equ => 1,
            BinOp::Add | BinOp::Sub => 2,
            BinOp::Mul | BinOp::Div | BinOp::Rem => 3,
            BinOp::Concat => 4,
            BinOp::Pow => 5,
            BinOp::Dot => 6, // not infix in grammar; programmatic-only
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
            BinOp::Equ => allocator.text(" == "),
            BinOp::And => allocator.text(" && "),
        }
    }

    fn is_nil(&self) -> bool {
        false
    }
}

/// Blanket Pretty impl for Spanned<T> — delegates to inner T's Pretty.
/// This lets all Pretty impls work with Spanned wrappers without .node calls.
impl<'a, D, A, T> Pretty<'a, D, A> for Spanned<T>
where
    T: Pretty<'a, D, A>,
    D: DocAllocator<'a, A>,
    D::Doc: Clone,
    A: 'a + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        self.node.pretty(allocator)
    }
    fn is_nil(&self) -> bool {
        self.node.is_nil()
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
                let parent_prec = op.precedence();
                let right_assoc = op.is_right_assoc();
                let lhs_needs_paren = matches!(&a.node,
                    Exp::Bin(child_op, _, _) if child_op.precedence() < parent_prec
                        || (child_op.precedence() == parent_prec && right_assoc));
                let rhs_needs_paren = matches!(&b.node,
                    Exp::Bin(child_op, _, _) if child_op.precedence() < parent_prec
                        || (child_op.precedence() == parent_prec && !right_assoc));
                let lhs = a.pretty(allocator);
                let lhs = if lhs_needs_paren {
                    allocator.concat([allocator.text("("), lhs, allocator.text(")")])
                } else {
                    lhs
                };
                let rhs = b.pretty(allocator);
                let rhs = if rhs_needs_paren {
                    allocator.concat([allocator.text("("), rhs, allocator.text(")")])
                } else {
                    rhs
                };
                allocator.concat([lhs, op.pretty(allocator), rhs])
            }
            Exp::Neg(a) => allocator.concat([allocator.text("-"), (*a).pretty(allocator)]),
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
            Exp::Let(Some(x), t, e) => {
                let mut docs = vec![
                    allocator.text("let "),
                    x.pretty(allocator),
                    allocator.text(" = "),
                    (*t).pretty(allocator),
                    allocator.text(";"),
                ];
                if let Some(e) = e {
                    docs.push(allocator.hardline());
                    docs.push((*e).pretty(allocator));
                }
                allocator.concat(docs)
            }
            Exp::Let(None, t, e) => {
                let mut docs = vec![(*t).pretty(allocator), allocator.text(";")];
                if let Some(e) = e {
                    docs.push(allocator.hardline());
                    docs.push((*e).pretty(allocator));
                }
                allocator.concat(docs)
            }
            Exp::Log(x, t, e) => {
                let mut docs = vec![
                    x.pretty(allocator),
                    allocator.text(" <- "),
                    (*t).pretty(allocator),
                    allocator.text(";"),
                ];
                if let Some(e) = e {
                    docs.push(allocator.hardline());
                    docs.push((*e).pretty(allocator));
                }
                allocator.concat(docs)
            }
            Exp::Assert(box exp) => allocator.concat([
                allocator.text("assert("),
                exp.pretty(allocator),
                allocator.text(")"),
            ]),
            Exp::Verify(box exp) => allocator.concat([
                allocator.text("verify("),
                exp.pretty(allocator),
                allocator.text(")"),
            ]),
            Exp::Fun(vars, body) => {
                let vars_str = vars
                    .iter()
                    .map(|v| v.node.0.as_str())
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
                            allocator.text(name.node),
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
                allocator.text(field.node),
            ]),
            Exp::SetRecord(box record, field, box value) => allocator.concat([
                record.pretty(allocator),
                allocator.text(".set("),
                allocator.text(field.node),
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

#[cfg(test)]
mod test {
    use super::*;
    use crate::ast::spanned::Spanned;
    use crate::ast::Size;
    use crate::id::Vid;

    fn varstr(x: &str) -> Spanned<Exp<Size>> {
        Spanned::dummy(Exp::Var(Spanned::dummy(Vid::from(x))))
    }
    fn bin(op: BinOp, l: Spanned<Exp<Size>>, r: Spanned<Exp<Size>>) -> Spanned<Exp<Size>> {
        Spanned::dummy(Exp::Bin(op, Box::new(l), Box::new(r)))
    }
    fn add(l: Spanned<Exp<Size>>, r: Spanned<Exp<Size>>) -> Spanned<Exp<Size>> {
        bin(BinOp::Add, l, r)
    }
    fn sub(l: Spanned<Exp<Size>>, r: Spanned<Exp<Size>>) -> Spanned<Exp<Size>> {
        bin(BinOp::Sub, l, r)
    }
    fn mul(l: Spanned<Exp<Size>>, r: Spanned<Exp<Size>>) -> Spanned<Exp<Size>> {
        bin(BinOp::Mul, l, r)
    }
    fn pow(l: Spanned<Exp<Size>>, r: Spanned<Exp<Size>>) -> Spanned<Exp<Size>> {
        bin(BinOp::Pow, l, r)
    }
    fn rem(l: Spanned<Exp<Size>>, r: Spanned<Exp<Size>>) -> Spanned<Exp<Size>> {
        bin(BinOp::Rem, l, r)
    }
    fn concat(l: Spanned<Exp<Size>>, r: Spanned<Exp<Size>>) -> Spanned<Exp<Size>> {
        bin(BinOp::Concat, l, r)
    }
    fn pair(t: Spanned<Exp<Size>>, e: Spanned<Exp<Size>>) -> Spanned<Exp<Size>> {
        Spanned::dummy(Exp::Pair(Box::new(t), Box::new(e)))
    }

    #[test]
    fn pretty_bin_parens() {
        // (a + b) * c must print with parens, not as "a + b * c"
        let expr = mul(add(varstr("a"), varstr("b")), varstr("c"));
        assert_eq!(format!("{}", expr), "(a + b) * c");

        // a * b + c needs no parens (higher prec child on left of lower prec parent)
        let expr = add(mul(varstr("a"), varstr("b")), varstr("c"));
        assert_eq!(format!("{}", expr), "a * b + c");

        // a - (b - c) needs rhs parens (left-assoc, same prec)
        let expr = sub(varstr("a"), sub(varstr("b"), varstr("c")));
        assert_eq!(format!("{}", expr), "a - (b - c)");

        // a - b - c needs no parens (left-assoc, left child same prec)
        let expr = sub(sub(varstr("a"), varstr("b")), varstr("c"));
        assert_eq!(format!("{}", expr), "a - b - c");

        // a ^ b ^ c needs no rhs parens (right-assoc)
        let expr = pow(varstr("a"), pow(varstr("b"), varstr("c")));
        assert_eq!(format!("{}", expr), "a ^ b ^ c");

        // (a ^ b) ^ c needs lhs parens (right-assoc, left child same prec)
        let expr = pow(pow(varstr("a"), varstr("b")), varstr("c"));
        assert_eq!(format!("{}", expr), "(a ^ b) ^ c");

        // a % b + c — Rem is same prec as Mul (AEXP_PARSER level 2), higher than Add
        let expr = add(rem(varstr("a"), varstr("b")), varstr("c"));
        assert_eq!(format!("{}", expr), "a % b + c");

        // (a + b) ++ c — Concat is higher prec than Add
        let expr = concat(add(varstr("a"), varstr("b")), varstr("c"));
        assert_eq!(format!("{}", expr), "(a + b) ++ c");

        // (a + b) + (c + d) — left-assoc: lhs no parens, rhs parens
        let expr = add(add(varstr("a"), varstr("b")), add(varstr("c"), varstr("d")));
        assert_eq!(format!("{}", expr), "a + b + (c + d)");
    }

    #[test]
    fn pretty_pair() {
        // pair(t, e) not t pair(e)
        let expr = pair(varstr("g1"), varstr("g2"));
        assert_eq!(format!("{}", expr), "pair(g1, g2)");
    }
}
