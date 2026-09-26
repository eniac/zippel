use share::Ctx;
use std::fmt;
use std::ops::Index;

use share::traversal::ToTraversal1;

use crate::ast::Size;
use crate::ast::range::{Range, RangeTraversal};
use crate::ast::spanned::Spanned;
use crate::id::{Tid, TidSubst, Vid};
use share::Set;

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
    /// Value variables that occur free in `self`, i.e. are not bound by an
    /// enclosing `let`, `map` binder or `fun` parameter.
    fn freevars(&self) -> Set<Vid>;
}

/// A sequence of expressions: a vector literal's elements, a call's actual
/// arguments, or a statement block whose value is its last expression.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Exps<N>(pub Vec<Spanned<Exp<N>>>);

/// Symbolic sized AST node, as parsed from input
pub type UExp = Exp<Size>;
/// Sequence of symbolically sized expressions.
pub type UExps = Exps<Size>;

/// Concrete size untyped AST node
pub type CExp = Exp<usize>;
/// Sequence of concretely sized expressions.
pub type CExps = Exps<usize>;

/// How to traverse the first type parameter `N` for `Exp<N>`
impl<N: Clone> ToTraversal1<N> for Exp<N> {
    type Output<Z> = Exp<Z>;
    fn traverse1<Z: Clone, E>(self, f: &mut dyn FnMut(N) -> Result<Z, E>) -> Result<Exp<Z>, E> {
        match self {
            Exp::Lit(x) => Ok(Exp::Lit(f(x)?)),
            Exp::Unit => Ok(Exp::Unit),
            Exp::Var(v) => Ok(Exp::Var(v)),
            Exp::Interpolate(po, deref!(evals)) => Ok(Exp::Interpolate(
                match po {
                    None => None,
                    Some(deref!(p)) => Some(Box::new(p.traverse1(f)?)),
                },
                Box::new(evals.traverse1(f)?),
            )),
            Exp::Poly(deref!(p)) => Ok(Exp::Poly(Box::new(p.traverse1(f)?))),
            Exp::Evaluate(deref!(p), selector, ox) => Ok(Exp::Evaluate(
                Box::new(p.traverse1(f)?),
                match selector {
                    None => None,
                    Some(r) => Some(r.traverse1(f)?),
                },
                match ox {
                    None => None,
                    Some(deref!(x)) => Some(Box::new(x.traverse1(f)?)),
                },
            )),
            Exp::Coef(deref!(p)) => Ok(Exp::Coef(Box::new(p.traverse1(f)?))),
            Exp::Mle(deref!(p)) => Ok(Exp::Mle(Box::new(p.traverse1(f)?))),
            Exp::Pair(deref!(x), deref!(y)) => Ok(Exp::Pair(
                Box::new(x.traverse1(f)?),
                Box::new(y.traverse1(f)?),
            )),
            Exp::Vec(v) => Ok(Exp::Vec(v.traverse1(f)?)),
            Exp::App(x, ts) => Ok(Exp::App(x, ts.traverse1(f)?)),
            Exp::Bin(op, deref!(x), deref!(y)) => Ok(Exp::Bin(
                op,
                Box::new(x.traverse1(f)?),
                Box::new(y.traverse1(f)?),
            )),
            Exp::Neg(deref!(x)) => Ok(Exp::Neg(Box::new(x.traverse1(f)?))),
            Exp::Map(deref!(x), id, deref!(r)) => Ok(Exp::Map(
                Box::new(x.traverse1(f)?),
                id,
                Box::new(r.traverse1(f)?),
            )),
            Exp::Reduce(op, deref!(x)) => Ok(Exp::Reduce(op, Box::new(x.traverse1(f)?))),
            Exp::Challenge(t, b) => Ok(Exp::Challenge(t, b)),
            Exp::Random(t, b) => Ok(Exp::Random(t, b)),
            Exp::Range(r) => Ok(Exp::Range(r.traverse1(f)?)),
            Exp::Ram(deref!(x), deref!(i)) => Ok(Exp::Ram(
                Box::new(x.traverse1(f)?),
                Box::new(i.traverse1(f)?),
            )),
            Exp::Let(x, deref!(a), b) => {
                let b = match b {
                    Some(b) => Some(Box::new((*b).traverse1(f)?)),
                    None => None,
                };
                Ok(Exp::Let(x, Box::new(a.traverse1(f)?), b))
            }
            Exp::Log(x, deref!(a), b) => {
                let b = match b {
                    Some(b) => Some(Box::new((*b).traverse1(f)?)),
                    None => None,
                };
                Ok(Exp::Log(x, Box::new(a.traverse1(f)?), b))
            }
            Exp::Assert(deref!(exp)) => Ok(Exp::Assert(Box::new(exp.traverse1(f)?))),
            Exp::Verify(deref!(exp)) => Ok(Exp::Verify(Box::new(exp.traverse1(f)?))),
            Exp::Fun(vars, deref!(body)) => Ok(Exp::Fun(vars, Box::new(body.traverse1(f)?))),
            Exp::Record(fields) => {
                let pairs: Vec<_> = fields
                    .into_iter()
                    .map(|(name, exp)| exp.traverse1(f).map(|new_exp| (name, new_exp)))
                    .collect::<Result<_, _>>()?;
                Ok(Exp::Record(Ctx::from_iter(pairs)))
            }
            Exp::Proj(deref!(exp), field) => Ok(Exp::Proj(Box::new(exp.traverse1(f)?), field)),
            Exp::SetRecord(deref!(record), field, deref!(value)) => Ok(Exp::SetRecord(
                Box::new(record.traverse1(f)?),
                field,
                Box::new(value.traverse1(f)?),
            )),
        }
    }
}

/// How to traverse the first type parameter `N` for `Exps<N>`
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

/// Traverse `Tid` inside `TExp`
impl TidSubst for CExp {
    fn tid_subst(&mut self, from: &Tid, to: &Tid) {
        match self {
            Exp::Challenge(t, _) if &t.node == from => t.node = to.clone(),
            Exp::Random(t, _) if &t.node == from => t.node = to.clone(),
            Exp::Interpolate(None, e) => e.tid_subst(from, to),
            Exp::Interpolate(Some(p), e) => {
                p.tid_subst(from, to);
                e.tid_subst(from, to);
            }
            Exp::Evaluate(p, _, None) => p.tid_subst(from, to),
            Exp::Evaluate(p, _, Some(x)) => {
                p.tid_subst(from, to);
                x.tid_subst(from, to);
            }
            Exp::Mle(p) | Exp::Poly(p) | Exp::Reduce(_, p) | Exp::Coef(p) | Exp::Neg(p) => {
                p.tid_subst(from, to)
            }
            Exp::Assert(exp) | Exp::Verify(exp) => {
                exp.tid_subst(from, to);
            }
            Exp::Vec(v) | Exp::App(_, v) => v.tid_subst(from, to),
            Exp::Bin(_, a, b) | Exp::Map(a, _, b) | Exp::Ram(a, b) | Exp::Pair(a, b) => {
                a.tid_subst(from, to);
                b.tid_subst(from, to);
            }
            Exp::Let(_, a, b) => {
                a.tid_subst(from, to);
                if let Some(b) = b {
                    b.tid_subst(from, to);
                }
            }
            Exp::Log(_, a, b) => {
                a.tid_subst(from, to);
                if let Some(b) = b {
                    b.tid_subst(from, to);
                }
            }
            Exp::Fun(_, body) => body.tid_subst(from, to),
            Exp::Record(fields) => {
                fields.modify(|_, field_exp| {
                    field_exp.tid_subst(from, to);
                });
            }
            Exp::Proj(exp, _) => exp.tid_subst(from, to),
            Exp::SetRecord(record, _, value) => {
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
            Exp::Mle(p) | Exp::Poly(p) | Exp::Reduce(_, p) | Exp::Coef(p) | Exp::Neg(p) => {
                p.freevars()
            }
            Exp::Assert(exp) | Exp::Verify(exp) => exp.freevars(),
            Exp::Vec(v) | Exp::App(_, v) => v.freevars(),
            Exp::Bin(_, a, b) | Exp::Pair(a, b) | Exp::Ram(a, b) | Exp::Map(a, _, b) => {
                a.freevars().union(b.freevars())
            }
            Exp::Let(_, a, b) => {
                let mut fv = a.freevars();
                if let Some(b) = b {
                    fv = fv.union(b.freevars());
                }
                fv
            }
            Exp::Log(_, a, b) => {
                let mut fv = a.freevars();
                if let Some(b) = b {
                    fv = fv.union(b.freevars());
                }
                fv
            }
            Exp::Fun(vars, body) => {
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
            Exp::Proj(exp, _) => exp.freevars(),
            Exp::SetRecord(record, _, value) => record.freevars().union(value.freevars()),
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
            Exp::Interpolate(po, evals) => Ok(Exp::Interpolate(
                match po {
                    None => None,
                    Some(p) => Some(Box::new(p.range_traverse(f)?)),
                },
                Box::new(evals.range_traverse(f)?),
            )),
            Exp::Poly(p) => Ok(Exp::Poly(Box::new(p.range_traverse(f)?))),
            Exp::Mle(p) => Ok(Exp::Mle(Box::new(p.range_traverse(f)?))),
            Exp::Vec(v) => Ok(Exp::Vec(v.range_traverse(f)?)),
            Exp::Evaluate(p, selector, ox) => Ok(Exp::Evaluate(
                Box::new(p.range_traverse(f)?),
                match selector {
                    None => None,
                    Some(r) => Some(f(r)?),
                },
                match ox {
                    None => None,
                    Some(x) => Some(Box::new(x.range_traverse(f)?)),
                },
            )),
            Exp::Bin(op, x, y) => Ok(Exp::Bin(
                op,
                Box::new(x.range_traverse(f)?),
                Box::new(y.range_traverse(f)?),
            )),
            Exp::Neg(x) => Ok(Exp::Neg(Box::new(x.range_traverse(f)?))),
            Exp::Map(x, id, r) => Ok(Exp::Map(
                Box::new(x.range_traverse(f)?),
                id,
                Box::new(r.range_traverse(f)?),
            )),
            Exp::Ram(x, i) => Ok(Exp::Ram(
                Box::new(x.range_traverse(f)?),
                Box::new(i.range_traverse(f)?),
            )),
            Exp::Coef(x) => Ok(Exp::Coef(Box::new(x.range_traverse(f)?))),
            Exp::Let(x, t, e) => {
                let e = match e {
                    Some(e) => Some(Box::new((*e).range_traverse(f)?)),
                    None => None,
                };
                Ok(Exp::Let(x, Box::new(t.range_traverse(f)?), e))
            }
            Exp::Log(x, t, e) => {
                let e = match e {
                    Some(e) => Some(Box::new((*e).range_traverse(f)?)),
                    None => None,
                };
                Ok(Exp::Log(x, Box::new(t.range_traverse(f)?), e))
            }
            Exp::Pair(t, e) => Ok(Exp::Pair(
                Box::new(t.range_traverse(f)?),
                Box::new(e.range_traverse(f)?),
            )),
            Exp::Assert(exp) => Ok(Exp::Assert(Box::new(exp.range_traverse(f)?))),
            Exp::Verify(exp) => Ok(Exp::Verify(Box::new(exp.range_traverse(f)?))),
            Exp::App(x, ts) => Ok(Exp::App(x, ts.range_traverse(f)?)),
            Exp::Fun(vars, body) => Ok(Exp::Fun(vars, Box::new(body.range_traverse(f)?))),
            Exp::Record(fields) => {
                let pairs: Vec<_> = fields
                    .into_iter()
                    .map(|(name, exp)| exp.range_traverse(f).map(|new_exp| (name, new_exp)))
                    .collect::<Result<_, _>>()?;
                Ok(Exp::Record(Ctx::from_iter(pairs)))
            }
            Exp::Proj(exp, field) => Ok(Exp::Proj(Box::new(exp.range_traverse(f)?), field)),
            Exp::SetRecord(record, field, value) => Ok(Exp::SetRecord(
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
    /// Borrowing iterator over the spanned elements, in source order.
    pub fn iter(&self) -> std::slice::Iter<'_, Spanned<Exp<N>>> {
        self.0.iter()
    }
    /// Whether the sequence holds no expressions.
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
    /// Number of expressions in the sequence.
    pub fn len(&self) -> usize {
        self.0.len()
    }
    // Parser guarantees that the vector is non-empty
    /// Last expression of the sequence — for a statement block this is the
    /// expression whose value the block returns.
    ///
    /// # Panics
    /// Panics if the sequence is empty. The grammar cannot produce an empty
    /// `Exps`, so an empty one means the AST was built programmatically and
    /// violates that invariant.
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
    /// The direct subexpressions of this expression, in source order.
    pub fn children(&self) -> Vec<&Spanned<Exp<N>>> {
        match self {
            Exp::Lit(_)
            | Exp::Unit
            | Exp::Var(_)
            | Exp::Range(_)
            | Exp::Random(_, _)
            | Exp::Challenge(_, _) => vec![],
            Exp::App(_, args) | Exp::Vec(args) => args.0.iter().collect(),
            Exp::Let(_, val, cont) | Exp::Log(_, val, cont) => {
                std::iter::once(&**val).chain(cont.as_deref()).collect()
            }
            Exp::Map(a, _, b)
            | Exp::Bin(_, a, b)
            | Exp::Pair(a, b)
            | Exp::Ram(a, b)
            | Exp::SetRecord(a, _, b)
            | Exp::Interpolate(Some(a), b) => vec![a, b],
            Exp::Evaluate(a, _, b) => std::iter::once(&**a).chain(b.as_deref()).collect(),
            Exp::Neg(a)
            | Exp::Interpolate(None, a)
            | Exp::Coef(a)
            | Exp::Poly(a)
            | Exp::Mle(a)
            | Exp::Reduce(_, a)
            | Exp::Assert(a)
            | Exp::Verify(a)
            | Exp::Fun(_, a)
            | Exp::Proj(a, _) => vec![a],
            Exp::Record(fields) => fields.iter().map(|(_, e)| e).collect(),
        }
    }

    /// Whether evaluating this expression has no protocol-visible effect:
    /// no transcript logging (`log`), no oracle `challenge`, no `random`
    /// sampling and no `assert`/`verify`. Purity is what lets the graph
    /// builder duplicate, hoist or drop a subexpression freely.
    pub fn is_pure(&self) -> bool {
        match self {
            Exp::Lit(_) | Exp::Unit | Exp::Var(_) | Exp::Range(_) => true,
            Exp::Interpolate(None, e) => e.is_pure(),
            Exp::Interpolate(Some(p), e) => p.is_pure() && e.is_pure(),
            Exp::Coef(p) => p.is_pure(),
            Exp::Poly(p) => p.is_pure(),
            Exp::Mle(p) => p.is_pure(),
            Exp::Reduce(_, p) => p.is_pure(),
            Exp::Vec(v) => v.iter().all(|e| e.node.is_pure()),
            Exp::Bin(_, a, b) => a.is_pure() && b.is_pure(),
            Exp::Neg(a) => a.is_pure(),
            Exp::Evaluate(p, _, ox) => p.is_pure() && ox.as_ref().is_none_or(|x| x.is_pure()),
            Exp::Pair(a, b) => a.is_pure() && b.is_pure(),
            Exp::Map(a, _, b) => a.is_pure() && b.is_pure(),
            Exp::Ram(a, b) => a.is_pure() && b.is_pure(),
            Exp::Let(_, a, b) => a.is_pure() && b.as_ref().is_none_or(|b| b.is_pure()),
            Exp::Log(_, _, _) => false,
            Exp::Challenge(_, _) | Exp::Random(_, _) => false,
            Exp::App(_, args) => args.iter().all(|e| e.node.is_pure()),
            Exp::Assert(_) | Exp::Verify(_) => false,
            Exp::Fun(_, body) => body.is_pure(),
            Exp::Record(fields) => fields.iter().all(|(_, e)| e.node.is_pure()),
            Exp::Proj(exp, _) => exp.is_pure(),
            Exp::SetRecord(record, _, value) => record.is_pure() && value.is_pure(),
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
            Exp::Let(_, val, cont) => {
                val.is_relation_pure() && cont.as_ref().is_none_or(|c| c.is_relation_pure())
            }
            Exp::Map(a, _, b) => a.is_relation_pure() && b.is_relation_pure(),
            Exp::Vec(v) => v.iter().all(|e| e.node.is_relation_pure()),
            Exp::Bin(_, a, b) => a.is_relation_pure() && b.is_relation_pure(),
            Exp::Neg(a) => a.is_relation_pure(),
            Exp::Pair(a, b) => a.is_relation_pure() && b.is_relation_pure(),
            Exp::Ram(a, b) => a.is_relation_pure() && b.is_relation_pure(),
            Exp::Interpolate(None, e) => e.is_relation_pure(),
            Exp::Interpolate(Some(p), e) => p.is_relation_pure() && e.is_relation_pure(),
            Exp::Coef(p) => p.is_relation_pure(),
            Exp::Poly(p) => p.is_relation_pure(),
            Exp::Mle(p) => p.is_relation_pure(),
            Exp::Reduce(_, p) => p.is_relation_pure(),
            Exp::Evaluate(p, _, ox) => {
                p.is_relation_pure() && ox.as_ref().is_none_or(|x| x.is_relation_pure())
            }
            Exp::App(_, args) => args.iter().all(|e| e.node.is_relation_pure()),
            Exp::Fun(_, body) => body.is_relation_pure(),
            Exp::Record(fields) => fields.iter().all(|(_, e)| e.node.is_relation_pure()),
            Exp::Proj(exp, _) => exp.is_relation_pure(),
            Exp::SetRecord(record, _, value) => {
                record.is_relation_pure() && value.is_relation_pure()
            }
            // Leaves: always valid
            Exp::Lit(_) | Exp::Unit | Exp::Var(_) | Exp::Range(_) => true,
        }
    }
}

impl BinOp {
    /// Precedence matching the parser's Pratt table; lower binds looser. Printers use it to
    /// produce text that parses back to the same AST.
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

    /// Whether `lhs` needs parentheses as the left operand of `self` to parse back unchanged.
    pub fn lhs_needs_paren<N>(&self, lhs: &Exp<N>) -> bool {
        match lhs {
            // `-x op y` parses as `(-x) op y` only when `op` binds looser than prefix minus.
            Exp::Neg(_) => self.precedence() >= NEG_PRECEDENCE,
            Exp::Range(_) => self.is_size_operator(),
            Exp::Bin(child, _, _) => {
                child.precedence() < self.precedence()
                    || (child.precedence() == self.precedence() && self.is_right_assoc())
            }
            _ => false,
        }
    }

    /// Whether `rhs` needs parentheses as the right operand of `self` to parse back unchanged.
    pub fn rhs_needs_paren<N>(&self, rhs: &Exp<N>) -> bool {
        match rhs {
            // Prefix minus is allowed in any operand position.
            Exp::Neg(_) => false,
            Exp::Range(_) => self.is_size_operator(),
            Exp::Bin(child, _, _) => {
                child.precedence() < self.precedence()
                    || (child.precedence() == self.precedence() && !self.is_right_assoc())
            }
            _ => false,
        }
    }

    /// Operators that range bounds also accept, so an unparenthesized range operand would
    /// absorb them into its bound.
    fn is_size_operator(&self) -> bool {
        matches!(
            self,
            BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Pow
        )
    }
}

impl<N> Exp<N> {
    /// Whether `self` must be parenthesized as the operand of prefix `-`: a binary operator
    /// that binds looser than `-` would otherwise take `-` into its left operand.
    pub fn needs_paren_under_neg(&self) -> bool {
        matches!(self, Exp::Bin(op, _, _) if op.precedence() < NEG_PRECEDENCE)
    }
}

/// Binding precedence of prefix `-`, on the scale of [`BinOp::precedence`].
const NEG_PRECEDENCE: usize = 4;

/// The operator as written in source, e.g. `+`.
impl fmt::Display for BinOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            BinOp::Add => "+",
            BinOp::Sub => "-",
            BinOp::Mul => "*",
            BinOp::Div => "/",
            BinOp::Pow => "^",
            BinOp::Dot => "dot",
            BinOp::Concat => "++",
            BinOp::Rem => "%",
            BinOp::Equ => "==",
            BinOp::And => "&&",
        })
    }
}

/// Source syntax, parenthesized only where needed to parse back to the same tree. `{}`
/// prints a `let`/`<-`/`;` chain on one line; `{:#}` puts each statement on its own line.
///
/// A precision limits the depth for use in messages: `{:.3}` prints three levels of the tree,
/// writes deeper subexpressions as `…` (variables, literals, and ranges are always printed),
/// and shortens lists to their first [`MAX_LISTED`] elements followed by `…`.
impl<N: fmt::Display> fmt::Display for Exp<N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if f.precision() == Some(0) && !self.is_leaf() {
            return f.write_str("…");
        }
        // Children print one level shallower, in the same one-line/multi-line mode.
        let m = Mode {
            alternate: f.alternate(),
            precision: f.precision(),
        };
        let star = |nonzero: &bool| if *nonzero { "*" } else { "" };
        match self {
            Exp::Lit(p) => write!(f, "{p}"),
            Exp::Unit => f.write_str("()"),
            Exp::Interpolate(None, ev) => write!(f, "interpolate({})", m.sub(ev)),
            Exp::Interpolate(Some(points), evals) => {
                write!(f, "interpolate({}, {})", m.sub(points), m.sub(evals))
            }
            Exp::Poly(p) => write!(f, "poly({})", m.sub(p)),
            Exp::Coef(p) => write!(f, "coef({})", m.sub(p)),
            Exp::Evaluate(p, None, None) => write!(f, "eval({})", m.sub(p)),
            Exp::Evaluate(p, None, Some(x)) => write!(f, "eval({}, {})", m.sub(p), m.sub(x)),
            Exp::Evaluate(p, Some(range), Some(x)) => {
                write!(f, "eval<{range}>({}, {})", m.sub(p), m.sub(x))
            }
            Exp::Evaluate(p, Some(range), None) => write!(f, "eval<{range}>({})", m.sub(p)),
            Exp::Mle(p) => write!(f, "mle({})", m.sub(p)),
            Exp::Vec(ts) => write!(f, "[{}]", m.list(ts)),
            // Dot products are written as a call, not infix.
            Exp::Bin(BinOp::Dot, a, b) => write!(f, "dot({}, {})", m.sub(a), m.sub(b)),
            Exp::Bin(op, a, b) => {
                let parens = |needed| if needed { ("(", ")") } else { ("", "") };
                let (l, r) = parens(op.lhs_needs_paren(&a.node));
                write!(f, "{l}{}{r} {op} ", m.sub(a))?;
                let (l, r) = parens(op.rhs_needs_paren(&b.node));
                write!(f, "{l}{}{r}", m.sub(b))
            }
            Exp::Neg(a) if a.node.needs_paren_under_neg() => write!(f, "-({})", m.sub(a)),
            Exp::Neg(a) => write!(f, "-{}", m.sub(a)),
            Exp::Map(x, id, range) => write!(f, "[{} for {id} in {}]", m.sub(x), m.sub(range)),
            Exp::Reduce(op, a) => write!(f, "reduce({op}, {})", m.sub(a)),
            Exp::Var(x) => write!(f, "{x}"),
            Exp::Challenge(t, nonzero) => write!(f, "challenge<{t}{}>", star(nonzero)),
            Exp::Random(t, nonzero) => write!(f, "random<{t}{}>", star(nonzero)),
            Exp::Pair(t, e) => write!(f, "pair({}, {})", m.sub(t), m.sub(e)),
            Exp::Range(r) => write!(f, "{r}"),
            Exp::App(x, d) => write!(f, "{x}({})", m.list(d)),
            Exp::Ram(x, i) => write!(f, "{}[{}]", m.sub(x), m.sub(i)),
            Exp::Let(Some(x), t, e) => {
                write!(f, "let {x} = {};", m.sub(t))?;
                rest(f, e)
            }
            Exp::Let(None, t, e) => {
                write!(f, "{};", m.sub(t))?;
                rest(f, e)
            }
            Exp::Log(x, t, e) => {
                write!(f, "{x} <- {};", m.sub(t))?;
                rest(f, e)
            }
            Exp::Assert(e) => write!(f, "assert({})", m.sub(e)),
            Exp::Verify(e) => write!(f, "verify({})", m.sub(e)),
            Exp::Fun(vars, body) => {
                f.write_str("fun ")?;
                crate::display::sep(f, vars.iter().map(|v| &v.node), ", ")?;
                write!(f, " => {}", m.sub(body))
            }
            Exp::Record(fields) => {
                f.write_str("{|")?;
                let limit = f.precision().map_or(usize::MAX, |_| MAX_LISTED);
                for (i, (name, e)) in fields.iter().enumerate() {
                    if i > 0 {
                        f.write_str(", ")?;
                    }
                    if i == limit {
                        f.write_str("…")?;
                        break;
                    }
                    write!(f, "{}: {}", name.node, m.sub(e))?;
                }
                f.write_str("|}")
            }
            Exp::Proj(e, field) => write!(f, "{}.{}", m.sub(e), field.node),
            Exp::SetRecord(record, field, value) => {
                write!(f, "{}.set({}, {})", m.sub(record), field.node, m.sub(value))
            }
        }
    }
}

/// How many elements of a list a depth-limited [`Exp`] display shows before `…`.
pub const MAX_LISTED: usize = 4;

impl<N> Exp<N> {
    /// Whether `self` prints in full at any depth.
    fn is_leaf(&self) -> bool {
        matches!(
            self,
            Exp::Lit(_)
                | Exp::Unit
                | Exp::Var(_)
                | Exp::Range(_)
                | Exp::Challenge(..)
                | Exp::Random(..)
        )
    }
}

/// The one-line/multi-line mode and remaining depth an expression is printed in.
#[derive(Clone, Copy)]
struct Mode {
    alternate: bool,
    precision: Option<usize>,
}

impl Mode {
    /// A child of the expression printed in this mode.
    fn sub<N>(self, e: &Spanned<Exp<N>>) -> Sub<'_, N> {
        Sub::new(&e.node, self.alternate, self.precision)
    }

    /// A list of children of the expression printed in this mode.
    fn list<N>(self, exps: &Exps<N>) -> List<'_, N> {
        List {
            exps,
            alternate: self.alternate,
            precision: self.precision,
        }
    }
}

/// A child expression, printed one level shallower than its parent and in its mode.
struct Sub<'a, N> {
    exp: &'a Exp<N>,
    alternate: bool,
    precision: Option<usize>,
}

impl<'a, N> Sub<'a, N> {
    /// `exp` as a child of a parent printed with `alternate` and depth `precision`.
    fn new(exp: &'a Exp<N>, alternate: bool, precision: Option<usize>) -> Self {
        Sub {
            exp,
            alternate,
            precision: precision.map(|p| p.saturating_sub(1)),
        }
    }
}

impl<N: fmt::Display> fmt::Display for Sub<'_, N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match (self.alternate, self.precision) {
            (false, None) => write!(f, "{}", self.exp),
            (true, None) => write!(f, "{:#}", self.exp),
            (false, Some(p)) => write!(f, "{:.*}", p, self.exp),
            (true, Some(p)) => write!(f, "{:#.*}", p, self.exp),
        }
    }
}

/// Comma-separated child expressions; with a depth limit, the first [`MAX_LISTED`] then `…`.
struct List<'a, N> {
    exps: &'a Exps<N>,
    alternate: bool,
    precision: Option<usize>,
}

impl<N: fmt::Display> fmt::Display for List<'_, N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let limit = self.precision.map_or(usize::MAX, |_| MAX_LISTED);
        for (i, e) in self.exps.0.iter().enumerate() {
            if i > 0 {
                f.write_str(", ")?;
            }
            if i == limit {
                return f.write_str("…");
            }
            write!(f, "{}", Sub::new(&e.node, self.alternate, self.precision))?;
        }
        Ok(())
    }
}

/// Prints the statements after the first in a chain.
fn rest<N: fmt::Display>(
    f: &mut fmt::Formatter<'_>,
    e: &Option<Box<Spanned<Exp<N>>>>,
) -> fmt::Result {
    let Some(e) = e else { return Ok(()) };
    let sep = if f.alternate() { "\n" } else { " " };
    // The chain continues at the same depth: its statements are siblings, not children.
    let next = Sub {
        exp: &e.node,
        alternate: f.alternate(),
        precision: f.precision(),
    };
    write!(f, "{sep}{next}")
}

impl<N: fmt::Display> fmt::Display for Exps<N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let list = List {
            exps: self,
            alternate: f.alternate(),
            precision: f.precision(),
        };
        write!(f, "{list}")
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::ast::Size;
    use crate::ast::spanned::Spanned;
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
