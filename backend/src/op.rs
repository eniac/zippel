use crate::{ABase, ATyp, ArkConfig, ArkScalarOps, Value};
use lang::ast::BinOp;
use lang::ast::range::CRange;
use lang::id::Vid;
use lang::typ::Nothing;
use lang::typ::lub::Lub;

use hashconsing::{HConsed, HConsign, HashConsign};
use petgraph::graph::NodeIndex;
use share::Ctx;
use std::fmt;
use std::ops::{
    Add, AddAssign, BitXor, BitXorAssign, Div, DivAssign, Mul, MulAssign, Rem, RemAssign, Sub,
    SubAssign,
};
use std::sync::RwLock;

/// A reference to a node in the graph by `NodeIndex`.
///
/// Issue #83 / Phase B: this is now a thin newtype around `NodeIndex`.
/// Previously a sum type `Node(NodeIndex) | Var(Vid, NodeIndex)`, the
/// `Var` variant existed solely to disambiguate scalar arguments that
/// would otherwise hash-cons identically when all sharing one `Inp` node.
/// Phase B splits each argument into its own `Node::Arg` with a unique
/// `NodeIndex`, making the `Vid` carrier on `Ref` redundant.
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug, Hash)]
pub struct Ref(pub NodeIndex);

/// Typed operations are expressions which are not important
/// enough to be nodes in the graph.
#[derive(PartialEq, Eq, Clone, Debug, Ord, PartialOrd, Hash)]
pub enum Op<C: ArkConfig, R> {
    /// Value
    Value(Value<C>),

    /// Reference to a node or variable
    Ref(R, ATyp),

    /// Binary operations
    Bin(BinOp, HOp<C>, HOp<C>, ATyp),

    /// Random access into a value
    Ram(HOp<C>, HOp<C>),

    /// Vector of values
    Vec(Vec<HOp<C>>),

    /// Record with named fields
    Record(Ctx<String, HOp<C>>),

    /// Random element
    Random(ATyp, bool),

    /// Billinear pairing
    Pair(HOp<C>, HOp<C>, ATyp),

    /// Random oracle challenge
    Challenge(ATyp, bool),

    /// Inverse FFT: evaluations on the FFT grid (n roots of unity, n a power of two)
    /// → univariate polynomial coefficients.
    Ifft(HOp<C>),

    /// Interpolate to univariate polynomial at explicit points: `points` is a
    /// vector of distinct x-coordinates, `evals` is the matching vector of y-values.
    Interpolate(HOp<C>, HOp<C>),

    /// Forward FFT: polynomial coefficients → evaluations on the FFT grid.
    Fft(HOp<C>),

    /// Polynomial
    Poly(HOp<C>),

    /// Multilinear extension
    Mle(HOp<C>),

    /// Project a field from a record value
    Proj(HOp<C>, String, ATyp),

    /// Coefficients of a polynomial
    Coef(HOp<C>),

    /// Evaluate a polynomial. `(None, None)` is FFT-grid evaluation;
    /// `(None, Some(points))` is ordinary scalar/vector evaluation;
    /// `(Some(range), Some(fixed))` keeps `range` free and fixes the rest.
    Evaluate(HOp<C>, Option<CRange>, Option<HOp<C>>),

    /// Placeholder for the current element of an enclosing Map/ReduceMap body.
    /// `usize` is a de Bruijn LEVEL into the runtime loop-parameter stack.
    LoopParam(usize, ATyp),

    /// Persistent map: `[body for x in domain]`. `body` may contain `LoopParam`.
    Map(HOp<C>, HOp<C>),

    /// Explicit-domain reduce-map: `reduce(op, [body for x in domain])`.
    ReduceMap(BinOp, HOp<C>, HOp<C>),

    /// Prover-side assertion: asserts that the operand is true at proving time.
    /// If the assertion fails, the prover aborts with `AssertionFailed`.
    Assert(HOp<C>),
    /// Verifier-side check: verifies that the operand is true at verification time.
    Verify(HOp<C>),

    /// Reduce a vector with a binary operation
    Reduce(BinOp, HOp<C>),
}

/// Graph operation (raw)
pub type GOp<C> = Op<C, Ref>;

/// Hash-consed graph operation
pub type HOp<C> = HConsed<GOp<C>>;

/// Factory type for hash-consing operations
pub type OpFactory<C> = HConsign<GOp<C>>;

/// Trait for types that have an associated Op factory
pub trait HasOpFactory: ArkConfig {
    /// Returns the process-wide hash-consing factory for this configuration's graph
    /// operations.
    ///
    /// Every `GOp<C>` handed out as an `HOp<C>` is interned here, so structural equality
    /// of operations becomes pointer equality. Implementors must return the same lock on
    /// every call — a fresh factory would break sharing across already-built subgraphs.
    fn op_factory() -> &'static RwLock<OpFactory<Self>>;
}

/// Construct a hash-consed operation
pub fn mk<C: HasOpFactory>(op: GOp<C>) -> HOp<C> {
    C::op_factory().write().unwrap().mk(op)
}

impl Ref {
    /// Wraps a `petgraph` `NodeIndex` as a graph reference.
    pub fn new(n: NodeIndex) -> Self {
        Ref(n)
    }

    /// Returns the `NodeIndex` of the graph node this reference resolves to.
    pub fn node(&self) -> NodeIndex {
        self.0
    }
}

impl From<Ref> for NodeIndex {
    fn from(r: Ref) -> Self {
        r.0
    }
}

/// Shape helper: a polynomial-producing op that consumes a
/// coefficient vector returns the corresponding polynomial type
/// under the phase-14 degree convention (`Vec<F, k>` ↔ `Uni(k-1)`).
///
/// Used by `Op::Poly::typ()` and `Op::Ifft::typ()`.
fn poly_typ_from_vec(t: ATyp) -> ATyp {
    match t {
        ATyp::Vec(_, k) if k >= 1 => ATyp::uni(k - 1),
        ATyp::Uni(m) => ATyp::uni(m), // already a poly; identity
        other => other,               // defensive: preserve shape
    }
}

/// Shape helper: an op that consumes a polynomial and produces its
/// coefficient vector. Length = `t.size()` — the canonical slot count
/// (m+1 for Uni, 2^n for Mle, C(n+m, n) for VPoly).
///
/// Used by `Op::Coef::typ()` and `Op::Fft::typ()`.
fn coef_typ_from_poly(t: ATyp) -> ATyp {
    match t {
        ATyp::Uni(m) => ATyp::vec(&ATyp::scalar(), m + 1),
        ATyp::Mle(n) => ATyp::vec(&ATyp::scalar(), 1usize << n),
        v @ ATyp::VPoly(_, _) => ATyp::vec(&ATyp::scalar(), v.physical_len()),
        ATyp::Vec(deref!(elem), n) => ATyp::vec(&elem, n), // already a vec; identity
        other => other,                                    // defensive
    }
}

fn selected_eval_typ<C: ArkConfig>(p: &HOp<C>, range: &CRange) -> ATyp {
    let free_len = range.len();
    match p.typ() {
        ATyp::Uni(d) => ATyp::vpoly(free_len, d),
        ATyp::Mle(_) => ATyp::vpoly(free_len, 1),
        ATyp::VPoly(_, d) => ATyp::vpoly(free_len, d),
        other => other,
    }
}

impl<C: ArkConfig, R> Op<C, R> {
    /// Assign a unique tag to each operation
    pub fn discriminant_order(&self) -> usize {
        match &self {
            Op::Value(_) => 1,
            Op::Ref(_, _) => 2,
            Op::Bin(BinOp::Add, _, _, _) => 3,
            Op::Bin(BinOp::Sub, _, _, _) => 4,
            Op::Bin(BinOp::Mul, _, _, _) => 5,
            Op::Bin(BinOp::Div, _, _, _) => 6,
            Op::Bin(BinOp::Rem, _, _, _) => 7,
            Op::Bin(BinOp::Dot, _, _, _) => 8,
            Op::Bin(BinOp::Concat, _, _, _) => 9,
            Op::Bin(BinOp::Pow, _, _, _) => 12,
            Op::Bin(BinOp::Equ, _, _, _) => 33,
            Op::Bin(BinOp::And, _, _, _) => 34,
            Op::Pair(_, _, _) => 13,
            Op::Ram(_, _) => 14,
            Op::Vec(_) => 15,
            Op::Record(_) => 16,
            Op::Random(_, _) => 17,
            Op::Challenge(_, _) => 18,
            Op::Interpolate(_, _) => 19,
            Op::Fft(_) => 20,
            Op::Assert(_) => 21,
            Op::Verify(_) => 24,
            Op::Poly(_) => 22,
            Op::Evaluate(_, _, _) => 23,
            Op::Map(_, _) => 30,
            Op::ReduceMap(_, _, _) => 31,
            Op::LoopParam(_, _) => 32,
            Op::Coef(_) => 25,
            Op::Mle(_) => 26,
            Op::Reduce(_, _) => 27,
            Op::Proj(_, _, _) => 28,
            Op::Ifft(_) => 29,
        }
    }

    /// Type inference for operations
    pub fn typ(&self) -> ATyp {
        match &self {
            Op::Value(v) => v.typ(),
            Op::Bin(_, _, _, typ) => typ.clone(),
            Op::Pair(_, _, typ) => typ.clone(),
            Op::Ref(_, t) => t.clone(),
            Op::Ram(l, r) => match (l.typ(), r.typ()) {
                (ATyp::Vec(deref!(typ), _), ATyp::Base(_)) => typ,
                (ATyp::Vec(deref!(typ), _), ATyp::Vec(_, m)) => ATyp::vec(&typ, m),
                (ATyp::Record(_), _) => {
                    panic!(
                        "Records do not support indexed access. Use direct field access (record.field) instead."
                    )
                }
                (a, b) => panic!(
                    "UncaughtError: Ram operand must be a vector, not {} [ {} ]",
                    a, b
                ),
            },
            Op::Vec(vs) => {
                let mut typ = vs[0].typ();
                for (i, v) in vs.iter().enumerate().skip(1) {
                    typ = ATyp::lub_equ(&typ, &v.typ(), &Nothing).unwrap_or_else(|_| {
                        panic!(
                            "UncaughtError: Vector operands must be of the same type: \
                             child[0] has type {}, child[{}] has type {} (total {} children)",
                            typ,
                            i,
                            v.typ(),
                            vs.len()
                        )
                    });
                }
                ATyp::vec(&typ, vs.len())
            }
            Op::Record(fields) => {
                let mut atyp_fields = Ctx::new();
                for (name, op) in fields.iter() {
                    let t = op.typ();
                    atyp_fields.insert(name, &t);
                }
                ATyp::Record(atyp_fields)
            }
            Op::Random(t, _) => t.clone(),
            Op::Challenge(t, _) => t.clone(),
            // Op::Ifft(v): v : Vec<F, k> / Uni(k-1) → Uni(k - 1).
            // Under the degree convention, k coefficients = max degree k-1.
            Op::Ifft(op) => poly_typ_from_vec(op.typ()),
            // Op::Fft(p): p : Uni(m) → Vec<F, m + 1>.
            Op::Fft(op) => coef_typ_from_poly(op.typ()),
            Op::Assert(op) | Op::Verify(op) => {
                // Assert/Verify are side-effects; their type is Unit.
                // The operand must be Bool (not Vec<Bool>).
                let t = op.typ();
                match &t {
                    ATyp::Base(ABase::Bool) => {}
                    _ => panic!(
                        "UncaughtError: Assert/Verify operand must be Bool, found {}",
                        t
                    ),
                }
                ATyp::unit()
            }
            // Op::Poly(v): v : Vec<F, k> → Uni(k - 1) under the degree
            // convention (see docs/poly-encoding.md).
            Op::Poly(op) => poly_typ_from_vec(op.typ()),
            Op::Evaluate(p, selector, points) => match (selector, points) {
                // Grid evaluation: polynomial coefficients → evaluations on the FFT grid.
                (None, None) => coef_typ_from_poly(p.typ()),
                // Ordinary evaluation at scalar/vector points.
                (None, Some(x)) => {
                    // Compute the result type of evaluating polynomial `p` at
                    // the k-length vector of points `x`.
                    //
                    // Shapes (k = |x|); a vector point is ONE multivariate point.
                    // (A univariate Uni at a vector is a type error, caught in lang::infer.)
                    //   VPoly(n, _)   with k == n   at Vec(b, n)          -> b           (full)
                    //   VPoly(n, m)   with k <  n   at Vec(b, k)          -> VPoly(n-k, m) (partial)
                    //   Mle(n)        with k == n   at Vec(b, n)          -> b           (full)
                    //   Mle(n)        with k <  n   at Vec(b, k)          -> Mle(n - k)  (partial)
                    let x_typ = x.typ();
                    let k = match &x_typ {
                        ATyp::Vec(_, n) => *n,
                        ATyp::Uni(n) => *n,
                        // Scalar point: univariate evaluation `p(t)`. The
                        // result is the polynomial's coefficient type, which
                        // is always Scalar under the canonical encoding (see
                        // `coef_typ_from_poly`). Returning `x_typ` here was a
                        // bug: a Fin-typed point (e.g. a loop iterator bound
                        // to `0..2`) leaked its index type into the result,
                        // diverging from the inferred `Scalar` and splitting
                        // one `(node, slot)` into distinct monomial variables
                        // across the prover/verifier projections.
                        _ => return ATyp::scalar(),
                    };
                    match p.typ() {
                        ATyp::VPoly(n, _) if k == n => ATyp::scalar(),
                        ATyp::Mle(n) if k == n => ATyp::scalar(),
                        ATyp::VPoly(n, m) if k < n => ATyp::VPoly(n - k, m),
                        ATyp::Mle(n) if k < n => ATyp::Mle(n - k),
                        _ => x_typ,
                    }
                }
                // Selected evaluation: keep a free range and fix the complement.
                (Some(range), Some(_)) => selected_eval_typ(p, range),
                (Some(_), None) => {
                    panic!("Op::Evaluate selected mode requires explicit points/fixed values")
                }
            },
            Op::LoopParam(_, typ) => typ.clone(),
            Op::Map(domain, body) => {
                let (_, n) = domain.typ().into_vec();
                ATyp::vec(&body.typ(), n)
            }
            Op::ReduceMap(op, domain, body) => {
                let (_, n) = domain.typ().into_vec();
                let elem = body.typ();
                let mut acc = elem.clone();
                for _ in 1..n {
                    let next = ATyp::lub_op(*op, &acc, &elem, &Nothing).unwrap_or_else(|_| {
                        panic!("ReduceMap: incompatible body type {:?} for {:?}", elem, op)
                    });
                    if next == acc {
                        break;
                    }
                    acc = next;
                }
                acc
            }
            // Op::Coef(p) flattens a polynomial to its coefficient vector.
            // The resulting Vec length equals the polynomial's coefficient
            // count (see ATyp::size).
            Op::Coef(op) => coef_typ_from_poly(op.typ()),
            // Op::Mle(v): v : Vec<F, 2^n> → Mle(n). The child is an
            // evaluation vector on the boolean hypercube of dimension n.
            Op::Mle(op) => match op.typ() {
                ATyp::Vec(_, k) if k.is_power_of_two() && k >= 1 => {
                    ATyp::mle(k.trailing_zeros() as usize)
                }
                t @ ATyp::Mle(_) => t,
                other => other,
            },
            Op::Reduce(op, v) => {
                let (elem, n) = v.typ().into_vec();
                let mut acc = elem.clone();
                for _ in 1..n {
                    acc = ATyp::lub_op(*op, &acc, &elem, &Nothing)
                        .unwrap_or_else(|_| panic!(
                            "Reduce: accumulator type {:?} is incompatible as left operand for {:?} with element type {:?}",
                            acc, op, elem
                        ));
                }
                acc
            }
            Op::Interpolate(points, evals) => match (points.typ(), evals.typ()) {
                (
                    ATyp::Vec(ATyp::Base(ABase::Scalar), m),
                    ATyp::Vec(ATyp::Base(ABase::Scalar), n),
                )
                | (
                    ATyp::Vec(ATyp::Base(ABase::Fin(_)), m),
                    ATyp::Vec(ATyp::Base(ABase::Scalar), n),
                )
                | (
                    ATyp::Vec(ATyp::Base(ABase::Scalar), m),
                    ATyp::Vec(ATyp::Base(ABase::Fin(_)), n),
                )
                | (
                    ATyp::Vec(ATyp::Base(ABase::Fin(_)), m),
                    ATyp::Vec(ATyp::Base(ABase::Fin(_)), n),
                ) => {
                    if m != n {
                        panic!(
                            "Op::Interpolate: points and evals must have the same length; got {} vs {}",
                            m, n
                        );
                    }
                    ATyp::uni(n)
                }
                (tp, te) => panic!(
                    "Op::Interpolate: both arguments must be Vec(Scalar | Fin, n); got points: {}, evals: {}",
                    tp, te
                ),
            },
            Op::Proj(_, _, typ) => typ.clone(),
        }
    }

    /// Builds the constant index `i`, the literal form used for positions into vectors
    /// and for values of `Fin` range types.
    pub fn index(i: usize) -> Self {
        Op::Value(Value::Index(i))
    }

    /// Lifts an already-evaluated runtime `Value<C>` into a constant operation.
    pub fn value(v: &Value<C>) -> Self {
        Op::Value(v.clone())
    }

    /// Builds the constant vector of indices enumerating `r`, the selector form consumed
    /// by `Op::Ram` when lowering a slice expression.
    pub fn range(r: CRange) -> Op<C, R> {
        Op::Value(Value::VecIndex(r.into_iter().collect()))
    }
    /// Builds the additive-identity constant of type `typ`.
    ///
    /// # Panics
    /// Panics if `typ` has no canonical zero representation, for instance a `Fin` range
    /// that does not contain `0`.
    pub fn zero(typ: &ATyp) -> Op<C, R> {
        Op::Value(Value::zero(typ))
    }

    /// Builds a reference to another graph node, carrying the referent's type explicitly
    /// because it is not recoverable from the reference alone.
    pub fn reference(r: R, typ: ATyp) -> Op<C, R> {
        Op::Ref(r, typ)
    }

    /// Builds a Fiat-Shamir random-oracle challenge of type `typ`, with no nonzero
    /// constraint.
    pub fn challenge(typ: ATyp) -> Op<C, R> {
        Op::Challenge(typ, false)
    }
    /// Builds a locally sampled random element of type `typ`, with no nonzero constraint.
    pub fn random(typ: ATyp) -> Op<C, R> {
        Op::Random(typ, false)
    }
    /// Builds a Fiat-Shamir challenge of type `typ` that is constrained to be nonzero
    /// (needed wherever the challenge is used as a divisor or evaluation denominator).
    pub fn challenge_nz(typ: ATyp) -> Op<C, R> {
        Op::Challenge(typ, true)
    }
    /// Builds a locally sampled random element of type `typ` constrained to be nonzero,
    /// e.g. a blinding factor that must be invertible.
    pub fn random_nz(typ: ATyp) -> Op<C, R> {
        Op::Random(typ, true)
    }
}

impl<C: HasOpFactory> GOp<C> {
    /// Dispatches to the smart constructor for `op`, so that constant folding and the
    /// vector/`Fft` commuting conversions apply uniformly.
    ///
    /// `typ` is the authoritative result type chosen by the lowering code; it is stored
    /// on the resulting `Op::Bin` rather than recomputed downstream.
    ///
    /// # Panics
    /// Panics via `Op::div` if `op` is `BinOp::Div` and `b` is the constant zero.
    pub fn bin(op: BinOp, a: Self, b: Self, typ: ATyp) -> Self {
        match op {
            BinOp::Add => Self::add(a, b, typ),
            BinOp::Sub => Self::sub(a, b, typ),
            BinOp::Mul => Self::mul(a, b, typ),
            BinOp::Div => Self::div(a, b, typ),
            BinOp::Rem => Self::rem(a, b, typ),
            BinOp::Pow => Self::pow(a, b, typ),
            BinOp::Dot => Self::dot(a, b, typ),
            BinOp::Concat => Self::concat(a, b, typ),
            BinOp::Equ => Op::Bin(BinOp::Equ, mk::<C>(a), mk::<C>(b), typ),
            BinOp::And => Op::Bin(BinOp::And, mk::<C>(a), mk::<C>(b), typ),
        }
    }

    /// Builds an evaluation of polynomial `p` at the point(s) `x` (a scalar for
    /// univariate evaluation, a vector for one multivariate point).
    pub fn evaluate(p: Self, x: Self) -> Self {
        Op::Evaluate(mk::<C>(p), None, Some(mk::<C>(x)))
    }

    /// Builds an evaluation of `p` over the whole FFT grid, i.e. the `(None, None)`
    /// mode of `Op::Evaluate` whose result is the coefficient/evaluation vector.
    pub fn evaluate_grid(p: Self) -> Self {
        Op::Evaluate(mk::<C>(p), None, None)
    }

    /// Builds a partial evaluation that leaves the variables in `range` free and binds
    /// the remaining ones to `fixed`, yielding a lower-arity polynomial.
    pub fn evaluate_selected(p: Self, range: CRange, fixed: Self) -> Self {
        Op::Evaluate(mk::<C>(p), Some(range), Some(mk::<C>(fixed)))
    }

    /// Builds a placeholder for the current element of an enclosing `Map`/`ReduceMap`
    /// body. `level` is a de Bruijn *level* into the runtime loop-parameter stack.
    pub fn loop_param(level: usize, typ: ATyp) -> Self {
        Op::LoopParam(level, typ)
    }

    /// Builds the persistent map `[body for x in domain]`; `body` may mention
    /// `Op::LoopParam` to refer to the current element.
    pub fn map(domain: Self, body: Self) -> Self {
        Op::Map(mk::<C>(domain), mk::<C>(body))
    }

    /// Builds `reduce(op, [body for x in domain])`, fusing the map and the fold so the
    /// intermediate vector is never materialized.
    pub fn reduce_map(op: BinOp, domain: Self, body: Self) -> Self {
        Op::ReduceMap(op, mk::<C>(domain), mk::<C>(body))
    }

    /// Random access simplifications
    pub fn ram(v: Self, i: Self) -> Self {
        // Handle nested Ram optimizations (need to inspect HOp children)
        if let (Op::Ram(_, idx_inner), _) = (&v, &i)
            && let Op::Value(Value::VecIndex(vl)) = idx_inner.get()
        {
            match &i {
                Op::Value(Value::VecIndex(vr)) => {
                    return Op::ram(
                        v_inner_clone(&v),
                        Op::Value(Value::VecIndex(
                            vr.iter().map(|j| vl[*j]).collect::<Vec<_>>(),
                        )),
                    );
                }
                Op::Value(Value::Index(j)) => {
                    return Op::ram(v_inner_clone(&v), Op::Value(Value::Index(vl[*j])));
                }
                _ => {}
            }
        }
        match (v, i) {
            // [e0, e1, ..., en][i] = e_i
            (Op::Vec(vs), Op::Value(Value::Index(i))) => vs[i].get().clone(),
            // [e0, e1, ..., en][r] = [e_i for i in r]
            (Op::Vec(vs), Op::Value(Value::VecIndex(vr))) => Op::vec(
                vr.into_iter()
                    .map(|i| vs[i].get().clone())
                    .collect::<Vec<_>>(),
            ),
            // v[v2]
            (Op::Value(a), Op::Value(b)) => Op::Value(Value::ram(a, b)),
            // Default constructor
            (v, i) => Op::Ram(mk::<C>(v), mk::<C>(i)),
        }
    }

    /// Concatenation simplifications
    pub fn concat(v1: Self, v2: Self, typ: ATyp) -> Self {
        match (v1, v2) {
            // [e0, e1, ..., en] + [e_n+1, e_n+2, ..., e_m] = [e0, e1, ..., e_m]
            (Op::Vec(mut vs1), Op::Vec(vs2)) => {
                vs1.extend(vs2);
                Op::Vec(vs1)
            }
            // [e0, e1, ..., en] + e = [e0, e1, ..., e_n, e]
            (Op::Vec(mut vs), v) => {
                let (t, _) = typ.clone().into_vec();
                if v.typ() == t {
                    vs.push(mk::<C>(v));
                    Op::Vec(vs)
                } else {
                    let v_h = mk::<C>(v);
                    Op::Bin(BinOp::Concat, mk::<C>(Op::Vec(vs)), v_h, typ)
                }
            }
            // e + [e0, e1, ..., en] = [e, e0, e1, ..., e_n]
            (v, Op::Vec(mut vs)) => {
                let (t, _) = typ.clone().into_vec();
                if v.typ() == t {
                    vs.insert(0, mk::<C>(v));
                    Op::Vec(vs)
                } else {
                    let v_h = mk::<C>(v);
                    Op::Bin(BinOp::Concat, v_h, mk::<C>(Op::Vec(vs)), typ)
                }
            }
            // v1 + v2 = v1.concat(v2)
            (Op::Value(a), Op::Value(mut b)) => {
                Value::concat(a, &mut b);
                Op::Value(b)
            }
            // Default constructor
            (v1, v2) => Op::Bin(BinOp::Concat, mk::<C>(v1), mk::<C>(v2), typ),
        }
    }

    /// Addition smart constructor.
    ///
    /// Folds constants, distributes elementwise over `Op::Vec` operands, and applies the
    /// commuting conversions `fft a + fft b = fft (a + b)`, the `ifft` dual, and the
    /// same for `interpolate` at identical point vectors. Falls back to `Op::Bin`.
    ///
    /// # Panics
    /// Panics if `typ` is not a vector type while either operand is a vector, since the
    /// elementwise arms destructure `typ` with `into_vec`.
    pub fn add(v1: Self, v2: Self, typ: ATyp) -> Self {
        match (v1, v2) {
            // v + 0 = 0 + v = v
            (Op::Value(a), Op::Value(b)) if a.is_zero() => Op::Value(b),
            (Op::Value(a), Op::Value(b)) if b.is_zero() => Op::Value(a),
            // v1 + v2
            (Op::Value(a), Op::Value(b)) => Op::Value(a + b),
            // e + v = v + e
            (Op::Vec(l), Op::Value(mut v)) | (Op::Value(mut v), Op::Vec(l)) => {
                let (t, _) = typ.clone().into_vec();
                Op::vec(
                    v.into_vec_mut()
                        .iter_mut()
                        .zip(l.iter())
                        .map(|(v, l)| Op::add(Op::Value(v.clone()), l.get().clone(), t.clone()))
                        .collect(),
                )
            }

            // [e0, e1, ... en] + [e0', e1', ... em'] = [e0 + e0', e1 + e1', ... en + em']
            (Op::Vec(l), Op::Vec(r)) => {
                let (t, _) = typ.into_vec();
                Op::vec(
                    l.into_iter()
                        .zip(r)
                        .map(|(l, r)| Op::add(l.get().clone(), r.get().clone(), t.clone()))
                        .collect(),
                )
            }
            // Commuting conversion (fft a + fft b) = fft (a + b)
            (Op::Fft(l), Op::Fft(r)) => {
                Op::Fft(mk::<C>(Op::add(l.get().clone(), r.get().clone(), typ)))
            }
            // Commuting conversion (ifft a + ifft b) = ifft (a + b)
            (Op::Ifft(l), Op::Ifft(r)) => {
                Op::Ifft(mk::<C>(Op::add(l.get().clone(), r.get().clone(), typ)))
            }
            // Commuting conversion (interpolate p a + interpolate p b) = interpolate p (a + b)
            (Op::Interpolate(lp, l), Op::Interpolate(rp, r)) if lp == rp => {
                Op::Interpolate(lp, mk::<C>(Op::add(l.get().clone(), r.get().clone(), typ)))
            }
            (v1, v2) => Op::Bin(BinOp::Add, mk::<C>(v1), mk::<C>(v2), typ),
        }
    }

    /// Subtraction smart constructor.
    ///
    /// Mirrors `Op::add`: constant folding, elementwise distribution over `Op::Vec`, and
    /// the `fft`/`ifft`/`interpolate` commuting conversions.
    ///
    /// # Panics
    /// Panics if `typ` is not a vector type while either operand is a vector.
    pub fn sub(v1: Self, v2: Self, typ: ATyp) -> Self {
        match (v1, v2) {
            // v - 0
            (Op::Value(a), Op::Value(b)) if b.is_zero() => Op::Value(a),
            // v1 - v2
            (Op::Value(a), Op::Value(b)) => Op::Value(a - b),
            // e - v = v - e
            (Op::Vec(l), Op::Value(mut v)) | (Op::Value(mut v), Op::Vec(l)) => {
                let (t, _) = typ.clone().into_vec();
                Op::vec(
                    v.into_vec_mut()
                        .iter_mut()
                        .zip(l.iter())
                        .map(|(v, l)| Op::sub(Op::Value(v.clone()), l.get().clone(), t.clone()))
                        .collect(),
                )
            }

            // [e0, e1, ... en] - [e0', e1', ... em'] = [e0 - e0', e1 - e1', ... en - em']
            (Op::Vec(l), Op::Vec(r)) => {
                let (t, _) = typ.into_vec();
                Op::vec(
                    l.into_iter()
                        .zip(r)
                        .map(|(l, r)| Op::sub(l.get().clone(), r.get().clone(), t.clone()))
                        .collect(),
                )
            }
            // Commuting conversion (fft a - fft b) = fft (a - b)
            (Op::Fft(l), Op::Fft(r)) => {
                Op::Fft(mk::<C>(Op::sub(l.get().clone(), r.get().clone(), typ)))
            }
            // Commuting conversion (ifft a - ifft b) = ifft (a - b)
            (Op::Ifft(l), Op::Ifft(r)) => {
                Op::Ifft(mk::<C>(Op::sub(l.get().clone(), r.get().clone(), typ)))
            }
            // Commuting conversion (interpolate p a - interpolate p b) = interpolate p (a - b)
            (Op::Interpolate(lp, l), Op::Interpolate(rp, r)) if lp == rp => {
                Op::Interpolate(lp, mk::<C>(Op::sub(l.get().clone(), r.get().clone(), typ)))
            }
            (v1, v2) => Op::Bin(BinOp::Sub, mk::<C>(v1), mk::<C>(v2), typ),
        }
    }

    /// Multiplication smart constructor.
    ///
    /// Folds `0 * v`, `1 * v`, and constant pairs, and distributes over `Op::Vec` either
    /// elementwise (vector constant) or by scalar broadcast.
    ///
    /// # Panics
    /// Panics if `typ` is not a vector type while either operand is a vector.
    pub fn mul(v1: Self, v2: Self, typ: ATyp) -> Self {
        match (v1, v2) {
            // 0 * v = v * 0 = 0
            (Op::Value(a), _) | (_, Op::Value(a)) if a.is_zero() => Op::zero(&typ),
            // 1 * v = v * 1 = v
            (Op::Value(a), b) | (b, Op::Value(a)) if a.is_one() => b,
            // v1 * v2 = v1.mul(v2)
            (Op::Value(a), Op::Value(b)) => Op::Value(a * b),
            // [e0, ..., en] * v = [e0 * v0, e1 * v1, ..., en * vn]
            (Op::Vec(l), Op::Value(mut v)) | (Op::Value(mut v), Op::Vec(l)) => {
                let (t, _) = typ.clone().into_vec();
                if v.is_vec() {
                    Op::vec(
                        v.into_vec_mut()
                            .iter_mut()
                            .zip(l.iter())
                            .map(|(v, l)| Op::mul(Op::Value(v.clone()), l.get().clone(), t.clone()))
                            .collect(),
                    )
                } else {
                    Op::vec(
                        l.into_iter()
                            .map(|l| Op::mul(Op::Value(v.clone()), l.get().clone(), t.clone()))
                            .collect(),
                    )
                }
            }
            // [e0, e1, ... en] * [e0', e1', ... en'] = [e0 * e0', e1 * e1', ... en * en']
            (Op::Vec(l), Op::Vec(r)) => {
                let (t, _) = typ.into_vec();
                Op::vec(
                    l.into_iter()
                        .zip(r)
                        .map(|(l, r)| Op::mul(l.get().clone(), r.get().clone(), t.clone()))
                        .collect(),
                )
            }
            // Default constructor
            (v1, v2) => Op::Bin(BinOp::Mul, mk::<C>(v1), mk::<C>(v2), typ),
        }
    }

    /// Division smart constructor.
    ///
    /// Folds `0 / v`, `v / 1`, and constant pairs, and distributes over `Op::Vec`.
    ///
    /// # Panics
    /// Panics on a syntactically zero divisor, and if `typ` is not a vector type while
    /// either operand is a vector.
    pub fn div(v1: Self, v2: Self, typ: ATyp) -> Self {
        match (v1, v2) {
            (_, Op::Value(b)) if b.is_zero() => panic!("UncaughtError: Division by zero"),
            (Op::Value(a), _) if a.is_zero() => Op::zero(&typ),
            (a, Op::Value(b)) if b.is_one() => a,
            // v1 / v2
            (Op::Value(a), Op::Value(b)) => Op::Value(a / b),
            // [e0, ..., en] / v = [e0 / v0, e1 / v1, ..., en / vn]
            (Op::Vec(l), Op::Value(mut v)) | (Op::Value(mut v), Op::Vec(l)) => {
                let (t, _) = typ.clone().into_vec();
                if v.is_vec() {
                    Op::vec(
                        v.into_vec_mut()
                            .iter_mut()
                            .zip(l.iter())
                            .map(|(v, l)| Op::div(Op::Value(v.clone()), l.get().clone(), t.clone()))
                            .collect(),
                    )
                } else {
                    Op::vec(
                        l.into_iter()
                            .map(|l| Op::div(Op::Value(v.clone()), l.get().clone(), t.clone()))
                            .collect(),
                    )
                }
            }
            // [e0, e1, ... en] / [e0', e1', ... en'] = [e0 / e0', e1 / e1', ... en / en']
            (Op::Vec(l), Op::Vec(r)) => {
                let (t, _) = typ.into_vec();
                Op::vec(
                    l.into_iter()
                        .zip(r)
                        .map(|(l, r)| Op::div(l.get().clone(), r.get().clone(), t.clone()))
                        .collect(),
                )
            }
            // Default constructor
            (v1, v2) => Op::Bin(BinOp::Div, mk::<C>(v1), mk::<C>(v2), typ),
        }
    }

    /// Bilinear pairing smart constructor: folds two group constants into their pairing
    /// output, otherwise builds `Op::Pair` carrying the target-group type `typ`.
    pub fn pair(v1: Self, v2: Self, typ: ATyp) -> Self {
        match (v1, v2) {
            (Op::Value(a), Op::Value(mut b)) => {
                a.value_pair(&mut b);
                Op::Value(b)
            }
            (v1, v2) => Op::Pair(mk::<C>(v1), mk::<C>(v2), typ),
        }
    }

    /// Remainder smart constructor: folds constant pairs and distributes over `Op::Vec`.
    ///
    /// # Panics
    /// Panics if `typ` is not a vector type while either operand is a vector.
    pub fn rem(v1: Self, v2: Self, typ: ATyp) -> Self {
        match (v1, v2) {
            // v1 % v2
            (Op::Value(a), Op::Value(b)) => Op::Value(a % b),
            // [e0, ..., en] % v = [e0 % v0, e1 % v1, ..., en % vn]
            (Op::Vec(l), Op::Value(mut v)) | (Op::Value(mut v), Op::Vec(l)) => {
                let (t, _) = typ.clone().into_vec();
                if v.is_vec() {
                    Op::vec(
                        v.into_vec_mut()
                            .iter_mut()
                            .zip(l.iter())
                            .map(|(v, l)| Op::rem(Op::Value(v.clone()), l.get().clone(), t.clone()))
                            .collect(),
                    )
                } else {
                    Op::vec(
                        l.into_iter()
                            .map(|l| Op::rem(Op::Value(v.clone()), l.get().clone(), t.clone()))
                            .collect(),
                    )
                }
            }
            // [e0, e1, ... en] % [e0', e1', ... en'] = [e0 % e0', e1 % e1', ... en % en']
            (Op::Vec(l), Op::Vec(r)) => {
                let (t, _) = typ.into_vec();
                Op::vec(
                    l.into_iter()
                        .zip(r)
                        .map(|(l, r)| Op::rem(l.get().clone(), r.get().clone(), t.clone()))
                        .collect(),
                )
            }
            // Default constructor
            (v1, v2) => Op::Bin(BinOp::Rem, mk::<C>(v1), mk::<C>(v2), typ),
        }
    }

    /// Builds the multiplicative-identity constant of type `typ`.
    ///
    /// For `Uni(n)` this is the constant-one polynomial encoded as its coefficient
    /// vector; for vectors it is the pointwise one.
    ///
    /// # Panics
    /// Panics if `typ` has no representable one, e.g. a `Fin` range excluding `1`, a
    /// group or record type, or `Uni(0)`.
    pub fn one(typ: &ATyp) -> GOp<C> {
        match typ {
            ATyp::Base(ABase::Fin(r)) if r.contains(1) => Op::Value(Value::Index(1)),
            ATyp::Base(ABase::Scalar) => Op::Value(Value::Scalar(C::FOps::one())),
            ATyp::Vec(ATyp::Base(ABase::Scalar), n) => {
                Op::Value(Value::VecScalar(vec![C::FOps::one(); *n]))
            }
            ATyp::Vec(ATyp::Base(ABase::Fin(r)), n) if r.contains(1) => {
                Op::Value(Value::VecIndex(vec![1; *n]))
            }
            ATyp::Vec(deref!(typ), n) => {
                let mut vs = vec![];
                for _ in 0..*n {
                    vs.push(Op::one(typ));
                }
                Op::vec(vs)
            }
            ATyp::Uni(n) if *n > 0 => {
                let mut vs = vec![0; *n];
                vs[0] = 1;
                Op::Value(Value::VecIndex(vs))
            }
            _ => unreachable!("UncaughtError: Op::one() not implemented for type {}", typ),
        }
    }

    /// Exponentiation smart constructor: folds `v ^ 0` to `Op::one` and `v ^ 1` to `v`.
    ///
    /// # Panics
    /// Panics through `Op::one` when the exponent is the literal `0` and `typ` has no
    /// representable one.
    pub fn pow(v1: Self, v2: Self, typ: ATyp) -> Self {
        match v2 {
            Op::Value(Value::Index(0)) => Op::one(&typ),
            Op::Value(Value::Index(1)) => v1,
            v2 => Op::Bin(BinOp::Pow, mk::<C>(v1), mk::<C>(v2), typ),
        }
    }

    /// Inner-product smart constructor: folds two constant vectors into their dot
    /// product, otherwise builds `Op::Bin(BinOp::Dot, ..)`.
    pub fn dot(v1: Self, v2: Self, typ: ATyp) -> Self {
        match (v1, v2) {
            // v1 . v2 = v1.dot(v2)
            (Op::Value(a), Op::Value(b)) => {
                let mut b = b;
                Value::value_dot(&a, &mut b);
                Op::Value(b)
            }
            // Default case, constructor
            (v1, v2) => Op::Bin(BinOp::Dot, mk::<C>(v1), mk::<C>(v2), typ),
        }
    }

    /// Builds `Op::Poly`, reading `op` as the coefficient vector of a univariate
    /// polynomial (`Vec<F, k>` becomes `Uni(k - 1)`).
    pub fn poly(op: Self) -> GOp<C> {
        Op::Poly(mk::<C>(op))
    }

    /// Builds `Op::Coef`, flattening a polynomial into its canonical coefficient vector.
    pub fn coef(op: Self) -> GOp<C> {
        Op::Coef(mk::<C>(op))
    }

    /// Builds `Op::Mle`, reading `op` as the evaluation table of a multilinear extension
    /// over the boolean hypercube.
    pub fn mle(op: Self) -> GOp<C> {
        Op::Mle(mk::<C>(op))
    }

    /// Builds a projection of field `field` out of a record-valued operation. `typ` is
    /// the field's type, stored because it is chosen by the lowering code.
    pub fn proj(record_op: Self, field: String, typ: ATyp) -> GOp<C> {
        Op::Proj(mk::<C>(record_op), field, typ)
    }

    /// Builds a fold of a vector-valued operation with the binary operation `op`.
    pub fn reduce(op: BinOp, v: Self) -> GOp<C> {
        Op::Reduce(op, mk::<C>(v))
    }
    /// Build an `Op::Interpolate(points, evals)` (binary form). Caller is responsible
    /// for using `Op::ifft(evals)` for the FFT-grid (unary) form.
    pub fn interpolate(points: Self, evals: Self) -> GOp<C> {
        Op::Interpolate(mk::<C>(points), mk::<C>(evals))
    }

    /// Inverse FFT smart constructor. Sound rewrite: `ifft(fft(p)) = p`.
    pub fn ifft(op: Self) -> GOp<C> {
        match op {
            Op::Fft(inner) => inner.get().clone(),
            op => Op::Ifft(mk::<C>(op)),
        }
    }

    /// Forward FFT smart constructor. Sound rewrite: `fft(ifft(v)) = v`.
    /// `fft(interpolate(points, evs))` is NOT identity for arbitrary points and is left as-is.
    pub fn fft(op: Self) -> GOp<C> {
        match op {
            Op::Ifft(inner) => inner.get().clone(),
            op => Op::Fft(mk::<C>(op)),
        }
    }

    /// Right-pads the vector-valued operation `v` with zeroes until it has length `n`,
    /// returning `v` unchanged when it is already at least that long. Used to align
    /// operands before an FFT-sized transform.
    ///
    /// # Panics
    /// Panics if `v` does not have a vector type.
    pub fn pad_zeroes(v: GOp<C>, n: usize) -> GOp<C> {
        let typ = v.typ();
        let (t, m) = typ.into_vec();
        if m < n {
            Op::concat(v, Op::vec(vec![Op::zero(&t); n - m]), ATyp::vec(&t, n))
        } else {
            v
        }
    }

    /// Builds an `Op::Vec` by hash-consing each element operation.
    pub fn vec(vs: Vec<GOp<C>>) -> GOp<C> {
        Op::Vec(vs.into_iter().map(mk::<C>).collect())
    }

    /// Builds a prover-side assertion; the operand must evaluate to `Bool` at proving
    /// time or the prover aborts.
    pub fn assert(op: GOp<C>) -> GOp<C> {
        Op::Assert(mk::<C>(op))
    }
    /// Builds a verifier-side check; its result feeds the `Vec<Value<C>>` returned by
    /// `run_verifier`.
    pub fn verify(op: GOp<C>) -> GOp<C> {
        Op::Verify(mk::<C>(op))
    }
}

/// Helper to extract the first child from an Op::Ram variant (cloned from HOp)
fn v_inner_clone<C: ArkConfig>(op: &GOp<C>) -> GOp<C> {
    match op {
        Op::Ram(v, _) => v.get().clone(),
        _ => unreachable!(),
    }
}

impl<C: ArkConfig> GOp<C> {
    /// Builds an anonymous reference to graph node `n` of type `typ`, used where the
    /// referent has no source-level variable name.
    pub fn underscore(n: NodeIndex, typ: ATyp) -> Self {
        Op::Ref(Ref(n), typ)
    }

    /// Construct a `GOp::Ref` for a variable. After Phase B, `var` and
    /// `underscore` are operationally identical: both produce
    /// `Op::Ref(Ref(n), typ)`. The `Vid` parameter is retained as a
    /// callsite-documentation aid but no longer carried on `Ref`.
    pub fn var(_v: &Vid, n: NodeIndex, typ: ATyp) -> Self {
        Op::Ref(Ref(n), typ)
    }

    /// Returns whether this operation is a bare reference to another graph node, i.e.
    /// whether it contributes no computation of its own.
    pub fn is_ref(&self) -> bool {
        matches!(self, Op::Ref(_, _))
    }

    /// Collects every graph node this operation depends on, in traversal order and with
    /// duplicates retained.
    ///
    /// `Op::LoopParam` contributes nothing: it names a loop element, not a node.
    pub fn references(&self) -> Vec<Ref> {
        match self {
            Op::Ref(n, _) => vec![*n],
            Op::Bin(_, a, b, _) | Op::Pair(a, b, _) | Op::Ram(a, b) => {
                a.references().into_iter().chain(b.references()).collect()
            }
            Op::Evaluate(p, _, points) => match points {
                None => p.references(),
                Some(x) => p.references().into_iter().chain(x.references()).collect(),
            },
            Op::LoopParam(_, _) => vec![],
            Op::Map(d, b) | Op::ReduceMap(_, d, b) => {
                d.references().into_iter().chain(b.references()).collect()
            }
            Op::Vec(vs) => vs.iter().flat_map(|v| v.references()).collect(),
            Op::Record(fields) => fields.iter().flat_map(|(_, v)| v.references()).collect(),
            Op::Interpolate(points, v) => points
                .references()
                .into_iter()
                .chain(v.references())
                .collect(),
            Op::Assert(op) | Op::Verify(op) => op.references(),
            Op::Poly(v)
            | Op::Mle(v)
            | Op::Coef(v)
            | Op::Reduce(_, v)
            | Op::Ifft(v)
            | Op::Fft(v) => v.references(),
            Op::Proj(v, _, _) => v.references(),
            Op::Value(_) | Op::Random(_, _) | Op::Challenge(_, _) => vec![],
        }
    }
}

impl<C: HasOpFactory> GOp<C> {
    /// Rebuilds this operation with every referenced `NodeIndex` rewritten by `f`,
    /// re-hash-consing each child. Used when a subgraph is copied into another `Dag`
    /// and node numbering shifts.
    pub fn map_node_indices<F: Fn(NodeIndex) -> NodeIndex>(&self, f: &F) -> GOp<C> {
        match self {
            Op::Ref(r, typ) => Op::Ref(Ref(f(r.0)), typ.clone()),
            Op::Bin(op, a, b, typ) => Op::Bin(
                *op,
                mk::<C>(a.map_node_indices(f)),
                mk::<C>(b.map_node_indices(f)),
                typ.clone(),
            ),
            Op::Ram(a, b) => Op::Ram(
                mk::<C>(a.map_node_indices(f)),
                mk::<C>(b.map_node_indices(f)),
            ),
            Op::Vec(vs) => Op::Vec(vs.iter().map(|v| mk::<C>(v.map_node_indices(f))).collect()),
            Op::Record(fields) => Op::Record(
                fields
                    .iter()
                    .map(|(k, v)| (k.clone(), mk::<C>(v.map_node_indices(f))))
                    .collect(),
            ),
            Op::Pair(a, b, typ) => Op::Pair(
                mk::<C>(a.map_node_indices(f)),
                mk::<C>(b.map_node_indices(f)),
                typ.clone(),
            ),
            Op::Evaluate(a, range, points) => Op::Evaluate(
                mk::<C>(a.map_node_indices(f)),
                range.clone(),
                points.as_ref().map(|b| mk::<C>(b.map_node_indices(f))),
            ),
            Op::LoopParam(i, t) => Op::LoopParam(*i, t.clone()),
            Op::Map(d, b) => Op::Map(
                mk::<C>(d.map_node_indices(f)),
                mk::<C>(b.map_node_indices(f)),
            ),
            Op::ReduceMap(op, d, b) => Op::ReduceMap(
                *op,
                mk::<C>(d.map_node_indices(f)),
                mk::<C>(b.map_node_indices(f)),
            ),
            Op::Poly(op) => Op::Poly(mk::<C>(op.map_node_indices(f))),
            Op::Coef(op) => Op::Coef(mk::<C>(op.map_node_indices(f))),
            Op::Assert(op) => Op::Assert(mk::<C>(op.map_node_indices(f))),
            Op::Verify(op) => Op::Verify(mk::<C>(op.map_node_indices(f))),
            Op::Interpolate(points, evals) => Op::Interpolate(
                mk::<C>(points.map_node_indices(f)),
                mk::<C>(evals.map_node_indices(f)),
            ),
            Op::Ifft(op) => Op::Ifft(mk::<C>(op.map_node_indices(f))),
            Op::Fft(op) => Op::Fft(mk::<C>(op.map_node_indices(f))),
            Op::Mle(op) => Op::Mle(mk::<C>(op.map_node_indices(f))),
            Op::Proj(op, field, typ) => {
                Op::Proj(mk::<C>(op.map_node_indices(f)), field.clone(), typ.clone())
            }
            Op::Reduce(op, v) => Op::Reduce(*op, mk::<C>(v.map_node_indices(f))),
            _ => self.clone(),
        }
    }

    /// Rebuilds this operation with every `Ref` rewritten by `f`, re-hash-consing each
    /// child. The `Ref`-level counterpart of `map_node_indices`.
    pub fn map_refs<F: Fn(Ref) -> Ref>(&self, f: &F) -> GOp<C> {
        match self {
            Op::Ref(r, typ) => Op::Ref(f(*r), typ.clone()),
            Op::Bin(op, a, b, typ) => Op::Bin(
                *op,
                mk::<C>(a.map_refs(f)),
                mk::<C>(b.map_refs(f)),
                typ.clone(),
            ),
            Op::Ram(a, b) => Op::Ram(mk::<C>(a.map_refs(f)), mk::<C>(b.map_refs(f))),
            Op::Vec(vs) => Op::Vec(vs.iter().map(|v| mk::<C>(v.map_refs(f))).collect()),
            Op::Record(fields) => Op::Record(
                fields
                    .iter()
                    .map(|(k, v)| (k.clone(), mk::<C>(v.map_refs(f))))
                    .collect(),
            ),
            Op::Pair(a, b, typ) => {
                Op::Pair(mk::<C>(a.map_refs(f)), mk::<C>(b.map_refs(f)), typ.clone())
            }
            Op::Assert(op) => Op::Assert(mk::<C>(op.map_refs(f))),
            Op::Verify(op) => Op::Verify(mk::<C>(op.map_refs(f))),
            Op::Interpolate(points, evals) => {
                Op::Interpolate(mk::<C>(points.map_refs(f)), mk::<C>(evals.map_refs(f)))
            }
            Op::Ifft(op) => Op::Ifft(mk::<C>(op.map_refs(f))),
            Op::Fft(op) => Op::Fft(mk::<C>(op.map_refs(f))),
            Op::Value(_) | Op::Random(_, _) | Op::Challenge(_, _) => self.clone(),
            Op::Poly(op) => Op::Poly(mk::<C>(op.map_refs(f))),
            Op::Coef(op) => Op::Coef(mk::<C>(op.map_refs(f))),
            Op::Evaluate(p, range, x) => Op::Evaluate(
                mk::<C>(p.map_refs(f)),
                range.clone(),
                x.as_ref().map(|x| mk::<C>(x.map_refs(f))),
            ),
            Op::LoopParam(i, t) => Op::LoopParam(*i, t.clone()),
            Op::Map(d, b) => Op::Map(mk::<C>(d.map_refs(f)), mk::<C>(b.map_refs(f))),
            Op::ReduceMap(op, d, b) => {
                Op::ReduceMap(*op, mk::<C>(d.map_refs(f)), mk::<C>(b.map_refs(f)))
            }
            Op::Mle(op) => Op::Mle(mk::<C>(op.map_refs(f))),
            Op::Proj(op, field, typ) => {
                Op::Proj(mk::<C>(op.map_refs(f)), field.clone(), typ.clone())
            }
            Op::Reduce(op, v) => Op::Reduce(*op, mk::<C>(v.map_refs(f))),
        }
    }

    /// Inline an operation, except for the nodes specified
    /// which remain as node identifiers.
    pub fn inline<F: Fn(&Ref, &GOp<C>) -> bool>(
        &self,
        vars: &Ctx<Ref, GOp<C>>,
        except: &F,
    ) -> GOp<C> {
        match self {
            Op::Ref(r, _) => {
                if let Some(next) = vars.get(r) {
                    if except(r, next) {
                        return self.clone();
                    }
                    next.inline(vars, except)
                } else {
                    self.clone()
                }
            }
            Op::Bin(op, a, b, typ) => {
                let oa = a.inline(vars, except);
                let ob = b.inline(vars, except);
                Op::bin(*op, oa, ob, typ.clone())
            }
            Op::Ram(a, b) => {
                let oa = a.inline(vars, except);
                let ob = b.inline(vars, except);
                Op::Ram(mk::<C>(oa), mk::<C>(ob))
            }
            Op::Vec(vs) => Op::Vec(
                vs.iter()
                    .map(|v| mk::<C>(v.inline(vars, except)))
                    .collect::<Vec<_>>(),
            ),
            Op::Record(fields) => Op::Record(
                fields
                    .iter()
                    .map(|(k, v)| (k.clone(), mk::<C>(v.inline(vars, except))))
                    .collect(),
            ),
            Op::Assert(op) => Op::Assert(mk::<C>(op.inline(vars, except))),
            Op::Verify(op) => Op::Verify(mk::<C>(op.inline(vars, except))),
            Op::Interpolate(points, evals) => Op::Interpolate(
                mk::<C>(points.inline(vars, except)),
                mk::<C>(evals.inline(vars, except)),
            ),
            Op::Ifft(v) => Op::Ifft(mk::<C>(v.inline(vars, except))),
            Op::Fft(v) => Op::Fft(mk::<C>(v.inline(vars, except))),
            Op::Proj(v, field, typ) => {
                Op::Proj(mk::<C>(v.inline(vars, except)), field.clone(), typ.clone())
            }
            Op::Reduce(op, v) => Op::Reduce(*op, mk::<C>(v.inline(vars, except))),
            Op::Evaluate(p, range, points) => Op::Evaluate(
                mk::<C>(p.inline(vars, except)),
                range.clone(),
                points.as_ref().map(|x| mk::<C>(x.inline(vars, except))),
            ),
            Op::LoopParam(i, t) => Op::LoopParam(*i, t.clone()),
            Op::Map(d, b) => Op::Map(
                mk::<C>(d.inline(vars, except)),
                mk::<C>(b.inline(vars, except)),
            ),
            Op::ReduceMap(op, d, b) => Op::ReduceMap(
                *op,
                mk::<C>(d.inline(vars, except)),
                mk::<C>(b.inline(vars, except)),
            ),
            _ => self.clone(),
        }
    }
}

/// `n<index>`
impl fmt::Display for Ref {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "n{}", self.0.index())
    }
}

impl From<NodeIndex> for Ref {
    fn from(n: NodeIndex) -> Self {
        Ref(n)
    }
}

impl<C: HasOpFactory> AddAssign<GOp<C>> for GOp<C> {
    fn add_assign(&mut self, other: GOp<C>) {
        *self = Op::add(self.clone(), other, self.typ());
    }
}

impl<C: HasOpFactory> SubAssign<GOp<C>> for GOp<C> {
    fn sub_assign(&mut self, other: GOp<C>) {
        *self = Op::sub(self.clone(), other, self.typ());
    }
}

impl<C: HasOpFactory> MulAssign<GOp<C>> for GOp<C> {
    fn mul_assign(&mut self, other: GOp<C>) {
        *self = Op::mul(self.clone(), other, self.typ());
    }
}

impl<C: HasOpFactory> DivAssign<GOp<C>> for GOp<C> {
    fn div_assign(&mut self, other: GOp<C>) {
        *self = Op::div(self.clone(), other, self.typ());
    }
}

impl<C: HasOpFactory> RemAssign<GOp<C>> for GOp<C> {
    fn rem_assign(&mut self, other: GOp<C>) {
        *self = Op::rem(self.clone(), other, self.typ());
    }
}

impl<C: HasOpFactory> BitXorAssign<GOp<C>> for GOp<C> {
    fn bitxor_assign(&mut self, other: GOp<C>) {
        *self = Op::pow(self.clone(), other, self.typ());
    }
}

impl<C: HasOpFactory> Add for GOp<C> {
    type Output = GOp<C>;

    fn add(self, other: GOp<C>) -> GOp<C> {
        let typ = self.typ().clone();
        Op::add(self, other, typ)
    }
}

impl<C: HasOpFactory> Sub for GOp<C> {
    type Output = GOp<C>;

    fn sub(self, other: GOp<C>) -> GOp<C> {
        let typ = self.typ().clone();
        Op::sub(self, other, typ)
    }
}

impl<C: HasOpFactory> Mul for GOp<C> {
    type Output = GOp<C>;

    fn mul(self, other: GOp<C>) -> GOp<C> {
        let typ = self.typ().clone();
        Op::mul(self, other, typ)
    }
}

impl<C: HasOpFactory> Div for GOp<C> {
    type Output = GOp<C>;

    fn div(self, other: GOp<C>) -> GOp<C> {
        let typ = self.typ().clone();
        Op::div(self, other, typ)
    }
}

impl<C: HasOpFactory> Rem for GOp<C> {
    type Output = GOp<C>;

    fn rem(self, other: GOp<C>) -> GOp<C> {
        let typ = self.typ().clone();
        Op::rem(self, other, typ)
    }
}

impl<C: HasOpFactory> BitXor for GOp<C> {
    type Output = GOp<C>;

    fn bitxor(self, other: GOp<C>) -> GOp<C> {
        let typ = self.typ().clone();
        Op::pow(self, other, typ)
    }
}

/// S-expression-like IR syntax, e.g. `(eval n3, n4)`; binary operators are infix.
impl<C: ArkConfig, R: fmt::Display> fmt::Display for Op<C, R> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Op::Value(v) => write!(f, "{v}"),
            // Dot products are written as a call, as in the source language.
            Op::Bin(BinOp::Dot, a, b, _) => write!(f, "dot({}, {})", a.get(), b.get()),
            Op::Bin(op, a, b, _) => {
                let (a, b) = (a.get(), b.get());
                let looser = |child: &Op<C, Ref>| matches!(child, Op::Bin(child_op, _, _, _) if child_op.precedence() < op.precedence());
                if looser(a) {
                    write!(f, "({a}) {op} {b}")
                } else if looser(b) {
                    write!(f, "{a} {op} ({b})")
                } else {
                    write!(f, "{a} {op} {b}")
                }
            }
            Op::Fft(v) => write!(f, "(fft {})", v.get()),
            Op::Ifft(v) => write!(f, "(ifft {})", v.get()),
            Op::Poly(v) => write!(f, "(poly {})", v.get()),
            Op::Coef(v) => write!(f, "(coef {})", v.get()),
            Op::Evaluate(p, None, None) => write!(f, "(eval {})", p.get()),
            Op::Evaluate(p, None, Some(x)) => write!(f, "(eval {}, {})", p.get(), x.get()),
            Op::Evaluate(p, Some(range), Some(fixed)) => {
                write!(f, "(eval<{range}> {}, {})", p.get(), fixed.get())
            }
            Op::Evaluate(p, Some(range), None) => write!(f, "(eval<{range}> {})", p.get()),
            Op::LoopParam(i, t) => write!(f, "loop_param#{i}: {t}"),
            Op::Map(d, b) => write!(f, "(map {} {})", d.get(), b.get()),
            Op::ReduceMap(op, d, b) => write!(f, "(reduce_map {op} {}, {})", d.get(), b.get()),
            Op::Mle(v) => write!(f, "(mle {})", v.get()),
            Op::Proj(v, field, _) => write!(f, "(proj {} .{field})", v.get()),
            Op::Pair(a, b, _) => write!(f, "(pair {}, {})", a.get(), b.get()),
            Op::Interpolate(points, evals) => {
                write!(f, "(interpolate {}, {})", points.get(), evals.get())
            }
            Op::Assert(op) => write!(f, "(assert {})", op.get()),
            Op::Verify(op) => write!(f, "(verify {})", op.get()),
            Op::Challenge(t, true) => write!(f, "challenge<{t}*>"),
            Op::Random(t, true) => write!(f, "random<{t}*>"),
            Op::Challenge(t, false) => write!(f, "challenge<{t}>"),
            Op::Random(t, false) => write!(f, "random<{t}>"),
            Op::Ram(v, r) => write!(f, "{}[{}]", v.get(), r.get()),
            Op::Vec(vs) => {
                f.write_str("[")?;
                for (i, v) in vs.iter().enumerate() {
                    if i > 0 {
                        f.write_str(", ")?;
                    }
                    write!(f, "{}", v.get())?;
                }
                f.write_str("]")
            }
            Op::Record(fields) => {
                f.write_str("{|")?;
                for (i, (name, op)) in fields.iter().enumerate() {
                    if i > 0 {
                        f.write_str(", ")?;
                    }
                    write!(f, "{name}: {}", op.get())?;
                }
                f.write_str("|}")
            }
            Op::Ref(n, _) => write!(f, "{n}"),
            Op::Reduce(op, v) => write!(f, "(reduce {op}, {})", v.get()),
        }
    }
}

impl<C: ArkConfig, R> From<Value<C>> for Op<C, R> {
    fn from(v: Value<C>) -> Self {
        Op::Value(v)
    }
}

impl<C: ArkConfig, R> From<usize> for Op<C, R> {
    fn from(v: usize) -> Self {
        Op::Value(Value::Index(v))
    }
}

impl<C: ArkConfig, R> From<CRange> for Op<C, R> {
    fn from(r: CRange) -> Self {
        Op::Value(Value::VecIndex(r.into_iter().collect()))
    }
}
