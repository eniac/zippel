use crate::{ABase, ATyp, ArkConfig, ArkScalarOps, Value};
use lang::ast::BinOp;
use lang::id::Vid;
use lang::typ::Nothing;
use lang::typ::lub::Lub;
use lang::typ::range::CRange;

use hashconsing::{HConsed, HConsign, HashConsign};
use petgraph::graph::NodeIndex;
use share::{BoxAllocator, Ctx, DocAllocator, DocBuilder, Pretty};
use std::fmt;
use std::ops::{
    Add, AddAssign, BitAnd, BitAndAssign, BitXor, BitXorAssign, Div, DivAssign, Mul, MulAssign,
    Rem, RemAssign, Sub, SubAssign,
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

    /// Sum-check marginalization helper
    Marginalize(HOp<C>),

    /// Project a field from a record value
    Proj(HOp<C>, String, ATyp),

    /// Coefficients of a polynomial
    Coef(HOp<C>),

    /// Evaluate a polynomial at a point (or vector of points)
    Evaluate(HOp<C>, HOp<C>),

    /// Assertion or verification check
    Check(HOp<C>),

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
    fn op_factory() -> &'static RwLock<OpFactory<Self>>;
}

/// Construct a hash-consed operation
pub fn mk<C: HasOpFactory>(op: GOp<C>) -> HOp<C> {
    C::op_factory().write().unwrap().mk(op)
}

impl Ref {
    pub fn new(n: NodeIndex) -> Self {
        Ref(n)
    }

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
        ATyp::Vec(box elem, n) => ATyp::vec(&elem, n), // already a vec; identity
        other => other,                                // defensive
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
            Op::Bin(BinOp::Equ, _, _, _) => 10,
            Op::Bin(BinOp::And, _, _, _) => 11,
            Op::Bin(BinOp::Pow, _, _, _) => 12,
            Op::Pair(_, _, _) => 13,
            Op::Ram(_, _) => 14,
            Op::Vec(_) => 15,
            Op::Record(_) => 16,
            Op::Random(_, _) => 17,
            Op::Challenge(_, _) => 18,
            Op::Interpolate(_, _) => 19,
            Op::Fft(_) => 20,
            Op::Check(_) => 21,
            Op::Poly(_) => 22,
            Op::Evaluate(_, _) => 23,
            Op::Coef(_) => 24,
            Op::Mle(_) => 25,
            Op::Reduce(_, _) => 26,
            Op::Marginalize(_) => 27,
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
                (ATyp::Vec(box typ, _), ATyp::Base(_)) => typ,
                (ATyp::Vec(box typ, _), ATyp::Vec(_, m)) => ATyp::vec(&typ, m),
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
            Op::Check(op) => op.typ(),
            // Op::Poly(v): v : Vec<F, k> → Uni(k - 1) under the degree
            // convention (see docs/poly-encoding.md).
            Op::Poly(op) => poly_typ_from_vec(op.typ()),
            Op::Evaluate(p, x) => {
                // Compute the result type of evaluating polynomial `p` at
                // the k-length vector of points `x`.
                //
                // Shapes (k = |x|):
                //   Uni(_) / VPoly(1, _)        at Vec(b, k) / Uni(k) -> Vec(b, k)  (batched)
                //   VPoly(n, _)   with k == n   at Vec(b, n)          -> b           (full)
                //   VPoly(n, m)   with k <  n   at Vec(b, k)          -> VPoly(n-k, m) (partial)
                //   Mle(n)        with k == n   at Vec(b, n)          -> b           (full)
                //   Mle(n)        with k <  n   at Vec(b, k)          -> Mle(n - k)  (partial)
                let x_typ = x.typ();
                let (elem_typ, k) = match x_typ.clone() {
                    ATyp::Vec(box t, n) => (t, n),
                    ATyp::Uni(n) => (ATyp::scalar(), n),
                    _ => return x_typ,
                };
                match p.typ() {
                    ATyp::Uni(_) => ATyp::Vec(Box::new(elem_typ), k),
                    ATyp::VPoly(1, _) => ATyp::Vec(Box::new(elem_typ), k),
                    ATyp::VPoly(n, _) if k == n => elem_typ,
                    ATyp::Mle(n) if k == n => elem_typ,
                    ATyp::VPoly(n, m) if k < n => ATyp::VPoly(n - k, m),
                    ATyp::Mle(n) if k < n => ATyp::Mle(n - k),
                    _ => x_typ,
                }
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
                let (elem, _) = v.typ().into_vec();
                let result_type = ATyp::lub_op(*op, &elem, &elem, &Nothing)
                    .expect("Reduce: type error in binary op");
                ATyp::lub_op(*op, &result_type, &elem, &Nothing)
                    .unwrap_or_else(|_| panic!(
                        "Reduce: accumulator type {:?} is incompatible as left operand for {:?} with element type {:?}",
                        result_type, op, elem
                    ))
            }
            Op::Interpolate(points, evals) => match (points.typ(), evals.typ()) {
                (
                    ATyp::Vec(box ATyp::Base(ABase::Scalar), m),
                    ATyp::Vec(box ATyp::Base(ABase::Scalar), n),
                )
                | (
                    ATyp::Vec(box ATyp::Base(ABase::Fin(_)), m),
                    ATyp::Vec(box ATyp::Base(ABase::Scalar), n),
                )
                | (
                    ATyp::Vec(box ATyp::Base(ABase::Scalar), m),
                    ATyp::Vec(box ATyp::Base(ABase::Fin(_)), n),
                )
                | (
                    ATyp::Vec(box ATyp::Base(ABase::Fin(_)), m),
                    ATyp::Vec(box ATyp::Base(ABase::Fin(_)), n),
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
            Op::Marginalize(op) => {
                let cfg_typ = op.typ();
                let ATyp::Record(fields) = cfg_typ else {
                    panic!("Op::Marginalize: input must be a record config");
                };
                let poly_typ = fields
                    .get(&"poly".to_string())
                    .unwrap_or_else(|| panic!("Op::Marginalize: missing 'poly' field"));
                let (n, d) = match poly_typ {
                    ATyp::Uni(deg) => (1usize, *deg),
                    ATyp::Mle(vars) => (*vars, 1usize),
                    ATyp::VPoly(vars, deg) => (*vars, *deg),
                    t => panic!(
                        "Op::Marginalize: 'poly' must be a polynomial type, got {}",
                        t,
                    ),
                };
                let out_degree = fields
                    .get(&"max_degree".to_string())
                    .and_then(|t| match t {
                        ATyp::Base(ABase::Fin(r))
                            if r.step == 1 && r.end == r.start.saturating_add(1) =>
                        {
                            Some(r.start)
                        }
                        _ => None,
                    })
                    .unwrap_or(d);
                let next_n = n.saturating_sub(1);
                let mut out_fields = Ctx::new();
                out_fields.insert(
                    &"evaluations".to_string(),
                    &ATyp::vec_scalar(out_degree + 1),
                );
                out_fields.insert(&"next_poly".to_string(), &ATyp::vpoly(next_n, out_degree));
                ATyp::Record(out_fields)
            }
            Op::Proj(_, _, typ) => typ.clone(),
        }
    }

    pub fn index(i: usize) -> Self {
        Op::Value(Value::Index(i))
    }

    pub fn value(v: &Value<C>) -> Self {
        Op::Value(v.clone())
    }

    pub fn range(r: CRange) -> Op<C, R> {
        Op::Value(Value::VecIndex(r.into_iter().collect()))
    }
    pub fn zero(typ: &ATyp) -> Op<C, R> {
        Op::Value(Value::zero(typ))
    }

    pub fn btrue() -> Self {
        Op::Value(Value::Bool(true))
    }
    pub fn bfalse() -> Self {
        Op::Value(Value::Bool(false))
    }

    pub fn reference(r: R, typ: ATyp) -> Op<C, R> {
        Op::Ref(r, typ)
    }

    pub fn challenge(typ: ATyp) -> Op<C, R> {
        Op::Challenge(typ, false)
    }
    pub fn random(typ: ATyp) -> Op<C, R> {
        Op::Random(typ, false)
    }
    pub fn challenge_nz(typ: ATyp) -> Op<C, R> {
        Op::Challenge(typ, true)
    }
    pub fn random_nz(typ: ATyp) -> Op<C, R> {
        Op::Random(typ, true)
    }
}

impl<C: HasOpFactory> GOp<C> {
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
            BinOp::Equ => Self::equ(a, b),
            BinOp::And => Self::and(a, b),
        }
    }

    pub fn evaluate(p: Self, x: Self) -> Self {
        Op::Evaluate(mk::<C>(p), mk::<C>(x))
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
            (Op::Vec(mut vs), v) | (v, Op::Vec(mut vs)) => {
                let (t, _) = typ.clone().into_vec();
                if v.typ() == t {
                    vs.push(mk::<C>(v));
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

    pub fn pair(v1: Self, v2: Self, typ: ATyp) -> Self {
        match (v1, v2) {
            (Op::Value(a), Op::Value(mut b)) => {
                a.value_pair(&mut b);
                Op::Value(b)
            }
            (v1, v2) => Op::Pair(mk::<C>(v1), mk::<C>(v2), typ),
        }
    }

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

    pub fn one(typ: &ATyp) -> GOp<C> {
        match typ {
            ATyp::Base(ABase::Fin(r)) if r.contains(1) => Op::Value(Value::Index(1)),
            ATyp::Base(ABase::Scalar) => Op::Value(Value::Scalar(C::FOps::one())),
            ATyp::Vec(box ATyp::Base(ABase::Scalar), n) => {
                Op::Value(Value::VecScalar(vec![C::FOps::one(); *n]))
            }
            ATyp::Vec(box ATyp::Base(ABase::Fin(r)), n) if r.contains(1) => {
                Op::Value(Value::VecIndex(vec![1; *n]))
            }
            ATyp::Vec(box typ, n) => {
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

    pub fn pow(v1: Self, v2: Self, typ: ATyp) -> Self {
        match v2 {
            Op::Value(Value::Index(0)) => Op::one(&typ),
            Op::Value(Value::Index(1)) => v1,
            v2 => Op::Bin(BinOp::Pow, mk::<C>(v1), mk::<C>(v2), typ),
        }
    }

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

    pub fn poly(op: Self) -> GOp<C> {
        Op::Poly(mk::<C>(op))
    }

    pub fn coef(op: Self) -> GOp<C> {
        Op::Coef(mk::<C>(op))
    }

    pub fn mle(op: Self) -> GOp<C> {
        Op::Mle(mk::<C>(op))
    }

    pub fn marginalize(op: Self) -> GOp<C> {
        Op::Marginalize(mk::<C>(op))
    }

    pub fn proj(record_op: Self, field: String, typ: ATyp) -> GOp<C> {
        Op::Proj(mk::<C>(record_op), field, typ)
    }

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

    pub fn pad_zeroes(v: GOp<C>, n: usize) -> GOp<C> {
        let typ = v.typ();
        let (t, m) = typ.into_vec();
        if m < n {
            Op::concat(v, Op::vec(vec![Op::zero(&t); n - m]), ATyp::vec(&t, n))
        } else {
            v
        }
    }

    pub fn equ(v1: Self, v2: Self) -> Self {
        match (v1, v2) {
            (Op::Value(a), Op::Value(b)) => Op::Value(a.value_equ(&b)),
            (v1, v2) => Op::Bin(BinOp::Equ, mk::<C>(v1), mk::<C>(v2), ATyp::bool()),
        }
    }

    pub fn and(v1: Self, v2: Self) -> Self {
        match (v1, v2) {
            (Op::Value(Value::Bool(false)), _) | (_, Op::Value(Value::Bool(false))) => Op::bfalse(),
            (Op::Value(a), Op::Value(b)) => Op::Value(a & b),
            (v1, v2) => Op::Bin(BinOp::And, mk::<C>(v1), mk::<C>(v2), ATyp::bool()),
        }
    }

    pub fn vec(vs: Vec<GOp<C>>) -> GOp<C> {
        Op::Vec(vs.into_iter().map(mk::<C>).collect())
    }

    pub fn check(op: GOp<C>) -> GOp<C> {
        Op::Check(mk::<C>(op))
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

    pub fn is_ref(&self) -> bool {
        matches!(self, Op::Ref(_, _))
    }

    pub fn references(&self) -> Vec<Ref> {
        match self {
            Op::Ref(n, _) => vec![*n],
            Op::Bin(_, a, b, _) | Op::Evaluate(a, b) | Op::Pair(a, b, _) | Op::Ram(a, b) => {
                a.references().into_iter().chain(b.references()).collect()
            }
            Op::Vec(vs) => vs.iter().flat_map(|v| v.references()).collect(),
            Op::Record(fields) => fields.iter().flat_map(|(_, v)| v.references()).collect(),
            Op::Interpolate(points, v) => points
                .references()
                .into_iter()
                .chain(v.references())
                .collect(),
            Op::Check(v)
            | Op::Poly(v)
            | Op::Mle(v)
            | Op::Coef(v)
            | Op::Reduce(_, v)
            | Op::Marginalize(v)
            | Op::Ifft(v)
            | Op::Fft(v) => v.references(),
            Op::Proj(v, _, _) => v.references(),
            Op::Value(_) | Op::Random(_, _) | Op::Challenge(_, _) => vec![],
        }
    }
}

impl<C: HasOpFactory> GOp<C> {
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
            Op::Evaluate(a, b) => Op::Evaluate(
                mk::<C>(a.map_node_indices(f)),
                mk::<C>(b.map_node_indices(f)),
            ),
            Op::Poly(op) => Op::Poly(mk::<C>(op.map_node_indices(f))),
            Op::Coef(op) => Op::Coef(mk::<C>(op.map_node_indices(f))),
            Op::Check(op) => Op::Check(mk::<C>(op.map_node_indices(f))),
            Op::Interpolate(points, evals) => Op::Interpolate(
                mk::<C>(points.map_node_indices(f)),
                mk::<C>(evals.map_node_indices(f)),
            ),
            Op::Ifft(op) => Op::Ifft(mk::<C>(op.map_node_indices(f))),
            Op::Fft(op) => Op::Fft(mk::<C>(op.map_node_indices(f))),
            Op::Mle(op) => Op::Mle(mk::<C>(op.map_node_indices(f))),
            Op::Marginalize(op) => Op::Marginalize(mk::<C>(op.map_node_indices(f))),
            Op::Proj(op, field, typ) => {
                Op::Proj(mk::<C>(op.map_node_indices(f)), field.clone(), typ.clone())
            }
            Op::Reduce(op, v) => Op::Reduce(*op, mk::<C>(v.map_node_indices(f))),
            _ => self.clone(),
        }
    }

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
            Op::Check(op) => Op::Check(mk::<C>(op.map_refs(f))),
            Op::Interpolate(points, evals) => {
                Op::Interpolate(mk::<C>(points.map_refs(f)), mk::<C>(evals.map_refs(f)))
            }
            Op::Ifft(op) => Op::Ifft(mk::<C>(op.map_refs(f))),
            Op::Fft(op) => Op::Fft(mk::<C>(op.map_refs(f))),
            Op::Value(_) | Op::Random(_, _) | Op::Challenge(_, _) => self.clone(),
            Op::Poly(op) => Op::Poly(mk::<C>(op.map_refs(f))),
            Op::Coef(op) => Op::Coef(mk::<C>(op.map_refs(f))),
            Op::Evaluate(p, x) => Op::Evaluate(mk::<C>(p.map_refs(f)), mk::<C>(x.map_refs(f))),
            Op::Mle(op) => Op::Mle(mk::<C>(op.map_refs(f))),
            Op::Marginalize(op) => Op::Marginalize(mk::<C>(op.map_refs(f))),
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
            Op::Check(op) => op.inline(vars, except),
            Op::Interpolate(points, evals) => Op::Interpolate(
                mk::<C>(points.inline(vars, except)),
                mk::<C>(evals.inline(vars, except)),
            ),
            Op::Ifft(v) => Op::Ifft(mk::<C>(v.inline(vars, except))),
            Op::Fft(v) => Op::Fft(mk::<C>(v.inline(vars, except))),
            Op::Marginalize(v) => Op::Marginalize(mk::<C>(v.inline(vars, except))),
            Op::Proj(v, field, typ) => {
                Op::Proj(mk::<C>(v.inline(vars, except)), field.clone(), typ.clone())
            }
            Op::Reduce(op, v) => Op::Reduce(*op, mk::<C>(v.inline(vars, except))),
            _ => self.clone(),
        }
    }
}

/// Pretty-printer for Operations
impl<'a, D, A> Pretty<'a, D, A> for Ref
where
    D: DocAllocator<'a, A>,
    D::Doc: Clone,
    A: 'a + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        allocator.text(format!("n{}", self.0.index()))
    }

    fn is_nil(&self) -> bool {
        false
    }
}

impl fmt::Display for Ref {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <Ref as Pretty<'_, BoxAllocator, ()>>::pretty(*self, &BoxAllocator)
            .1
            .render_fmt(100, f)
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

impl<C: HasOpFactory> BitAndAssign<GOp<C>> for GOp<C> {
    fn bitand_assign(&mut self, other: GOp<C>) {
        *self = Op::and(self.clone(), other);
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

impl<C: HasOpFactory> BitAnd for GOp<C> {
    type Output = GOp<C>;

    fn bitand(self, other: GOp<C>) -> GOp<C> {
        Op::and(self, other)
    }
}

/// Pretty-printer for Operations
impl<'a, D, C, A, R> Pretty<'a, D, A> for Op<C, R>
where
    D: DocAllocator<'a, A>,
    C: ArkConfig,
    R: Pretty<'a, D, A>,
    D::Doc: Clone,
    A: 'a + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        match self {
            Op::Value(v) => allocator.text(format!("{}", v)),
            Op::Bin(op, a, b, _) => {
                let a_op = a.get().clone();
                let b_op = b.get().clone();
                let needs_left_paren =
                    matches!(&a_op, Op::Bin(op1, _, _, _) if op1.precedence() < op.precedence());
                let needs_right_paren =
                    matches!(&b_op, Op::Bin(op2, _, _, _) if op2.precedence() < op.precedence());
                if needs_left_paren {
                    allocator.concat(vec![
                        allocator.text("("),
                        a_op.pretty(allocator),
                        allocator.text(")"),
                        allocator.text(format!("{}", op)),
                        b_op.pretty(allocator),
                    ])
                } else if needs_right_paren {
                    allocator.concat(vec![
                        a_op.pretty(allocator),
                        allocator.text(format!("{}", op)),
                        allocator.text("("),
                        b_op.pretty(allocator),
                        allocator.text(")"),
                    ])
                } else {
                    allocator.concat(vec![
                        a_op.pretty(allocator),
                        allocator.text(format!("{}", op)),
                        b_op.pretty(allocator),
                    ])
                }
            }
            Op::Fft(v) => allocator.concat([
                allocator.text("(fft "),
                v.get().clone().pretty(allocator),
                allocator.text(")"),
            ]),
            Op::Ifft(v) => allocator.concat([
                allocator.text("(ifft "),
                v.get().clone().pretty(allocator),
                allocator.text(")"),
            ]),
            Op::Poly(v) => allocator.concat([
                allocator.text("(poly "),
                v.get().clone().pretty(allocator),
                allocator.text(")"),
            ]),
            Op::Coef(v) => allocator.concat([
                allocator.text("(coef "),
                v.get().clone().pretty(allocator),
                allocator.text(")"),
            ]),
            Op::Evaluate(p, x) => allocator.concat([
                allocator.text("(eval "),
                p.get().clone().pretty(allocator),
                allocator.text(", "),
                x.get().clone().pretty(allocator),
                allocator.text(")"),
            ]),
            Op::Mle(v) => allocator.concat([
                allocator.text("(mle "),
                v.get().clone().pretty(allocator),
                allocator.text(")"),
            ]),
            Op::Marginalize(v) => allocator.concat([
                allocator.text("(marginalize "),
                v.get().clone().pretty(allocator),
                allocator.text(")"),
            ]),
            Op::Proj(v, field, _) => allocator.concat([
                allocator.text("(proj "),
                v.get().clone().pretty(allocator),
                allocator.text(" ."),
                allocator.text(field.clone()),
                allocator.text(")"),
            ]),
            Op::Pair(a, b, _) => allocator.concat([
                allocator.text("(pair "),
                a.get().clone().pretty(allocator),
                allocator.text(", "),
                b.get().clone().pretty(allocator),
                allocator.text(")"),
            ]),
            Op::Interpolate(points, evals) => allocator.concat([
                allocator.text("(interpolate "),
                points.get().clone().pretty(allocator),
                allocator.text(", "),
                evals.get().clone().pretty(allocator),
                allocator.text(")"),
            ]),
            Op::Check(v) => allocator.concat([
                allocator.text("(check "),
                v.get().clone().pretty(allocator),
                allocator.text(")"),
            ]),
            Op::Challenge(t, true) => allocator.text(format!("challenge<{}*>", t)),
            Op::Random(t, true) => allocator.text(format!("random<{}*>", t)),
            Op::Challenge(t, false) => allocator.text(format!("challenge<{}>", t)),
            Op::Random(t, false) => allocator.text(format!("random<{}>", t)),
            Op::Ram(v, r) => allocator.concat([
                v.get().clone().pretty(allocator),
                allocator.text("["),
                r.get().clone().pretty(allocator),
                allocator.text("]"),
            ]),
            Op::Vec(vs) => allocator.concat([
                allocator.text("["),
                allocator.intersperse(
                    vs.into_iter().map(|v| v.get().clone().pretty(allocator)),
                    ", ",
                ),
                allocator.text("]"),
            ]),
            Op::Record(fields) => {
                let mut field_docs = Vec::new();
                for (name, op) in fields {
                    field_docs.push(allocator.concat([
                        allocator.text(name.clone()),
                        allocator.text(": "),
                        op.get().clone().pretty(allocator),
                    ]));
                }
                allocator.concat([
                    allocator.text("{|"),
                    allocator.intersperse(field_docs, ", "),
                    allocator.text("|}"),
                ])
            }
            Op::Ref(n, _) => n.pretty(allocator),
            Op::Reduce(op, v) => allocator.concat([
                allocator.text("(reduce "),
                allocator.text(format!("{}", op)),
                allocator.text(", "),
                v.get().clone().pretty(allocator),
                allocator.text(")"),
            ]),
        }
    }

    fn is_nil(&self) -> bool {
        false
    }
}

impl<'a, C: ArkConfig, R: Pretty<'a, BoxAllocator, ()> + Clone> fmt::Display for Op<C, R> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <Op<C, R> as Pretty<'a, BoxAllocator, ()>>::pretty(self.clone(), &BoxAllocator)
            .1
            .render_fmt(100, f)
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
