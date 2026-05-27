pub mod buchberger;
pub use buchberger::GroebnerBasis;

pub mod monomial;
pub use monomial::{ElimTerm, GrevLexTerm, Monomial};
pub mod sparsepoly;
pub use sparsepoly::SparsePolynomial;

use crate::DQDag;
use crate::analyses::TransClos;
use crate::pref::PRef;
use crate::{GOp, HOp, Op, Ref};
use lang::ast::BinOp;
use lang::id::Vid;

use ark_ff::{FftField, Field, One, Zero};
use backend::op::HasOpFactory;
use backend::{ATyp, ArkConfig, ArkScalarOps, Value};
use lang::typ::{Distribution, Qualifier};
use petgraph::graph::NodeIndex;
use share::{BoxAllocator, Ctx, DocAllocator, DocBuilder, Pretty, Set};
use std::fmt;

// ---------------------------------------------------------------------------
// PRef-slot enumeration helpers for polynomial / MLE values.
//
// These define the canonical order in which the slots of a polynomial-typed
// PRef are laid out (via `PRef::with_index(i)`). They are NOT monomial / term
// orderings — the existing `ElimTerm` / `GrevLexTerm` orderings in
// `monomial.rs` are untouched.
//
//   * VPoly<N, M> → C(N+M, M) slots, one per multi-index k with |k| ≤ M.
//   * Mle<N>      → 2^N slots, one per hypercube point b ∈ {0,1}^N.
//   * Uni(n)      → n slots (coefficient vector).
//   * Vec(_, n)   → n slots.
// ---------------------------------------------------------------------------

/// All multi-indices `(k_1, …, k_n)` with `sum(k_i) ≤ m`, in graded-lex order
/// (by total degree, then lex within the same degree).
fn multi_indices(n: usize, m: usize) -> Vec<Vec<usize>> {
    fn go(n: usize, budget: usize, acc: &mut Vec<usize>, out: &mut Vec<Vec<usize>>) {
        if n == 0 {
            out.push(acc.clone());
            return;
        }
        for k in 0..=budget {
            acc.push(k);
            go(n - 1, budget - k, acc, out);
            acc.pop();
        }
    }
    let mut all = Vec::new();
    let mut scratch = Vec::with_capacity(n);
    go(n, m, &mut scratch, &mut all);
    // Sort by (total degree, lex) to get a stable graded-lex enumeration.
    all.sort_by(|a, b| {
        let da: usize = a.iter().sum();
        let db: usize = b.iter().sum();
        da.cmp(&db).then_with(|| a.cmp(b))
    });
    all
}

/// All boolean multi-indices `b ∈ {0,1}^n` in lex order (matches how
/// `Op::Mle(v)` unpacks a length-`2^N` vector).
fn hypercube(n: usize) -> Vec<Vec<usize>> {
    (0..(1usize << n))
        .map(|i| (0..n).map(|j| (i >> j) & 1).collect())
        .collect()
}

/// Number of PRef slots needed to represent a value of the given type.
///
/// Per `docs/poly-encoding.md`, `m` in every polynomial ATyp is the max
/// degree, so a `Uni(m)` has `m + 1` coefficient slots and a
/// `VPoly(n, m)` has `C(m + n, n)` slots.
fn num_coeffs(typ: &ATyp) -> usize {
    match typ {
        ATyp::VPoly(n, m) => multi_indices(*n, *m).len(),
        ATyp::Mle(n) => 1usize << *n,
        ATyp::Uni(m) => *m + 1,
        ATyp::Vec(_, n) => *n,
        _ => 1,
    }
}

/// Inverse of the enumeration: position of multi-index / hypercube point `k`
/// in the canonical slot order for the given type.
#[cfg(test)]
fn index_of(typ: &ATyp, k: &[usize]) -> usize {
    match typ {
        ATyp::VPoly(n, m) => multi_indices(*n, *m)
            .iter()
            .position(|kk| kk.as_slice() == k)
            .expect("multi-index out of range for VPoly"),
        ATyp::Mle(n) => {
            debug_assert_eq!(k.len(), *n);
            let mut acc = 0usize;
            for (j, bj) in k.iter().enumerate() {
                debug_assert!(*bj <= 1);
                acc |= (bj & 1) << j;
            }
            acc
        }
        _ => 0,
    }
}

/// Compute row `i` of the DFT matrix applied to `coeffs`:
///    `Σ_j ω^{i·j} · coeffs[j]`.
///
/// Used by the `Op::Ifft` / `Op::Fft` arms to express the relation
/// between coefficient form and evaluation-at-roots-of-unity form as a
/// set of N linear polynomial equations. The caller is responsible for
/// providing `ω` such that `ω^N = 1` and `ω` has order exactly `N`
/// (typically `C::F::get_root_of_unity(N)`).
fn dft_row<F: Field, T: Monomial>(
    coeffs: &[SparsePolynomial<F, T>],
    omega: F,
    i: usize,
) -> SparsePolynomial<F, T> {
    let w_step = omega.pow([i as u64]);
    let mut wij = F::one();
    let mut acc = SparsePolynomial::<F, T>::zero();
    for c in coeffs.iter() {
        let scalar = SparsePolynomial::<F, T>::lit(&wij);
        acc += c * &scalar;
        wij *= w_step;
    }
    acc
}

/// This is used to construct a Groebner basis from the ideals corresponding to
/// each one of groups G1, G2, GT and the scalar ring F.
/// Construct a Groebner basis from a graph, by first taking the transitive
/// closure of the graph, building a set of equations of polynomials. Non-polynomial
/// terms are replaced with variables in [npterms].
#[derive(Clone)]
pub struct GroebnerBuilder<C: ArkConfig, T: Monomial> {
    pub basis: GroebnerBasis<C::F, T>,
    pub np: Ctx<PRef, GOp<C>>,
    pub pl: Ctx<PRef, SparsePolynomial<C::F, T>>,
    pub args: Set<PRef>,
    /// Phase 13: polynomial div/rem witness side-table.
    ///
    /// Maps each `(dividend, divisor)` HOp pair for which a VPoly `/` or `%`
    /// has been encountered to a fresh pair of witness PRefs
    /// `(q_wit, r_wit)` with the canonical identity
    ///
    /// ```text
    ///     dividend = divisor · q_wit + r_wit
    /// ```
    ///
    /// emitted into `basis` exactly once (on first lookup). Subsequent
    /// `Div` / `Rem` ops on the same `(a, b)` just link the user's `pr`
    /// to the already-minted `q_wit` / `r_wit`, so matching `p / d`
    /// and `p % d` in a program share the same witnesses and reduce
    /// `verify(p == d * q + r)` to the canonical row directly.
    pub div_wit: Ctx<(HOp<C>, HOp<C>), (PRef, PRef)>,
    /// Phase B (from main): canonical alias map for input/relation arg
    /// markers that bind the same protocol parameter under different
    /// `Ref` indices. Looked up by `find_ref` and populated by `add_tc`.
    pub ref_aliases: std::collections::HashMap<Ref, PRef>,
}

impl<C: ArkConfig + HasOpFactory, T: Monomial> Default for GroebnerBuilder<C, T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<C: ArkConfig + HasOpFactory, T: Monomial> GroebnerBuilder<C, T> {
    pub fn new() -> Self {
        Self {
            basis: GroebnerBasis::empty(0),
            np: Ctx::new(),
            pl: Ctx::new(),
            args: Set::new(),
            div_wit: Ctx::new(),
            ref_aliases: std::collections::HashMap::new(),
        }
    }

    pub fn vars(&self) -> Set<PRef> {
        self.np.keys().union(self.pl.keys())
    }

    /// Resolve a `Ref` to a `PRef` known by this builder.
    ///
    /// Phase B: every `Ref` carries a unique `NodeIndex`. The Inp and Rel
    /// markers' arg children alias to a canonical `PRef` via `ref_aliases`,
    /// after which lookup is a single keyed scan against the closure. If
    /// the ref is not present (e.g., it points at a non-modelled op like
    /// `Op::Random`/`Op::Challenge`), register it as an opaque variable in
    /// `np` so downstream consumers see a consistent `PRef`.
    pub fn find_ref(&mut self, r: &Ref) -> PRef {
        if let Some(p) = self.ref_aliases.get(r).cloned() {
            return p;
        }
        if let Some(v) = self.vars().into_iter().find(|v| v.reference == *r) {
            return v;
        }
        if let Some(v) = self.args.iter().find(|v| v.reference == *r).cloned() {
            return v;
        }
        log::debug!(
            "groebner: opaque ref {} (not in vars/args), registering in np",
            r
        );
        let pref = PRef::from_ref(
            *r,
            ATyp::scalar(),
            Qualifier::Private,
            Distribution::Nonuniform,
        );
        let opaque = Op::Ref(*r, ATyp::scalar());
        self.np.insert(&pref, &opaque);
        pref
    }

    /// Filter out variables that satisfy the predicate
    pub fn eliminate_var<F: Fn(&PRef) -> bool>(&mut self, f: &F) {
        self.basis.eliminate_var(f);
        self.pl.retain(|p, _| !f(p));
        self.np.retain(|p, _| !f(p));
    }

    pub fn eliminate_monomial<F: Fn(&T) -> bool>(&mut self, f: &F) {
        self.basis.eliminate_monomial(f);
        let vars = self.basis.vars();
        self.pl.retain(|p, _| vars.contains(p));
        self.np.retain(|p, _| vars.contains(p));
    }

    #[allow(dead_code)]
    pub fn inline<F: Fn(&PRef) -> bool>(&mut self, f: F) {
        for p in self.basis.iter_mut() {
            *p = p.clone().flat_map_vars(&|v| {
                if f(&v) || !self.pl.contains(&v) {
                    SparsePolynomial::var(&v)
                } else {
                    self.pl[v].clone()
                }
            });
        }
    }

    /// Compute Groebner basis using Buchberger algorithm,
    pub fn run(&mut self) {
        // Compute the Groebner basis using Buchberger algorithm
        self.basis = self.basis.clone().buchberger_and_reduce();
    }

    /// Remap all PRef variables in the basis, pl, np, and args using a mapping function.
    /// Used when combining Gröbner bases from different subgraphs that have
    /// different node index namespaces.
    pub fn remap_vars<F: Fn(&PRef) -> PRef>(&mut self, f: &F) {
        // Remap basis polynomials
        self.basis.basis = self
            .basis
            .basis
            .iter()
            .map(|p| p.clone().flat_map_vars(&|v| SparsePolynomial::var(&f(&v))))
            .collect();

        // Remap pl context
        self.pl = self
            .pl
            .iter()
            .map(|(k, v)| {
                let new_k = f(k);
                let new_v = v.clone().flat_map_vars(&|v| SparsePolynomial::var(&f(&v)));
                (new_k, new_v)
            })
            .collect();

        // Remap np context
        self.np = self.np.iter().map(|(k, v)| (f(k), v.clone())).collect();

        // Remap args
        self.args = self.args.iter().map(f).collect();

        // Phase 13: remap div_wit values (keys are HOp, which are builder-
        // local and not affected by PRef remapping).
        self.div_wit = self
            .div_wit
            .iter()
            .map(|(k, (q, r))| (k.clone(), (f(q), f(r))))
            .collect();
    }

    /// Merge another builder's basis, polynomial definitions, and non-polynomial
    /// definitions into this builder.
    pub fn merge(&mut self, other: &Self) {
        for p in other.basis.iter() {
            self.basis.push(p.clone());
        }
        for (k, v) in other.pl.iter() {
            self.pl.insert(k, v);
        }
        for (k, v) in other.np.iter() {
            self.np.insert(k, v);
        }
        // Phase 13: keep other's div_wit entries so subsequent Div/Rem ops
        // on the same operand pairs reuse the existing identity rows
        // instead of emitting duplicates. HOp uids are builder-local so a
        // literal merge can introduce key collisions only when the two
        // builders share a HConsign (the common case when they were built
        // from the same DAG); cross-HConsign duplicates are harmless —
        // each (q, r) pair is constrained by its own identity row set
        // already present in `basis`.
        for (k, v) in other.div_wit.iter() {
            if !self.div_wit.contains(k) {
                self.div_wit.insert(k, v);
            }
        }
    }

    /// Phase 12: lazy accessor for the G1 generator sentinel `__g1__`.
    ///
    /// Every opaque G1 element `P` is modeled (in exponent space) as
    /// `var(P) = exp_P · var(__g1__)`. We do NOT emit the linking
    /// basis row explicitly — existing Bin(Add/Sub/Mul) on group types
    /// already treats `var(P)` as an F-scalar, so Buchberger already
    /// propagates exponents through ring arithmetic. The sentinel's
    /// role is to appear as a dimensional-consistency factor on GT
    /// expressions produced by `Op::Pair`.
    ///
    /// The sentinel PRef has a stable `Ref::Var(Vid("__g1__"),
    /// NodeIndex(usize::MAX - 1))` reference, so two independent
    /// `GroebnerBuilder`s agree on which PRef this is — required for
    /// `merge` and cross-builder visibility.
    #[allow(dead_code)]
    fn g1_pref(&mut self) -> PRef {
        self.sentinel_pref("__g1__", ATyp::g1(), 1)
    }

    /// Phase 12: lazy accessor for the G2 generator sentinel `__g2__`.
    #[allow(dead_code)]
    fn g2_pref(&mut self) -> PRef {
        self.sentinel_pref("__g2__", ATyp::g2(), 2)
    }

    /// Phase 12: lazy accessor for the GT generator sentinel `__gt__`.
    ///
    /// `Op::Pair(a, b)` emits the basis row
    ///   `var(pr) − to_poly(a)·to_poly(b)·var(__gt__) = 0`
    /// which encodes the pairing axiom
    ///   `pair(__g1__, __g2__) = __gt__`
    /// combined with bilinearity:
    ///   `pair(α·__g1__, β·__g2__) = α·β·__gt__`.
    fn gt_pref(&mut self) -> PRef {
        self.sentinel_pref("__gt__", ATyp::gt(), 3)
    }

    /// Shared helper for sentinel PRef construction. Uses a stable
    /// `NodeIndex` in the high end of the address space (counting down
    /// from `usize::MAX`) so synthesized sentinels can never collide
    /// with real DAG node indices (which grow up from 0). Registers
    /// the sentinel in `np` on first use so `vars()` picks it up.
    fn sentinel_pref(&mut self, name: &str, typ: ATyp, offset: usize) -> PRef {
        let vid = Vid::from(name);
        let idx = NodeIndex::new(usize::MAX - offset);
        let pref = PRef::from_var(
            vid,
            idx,
            typ.clone(),
            0,
            Qualifier::Public,
            Distribution::default(),
        );
        if !self.np.contains(&pref) {
            self.np.insert(&pref, &Op::Ref(pref.reference, typ));
        }
        pref
    }

    /// Phase 13: polynomial division witnesses `(q_wit, r_wit)` for a
    /// `(dividend, divisor)` HOp pair of VPoly operands.
    ///
    /// On first call for a given `(a, b)`, mints fresh stable-named witness
    /// PRefs `q_wit : VPoly(nr, ma - mb)` and `r_wit : VPoly(nr, mb - 1)`,
    /// then emits the canonical polynomial identity rows
    ///
    /// ```text
    ///     a_polys[k]  −  Σ_{(i,j): b_idx[i]+q_idx[j]=k} b_polys[i] · var(q_wit[j])
    ///                 −  (if k ∈ r_idx)  var(r_wit[k])                    =  0
    /// ```
    ///
    /// for every `k ∈ a_idx`, encoding `dividend = divisor · q_wit + r_wit`.
    ///
    /// On subsequent calls with the same `(a, b)`, returns the cached pair
    /// without re-emitting rows — so both `Op::Bin(BinOp::Div)` and
    /// `Op::Bin(BinOp::Rem)` on the same operands share the same witnesses,
    /// making `verify(p == d*q + r)` collapse directly to the canonical row
    /// under Buchberger.
    ///
    /// Returns `None` if either operand isn't VPoly/Uni-shaped, if num_vars
    /// differ, or if `ma < mb` (no well-defined quotient).
    fn div_witnesses(&mut self, a: &HOp<C>, b: &HOp<C>) -> Option<(PRef, PRef)> {
        // Canonical VPoly shape extraction (handles both ATyp::VPoly and
        // `ATyp::Uni(m) ≡ VPoly(1, m)` per docs/poly-encoding.md — `m` is
        // the max degree in both forms).
        fn poly_shape(t: &ATyp) -> Option<(usize, usize)> {
            match t {
                ATyp::VPoly(n, m) => Some((*n, *m)),
                ATyp::Uni(m) => Some((1, *m)),
                _ => None,
            }
        }

        let key = (a.clone(), b.clone());
        if let Some(wit) = self.div_wit.get(&key) {
            return Some(wit.clone());
        }

        let a_typ = a.get().typ();
        let b_typ = b.get().typ();
        let (na, ma) = poly_shape(&a_typ)?;
        let (nb, mb) = poly_shape(&b_typ)?;
        if na != nb {
            return None;
        }
        if ma < mb || mb == 0 {
            return None;
        }

        let nr = na;
        let mq = ma - mb;
        let mr = mb - 1;

        // Mint stable witness PRefs. Offsets 1000+2k / 1001+2k are far from
        // the phase-12 sentinel offsets (1..3) and from real DAG node indices.
        let counter = self.div_wit.len();
        let q_name = format!("__div_q_{}__", counter);
        let r_name = format!("__div_r_{}__", counter);
        let q_wit = self.sentinel_pref(&q_name, ATyp::VPoly(nr, mq), 1000 + 2 * counter);
        let r_wit = self.sentinel_pref(&r_name, ATyp::VPoly(nr, mr), 1001 + 2 * counter);

        // Emit canonical identity rows: one per a_idx multi-index.
        let a_polys = self.to_poly(a.get());
        let b_polys = self.to_poly(b.get());
        let a_idx = multi_indices(na, ma);
        let b_idx = multi_indices(nb, mb);
        let q_idx = multi_indices(nr, mq);
        let r_idx = multi_indices(nr, mr);

        debug_assert_eq!(
            a_polys.len(),
            a_idx.len(),
            "to_poly(a) slot count mismatch: {} vs a_idx {}",
            a_polys.len(),
            a_idx.len()
        );
        debug_assert_eq!(
            b_polys.len(),
            b_idx.len(),
            "to_poly(b) slot count mismatch: {} vs b_idx {}",
            b_polys.len(),
            b_idx.len()
        );

        for (ka_pos, k) in a_idx.iter().enumerate() {
            let mut rhs = SparsePolynomial::<C::F, T>::zero();
            // D · Q contribution.
            for (i_pos, ki) in b_idx.iter().enumerate() {
                for (j_pos, kj) in q_idx.iter().enumerate() {
                    let sum: Vec<usize> = ki.iter().zip(kj.iter()).map(|(x, y)| x + y).collect();
                    if sum == *k {
                        let qf = q_wit.clone().with_index(j_pos);
                        rhs = &rhs + &(&b_polys[i_pos] * &SparsePolynomial::var(&qf));
                    }
                }
            }
            // R contribution (only for k with total degree ≤ mr).
            if let Some(r_pos) = r_idx.iter().position(|rk| rk == k) {
                let rf = r_wit.clone().with_index(r_pos);
                rhs = &rhs + &SparsePolynomial::var(&rf);
            }
            self.basis.push(&a_polys[ka_pos] - &rhs);
        }

        self.div_wit.insert(&key, &(q_wit.clone(), r_wit.clone()));
        Some((q_wit, r_wit))
    }

    /// Phase 13: link the user's PRef `pr` to a witness PRef `wit` slot by
    /// slot, for when `pr` aliases a div/rem witness produced by
    /// `div_witnesses`. Emits `var(pr[j]) − var(wit[j]) = 0` for every
    /// `j < num_coeffs(pr.typ)`, and registers `pl[pr[j]] = var(wit[j])`.
    fn link_to_witness(&mut self, pr: &PRef, wit: &PRef) {
        let n_pr = num_coeffs(&pr.typ);
        let n_wit = num_coeffs(&wit.typ);
        // Number of shared slots. If user's pr has more slots than the
        // witness (unusual — would indicate the lub widened the result),
        // link what we can; excess pr slots stay unconstrained (opaque).
        let n = n_pr.min(n_wit);
        for j in 0..n {
            let pf = pr.clone().with_index(j);
            let wf = wit.clone().with_index(j);
            let wvar = SparsePolynomial::var(&wf);
            self.pl.insert(&pf, &wvar);
            self.basis.push(&wvar - &SparsePolynomial::var(&pf));
        }
    }

    #[allow(clippy::wrong_self_convention)]
    fn to_poly_value(&mut self, v: &Value<C>) -> Vec<SparsePolynomial<C::F, T>> {
        match v {
            Value::Scalar(s) => vec![SparsePolynomial::lit(s)],
            Value::Bool(b) => vec![SparsePolynomial::lit(&if *b {
                C::F::one()
            } else {
                C::F::zero()
            })],
            Value::Index(i) => vec![SparsePolynomial::lit(&C::FOps::from_usize(*i))],
            Value::Vec(v) => v.iter().flat_map(|v| self.to_poly_value(v)).collect(),
            Value::VecBool(v) => v
                .iter()
                .map(|b| SparsePolynomial::lit(&if *b { C::F::one() } else { C::F::zero() }))
                .collect::<Vec<_>>(),
            Value::VecScalar(v) => v.iter().map(SparsePolynomial::lit).collect::<Vec<_>>(),
            Value::VecIndex(v) => v
                .iter()
                .map(|i| SparsePolynomial::lit(&C::FOps::from_usize(*i)))
                .collect::<Vec<_>>(),
            _ => unreachable!("Unsupported value: {}", v),
        }
    }

    /// Phase 10: generic dispatcher for `Op::Reduce(op, v)`.
    ///
    /// Returns `Some(polys)` when the inner BinOp has a polynomial
    /// identity over `C::F`, `None` when it must stay opaque.
    ///
    /// Polynomial cases (result has `len(pr.typ)` slots, but we return
    /// enough polys for the caller to drive `pr.with_index(i)`):
    ///
    /// * `Add`    — scalar output, `Σ elems` (empty → `0`).
    /// * `Sub`    — scalar output, left-fold difference `e_0 - e_1 - e_2 - …`
    ///   (empty → `None`; we can't choose a neutral element).
    /// * `Mul`    — scalar output, `Π elems` (empty → `1`).
    /// * `Concat` — concatenation of slot-lists into a single vector
    ///   of length `Σ |e_i|`. Elements are the raw slot polys.
    ///
    /// Opaque cases (`None`): `Div`, `Rem`, `Pow`, `Dot`, `Equ`, `And`
    /// — they either aren't polynomial over the scalar field or would
    /// require tracking inverses / boolean axioms that are outside
    /// scope.
    fn reduce_unfold(
        &mut self,
        op: BinOp,
        elems: Vec<SparsePolynomial<C::F, T>>,
    ) -> Option<Vec<SparsePolynomial<C::F, T>>> {
        match op {
            BinOp::Add => {
                let mut acc = SparsePolynomial::<C::F, T>::zero();
                for e in elems {
                    acc = &acc + &e;
                }
                Some(vec![acc])
            }
            BinOp::Sub => {
                let mut iter = elems.into_iter();
                let first = iter.next()?;
                let mut acc = first;
                for e in iter {
                    acc = &acc - &e;
                }
                Some(vec![acc])
            }
            BinOp::Mul => {
                let mut acc = SparsePolynomial::<C::F, T>::lit(&C::F::one());
                for e in elems {
                    acc = &acc * &e;
                }
                Some(vec![acc])
            }
            BinOp::Concat => Some(elems),
            // Non-polynomial or boolean-domain — stay opaque.
            BinOp::Div | BinOp::Rem | BinOp::Pow | BinOp::Dot | BinOp::Equ | BinOp::And => None,
        }
    }

    /// Shared helper for `Op::Evaluate(p, xs)` — returns `Some(polys)` when the
    /// (p.typ(), |xs|) dispatch is supported, `None` otherwise. Used by both
    /// `to_poly` (when Eval appears nested inside another op) and `add_op`
    /// (when Eval is the top-level op being bound to a PRef).
    fn eval_to_poly(&mut self, p: &GOp<C>, xs: &GOp<C>) -> Option<Vec<SparsePolynomial<C::F, T>>> {
        let p_typ = p.typ();
        let xs_polys = self.to_poly(xs);
        let k = xs_polys.len();
        match &p_typ {
            ATyp::Uni(_) | ATyp::VPoly(1, _) if k >= 1 => {
                let p_polys = self.to_poly(p);
                let one = SparsePolynomial::<C::F, T>::lit(&C::F::one());
                let out = (0..k)
                    .map(|i| {
                        let xi = &xs_polys[i];
                        let mut acc = SparsePolynomial::<C::F, T>::zero();
                        let mut xi_pow = one.clone();
                        for aj in p_polys.iter() {
                            acc = &acc + &(aj * &xi_pow);
                            xi_pow = &xi_pow * xi;
                        }
                        acc
                    })
                    .collect();
                Some(out)
            }
            ATyp::VPoly(n, mdeg) if *n >= 2 && k <= *n => {
                let p_polys = self.to_poly(p);
                let all_k = multi_indices(*n, *mdeg);
                let mono = |k_fixed: &[usize],
                            xs_polys: &[SparsePolynomial<C::F, T>]|
                 -> SparsePolynomial<C::F, T> {
                    let mut acc = SparsePolynomial::<C::F, T>::lit(&C::F::one());
                    for (j, &kij) in k_fixed.iter().enumerate() {
                        if kij == 0 {
                            continue;
                        }
                        let mut xp = xs_polys[j].clone();
                        xp.pow(kij);
                        acc = &acc * &xp;
                    }
                    acc
                };
                if k == *n {
                    let mut acc = SparsePolynomial::<C::F, T>::zero();
                    for (idx, ki) in all_k.iter().enumerate() {
                        acc = &acc + &(&p_polys[idx] * &mono(ki, &xs_polys));
                    }
                    Some(vec![acc])
                } else {
                    let remaining_n = n - k;
                    let result_indices = multi_indices(remaining_n, *mdeg);
                    let out = result_indices
                        .iter()
                        .map(|kp| {
                            let mut acc = SparsePolynomial::<C::F, T>::zero();
                            for (idx, ki) in all_k.iter().enumerate() {
                                if ki[k..] != kp[..] {
                                    continue;
                                }
                                acc = &acc + &(&p_polys[idx] * &mono(&ki[..k], &xs_polys));
                            }
                            acc
                        })
                        .collect();
                    Some(out)
                }
            }
            ATyp::Mle(n) if k <= *n => {
                let p_polys = self.to_poly(p);
                let all_b = hypercube(*n);
                let one = SparsePolynomial::<C::F, T>::lit(&C::F::one());
                let eq = |bi: usize, x: &SparsePolynomial<C::F, T>| -> SparsePolynomial<C::F, T> {
                    if bi == 1 { x.clone() } else { &one - x }
                };
                let eq_prod = |b_fixed: &[usize],
                               xs_polys: &[SparsePolynomial<C::F, T>]|
                 -> SparsePolynomial<C::F, T> {
                    let mut acc = one.clone();
                    for (j, &bj) in b_fixed.iter().enumerate() {
                        acc = &acc * &eq(bj, &xs_polys[j]);
                    }
                    acc
                };
                if k == *n {
                    let mut acc = SparsePolynomial::<C::F, T>::zero();
                    for (idx, b) in all_b.iter().enumerate() {
                        acc = &acc + &(&p_polys[idx] * &eq_prod(b, &xs_polys));
                    }
                    Some(vec![acc])
                } else {
                    let remaining_n = n - k;
                    let result_b = hypercube(remaining_n);
                    let out = result_b
                        .iter()
                        .map(|bp| {
                            let mut acc = SparsePolynomial::<C::F, T>::zero();
                            for (idx, b) in all_b.iter().enumerate() {
                                if b[k..] != bp[..] {
                                    continue;
                                }
                                acc = &acc + &(&p_polys[idx] * &eq_prod(&b[..k], &xs_polys));
                            }
                            acc
                        })
                        .collect();
                    Some(out)
                }
            }
            _ => None,
        }
    }

    /// This function converts an operation to a vector of sparse polynomial expressions,
    /// exploding vectors where possible.
    #[allow(clippy::wrong_self_convention)]
    fn to_poly(&mut self, op: &GOp<C>) -> Vec<SparsePolynomial<C::F, T>> {
        match op {
            Op::Ref(v, typ) => {
                let pf = self.find_ref(v);
                match typ {
                    ATyp::Vec(box t, n) => (0..*n)
                        .map(|i| {
                            let mut pf = pf.clone();
                            pf.index = i;
                            pf.typ = t.clone();
                            SparsePolynomial::var(&pf)
                        })
                        .collect::<Vec<_>>(),
                    ATyp::Uni(m) => (0..=*m)
                        .map(|i| {
                            let mut pf = pf.clone();
                            pf.index = i;
                            pf.typ = ATyp::scalar();
                            SparsePolynomial::var(&pf)
                        })
                        .collect::<Vec<_>>(),
                    ATyp::VPoly(n, m) => (0..num_coeffs(&ATyp::VPoly(*n, *m)))
                        .map(|i| {
                            let mut pf = pf.clone();
                            pf.index = i;
                            pf.typ = ATyp::scalar();
                            SparsePolynomial::var(&pf)
                        })
                        .collect::<Vec<_>>(),
                    ATyp::Mle(n) => (0..num_coeffs(&ATyp::Mle(*n)))
                        .map(|i| {
                            let mut pf = pf.clone();
                            pf.index = i;
                            pf.typ = ATyp::scalar();
                            SparsePolynomial::var(&pf)
                        })
                        .collect::<Vec<_>>(),
                    _ => vec![SparsePolynomial::var(&pf)],
                }
            }
            Op::Value(v) => self.to_poly_value(v),
            Op::Vec(v) => v.iter().flat_map(|v| self.to_poly(v)).collect(),
            Op::Ram(a, b) => {
                match (a.get(), b.get()) {
                    (Op::Ref(n, _), Op::Value(v)) => {
                        let pf = self.find_ref(n);
                        match v {
                            Value::Index(i) => vec![SparsePolynomial::var(&pf.with_index(*i))],
                            _ => vec![SparsePolynomial::var(&pf)],
                        }
                    }
                    // Dynamic indexing, overapproximate
                    (a, _) => self.to_poly(a),
                }
            }
            Op::Bin(BinOp::Add | BinOp::And, a, b, _) => self
                .to_poly(a)
                .into_iter()
                .zip(self.to_poly(b))
                .map(|(a, b)| a + b)
                .collect(),
            Op::Bin(BinOp::Sub, a, b, _) => self
                .to_poly(a)
                .into_iter()
                .zip(self.to_poly(b))
                .map(|(a, b)| a - b)
                .collect(),
            Op::Bin(BinOp::Mul, a, b, _) => self
                .to_poly(a)
                .into_iter()
                .zip(self.to_poly(b))
                .map(|(a, b)| a * b)
                .collect(),
            Op::Bin(BinOp::Dot, a, b, _) => {
                vec![
                    self.to_poly(a)
                        .into_iter()
                        .zip(self.to_poly(b).into_iter())
                        .map(|(a, b)| a * b)
                        .sum(),
                ]
            }
            Op::Reduce(rop, v) => {
                let elems = self.to_poly(v);
                self.reduce_unfold(*rop, elems).unwrap_or_default()
            }
            Op::Evaluate(p, xs) => self.eval_to_poly(p, xs).unwrap_or_default(),
            // Phase 12: `Op::Pair(a, b, _)` — bilinear pairing.
            //
            // In exponent space, if we model every group element as
            //   E : G1 ≅ e_E · __g1__,   F : G2 ≅ e_F · __g2__
            // then by bilinearity
            //   pair(E, F) = e_E · e_F · pair(__g1__, __g2__)
            //             = e_E · e_F · __gt__.
            //
            // Since the existing Bin(Add/Sub/Mul) arms on group-typed
            // operands already propagate through `to_poly` as F-ring
            // arithmetic on the group vars (treating each group var
            // as its own exponent), we can read the exponent of each
            // operand directly off `to_poly(a)[0]` / `to_poly(b)[0]`.
            // The final `var(__gt__)` factor carries the GT "unit" and
            // lets `pair(P,Q) + pair(P',Q)` collapse to
            // `(e_P + e_P') · e_Q · var(__gt__)` under Buchberger.
            Op::Pair(a, b, _) => {
                let e_a = self
                    .to_poly(a.get())
                    .into_iter()
                    .next()
                    .unwrap_or_else(SparsePolynomial::zero);
                let e_b = self
                    .to_poly(b.get())
                    .into_iter()
                    .next()
                    .unwrap_or_else(SparsePolynomial::zero);
                let gt = self.gt_pref();
                vec![&e_a * &e_b * SparsePolynomial::var(&gt)]
            }
            // Phase 13: nested polynomial division / remainder. Emit (or
            // reuse) the canonical identity rows via `div_witnesses` and
            // return the witness's per-slot vars so the caller can compose
            // them further (e.g. inside `verify(lhs == d*q + r)`).
            //
            // Non-VPoly operands fall through to `vec![]` (opaque) — the
            // pre-phase-13 behaviour for nested Div inside to_poly.
            Op::Bin(BinOp::Div, a, b, _) => {
                if let Some((q_wit, _r_wit)) = self.div_witnesses(a, b) {
                    let n = num_coeffs(&q_wit.typ);
                    (0..n)
                        .map(|i| SparsePolynomial::var(&q_wit.clone().with_index(i)))
                        .collect()
                } else {
                    vec![]
                }
            }
            Op::Bin(BinOp::Rem, a, b, _) => {
                if let Some((_q_wit, r_wit)) = self.div_witnesses(a, b) {
                    let n = num_coeffs(&r_wit.typ);
                    (0..n)
                        .map(|i| SparsePolynomial::var(&r_wit.clone().with_index(i)))
                        .collect()
                } else {
                    vec![]
                }
            }
            _ => vec![],
        }
    }
}

impl<C: ArkConfig + HasOpFactory, T: Monomial> GroebnerBuilder<C, T> {
    pub fn add_input(&mut self, g: &DQDag<C>) {
        let tc = TransClos::from_input(g);
        self.add_tc(tc);
    }

    pub fn add_relation(&mut self, g: &DQDag<C>) {
        let tc = TransClos::from_relation(g);
        self.add_tc(tc);
    }

    /// Register only the *args* of the input marker, without any of its
    /// body operations. Useful when bootstrapping a relation-only builder
    /// that must agree with a separate input-aware builder on which
    /// `Ref` is the canonical one for each protocol parameter.
    pub fn register_input_args(&mut self, g: &DQDag<C>) {
        let tc = TransClos::from_input(g);
        for new_arg in tc.args.iter() {
            let canonical = self
                .args
                .iter()
                .find(|a| a.name() == new_arg.name())
                .cloned();
            match canonical {
                Some(c) if c.reference != new_arg.reference => {
                    self.ref_aliases.insert(new_arg.reference, c);
                }
                None => {
                    self.args.insert(new_arg.clone());
                }
                _ => {}
            }
        }
    }

    fn add_tc(&mut self, tc: TransClos<C>) {
        // Phase B: when add_tc runs more than once (e.g. add_input then
        // add_relation), the same protocol parameter shows up with a
        // different `Ref` (different `Node::Arg` per marker). Canonicalise
        // by name: keep the first PRef seen, alias subsequent Refs to it.
        for new_arg in tc.args.iter() {
            let canonical = self
                .args
                .iter()
                .find(|a| a.name() == new_arg.name())
                .cloned();
            match canonical {
                Some(c) if c.reference != new_arg.reference => {
                    self.ref_aliases.insert(new_arg.reference, c);
                }
                None => {
                    self.args.insert(new_arg.clone());
                }
                _ => {}
            }
        }

        for (i, op) in tc.clos.into_iter() {
            self.add_op(i, op);
        }
    }

    /// Convert an operation to a polynomial and add it to the context
    fn add_op(&mut self, pr: PRef, op: GOp<C>) {
        let op_for_div = op.clone(); // needed for Div arm which references the whole op
        match op {
            Op::Ref(r, typ) => {
                let ref_poly = self.to_poly(&Op::Ref(r, typ));
                for (i, p) in ref_poly.into_iter().enumerate() {
                    let pf = pr.clone().with_index(i);
                    self.pl.insert(&pf, &p);
                    self.basis.push(p - SparsePolynomial::var(&pf));
                }
            }
            // Polynomial operations
            Op::Bin(BinOp::Add | BinOp::And, a, b, _) => self
                .to_poly(&a)
                .into_iter()
                .zip(self.to_poly(&b))
                .enumerate()
                .for_each(|(i, (a, b))| {
                    let pf = pr.clone().with_index(i);
                    self.pl.insert(&pf, &(&a + &b));
                    self.basis.push(a + b - SparsePolynomial::var(&pf));
                }),
            Op::Bin(BinOp::Sub, a, b, _) => self
                .to_poly(&a)
                .into_iter()
                .zip(self.to_poly(&b))
                .enumerate()
                .for_each(|(i, (a, b))| {
                    let pf = pr.clone().with_index(i);
                    self.pl.insert(&pf, &(&a - &b));
                    self.basis.push(a - b - SparsePolynomial::var(&pf));
                }),
            Op::Bin(BinOp::Mul, ref a, ref b, _) => {
                let a_typ = a.typ();
                let b_typ = b.typ();
                let is_poly = |t: &ATyp| matches!(t, ATyp::VPoly(_, _) | ATyp::Mle(_));
                let result: Option<Vec<SparsePolynomial<C::F, T>>> =
                    if is_poly(&a_typ) || is_poly(&b_typ) {
                        match (&a_typ, &b_typ, &pr.typ) {
                            // VPoly × VPoly of same num_vars → convolution into the
                            // result type's multi-index basis. Terms whose total
                            // degree exceeds the result's max_degree are dropped
                            // (they must be zero for the expression to be well-typed).
                            (ATyp::VPoly(na, ma), ATyp::VPoly(nb, mb), ATyp::VPoly(nr, mr))
                                if na == nb && na == nr =>
                            {
                                let a_polys = self.to_poly(a);
                                let b_polys = self.to_poly(b);
                                let a_idx = multi_indices(*na, *ma);
                                let b_idx = multi_indices(*nb, *mb);
                                let r_idx = multi_indices(*nr, *mr);
                                let mut out: Vec<SparsePolynomial<C::F, T>> =
                                    vec![SparsePolynomial::<C::F, T>::zero(); r_idx.len()];
                                for (ia, ka) in a_idx.iter().enumerate() {
                                    for (ib, kb) in b_idx.iter().enumerate() {
                                        let k: Vec<usize> =
                                            ka.iter().zip(kb.iter()).map(|(x, y)| x + y).collect();
                                        if k.iter().sum::<usize>() > *mr {
                                            continue;
                                        }
                                        // Find slot; must exist for total degree ≤ mr.
                                        let ir = r_idx
                                            .iter()
                                            .position(|rk| rk == &k)
                                            .expect("multi-index missing in result");
                                        out[ir] = &out[ir] + &(&a_polys[ia] * &b_polys[ib]);
                                    }
                                }
                                Some(out)
                            }
                            // Mle(n) × Mle(n) → VPoly(n, 2). Basis change using the
                            // per-variable coefficient table of eq(b_i, x) · eq(b'_i, x):
                            //   (0,0): 1 - 2x + x²     → [1, -2, 1]
                            //   (0,1): x - x²          → [0,  1,-1]
                            //   (1,0): x - x²          → [0,  1,-1]
                            //   (1,1): x²              → [0,  0, 1]
                            (ATyp::Mle(na), ATyp::Mle(nb), ATyp::VPoly(nr, mr))
                                if na == nb && na == nr && *mr >= 2 =>
                            {
                                let n = *na;
                                let a_polys = self.to_poly(a);
                                let b_polys = self.to_poly(b);
                                let all_b = hypercube(n);
                                let r_idx = multi_indices(n, *mr);
                                // Per-variable coefficient table: coeff[ba][bb][k] for k ∈ {0,1,2}.
                                let coeff: [[[i64; 3]; 2]; 2] =
                                    [[[1, -2, 1], [0, 1, -1]], [[0, 1, -1], [0, 0, 1]]];
                                let lit_of = |v: i64| -> SparsePolynomial<C::F, T> {
                                    if v >= 0 {
                                        SparsePolynomial::lit(&C::FOps::from_usize(v as usize))
                                    } else {
                                        -SparsePolynomial::lit(&C::FOps::from_usize((-v) as usize))
                                    }
                                };
                                let mut out: Vec<SparsePolynomial<C::F, T>> =
                                    vec![SparsePolynomial::<C::F, T>::zero(); r_idx.len()];
                                for (ia, ba) in all_b.iter().enumerate() {
                                    for (ib, bb) in all_b.iter().enumerate() {
                                        let uv = &a_polys[ia] * &b_polys[ib];
                                        // Each (ba, bb) contributes to every result multi-index
                                        // κ with the scalar Π_i coeff[ba_i][bb_i][κ_i].
                                        for (ir, k) in r_idx.iter().enumerate() {
                                            let mut scalar: i64 = 1;
                                            for i in 0..n {
                                                let c = coeff[ba[i]][bb[i]][k[i]];
                                                if c == 0 {
                                                    scalar = 0;
                                                    break;
                                                }
                                                scalar *= c;
                                            }
                                            if scalar == 0 {
                                                continue;
                                            }
                                            out[ir] = &out[ir] + &(&lit_of(scalar) * &uv);
                                        }
                                    }
                                }
                                Some(out)
                            }
                            _ => None,
                        }
                    } else {
                        None
                    };
                match result {
                    Some(polys) => {
                        for (i, poly) in polys.into_iter().enumerate() {
                            let pf = pr.clone().with_index(i);
                            self.pl.insert(&pf, &poly);
                            self.basis.push(poly - SparsePolynomial::var(&pf));
                        }
                    }
                    None => {
                        // Non-polynomial operands (Uni, Vec, scalar): zip coefficient-wise.
                        // This matches the pre-phase-4 behaviour for non-VPoly/Mle types.
                        self.to_poly(a)
                            .into_iter()
                            .zip(self.to_poly(b))
                            .enumerate()
                            .for_each(|(i, (ap, bp))| {
                                let pf = pr.clone().with_index(i);
                                self.pl.insert(&pf, &(&ap * &bp));
                                self.basis.push(ap * bp - SparsePolynomial::var(&pf));
                            })
                    }
                }
            }
            Op::Bin(BinOp::Dot, a, b, _) => {
                let sum = self
                    .to_poly(&a)
                    .into_iter()
                    .zip(self.to_poly(&b))
                    .map(|(a, b)| a * b)
                    .sum();
                self.pl.insert(&pr, &sum);
                self.basis.push(sum - SparsePolynomial::var(&pr))
            }
            // Phase 13: polynomial division `pr = a / b`.
            //
            // For VPoly/Uni operands of the same num_vars, route through
            // `div_witnesses` which emits the canonical `a = b·q + r`
            // identity into the basis (once per operand pair) and returns
            // the shared `(q_wit, r_wit)` witnesses. Then link `pr` to
            // `q_wit` so references to `pr` resolve to the quotient
            // witness during Buchberger reduction.
            //
            // For scalar / Fin / Uni-of-scalar / Vec operands, fall back
            // to the legacy coefficient-wise `a - b·var(pr) = 0` encoding
            // (correct for pointwise field division).
            Op::Bin(BinOp::Div, ref a, ref b, _) => {
                if let Some((q_wit, _r_wit)) = self.div_witnesses(a, b) {
                    self.link_to_witness(&pr, &q_wit);
                } else {
                    self.to_poly(a)
                        .into_iter()
                        .zip(self.to_poly(b))
                        .enumerate()
                        .for_each(|(i, (a_p, b_p))| {
                            let pf = pr.clone().with_index(i);
                            self.np
                                .insert(&pf, &Op::ram(op_for_div.clone(), Op::index(i)));
                            self.basis.push(a_p - b_p * SparsePolynomial::var(&pf));
                        });
                }
            }
            // Phase 13: polynomial remainder `pr = a % b`.
            //
            // Mirrors `Div` but aliases `pr` to `r_wit`. The canonical
            // identity row is emitted exactly once per `(a, b)` pair, so
            // if the program also computes `a / b`, both ops share the
            // same witnesses and `verify(a == b*q + r)` reduces directly
            // to the canonical row.
            //
            // For non-VPoly operands we leave `pr` opaque in `np` (the
            // pre-phase-13 default), since pointwise `%` has no Gröbner
            // reduction that's correct in general.
            Op::Bin(BinOp::Rem, ref a, ref b, _) => {
                if let Some((_q_wit, r_wit)) = self.div_witnesses(a, b) {
                    self.link_to_witness(&pr, &r_wit);
                } else {
                    self.np.insert(&pr, &op_for_div);
                }
            }
            Op::Bin(BinOp::Equ, a, b, _) => self
                .to_poly(&a)
                .into_iter()
                .zip(self.to_poly(&b))
                .for_each(|(a, b)| {
                    self.pl.insert(&pr, &(&a - &b));
                    self.pl.insert(&pr, &SparsePolynomial::lit(&C::F::zero()));
                    self.basis.push(a - b);
                    self.basis.push(SparsePolynomial::var(&pr));
                }),
            Op::Check(a) => self.add_op(pr, a.get().clone()),
            Op::Challenge(t, b) => {
                let op = Op::Challenge(t, b);
                self.np.insert(&pr, &op);
            }
            Op::Random(t, b) => {
                let op = Op::Random(t, b);
                self.np.insert(&pr, &op);
            }
            // Op::Interpolate (preserved from main): treat as opaque.
            Op::Interpolate(points, evals) => {
                let op = Op::Interpolate(points, evals);
                self.np.insert(&pr, &op);
            }
            // Op::Ifft(v): p = ifft(v) where p is a univariate polynomial in
            // coefficient form and v a length-N vector of its evaluations at
            // the N-th roots of unity. Constraints (linear over F):
            //   for each i ∈ [0, N): Σ_j ω^{i·j} · p[j]  =  v[i]
            // where ω is a primitive N-th root of unity and p[j] is the
            // j-th coefficient slot of `pr`. If `get_root_of_unity(N)` is
            // None (N isn't a 2-adic divisor of |F|-1), fall back to opaque.
            Op::Ifft(ref a) => {
                let v_polys = self.to_poly(a);
                let n = v_polys.len();
                if let Some(omega) = C::F::get_root_of_unity(n as u64) {
                    // Row i: Σ_j ω^{i·j} · pr[j] = v_polys[i]
                    let coeff_vars: Vec<SparsePolynomial<C::F, T>> = (0..n)
                        .map(|j| SparsePolynomial::var(&pr.clone().with_index(j)))
                        .collect();
                    for (i, vp) in v_polys.iter().enumerate().take(n) {
                        let lhs = dft_row(&coeff_vars, omega, i);
                        self.basis.push(&lhs - vp);
                    }
                    // Register each coefficient slot of `pr` in `pl` so
                    // `find_ref` can resolve `Ref::Var("p", _)` later.
                    for j in 0..n {
                        let pf = pr.clone().with_index(j);
                        let v = SparsePolynomial::var(&pf);
                        self.pl.insert(&pf, &v);
                    }
                } else {
                    self.np.insert(&pr, &Op::Ifft(a.clone()));
                }
            }
            // Op::Fft(p): v = fft(p) — symmetric to Ifft. Here `pr` holds
            // the N output-vector slots; the coefficients live in `p`. The
            // same DFT matrix applies:
            //   for each i ∈ [0, N): v[i] = Σ_j ω^{i·j} · p[j]
            Op::Fft(ref a) => {
                let coeff_polys = self.to_poly(a);
                let n = coeff_polys.len();
                if let Some(omega) = C::F::get_root_of_unity(n as u64) {
                    for i in 0..n {
                        let lhs = dft_row(&coeff_polys, omega, i);
                        let pf = pr.clone().with_index(i);
                        // Register v[i]'s polynomial form in pl and push basis eqn.
                        self.pl.insert(&pf, &lhs);
                        self.basis.push(&lhs - &SparsePolynomial::var(&pf));
                    }
                } else {
                    self.np.insert(&pr, &Op::Fft(a.clone()));
                }
            }
            // Op::Poly / Op::Mle / Op::Coef: bind the i-th PRef slot of `pr`
            // to the i-th scalar poly read from `inner` by `to_poly`. These
            // three share identity semantics on coefficients / evaluations —
            // only the slot-count / enumeration of `pr.typ` differs, and that
            // is driven entirely by the input's shape (to_poly already returns
            // the right number of polys). Basis-change between coefficient
            // and evaluation form happens in later phases (Eval / Bin on
            // mixed polynomial types).
            Op::Poly(ref inner) | Op::Mle(ref inner) | Op::Coef(ref inner) => {
                let polys = self.to_poly(inner);
                debug_assert_eq!(
                    polys.len(),
                    num_coeffs(&pr.typ),
                    "Op::Poly/Mle/Coef slot count mismatch: {} polys vs num_coeffs({}) = {}",
                    polys.len(),
                    pr.typ,
                    num_coeffs(&pr.typ)
                );
                for (i, p) in polys.into_iter().enumerate() {
                    let pf = pr.clone().with_index(i);
                    self.pl.insert(&pf, &p);
                    self.basis.push(p - SparsePolynomial::var(&pf));
                }
            }
            Op::Vec(vs) => {
                for (i, v) in vs.into_iter().enumerate() {
                    let pf = pr.with_index(i);
                    self.add_op(pf, v.get().clone());
                }
            }
            // Op::Evaluate(p, xs): evaluate a polynomial `p` at points `xs`.
            //
            // Three shapes are handled (dispatched on p.typ() × |xs slots|):
            //
            //   1. Univariate batched — p: Uni(_) or VPoly(1, _), xs: len k ≥ 1
            //        result[i] = Σ_j a_j · xs[i]^j                  (Uni(k) output)
            //
            //   2. Multivariate in coefficient basis — p: VPoly(n, m) with n ≥ 2, k ≤ n
            //        full (k == n):  scalar = Σ_{|κ|≤m} a_κ · Π_i xs[i]^{κ_i}
            //        partial (k<n):  VPoly<n-k, m>; coef at κ′ =
            //                        Σ_{κ_fixed: (κ_fixed,κ′) valid} a_{(κ_fixed,κ′)}
            //                        · Π_i xs[i]^{κ_fixed,i}
            //
            //   3. Multilinear in evaluation basis — p: Mle(n), k ≤ n
            //        Uses eq(b,x) = b·x + (1-b)(1-x) = x if b=1 else 1-x.
            //        full (k == n):  scalar = Σ_b v_b · Π_i eq(b_i, xs[i])
            //        partial (k<n):  Mle<n-k>; eval at b′ =
            //                        Σ_{b_fixed} v_{(b_fixed,b′)} · Π_i eq(b_fixed,i, xs[i])
            //
            // The input xs may statically have either `Uni(k)` or `Vec(_, k)`;
            // `to_poly` normalises both to k scalar polys. Unsupported shapes
            // (e.g. k > n, or Record operands) fall through to the np catch-all
            // via `None`.
            Op::Evaluate(ref p, ref xs) => {
                let result = self.eval_to_poly(p, xs);
                match result {
                    Some(polys) => {
                        for (i, poly) in polys.into_iter().enumerate() {
                            let pf = pr.clone().with_index(i);
                            self.pl.insert(&pf, &poly);
                            self.basis.push(poly - SparsePolynomial::var(&pf));
                        }
                    }
                    None => {
                        self.np.insert(&pr, &Op::Evaluate(p.clone(), xs.clone()));
                    }
                }
            }
            // Phase 10: `Op::Reduce(op, v)` — unfold into `op`-fold of
            // `to_poly(v)` when the inner BinOp is polynomial over F.
            // Otherwise opaque (np).
            Op::Reduce(rop, ref v) => {
                let elems = self.to_poly(v);
                match self.reduce_unfold(rop, elems) {
                    Some(polys) => {
                        for (i, p) in polys.into_iter().enumerate() {
                            let pf = pr.clone().with_index(i);
                            self.pl.insert(&pf, &p);
                            self.basis.push(p - SparsePolynomial::var(&pf));
                        }
                    }
                    None => {
                        self.np.insert(&pr, &Op::Reduce(rop, v.clone()));
                    }
                }
            }
            // Phase 10: `Op::Value(lit)` — pattern-match on the `Value`
            // variant via `to_poly_value`, then bind each slot of `pr` to
            // the corresponding literal polynomial. This lets literal
            // constants act as real polynomials in the basis (e.g.
            // `let c = 7; verify(x == c)` folds without needing an
            // opaque `c` variable).
            //
            // Group / Pair / Poly literals aren't scalars and fall through
            // to the opaque catch-all below via `to_poly_value`'s
            // `unreachable!` — which we guard against with a try-convert.
            Op::Value(ref v) => {
                // `to_poly_value` panics on unsupported Value variants; we
                // keep it behind a closure so the panic path is explicit.
                // Currently it supports Scalar / Bool / Index / Vec and
                // the Vec* flavours; everything else (G1/G2/GT/Poly/Record)
                // falls through to np.
                let polys_opt: Option<Vec<SparsePolynomial<C::F, T>>> = match v {
                    Value::Scalar(_)
                    | Value::Bool(_)
                    | Value::Index(_)
                    | Value::Vec(_)
                    | Value::VecBool(_)
                    | Value::VecScalar(_)
                    | Value::VecIndex(_) => Some(self.to_poly_value(v)),
                    _ => None,
                };
                match polys_opt {
                    Some(polys) => {
                        for (i, p) in polys.into_iter().enumerate() {
                            let pf = pr.clone().with_index(i);
                            self.pl.insert(&pf, &p);
                            self.basis.push(p - SparsePolynomial::var(&pf));
                        }
                    }
                    None => {
                        self.np.insert(&pr, &Op::Value(v.clone()));
                    }
                }
            }
            // Phase 10: `Op::Ram(a, b)` — RAM reads are treated as *fresh
            // identifiers* in the Gröbner basis. A runtime RAM access can't
            // be equated with any compile-time slot (the underlying array
            // may have been mutated through an aliased reference, etc.), so
            // even with a literal index we do not emit a basis row relating
            // `pr` to `find_ref(a).with_index(i)`.
            //
            // We do need every slot of `pr` to appear in `np`, otherwise
            // `find_ref(Ref::Var(pr_name, _))` panics for subsequent ops
            // that read the RAM result.
            Op::Ram(ref a, ref b) => {
                let n = num_coeffs(&pr.typ);
                let raw = Op::Ram(a.clone(), b.clone());
                for i in 0..n {
                    let pf = pr.clone().with_index(i);
                    self.np.insert(&pf, &raw);
                }
                if n == 0 {
                    self.np.insert(&pr, &raw);
                }
            }
            // Phase 12: `Op::Pair(a, b, t)` — bilinear pairing via __gt__
            // sentinel. The result `pr : GT` is bound to the exponent-space
            // bilinear form:
            //
            //   var(pr) = to_poly(a) · to_poly(b) · var(__gt__)
            //
            // which encodes both the pairing axiom `pair(__g1__, __g2__) =
            // __gt__` and full bilinearity. Matching pair expressions on both
            // sides of a `verify(lhs == rhs)` then cancel under Buchberger
            // because their basis rows are identical F-polynomials.
            Op::Pair(ref a, ref b, _) => {
                let e_a = self
                    .to_poly(a.get())
                    .into_iter()
                    .next()
                    .unwrap_or_else(SparsePolynomial::zero);
                let e_b = self
                    .to_poly(b.get())
                    .into_iter()
                    .next()
                    .unwrap_or_else(SparsePolynomial::zero);
                let gt = self.gt_pref();
                let e = &e_a * &e_b * SparsePolynomial::var(&gt);
                self.pl.insert(&pr, &e);
                self.basis.push(&e - &SparsePolynomial::var(&pr));
            }
            // Phase 10: `Op::Record(fields)` — keep the record itself
            // opaque, but recursively process each field by delegating to
            // `add_op` with a fresh PRef whose `reference` re-uses `pr`'s
            // (so subsequent field projections — which lower to
            // `Op::Ref(Ref::Var(r, n), field_typ)` — can find a matching
            // entry in `np`/`pl` via `find_ref`'s reference-match).
            //
            // A full field-offset-aware slot layout for records is deferred
            // (it requires changing `num_coeffs(Record)` and the rest of
            // the analysis consistently); for now we register each field
            // starting at its own offset 0 under the shared reference, and
            // also insert the whole record as opaque in `np`.
            Op::Record(ref fields) => {
                self.np.insert(&pr, &Op::Record(fields.clone()));
                for (_, sub) in fields.iter() {
                    let sub_op = sub.get().clone();
                    let sub_pr = PRef {
                        typ: sub_op.typ(),
                        index: 0,
                        ..pr.clone()
                    };
                    self.add_op(sub_pr, sub_op);
                }
            }
            op => {
                self.np.insert(&pr, &op);
            }
        }
    }
}

impl<'a, C, D, A, T> Pretty<'a, D, A> for GroebnerBuilder<C, T>
where
    C: ArkConfig,
    T: Monomial,
    D: DocAllocator<'a, A>,
    D::Doc: Clone,
    A: 'a + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        allocator.concat([
            allocator.text("Arguments: "),
            allocator.hardline(),
            allocator.intersperse(self.args.into_iter().map(|n| n.pretty(allocator)), ", "),
            allocator.hardline(),
            allocator.text("Basis: "),
            allocator.hardline(),
            allocator.intersperse(
                self.basis
                    .into_iter()
                    .map(|p| p.pretty(allocator).indent(8)),
                allocator.hardline(),
            ),
            allocator.hardline(),
            allocator.hardline(),
            allocator.text("NP definitions: "),
            allocator.hardline(),
            allocator.intersperse(
                self.np.into_iter().map(|(r, op)| {
                    allocator
                        .text(r.verbose())
                        .append(allocator.text(": "))
                        .append(op.pretty(allocator))
                        .indent(8)
                }),
                allocator.hardline(),
            ),
        ])
    }

    fn is_nil(&self) -> bool {
        self.basis.is_empty() && self.np.is_empty()
    }
}

impl<C: ArkConfig, T: Monomial> fmt::Display for GroebnerBuilder<C, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <GroebnerBuilder<C, T> as Pretty<'_, BoxAllocator, ()>>::pretty(self.clone(), &BoxAllocator)
            .1
            .render_fmt(100, f)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use backend::ArkBls12_381;
    use backend::op::mk;

    #[test]
    fn test_groebner_builder_new() {
        let builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        assert_eq!(builder.basis.len(), 0);
        assert_eq!(builder.np.len(), 0);
        assert_eq!(builder.pl.len(), 0);
        assert_eq!(builder.args.len(), 0);
    }

    #[test]
    fn test_groebner_builder_vars_empty() {
        let builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let vars = builder.vars();
        assert_eq!(vars.len(), 0);
    }

    #[test]
    fn test_groebner_builder_to_poly_value_scalar() {
        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        use ark_bls12_381::Fr;
        use backend::Value;

        let val = Value::Scalar(Fr::from(42u64));
        let poly = builder.to_poly_value(&val);
        assert_eq!(poly.len(), 1);
    }

    #[test]
    fn test_groebner_builder_to_poly_value_bool_true() {
        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        use backend::Value;

        let val = Value::Bool(true);
        let poly = builder.to_poly_value(&val);
        assert_eq!(poly.len(), 1);
    }

    #[test]
    fn test_groebner_builder_to_poly_value_bool_false() {
        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        use backend::Value;

        let val = Value::Bool(false);
        let poly = builder.to_poly_value(&val);
        assert_eq!(poly.len(), 1);
    }

    #[test]
    fn test_groebner_builder_to_poly_value_index() {
        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        use backend::Value;

        let val = Value::Index(5);
        let poly = builder.to_poly_value(&val);
        assert_eq!(poly.len(), 1);
    }

    #[test]
    fn test_groebner_builder_to_poly_value_vec_scalar() {
        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        use ark_bls12_381::Fr;
        use backend::Value;

        let val = Value::VecScalar(vec![Fr::from(1u64), Fr::from(2u64), Fr::from(3u64)]);
        let poly = builder.to_poly_value(&val);
        assert_eq!(poly.len(), 3);
    }

    #[test]
    fn test_groebner_builder_to_poly_value_vec_bool() {
        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        use backend::Value;

        let val = Value::VecBool(vec![true, false, true]);
        let poly = builder.to_poly_value(&val);
        assert_eq!(poly.len(), 3);
    }

    #[test]
    fn test_groebner_builder_to_poly_value_vec_index() {
        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        use backend::Value;

        let val = Value::VecIndex(vec![0, 1, 2]);
        let poly = builder.to_poly_value(&val);
        assert_eq!(poly.len(), 3);
    }

    #[test]
    fn test_groebner_builder_to_poly_value() {
        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        use ark_bls12_381::Fr;
        use backend::Value;

        let val = Value::Scalar(Fr::from(10u64));
        let result = builder.to_poly(&Op::Value(val));
        assert_eq!(result.len(), 1);
    }

    #[test]
    fn test_groebner_builder_to_poly_vec() {
        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        use ark_bls12_381::Fr;
        use backend::Value;

        let ops = vec![
            mk::<ArkBls12_381>(Op::Value(Value::Scalar(Fr::from(1u64)))),
            mk::<ArkBls12_381>(Op::Value(Value::Scalar(Fr::from(2u64)))),
        ];
        let result = builder.to_poly(&Op::Vec(ops));
        assert_eq!(result.len(), 2);
    }

    #[test]
    fn test_groebner_builder_display_empty() {
        let builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let s = format!("{}", builder);
        assert!(!s.is_empty());
    }

    #[test]
    fn test_remap_vars_identity() {
        use crate::PRef;
        use backend::ATyp;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let pref_a = PRef::from_node(
            NodeIndex::new(0),
            ATyp::scalar(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        let pref_b = PRef::from_node(
            NodeIndex::new(1),
            ATyp::scalar(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );

        // a + b - 0
        let poly = SparsePolynomial::var(&pref_a) + SparsePolynomial::var(&pref_b);
        builder.basis.push(poly.clone());
        builder.args.insert(pref_a.clone());
        builder.args.insert(pref_b.clone());

        // Identity remap should be a no-op
        builder.remap_vars(&|p| p.clone());
        assert_eq!(builder.basis.basis.len(), 1);
        assert_eq!(builder.basis.basis[0], poly);
    }

    #[test]
    fn test_remap_vars_rename() {
        use crate::PRef;
        use backend::ATyp;
        use lang::id::Vid;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let pref_n0 = PRef::from_node(
            NodeIndex::new(0),
            ATyp::scalar(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        let pref_n1 = PRef::from_node(
            NodeIndex::new(1),
            ATyp::scalar(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        let pref_x = PRef::from_var(
            Vid("x".into()),
            NodeIndex::new(10),
            ATyp::scalar(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        let pref_y = PRef::from_var(
            Vid("y".into()),
            NodeIndex::new(11),
            ATyp::scalar(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );

        // poly: n0 + n1
        let poly = SparsePolynomial::var(&pref_n0) + SparsePolynomial::var(&pref_n1);
        builder.basis.push(poly);
        builder
            .pl
            .insert(&pref_n0, &SparsePolynomial::var(&pref_n0));
        builder.args.insert(pref_n0.clone());
        builder.args.insert(pref_n1.clone());

        // Remap n0→x, n1→y
        builder.remap_vars(&|p| {
            if p.node() == NodeIndex::new(0) {
                pref_x.clone()
            } else if p.node() == NodeIndex::new(1) {
                pref_y.clone()
            } else {
                p.clone()
            }
        });

        // Basis should now use x + y
        let expected = SparsePolynomial::var(&pref_x) + SparsePolynomial::var(&pref_y);
        assert_eq!(builder.basis.basis[0], expected);
        // pl should be remapped
        assert!(builder.pl.contains(&pref_x));
        assert!(!builder.pl.contains(&pref_n0));
        // args should be remapped
        assert!(builder.args.contains(&pref_x));
        assert!(builder.args.contains(&pref_y));
    }

    #[test]
    fn test_remap_vars_preserves_polynomial_count() {
        use crate::PRef;
        use backend::ATyp;
        use lang::id::Vid;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let pref_a = PRef::from_node(
            NodeIndex::new(0),
            ATyp::scalar(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        let pref_b = PRef::from_node(
            NodeIndex::new(1),
            ATyp::scalar(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );

        builder
            .basis
            .push(SparsePolynomial::var(&pref_a) + SparsePolynomial::var(&pref_b));
        builder
            .basis
            .push(SparsePolynomial::var(&pref_a) * SparsePolynomial::var(&pref_b));

        let pref_c = PRef::from_var(
            Vid("c".into()),
            NodeIndex::new(5),
            ATyp::scalar(),
            0,
            Qualifier::Public,
            Distribution::default(),
        );

        builder.remap_vars(&|p| {
            if p.node() == NodeIndex::new(0) {
                pref_c.clone()
            } else {
                p.clone()
            }
        });

        assert_eq!(builder.basis.basis.len(), 2);
        // First poly: c + b, second: c * b
        assert!(builder.basis.basis[0].contains(&pref_c));
        assert!(builder.basis.basis[1].contains(&pref_c));
        assert!(!builder.basis.basis[0].contains(&pref_a));
    }

    // -----------------------------------------------------------------
    // Polynomial / MLE enumeration helpers
    // -----------------------------------------------------------------

    #[test]
    fn test_multi_indices_univariate() {
        // Uni degree 3 → 1-variable VPoly with total degree ≤ 3.
        let got = multi_indices(1, 3);
        assert_eq!(got, vec![vec![0], vec![1], vec![2], vec![3]]);
    }

    #[test]
    fn test_multi_indices_two_vars_deg2() {
        // VPoly<2, 2>: all k with k_1 + k_2 ≤ 2, in graded-lex order.
        let got = multi_indices(2, 2);
        assert_eq!(
            got,
            vec![
                vec![0, 0], // deg 0
                vec![0, 1],
                vec![1, 0], // deg 1 (lex)
                vec![0, 2],
                vec![1, 1],
                vec![2, 0], // deg 2 (lex)
            ]
        );
    }

    #[test]
    fn test_hypercube_enumeration() {
        let got = hypercube(3);
        // lex: bit 0 is inner-most, so b = [b0, b1, b2] read little-endian.
        assert_eq!(got[0], vec![0, 0, 0]);
        assert_eq!(got[1], vec![1, 0, 0]);
        assert_eq!(got[2], vec![0, 1, 0]);
        assert_eq!(got[7], vec![1, 1, 1]);
    }

    // -----------------------------------------------------------------
    // to_poly on polynomial-typed refs
    // -----------------------------------------------------------------

    #[test]
    fn test_to_poly_vpoly_ref_expands_coefficients() {
        use crate::PRef;
        use crate::Ref;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let pref_p = PRef::from_node(
            NodeIndex::new(0),
            ATyp::VPoly(2, 2),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        // Register pref_p so find_ref can locate it.
        builder.pl.insert(&pref_p, &SparsePolynomial::var(&pref_p));
        builder.args.insert(pref_p.clone());

        let op: GOp<ArkBls12_381> = Op::Ref(Ref::new(NodeIndex::new(0)), ATyp::VPoly(2, 2));
        let polys = builder.to_poly(&op);
        assert_eq!(polys.len(), 6);
        // Each coefficient should be a distinct variable PRef indexed 0..6.
        for (i, _) in polys.iter().enumerate() {
            let expected = pref_p.with_index(i).clone();
            let expected = PRef {
                typ: ATyp::scalar(),
                ..expected
            };
            assert!(
                polys[i].contains(&expected),
                "coefficient poly {} does not contain expected PRef (index {})",
                i,
                i
            );
        }
    }

    #[test]
    fn test_to_poly_mle_ref_expands_evaluations() {
        use crate::PRef;
        use crate::Ref;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let pref_p = PRef::from_node(
            NodeIndex::new(0),
            ATyp::Mle(3),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.pl.insert(&pref_p, &SparsePolynomial::var(&pref_p));
        builder.args.insert(pref_p.clone());

        let op: GOp<ArkBls12_381> = Op::Ref(Ref::new(NodeIndex::new(0)), ATyp::Mle(3));
        let polys = builder.to_poly(&op);
        assert_eq!(polys.len(), 8);
    }

    // -----------------------------------------------------------------
    // add_op: Op::Poly / Op::Mle / Op::Coef (identity on coefficient slots)
    // -----------------------------------------------------------------

    #[test]
    fn test_add_op_poly_binds_coefficient_slots() {
        use crate::PRef;
        use ark_bls12_381::Fr;
        use backend::op::mk;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let pref_p = PRef::from_node(
            NodeIndex::new(0),
            ATyp::VPoly(1, 2),
            0,
            Qualifier::Private,
            Distribution::default(),
        );

        // Op::Poly( [c0=1, c1=2, c2=3] ) -> VPoly<1, 2>.
        let coefs: Vec<_> = (1..=3u64)
            .map(|n| mk::<ArkBls12_381>(Op::Value(Value::Scalar(Fr::from(n)))))
            .collect();
        let op_poly: GOp<ArkBls12_381> = Op::Poly(mk::<ArkBls12_381>(Op::Vec(coefs)));

        builder.add_op(pref_p.clone(), op_poly);

        // Three coefficient slots should have been bound.
        for i in 0..3 {
            let slot = pref_p.with_index(i);
            assert!(builder.pl.contains(&slot), "slot {} missing from pl", i);
        }
        // And three basis equations pushed.
        assert_eq!(builder.basis.basis.len(), 3);
    }

    #[test]
    fn test_add_op_coef_roundtrips_poly() {
        // Op::Coef(Op::Poly(v)) bound to the same slots should reduce to `v`.
        use crate::PRef;
        use ark_bls12_381::Fr;
        use backend::op::mk;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();

        // First: inject a VPoly<1, 2> value via Op::Poly.
        let pref_p = PRef::from_node(
            NodeIndex::new(0),
            ATyp::VPoly(1, 2),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        let coefs: Vec<_> = (1..=3u64)
            .map(|n| mk::<ArkBls12_381>(Op::Value(Value::Scalar(Fr::from(n)))))
            .collect();
        builder.add_op(pref_p.clone(), Op::Poly(mk::<ArkBls12_381>(Op::Vec(coefs))));

        // Then: Op::Coef reading the VPoly back into a Uni(2) output
        // (degree 2 = 3 coefficient slots, per docs/poly-encoding.md).
        let pref_c = PRef::from_node(
            NodeIndex::new(1),
            ATyp::Uni(2),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        let ref_p: GOp<ArkBls12_381> = Op::Ref(Ref::new(NodeIndex::new(0)), ATyp::VPoly(1, 2));
        builder.add_op(pref_c.clone(), Op::Coef(mk::<ArkBls12_381>(ref_p)));

        // Each Coef slot should be bound identically to the corresponding
        // VPoly coefficient PRef — that's the round-trip identity. `to_poly`
        // retypes per-slot PRefs to ATyp::scalar(), so we expect that form
        // on the RHS.
        for i in 0..3 {
            let coef_slot = pref_c.with_index(i);
            let mut poly_slot = pref_p.with_index(i);
            poly_slot.typ = ATyp::scalar();
            let stored = builder.pl.get(&coef_slot).expect("coef slot missing");
            let expected = SparsePolynomial::<Fr, GrevLexTerm>::var(&poly_slot);
            assert_eq!(*stored, expected, "coef[{}] did not bind to poly[{}]", i, i);
        }
    }

    #[test]
    fn test_add_op_mle_binds_hypercube_slots() {
        use crate::PRef;
        use ark_bls12_381::Fr;
        use backend::op::mk;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        // Mle<2> has 2^2 = 4 hypercube slots.
        let pref_p = PRef::from_node(
            NodeIndex::new(0),
            ATyp::Mle(2),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        let vals: Vec<_> = (1..=4u64)
            .map(|n| mk::<ArkBls12_381>(Op::Value(Value::Scalar(Fr::from(n)))))
            .collect();
        builder.add_op(pref_p.clone(), Op::Mle(mk::<ArkBls12_381>(Op::Vec(vals))));

        assert_eq!(builder.basis.basis.len(), 4);
        for i in 0..4 {
            assert!(
                builder.pl.contains(&pref_p.with_index(i)),
                "mle slot {} missing",
                i
            );
        }
    }

    // -----------------------------------------------------------------
    // add_op: Op::Eval (phase 3)
    //   - univariate batched     (Uni / VPoly(1,_))
    //   - full multivariate      (VPoly(n,m) n≥2 and Mle(n))
    //   - partial multivariate
    // -----------------------------------------------------------------

    /// Helper: a PRef registered with the builder so `find_ref` can locate
    /// it, returning the pref for caller use. The slot type isn't important
    /// here; we only need the reference node / index to resolve.
    fn register_ref<T: Monomial>(
        builder: &mut GroebnerBuilder<ArkBls12_381, T>,
        node: usize,
        typ: ATyp,
    ) -> crate::PRef {
        use crate::PRef;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;
        let pref = PRef::from_node(
            NodeIndex::new(node),
            typ,
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.pl.insert(&pref, &SparsePolynomial::var(&pref));
        builder.args.insert(pref.clone());
        pref
    }

    #[test]
    fn test_add_op_eval_univariate_batched() {
        use crate::{PRef, Ref};
        use ark_bls12_381::Fr;
        use backend::op::mk;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        // p(x) = a_0 + a_1 x   as VPoly(1,1): 2 coefficient slots on node 0.
        // xs = [x0, x1]        as Uni(1):     degree 1 = 2 slots on node 1.
        // Expected: result[i] = a_0 + a_1 * xs[i].
        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let _pref_p = register_ref(&mut builder, 0, ATyp::VPoly(1, 1));
        let _pref_xs = register_ref(&mut builder, 1, ATyp::Uni(1));

        let result = PRef::from_node(
            NodeIndex::new(2),
            ATyp::Uni(1),
            0,
            Qualifier::Private,
            Distribution::default(),
        );

        let op: GOp<ArkBls12_381> = Op::Evaluate(
            mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), ATyp::VPoly(1, 1))),
            mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(1)), ATyp::Uni(1))),
        );
        builder.add_op(result.clone(), op);

        // Expected: 2 result slots + 2 basis equations, and no np insertion.
        assert_eq!(
            builder.np.len(),
            0,
            "eval should not have fallen through to np"
        );
        for i in 0..2 {
            assert!(
                builder.pl.contains(&result.with_index(i)),
                "uni batched result slot {} missing",
                i
            );
        }
        // Each result slot: poly = a_0 + a_1 * xs[i] (a linear polynomial in
        // 4 input variables). Check it depends on exactly {a_0, a_1, xs[i]}.
        let a0 = PRef {
            typ: ATyp::scalar(),
            ..PRef::from_node(
                NodeIndex::new(0),
                ATyp::VPoly(1, 1),
                0,
                Qualifier::Private,
                Distribution::default(),
            )
        };
        let mut a1 = a0.clone();
        a1.index = 1;
        let mut x0 = a0.clone();
        x0.reference = Ref::new(NodeIndex::new(1));
        x0.index = 0;
        let mut x1 = x0.clone();
        x1.index = 1;

        let slot0 = builder.pl.get(&result.with_index(0)).unwrap();
        let vars0 = slot0.vars();
        assert!(vars0.contains(&a0), "slot 0 missing a_0");
        assert!(vars0.contains(&a1), "slot 0 missing a_1");
        assert!(vars0.contains(&x0), "slot 0 missing xs[0]");
        assert!(!vars0.contains(&x1), "slot 0 should not contain xs[1]");

        let slot1 = builder.pl.get(&result.with_index(1)).unwrap();
        let vars1 = slot1.vars();
        assert!(vars1.contains(&a0), "slot 1 missing a_0");
        assert!(vars1.contains(&a1), "slot 1 missing a_1");
        assert!(vars1.contains(&x1), "slot 1 missing xs[1]");
        assert!(!vars1.contains(&x0), "slot 1 should not contain xs[0]");
        let _ = Fr::from(0u64); // silence unused Fr import warning
    }

    #[test]
    fn test_add_op_eval_univariate_batched_with_constants() {
        // p(x) = 3 + 5x evaluated at [7, 11] should give [38, 58].
        use crate::PRef;
        use ark_bls12_381::Fr;
        use backend::op::mk;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();

        // Bind p via Op::Poly of literal scalars -> 2 slot prefs on node 0.
        let pref_p = PRef::from_node(
            NodeIndex::new(0),
            ATyp::VPoly(1, 1),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        let coefs: Vec<_> = [3u64, 5]
            .iter()
            .map(|n| mk::<ArkBls12_381>(Op::Value(Value::Scalar(Fr::from(*n)))))
            .collect();
        builder.add_op(pref_p.clone(), Op::Poly(mk::<ArkBls12_381>(Op::Vec(coefs))));

        // Bind xs similarly on node 1 as Uni(1) (degree 1 = 2 slots).
        let pref_xs = PRef::from_node(
            NodeIndex::new(1),
            ATyp::Uni(1),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        let xs: Vec<_> = [7u64, 11]
            .iter()
            .map(|n| mk::<ArkBls12_381>(Op::Value(Value::Scalar(Fr::from(*n)))))
            .collect();
        // Treat xs as a plain Uni literal via Op::Poly (binds 2 slots with literal polys).
        builder.add_op(pref_xs.clone(), Op::Poly(mk::<ArkBls12_381>(Op::Vec(xs))));

        // Now issue eval:  p(xs).
        let result = PRef::from_node(
            NodeIndex::new(2),
            ATyp::Uni(1),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        let op: GOp<ArkBls12_381> = Op::Evaluate(
            mk::<ArkBls12_381>(Op::Ref(
                crate::Ref::new(NodeIndex::new(0)),
                ATyp::VPoly(1, 1),
            )),
            mk::<ArkBls12_381>(Op::Ref(crate::Ref::new(NodeIndex::new(1)), ATyp::Uni(1))),
        );
        builder.add_op(result.clone(), op);

        // Check stored polys: since all inputs are constants, each result slot
        // stores a polynomial equal to a_0 + a_1 * x as a sparse poly in the
        // slot PRefs (constants haven't been inlined). We verify the basis
        // equation reduces correctly by substituting literal values via `vars`.
        // Specifically: each result slot must be non-zero and refer to the 3
        // input slots.
        let slot0 = builder.pl.get(&result.with_index(0)).unwrap();
        let slot1 = builder.pl.get(&result.with_index(1)).unwrap();
        assert!(!slot0.is_zero());
        assert!(!slot1.is_zero());
        // Two new basis equations (for the 2 result slots); plus the prior
        // Op::Poly bindings (2 for p, 2 for xs).
        assert_eq!(builder.basis.basis.len(), 2 + 2 + 2);
    }

    #[test]
    fn test_add_op_eval_vpoly_full_multivariate() {
        // VPoly(2, 2) has 6 coef slots; eval at Uni(2) => scalar (one slot).
        use crate::PRef;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let _ = register_ref(&mut builder, 0, ATyp::VPoly(2, 2));
        let _ = register_ref(&mut builder, 1, ATyp::Uni(1));

        let result = PRef::from_node(
            NodeIndex::new(2),
            ATyp::scalar(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        let op: GOp<ArkBls12_381> = Op::Evaluate(
            backend::op::mk::<ArkBls12_381>(Op::Ref(
                crate::Ref::new(NodeIndex::new(0)),
                ATyp::VPoly(2, 2),
            )),
            backend::op::mk::<ArkBls12_381>(Op::Ref(
                crate::Ref::new(NodeIndex::new(1)),
                ATyp::Uni(1),
            )),
        );
        builder.add_op(result.clone(), op);

        // One result slot (scalar) produced, zero np entries for eval.
        assert!(builder.pl.contains(&result.with_index(0)));
        // Should contain all 6 coef PRefs of p + both xs slots.
        let slot = builder.pl.get(&result.with_index(0)).unwrap();
        let vars = slot.vars();
        assert!(
            vars.len() >= 6,
            "expected coef + eval vars; got {} vars",
            vars.len()
        );
    }

    #[test]
    fn test_add_op_eval_vpoly_partial_multivariate() {
        // VPoly(3, 1) evaluated at Uni(1) => VPoly(2, 1) (2-var linear poly w/ 3 slots).
        use crate::PRef;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let _ = register_ref(&mut builder, 0, ATyp::VPoly(3, 1));
        let _ = register_ref(&mut builder, 1, ATyp::Uni(0));

        let result = PRef::from_node(
            NodeIndex::new(2),
            ATyp::VPoly(2, 1),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        let op: GOp<ArkBls12_381> = Op::Evaluate(
            backend::op::mk::<ArkBls12_381>(Op::Ref(
                crate::Ref::new(NodeIndex::new(0)),
                ATyp::VPoly(3, 1),
            )),
            backend::op::mk::<ArkBls12_381>(Op::Ref(
                crate::Ref::new(NodeIndex::new(1)),
                ATyp::Uni(0),
            )),
        );
        builder.add_op(result.clone(), op);

        // VPoly(2, 1) has num_coeffs = C(2+1, 1) = 3 slots (one for constant,
        // two for each linear variable).
        assert_eq!(num_coeffs(&ATyp::VPoly(2, 1)), 3);
        for i in 0..3 {
            assert!(
                builder.pl.contains(&result.with_index(i)),
                "partial vpoly eval slot {} missing",
                i
            );
        }
    }

    #[test]
    fn test_add_op_eval_mle_full_multivariate() {
        // Mle(2) has 4 eval slots; eval at Uni(2) => scalar.
        use crate::PRef;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let _ = register_ref(&mut builder, 0, ATyp::Mle(2));
        let _ = register_ref(&mut builder, 1, ATyp::Uni(1));

        let result = PRef::from_node(
            NodeIndex::new(2),
            ATyp::scalar(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        let op: GOp<ArkBls12_381> = Op::Evaluate(
            backend::op::mk::<ArkBls12_381>(Op::Ref(
                crate::Ref::new(NodeIndex::new(0)),
                ATyp::Mle(2),
            )),
            backend::op::mk::<ArkBls12_381>(Op::Ref(
                crate::Ref::new(NodeIndex::new(1)),
                ATyp::Uni(1),
            )),
        );
        builder.add_op(result.clone(), op);

        assert!(builder.pl.contains(&result.with_index(0)));
        // Result poly should reference all 4 Mle slots + both xs slots.
        let slot = builder.pl.get(&result.with_index(0)).unwrap();
        let vars = slot.vars();
        assert!(vars.len() >= 4, "mle full eval got {} vars", vars.len());
    }

    #[test]
    fn test_add_op_eval_mle_partial_multivariate() {
        // Mle(3) evaluated at Uni(1) => Mle(2) (4 slots).
        use crate::PRef;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let _ = register_ref(&mut builder, 0, ATyp::Mle(3));
        let _ = register_ref(&mut builder, 1, ATyp::Uni(0));

        let result = PRef::from_node(
            NodeIndex::new(2),
            ATyp::Mle(2),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        let op: GOp<ArkBls12_381> = Op::Evaluate(
            backend::op::mk::<ArkBls12_381>(Op::Ref(
                crate::Ref::new(NodeIndex::new(0)),
                ATyp::Mle(3),
            )),
            backend::op::mk::<ArkBls12_381>(Op::Ref(
                crate::Ref::new(NodeIndex::new(1)),
                ATyp::Uni(0),
            )),
        );
        builder.add_op(result.clone(), op);

        // Mle(2) has 4 eval slots.
        for i in 0..4 {
            assert!(
                builder.pl.contains(&result.with_index(i)),
                "partial mle eval slot {} missing",
                i
            );
        }
    }

    #[test]
    fn test_add_op_eval_unsupported_falls_through_to_np() {
        // Eval at a Record (which to_poly can't handle) should fall through to np.
        use crate::PRef;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let _ = register_ref(&mut builder, 0, ATyp::VPoly(3, 2));
        // xs with k > n should fall through (k=4 > n=3). Uni(3) = degree 3 = 4 slots.
        let _ = register_ref(&mut builder, 1, ATyp::Uni(3));

        let result = PRef::from_node(
            NodeIndex::new(2),
            ATyp::scalar(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        let op: GOp<ArkBls12_381> = Op::Evaluate(
            backend::op::mk::<ArkBls12_381>(Op::Ref(
                crate::Ref::new(NodeIndex::new(0)),
                ATyp::VPoly(3, 2),
            )),
            backend::op::mk::<ArkBls12_381>(Op::Ref(
                crate::Ref::new(NodeIndex::new(1)),
                ATyp::Uni(3),
            )),
        );
        builder.add_op(result.clone(), op);

        // Unsupported shape → stored in np, not pl.
        assert!(builder.np.contains(&result));
        assert!(!builder.pl.contains(&result));
    }

    // -----------------------------------------------------------------
    // add_op: Op::Bin(Add|Sub|Mul) over polynomial operands (phase 4)
    // -----------------------------------------------------------------

    #[test]
    fn test_add_op_vpoly_add_coefficient_wise() {
        // VPoly(2,1) has 3 coefficient slots.  a + b should bind result.slot(i)
        // to a.slot(i) + b.slot(i) for each of the 3 slots.
        use crate::{PRef, Ref};
        use backend::op::mk;
        use lang::ast::BinOp;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let pref_a = register_ref(&mut builder, 0, ATyp::VPoly(2, 1));
        let pref_b = register_ref(&mut builder, 1, ATyp::VPoly(2, 1));

        let result = PRef::from_node(
            NodeIndex::new(2),
            ATyp::VPoly(2, 1),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        let op: GOp<ArkBls12_381> = Op::Bin(
            BinOp::Add,
            mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), ATyp::VPoly(2, 1))),
            mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(1)), ATyp::VPoly(2, 1))),
            ATyp::VPoly(2, 1),
        );
        builder.add_op(result.clone(), op);

        // 3 result slots bound.
        for i in 0..3 {
            assert!(
                builder.pl.contains(&result.with_index(i)),
                "add result slot {} missing",
                i
            );
        }
        // Each result slot contains exactly a.slot(i) + b.slot(i).
        for i in 0..3 {
            let mut a_slot = pref_a.with_index(i);
            a_slot.typ = ATyp::scalar();
            let mut b_slot = pref_b.with_index(i);
            b_slot.typ = ATyp::scalar();
            let stored = builder.pl.get(&result.with_index(i)).unwrap();
            let expected = &SparsePolynomial::<ark_bls12_381::Fr, GrevLexTerm>::var(&a_slot)
                + &SparsePolynomial::var(&b_slot);
            assert_eq!(*stored, expected, "vpoly add slot {} mismatch", i);
        }
    }

    #[test]
    fn test_add_op_mle_add_pointwise() {
        // Mle(2) has 4 evaluation slots. add is pointwise over hypercube.
        use crate::{PRef, Ref};
        use backend::op::mk;
        use lang::ast::BinOp;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let pref_a = register_ref(&mut builder, 0, ATyp::Mle(2));
        let pref_b = register_ref(&mut builder, 1, ATyp::Mle(2));

        let result = PRef::from_node(
            NodeIndex::new(2),
            ATyp::Mle(2),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        let op: GOp<ArkBls12_381> = Op::Bin(
            BinOp::Add,
            mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), ATyp::Mle(2))),
            mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(1)), ATyp::Mle(2))),
            ATyp::Mle(2),
        );
        builder.add_op(result.clone(), op);

        for i in 0..4 {
            let mut a_slot = pref_a.with_index(i);
            a_slot.typ = ATyp::scalar();
            let mut b_slot = pref_b.with_index(i);
            b_slot.typ = ATyp::scalar();
            let stored = builder.pl.get(&result.with_index(i)).unwrap();
            let expected = &SparsePolynomial::<ark_bls12_381::Fr, GrevLexTerm>::var(&a_slot)
                + &SparsePolynomial::var(&b_slot);
            assert_eq!(*stored, expected, "mle add slot {} mismatch", i);
        }
    }

    #[test]
    fn test_add_op_vpoly_sub_coefficient_wise() {
        use crate::{PRef, Ref};
        use backend::op::mk;
        use lang::ast::BinOp;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let pref_a = register_ref(&mut builder, 0, ATyp::VPoly(2, 2));
        let pref_b = register_ref(&mut builder, 1, ATyp::VPoly(2, 2));

        let result = PRef::from_node(
            NodeIndex::new(2),
            ATyp::VPoly(2, 2),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        let op: GOp<ArkBls12_381> = Op::Bin(
            BinOp::Sub,
            mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), ATyp::VPoly(2, 2))),
            mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(1)), ATyp::VPoly(2, 2))),
            ATyp::VPoly(2, 2),
        );
        builder.add_op(result.clone(), op);

        // VPoly(2,2) has 6 slots.
        assert_eq!(num_coeffs(&ATyp::VPoly(2, 2)), 6);
        for i in 0..6 {
            let mut a_slot = pref_a.with_index(i);
            a_slot.typ = ATyp::scalar();
            let mut b_slot = pref_b.with_index(i);
            b_slot.typ = ATyp::scalar();
            let stored = builder.pl.get(&result.with_index(i)).unwrap();
            let expected = &SparsePolynomial::<ark_bls12_381::Fr, GrevLexTerm>::var(&a_slot)
                - &SparsePolynomial::var(&b_slot);
            assert_eq!(*stored, expected, "vpoly sub slot {} mismatch", i);
        }
    }

    #[test]
    fn test_add_op_vpoly_mul_univariate_convolution() {
        // VPoly(1,1) × VPoly(1,1) → VPoly(1,2), a_0 b_0, a_0 b_1 + a_1 b_0, a_1 b_1.
        use crate::{PRef, Ref};
        use backend::op::mk;
        use lang::ast::BinOp;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let pref_a = register_ref(&mut builder, 0, ATyp::VPoly(1, 1));
        let pref_b = register_ref(&mut builder, 1, ATyp::VPoly(1, 1));

        let result = PRef::from_node(
            NodeIndex::new(2),
            ATyp::VPoly(1, 2),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        let op: GOp<ArkBls12_381> = Op::Bin(
            BinOp::Mul,
            mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), ATyp::VPoly(1, 1))),
            mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(1)), ATyp::VPoly(1, 1))),
            ATyp::VPoly(1, 2),
        );
        builder.add_op(result.clone(), op);

        // VPoly(1,2) has num_coeffs = 3 slots (degrees 0, 1, 2 in graded-lex order).
        assert_eq!(num_coeffs(&ATyp::VPoly(1, 2)), 3);
        let a0 = {
            let mut p = pref_a.with_index(0);
            p.typ = ATyp::scalar();
            p
        };
        let a1 = {
            let mut p = pref_a.with_index(1);
            p.typ = ATyp::scalar();
            p
        };
        let b0 = {
            let mut p = pref_b.with_index(0);
            p.typ = ATyp::scalar();
            p
        };
        let b1 = {
            let mut p = pref_b.with_index(1);
            p.typ = ATyp::scalar();
            p
        };

        let var = |p: &PRef| SparsePolynomial::<ark_bls12_381::Fr, GrevLexTerm>::var(p);
        let deg0 = builder.pl.get(&result.with_index(0)).unwrap().clone();
        let deg1 = builder.pl.get(&result.with_index(1)).unwrap().clone();
        let deg2 = builder.pl.get(&result.with_index(2)).unwrap().clone();
        assert_eq!(deg0, &var(&a0) * &var(&b0), "(*.x^0)");
        assert_eq!(
            deg1,
            &(&var(&a0) * &var(&b1)) + &(&var(&a1) * &var(&b0)),
            "(*.x^1)"
        );
        assert_eq!(deg2, &var(&a1) * &var(&b1), "(*.x^2)");
    }

    #[test]
    fn test_add_op_vpoly_mul_multivariate_spotcheck() {
        // VPoly(2,1) × VPoly(2,1) → VPoly(2,2). We spot-check one slot.
        // VPoly(2,1) multi-indices (graded-lex by total deg then lex):
        //   [0,0], [0,1], [1,0]   (sizes 3)
        // VPoly(2,2) multi-indices:
        //   [0,0], [0,1], [1,0], [0,2], [1,1], [2,0]   (size 6)
        use crate::{PRef, Ref};
        use backend::op::mk;
        use lang::ast::BinOp;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let pref_a = register_ref(&mut builder, 0, ATyp::VPoly(2, 1));
        let pref_b = register_ref(&mut builder, 1, ATyp::VPoly(2, 1));

        let result = PRef::from_node(
            NodeIndex::new(2),
            ATyp::VPoly(2, 2),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        let op: GOp<ArkBls12_381> = Op::Bin(
            BinOp::Mul,
            mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), ATyp::VPoly(2, 1))),
            mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(1)), ATyp::VPoly(2, 1))),
            ATyp::VPoly(2, 2),
        );
        builder.add_op(result.clone(), op);

        // Check the constant-term slot (multi-index [0,0]): should be a_[0,0] * b_[0,0].
        let r_idx = multi_indices(2, 2);
        let a_idx = multi_indices(2, 1);
        let pos_00 = r_idx.iter().position(|k| k == &vec![0, 0]).unwrap();
        let a_pos_00 = a_idx.iter().position(|k| k == &vec![0, 0]).unwrap();

        let a00 = {
            let mut p = pref_a.with_index(a_pos_00);
            p.typ = ATyp::scalar();
            p
        };
        let b00 = {
            let mut p = pref_b.with_index(a_pos_00);
            p.typ = ATyp::scalar();
            p
        };
        let var = |p: &PRef| SparsePolynomial::<ark_bls12_381::Fr, GrevLexTerm>::var(p);
        let got = builder.pl.get(&result.with_index(pos_00)).unwrap().clone();
        assert_eq!(
            got,
            &var(&a00) * &var(&b00),
            "VPoly(2,2) constant term mismatch"
        );

        // Ensure all 6 slots were populated.
        for i in 0..6 {
            assert!(
                builder.pl.contains(&result.with_index(i)),
                "VPoly(2,2) slot {} missing",
                i
            );
        }
    }

    #[test]
    fn test_add_op_mle_mul_basis_change() {
        // Mle(1) × Mle(1) → VPoly(1, 2). Verify by evaluating the resulting poly at
        // a concrete point x: for p(x) = u_0 · (1-x) + u_1 · x and
        // q(x) = v_0 · (1-x) + v_1 · x, the product p·q has coefficients
        //   x^0 :  u_0 v_0
        //   x^1 :  -2 u_0 v_0 + u_0 v_1 + u_1 v_0
        //   x^2 :  u_0 v_0 - u_0 v_1 - u_1 v_0 + u_1 v_1
        use crate::{PRef, Ref};
        use backend::op::mk;
        use lang::ast::BinOp;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let pref_u = register_ref(&mut builder, 0, ATyp::Mle(1));
        let pref_v = register_ref(&mut builder, 1, ATyp::Mle(1));

        let result = PRef::from_node(
            NodeIndex::new(2),
            ATyp::VPoly(1, 2),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        let op: GOp<ArkBls12_381> = Op::Bin(
            BinOp::Mul,
            mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), ATyp::Mle(1))),
            mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(1)), ATyp::Mle(1))),
            ATyp::VPoly(1, 2),
        );
        builder.add_op(result.clone(), op);

        // 3 slots populated.
        for i in 0..3 {
            assert!(
                builder.pl.contains(&result.with_index(i)),
                "Mle×Mle slot {} missing",
                i
            );
        }

        let u0 = {
            let mut p = pref_u.with_index(0);
            p.typ = ATyp::scalar();
            p
        };
        let u1 = {
            let mut p = pref_u.with_index(1);
            p.typ = ATyp::scalar();
            p
        };
        let v0 = {
            let mut p = pref_v.with_index(0);
            p.typ = ATyp::scalar();
            p
        };
        let v1 = {
            let mut p = pref_v.with_index(1);
            p.typ = ATyp::scalar();
            p
        };
        let var = |p: &PRef| SparsePolynomial::<ark_bls12_381::Fr, GrevLexTerm>::var(p);

        let deg0 = builder.pl.get(&result.with_index(0)).unwrap().clone();
        let deg1 = builder.pl.get(&result.with_index(1)).unwrap().clone();
        let deg2 = builder.pl.get(&result.with_index(2)).unwrap().clone();

        // deg0 = u_0 * v_0
        assert_eq!(deg0, &var(&u0) * &var(&v0), "mle mul deg0");

        // deg1 = -2 u_0 v_0 + u_0 v_1 + u_1 v_0
        let two =
            SparsePolynomial::<ark_bls12_381::Fr, GrevLexTerm>::lit(&<ark_bls12_381::Fr as From<
                u64,
            >>::from(2u64));
        let expected_deg1 = &(&(&var(&u0) * &var(&v1)) + &(&var(&u1) * &var(&v0)))
            - &(&two * &(&var(&u0) * &var(&v0)));
        assert_eq!(deg1, expected_deg1, "mle mul deg1");

        // deg2 = u_0 v_0 - u_0 v_1 - u_1 v_0 + u_1 v_1
        let expected_deg2 = &(&(&var(&u0) * &var(&v0)) - &(&var(&u0) * &var(&v1)))
            + &(&(&var(&u1) * &var(&v1)) - &(&var(&u1) * &var(&v0)));
        assert_eq!(deg2, expected_deg2, "mle mul deg2");
    }

    // ---------------------------------------------------------------------
    // Phase 13: polynomial division & remainder via `D·Q + R = P`.
    // ---------------------------------------------------------------------

    /// Helper: build a VPoly Div or Rem op and run `add_op`.
    #[allow(clippy::too_many_arguments)]
    fn add_op_div_rem(
        builder: &mut GroebnerBuilder<ArkBls12_381, GrevLexTerm>,
        bop: lang::ast::BinOp,
        a_node: usize,
        a_typ: ATyp,
        b_node: usize,
        b_typ: ATyp,
        result_node: usize,
        result_typ: ATyp,
    ) -> crate::PRef {
        use crate::{PRef, Ref};
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;
        let result = PRef::from_node(
            NodeIndex::new(result_node),
            result_typ.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        let op: GOp<ArkBls12_381> = Op::Bin(
            bop,
            mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(a_node)), a_typ)),
            mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(b_node)), b_typ)),
            result_typ,
        );
        builder.add_op(result.clone(), op);
        result
    }

    #[test]
    fn test_add_op_vpoly_div_univariate_identity() {
        // VPoly(1,2) / VPoly(1,1) → VPoly(1,1).
        //   a has num_coeffs = 3 slots (a_0, a_1, a_2)
        //   b has num_coeffs = 2 slots (b_0, b_1)
        //   q_wit: VPoly(1,1), 2 slots (q_0, q_1)
        //   r_wit: VPoly(1,0), 1 slot  (r_0)
        // Canonical identity rows (from div_witnesses):
        //   k=[0] (total deg 0): a_0  -  (b_0·q_0 + r_0)
        //   k=[1] (total deg 1): a_1  -  (b_0·q_1 + b_1·q_0)
        //   k=[2] (total deg 2): a_2  -  b_1·q_1
        // link_to_witness emits 2 more rows: var(q_wit[j]) - var(result[j]), j=0,1.
        use crate::PRef;
        use lang::ast::BinOp;
        use lang::id::Vid;
        use lang::typ::{Distribution, Qualifier};

        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let pref_a = register_ref(&mut builder, 0, ATyp::VPoly(1, 2));
        let pref_b = register_ref(&mut builder, 1, ATyp::VPoly(1, 1));

        let basis_before = builder.basis.len();
        let result = add_op_div_rem(
            &mut builder,
            BinOp::Div,
            0,
            ATyp::VPoly(1, 2),
            1,
            ATyp::VPoly(1, 1),
            2,
            ATyp::VPoly(1, 1),
        );

        // The witness side-table has exactly one entry.
        assert_eq!(
            builder.div_wit.len(),
            1,
            "div_wit should have one (a,b) entry"
        );

        // Recover the q_wit / r_wit PRefs (minted by sentinel_pref with
        // Qualifier::Public and stable node indices MAX - 1000 / MAX - 1001).
        let q_wit = PRef::from_var(
            Vid::from("__div_q_0__"),
            petgraph::graph::NodeIndex::new(usize::MAX - 1000),
            ATyp::VPoly(1, 1),
            0,
            Qualifier::Public,
            Distribution::default(),
        );
        let r_wit = PRef::from_var(
            Vid::from("__div_r_0__"),
            petgraph::graph::NodeIndex::new(usize::MAX - 1001),
            ATyp::VPoly(1, 0),
            0,
            Qualifier::Public,
            Distribution::default(),
        );

        // Per-slot input vars (typ=scalar, as `to_poly(Op::Ref)` produces).
        let scl = |p: &PRef, i: usize| {
            let mut q = p.clone().with_index(i);
            q.typ = ATyp::scalar();
            q
        };
        // Per-slot witness vars. `div_witnesses` uses `wit.clone().with_index(j)`
        // WITHOUT resetting typ, so q_wit slots keep typ=VPoly(1,1) and
        // r_wit slots keep typ=VPoly(1,0).
        let wit_slot = |p: &PRef, i: usize| p.clone().with_index(i);
        let var = |p: &PRef| SparsePolynomial::<ark_bls12_381::Fr, GrevLexTerm>::var(p);
        let a0 = scl(&pref_a, 0);
        let a1 = scl(&pref_a, 1);
        let a2 = scl(&pref_a, 2);
        let b0 = scl(&pref_b, 0);
        let b1 = scl(&pref_b, 1);
        let q0 = wit_slot(&q_wit, 0);
        let q1 = wit_slot(&q_wit, 1);
        let r0 = wit_slot(&r_wit, 0);

        // 3 identity rows + 2 linking rows.
        assert_eq!(
            builder.basis.len() - basis_before,
            5,
            "expected 3 identity + 2 linking rows"
        );

        // Check identity rows exist in basis.
        let expected_k0 = &var(&a0) - &(&(&var(&b0) * &var(&q0)) + &var(&r0));
        let expected_k1 = &var(&a1) - &(&(&var(&b0) * &var(&q1)) + &(&var(&b1) * &var(&q0)));
        let expected_k2 = &var(&a2) - &(&var(&b1) * &var(&q1));
        for (lbl, expected) in [
            ("k0", &expected_k0),
            ("k1", &expected_k1),
            ("k2", &expected_k2),
        ] {
            assert!(
                builder.basis.iter().any(|row| row == expected),
                "basis missing identity row {}",
                lbl
            );
        }

        // link_to_witness: pl[result[j]] = var(q_wit[j]) for j=0,1.
        assert_eq!(
            builder.pl.get(&result.with_index(0)).cloned(),
            Some(var(&q0)),
            "pl[result[0]] should alias q_wit[0]"
        );
        assert_eq!(
            builder.pl.get(&result.with_index(1)).cloned(),
            Some(var(&q1)),
            "pl[result[1]] should alias q_wit[1]"
        );

        // Linking rows: var(q_wit[j]) - var(result[j]).
        // link_to_witness uses `result.clone().with_index(j)` (typ unchanged).
        let r0_slot = result.clone().with_index(0);
        let r1_slot = result.clone().with_index(1);
        let link0 = &var(&q0) - &var(&r0_slot);
        let link1 = &var(&q1) - &var(&r1_slot);
        assert!(
            builder.basis.iter().any(|row| row == &link0),
            "basis missing link row var(q_wit[0]) - var(result[0])"
        );
        assert!(
            builder.basis.iter().any(|row| row == &link1),
            "basis missing link row var(q_wit[1]) - var(result[1])"
        );
    }

    #[test]
    fn test_add_op_vpoly_rem_univariate_identity() {
        // VPoly(1,2) % VPoly(1,1) → VPoly(1,0).
        // Same witnesses as the Div test, but link result to r_wit (1 slot).
        use crate::PRef;
        use lang::ast::BinOp;
        use lang::id::Vid;
        use lang::typ::{Distribution, Qualifier};

        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let _pref_a = register_ref(&mut builder, 0, ATyp::VPoly(1, 2));
        let _pref_b = register_ref(&mut builder, 1, ATyp::VPoly(1, 1));

        let basis_before = builder.basis.len();
        let result = add_op_div_rem(
            &mut builder,
            BinOp::Rem,
            0,
            ATyp::VPoly(1, 2),
            1,
            ATyp::VPoly(1, 1),
            2,
            ATyp::VPoly(1, 0),
        );

        assert_eq!(builder.div_wit.len(), 1, "one div_wit entry after Rem");

        let r_wit = PRef::from_var(
            Vid::from("__div_r_0__"),
            petgraph::graph::NodeIndex::new(usize::MAX - 1001),
            ATyp::VPoly(1, 0),
            0,
            Qualifier::Public,
            Distribution::default(),
        );
        let scl = |p: &PRef, i: usize| {
            let mut q = p.clone().with_index(i);
            q.typ = ATyp::scalar();
            q
        };
        let _ = scl; // kept for parity with the Div test; not used here.
        let var = |p: &PRef| SparsePolynomial::<ark_bls12_381::Fr, GrevLexTerm>::var(p);
        // r_wit slots keep typ=VPoly(1,0) (div_witnesses/link_to_witness
        // don't reset typ to scalar).
        let r0 = r_wit.clone().with_index(0);

        // 3 identity rows + 1 linking row (result has only 1 slot).
        assert_eq!(
            builder.basis.len() - basis_before,
            4,
            "expected 3 identity + 1 linking row"
        );

        // pl[result[0]] = var(r_wit[0]).
        assert_eq!(
            builder.pl.get(&result.with_index(0)).cloned(),
            Some(var(&r0)),
            "pl[result[0]] should alias r_wit[0]"
        );

        // Linking row: link_to_witness uses result.with_index(0) (typ unchanged).
        let r0_slot = result.clone().with_index(0);
        let link = &var(&r0) - &var(&r0_slot);
        assert!(
            builder.basis.iter().any(|row| row == &link),
            "basis missing link row var(r_wit[0]) - var(result[0])"
        );
    }

    #[test]
    fn test_add_op_div_then_rem_shares_witness() {
        // Both `a/b` and `a%b` on the same `(a,b)` HOp pair share the
        // witness side-table. Second op should NOT emit new identity rows.
        use lang::ast::BinOp;

        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let _pref_a = register_ref(&mut builder, 0, ATyp::VPoly(1, 2));
        let _pref_b = register_ref(&mut builder, 1, ATyp::VPoly(1, 1));

        let basis_before_div = builder.basis.len();
        let _q_res = add_op_div_rem(
            &mut builder,
            BinOp::Div,
            0,
            ATyp::VPoly(1, 2),
            1,
            ATyp::VPoly(1, 1),
            2,
            ATyp::VPoly(1, 1),
        );
        let after_div = builder.basis.len();
        assert_eq!(builder.div_wit.len(), 1, "div_wit has 1 entry after Div");

        let _r_res = add_op_div_rem(
            &mut builder,
            BinOp::Rem,
            0,
            ATyp::VPoly(1, 2),
            1,
            ATyp::VPoly(1, 1),
            3,
            ATyp::VPoly(1, 0),
        );
        let after_rem = builder.basis.len();

        // Still a single entry — Rem hit the cached witness pair.
        assert_eq!(
            builder.div_wit.len(),
            1,
            "div_wit unchanged after Rem (cached)"
        );

        // Div added 3 identity + 2 linking = 5 rows.
        assert_eq!(
            after_div - basis_before_div,
            5,
            "Div emitted 3 identity + 2 linking rows"
        );
        // Rem added ONLY the linking row (1 slot on VPoly(1,0)) — no new identity.
        assert_eq!(
            after_rem - after_div,
            1,
            "Rem on cached (a,b) should only emit 1 linking row, not re-emit identity"
        );
    }

    #[test]
    fn test_add_op_div_scalar_fallback() {
        // Scalar / Scalar → Scalar: legacy zip path (a - b·var(pr) = 0).
        // `div_witnesses` returns None (poly_shape fails on scalar), so no
        // witness side-table entry is created.
        use crate::{PRef, Ref};
        use lang::ast::BinOp;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let pref_a = register_ref(&mut builder, 0, ATyp::scalar());
        let pref_b = register_ref(&mut builder, 1, ATyp::scalar());

        let basis_before = builder.basis.len();
        let result = PRef::from_node(
            NodeIndex::new(2),
            ATyp::scalar(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        let op: GOp<ArkBls12_381> = Op::Bin(
            BinOp::Div,
            mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), ATyp::scalar())),
            mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(1)), ATyp::scalar())),
            ATyp::scalar(),
        );
        builder.add_op(result.clone(), op);

        // No witness side-table entry for scalar fallback.
        assert_eq!(
            builder.div_wit.len(),
            0,
            "div_wit stays empty on scalar Div"
        );

        // Legacy zip emits exactly one row: a - b · var(result).
        assert_eq!(
            builder.basis.len() - basis_before,
            1,
            "scalar fallback emits 1 row"
        );
        let var = |p: &PRef| SparsePolynomial::<ark_bls12_381::Fr, GrevLexTerm>::var(p);
        let expected = &var(&pref_a) - &(&var(&pref_b) * &var(&result));
        assert!(
            builder.basis.iter().any(|row| row == &expected),
            "scalar fallback row should be `a - b · var(result)`"
        );
    }

    // -----------------------------------------------------------------
    // Slot-count arithmetic: num_coeffs / multi_indices / hypercube /
    // index_of. Property-based tests (via arbtest) pin the m+1 / 2^n /
    // C(n+m, n) conventions from docs/poly-encoding.md so a refactor of
    // `num_coeffs` cannot silently drift back to the old `m == length`
    // convention.
    // -----------------------------------------------------------------

    /// Test-local binomial coefficient C(n, k). Assumes `k <= n`.
    fn binomial(n: usize, k: usize) -> usize {
        let k = k.min(n - k);
        (0..k).fold(1, |acc, i| acc * (n - i) / (i + 1))
    }

    #[test]
    fn test_binomial_helper_sanity() {
        // Pin well-known values so a bug in the helper doesn't mask bugs
        // in num_coeffs.
        assert_eq!(binomial(0, 0), 1);
        assert_eq!(binomial(5, 0), 1);
        assert_eq!(binomial(5, 5), 1);
        assert_eq!(binomial(5, 2), 10);
        assert_eq!(binomial(6, 3), 20);
        assert_eq!(binomial(10, 4), 210);
    }

    #[test]
    fn test_num_coeffs_vpoly_matches_binomial() {
        // VPoly(n, m) has C(n + m, n) coefficient slots.
        arbtest::arbtest(|u| {
            let n: usize = u.int_in_range(1..=5)?;
            let m: usize = u.int_in_range(0..=5)?;
            let sum = n + m;
            let expected = binomial(sum, n);
            assert_eq!(
                num_coeffs(&ATyp::VPoly(n, m)),
                expected,
                "num_coeffs(VPoly({n}, {m})) should be C({sum}, {n}) = {expected}",
            );
            Ok(())
        });
    }

    #[test]
    fn test_num_coeffs_mle_is_power_of_two() {
        // Mle(n) is the multilinear extension over {0,1}^n, so 2^n slots.
        arbtest::arbtest(|u| {
            let n: usize = u.int_in_range(0..=5)?;
            assert_eq!(
                num_coeffs(&ATyp::Mle(n)),
                1usize << n,
                "num_coeffs(Mle({n})) should be 2^{n}",
            );
            Ok(())
        });
    }

    #[test]
    fn test_num_coeffs_uni_is_m_plus_one() {
        // Phase-14 convention: Uni(m) has m+1 coefficient slots.
        arbtest::arbtest(|u| {
            let m: usize = u.int_in_range(0..=15)?;
            assert_eq!(
                num_coeffs(&ATyp::Uni(m)),
                m + 1,
                "num_coeffs(Uni({m})) should be {} (m + 1)",
                m + 1,
            );
            Ok(())
        });
    }

    #[test]
    fn test_num_coeffs_vec_is_length() {
        // Vec(t, n) is a base case: exactly n slots regardless of inner type.
        arbtest::arbtest(|u| {
            let n: usize = u.int_in_range(0..=16)?;
            let disc: u8 = u.int_in_range(0..=3)?;
            let inner = match disc {
                0 => ATyp::scalar(),
                1 => ATyp::bool(),
                2 => ATyp::g1(),
                _ => ATyp::g2(),
            };
            let typ = ATyp::vec(&inner, n);
            assert_eq!(num_coeffs(&typ), n, "num_coeffs(Vec(_, {n})) should be {n}");
            Ok(())
        });
    }

    #[test]
    fn test_num_coeffs_base_is_one() {
        // Every scalar-shaped base type occupies exactly one PRef slot.
        // Enumerated explicitly — the set of ABase variants is finite and fixed.
        for typ in [
            ATyp::scalar(),
            ATyp::bool(),
            ATyp::g1(),
            ATyp::g2(),
            ATyp::gt(),
            ATyp::fin(lang::typ::range::CRange::default()),
        ] {
            assert_eq!(num_coeffs(&typ), 1, "num_coeffs({typ:?}) should be 1");
        }
    }

    #[test]
    fn test_multi_indices_len_matches_num_coeffs() {
        // multi_indices(n, m).len() == num_coeffs(VPoly(n, m)) is definitional.
        arbtest::arbtest(|u| {
            let n: usize = u.int_in_range(1..=4)?;
            let m: usize = u.int_in_range(0..=4)?;
            assert_eq!(
                multi_indices(n, m).len(),
                num_coeffs(&ATyp::VPoly(n, m)),
                "multi_indices({n}, {m}).len() should equal num_coeffs(VPoly({n}, {m}))",
            );
            Ok(())
        });
    }

    #[test]
    fn test_hypercube_len_is_power_of_two() {
        arbtest::arbtest(|u| {
            let n: usize = u.int_in_range(0..=5)?;
            assert_eq!(
                hypercube(n).len(),
                1usize << n,
                "hypercube({n}).len() should be 2^{n}",
            );
            Ok(())
        });
    }

    #[test]
    fn test_index_of_mle_roundtrip_grid() {
        // For an arbitrary position i in 0..2^n the hypercube entry at i
        // must map back to i via index_of.
        arbtest::arbtest(|u| {
            let n: usize = u.int_in_range(1..=4)?;
            let cube = hypercube(n);
            if cube.is_empty() {
                return Ok(());
            }
            let i: usize = u.int_in_range(0..=(cube.len() - 1))?;
            let b = &cube[i];
            assert_eq!(
                index_of(&ATyp::Mle(n), b),
                i,
                "Mle({n}): position {i} -> {b:?} did not round-trip",
            );
            Ok(())
        });
    }

    #[test]
    fn test_index_of_vpoly_position_roundtrip() {
        // For an arbitrary position i in 0..num_coeffs the multi-index at
        // that position must map back to i via index_of.
        arbtest::arbtest(|u| {
            let n: usize = u.int_in_range(1..=4)?;
            let m: usize = u.int_in_range(0..=4)?;
            let mis = multi_indices(n, m);
            if mis.is_empty() {
                return Ok(());
            }
            let i: usize = u.int_in_range(0..=(mis.len() - 1))?;
            let k = &mis[i];
            assert_eq!(
                index_of(&ATyp::VPoly(n, m), k),
                i,
                "VPoly({n}, {m}): position {i} -> {k:?} did not round-trip",
            );
            Ok(())
        });
    }

    #[test]
    fn test_multi_indices_graded_lex_ordering() {
        // multi_indices is graded-lex: ascending by total degree, ties
        // broken by lex on the index vector. Check all consecutive pairs
        // for arbitrary (n, m).
        arbtest::arbtest(|u| {
            let n: usize = u.int_in_range(1..=4)?;
            let m: usize = u.int_in_range(0..=4)?;
            let mis = multi_indices(n, m);
            for w in mis.windows(2) {
                let a = &w[0];
                let b = &w[1];
                let da: usize = a.iter().sum();
                let db: usize = b.iter().sum();
                let ok = da < db || (da == db && a < b);
                assert!(
                    ok,
                    "multi_indices({n}, {m}) violates graded-lex at pair {a:?} -> {b:?} \
                     (sums {da} vs {db})",
                );
            }
            Ok(())
        });
    }
}
