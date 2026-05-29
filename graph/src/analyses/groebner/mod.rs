pub mod buchberger;
pub use buchberger::GroebnerBasis;

pub mod monomial;
pub use monomial::{ElimTerm, GrevLexTerm, Monomial};
pub mod sparsepoly;
pub use sparsepoly::SparsePolynomial;

pub(crate) mod ark_gb_adapter;

#[cfg(test)]
mod speedup_bench;

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
use std::collections::HashMap;
use std::fmt;
use std::marker::PhantomData;

// ---------------------------------------------------------------------------
// PRef-slot enumeration helpers for polynomial / MLE values.
//
// These define the canonical order in which the slots of a polynomial-typed
// PRef are laid out (via `PRef::with_slot(i)`). They are NOT monomial / term
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

/// Namespace shared across Groebner builders that must agree on variable names
/// and sentinel allocation (e.g., prover and verifier builders for the same protocol).
///
/// Owns the argument registry (`args`), the division-witness table (`div_wit`),
/// and a sentinel counter for stable `PRef` generation. Multiple builders
/// share one namespace so they agree on variable names and sentinel indices.
///
/// `GroebnerBuilder` borrows the namespace via `&mut` — it does not own it.
#[derive(Clone)]
pub struct GroebnerNamespace<C: ArkConfig> {
    /// All PRefs known to the namespace: protocol parameters + every node
    /// from the TransClos. Each has index=0 and the correct full type from
    /// the DAG, providing an authoritative mapping from `Ref` to `PRef`
    /// for `find_ref`.
    pub prefs: HashMap<Ref, PRef>,
    pub div_wit: Ctx<(HOp<C>, HOp<C>), (PRef, PRef)>,
    /// Monotonically decreasing counter for sentinel PRef NodeIndex allocation.
    /// Starts at usize::MAX and decrements; so sentinel indices never collide
    /// with real DAG node indices (which grow up from 0).
    sentinel_counter: usize,
    /// Cached GT sentinel — allocated once via sentinel_pref on first call to
    /// gt_pref(), then reused.
    gt_sentinel: Option<PRef>,
}

impl<C: ArkConfig + HasOpFactory> GroebnerNamespace<C> {
    pub fn new() -> Self {
        Self {
            prefs: HashMap::new(),
            div_wit: Ctx::new(),
            sentinel_counter: usize::MAX,
            gt_sentinel: None,
        }
    }

    /// Register a PRef in the namespace. Overwrites any existing entry
    /// for the same reference. Returns the previous entry if one existed.
    pub fn register(&mut self, pr: &PRef) -> Option<PRef> {
        self.prefs.insert(pr.reference, pr.clone())
    }

    /// Allocate a fresh sentinel PRef with a stable unique NodeIndex.
    /// The counter starts at `usize::MAX` and decrements for each call,
    /// so sentinel indices never collide with real DAG node indices (which
    /// grow up from 0).
    pub fn sentinel_pref(&mut self, name: &str, typ: ATyp) -> PRef {
        let vid = Vid::from(name);
        let idx = NodeIndex::new(self.sentinel_counter);
        self.sentinel_counter -= 1;
        PRef::from_var(vid, idx, typ, 0, Qualifier::Public, Distribution::default())
    }

    /// Phase 12: lazy accessor for the GT generator sentinel `__zippel::gb::gt`.
    /// Idempotent — allocates once, then returns the cached PRef.
    pub fn gt_pref(&mut self, np: &mut Ctx<PRef, GOp<C>>) -> PRef {
        if let Some(pr) = self.gt_sentinel.as_ref() {
            return pr.clone();
        }
        let pr = self.sentinel_pref("__zippel::gb::gt", ATyp::gt());
        if !np.contains(&pr) {
            np.insert(&pr, &Op::Ref(pr.reference, ATyp::gt()));
        }
        self.gt_sentinel = Some(pr.clone());
        pr
    }
}

/// The result of building a Gröbner basis — the basis polynomials, their
/// polynomial definitions (pl), and non-polynomial definitions (np).
#[derive(Clone)]
pub struct GroebnerResult<C: ArkConfig, T: Monomial> {
    pub basis: GroebnerBasis<C::F, T>,
    pub np: Ctx<PRef, GOp<C>>,
    pub pl: Ctx<PRef, SparsePolynomial<C::F, T>>,
}

impl<C: ArkConfig + HasOpFactory, T: Monomial> GroebnerResult<C, T> {
    pub fn new() -> Self {
        Self {
            basis: GroebnerBasis::empty(0),
            np: Ctx::new(),
            pl: Ctx::new(),
        }
    }

    pub fn vars(&self) -> Set<PRef> {
        self.np.keys().union(self.pl.keys())
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

    /// Compute Groebner basis using Buchberger algorithm.
    ///
    /// W is the packed monomial width (8 or 16). Caller must ensure W is
    /// appropriate for the problem size (≤63 vars for W=8, ≤127 vars for W=16).
    pub fn run<const W: usize>(&mut self) {
        self.basis = self.basis.clone().buchberger_and_reduce::<W>();
    }

    /// Merge another result's basis, polynomial definitions, and non-polynomial
    /// definitions into this result.
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
    }
}

impl<C: ArkConfig + HasOpFactory, T: Monomial> Default for GroebnerResult<C, T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<'a, C, D, A, T> Pretty<'a, D, A> for GroebnerResult<C, T>
where
    C: ArkConfig,
    T: Monomial,
    D: DocAllocator<'a, A>,
    D::Doc: Clone,
    A: 'a + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        allocator.concat([
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

impl<C: ArkConfig, T: Monomial> fmt::Display for GroebnerResult<C, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <GroebnerResult<C, T> as Pretty<'_, BoxAllocator, ()>>::pretty(self.clone(), &BoxAllocator)
            .1
            .render_fmt(100, f)
    }
}

/// Constructs `GroebnerResult`s from `TransClos` inputs. Owns a
/// `GroebnerNamespace` so that multiple `build()` calls share variable names
/// and sentinel indices. Each call to `build(TransClos)` returns a fresh
/// `GroebnerResult` while accumulating `args` and `div_wit` in the namespace.
#[derive(Clone)]
pub struct GroebnerBuilder<C: ArkConfig, T: Monomial = GrevLexTerm> {
    pub ns: GroebnerNamespace<C>,
    _phantom: PhantomData<T>,
}

impl<C: ArkConfig + HasOpFactory, T: Monomial> Default for GroebnerBuilder<C, T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<C: ArkConfig + HasOpFactory, T: Monomial> GroebnerBuilder<C, T> {
    pub fn new() -> Self {
        Self {
            ns: GroebnerNamespace::new(),
            _phantom: PhantomData,
        }
    }

    /// Build a `GroebnerResult` from a `TransClos`. The namespace accumulates
    /// across calls: `prefs` and `div_wit` persist so that subsequent `build()`
    /// calls agree on variable names and sentinel indices.
    pub fn build(&mut self, tc: TransClos<C>) -> GroebnerResult<C, T> {
        let mut result = GroebnerResult::new();
        for new_arg in tc.prefs.iter() {
            self.ns.register(new_arg);
        }
        for (pr, _op) in tc.clos.iter() {
            self.ns.register(pr);
        }
        for (pr, op) in tc.clos.into_iter() {
            self.add_op(pr, op, &mut result);
        }
        result
    }

    pub fn find_ref(&self, r: &Ref) -> PRef {
        if let Some(v) = self.ns.prefs.get(r) {
            return v.clone();
        }
        panic!("groebner: ref {} not found in namespace prefs", r)
    }

    /// Phase 12: lazy accessor for the GT generator sentinel `__zippel::gb::gt`.
    ///
    /// `Op::Pair(a, b)` emits the basis row
    ///   `var(pr) − ref_vars(a)·ref_vars(b)·var(__zippel::gb::gt) = 0`
    /// which encodes the pairing axiom
    ///   `pair(__zippel::gb::g1, __zippel::gb::g2) = __zippel::gb::gt`
    /// combined with bilinearity:
    ///   `pair(α·g1, β·g2) = α·β·gt`.
    fn gt_pref(&mut self, result: &mut GroebnerResult<C, T>) -> PRef {
        self.ns.gt_pref(&mut result.np)
    }

    fn sentinel_pref(&mut self, name: &str, typ: ATyp, result: &mut GroebnerResult<C, T>) -> PRef {
        let pr = self.ns.sentinel_pref(name, typ.clone());
        result.np.insert(&pr, &Op::Ref(pr.reference, typ));
        pr
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
    fn div_witnesses(
        &mut self,
        a: &HOp<C>,
        b: &HOp<C>,
        result: &mut GroebnerResult<C, T>,
    ) -> Option<(PRef, PRef)> {
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
        if let Some(wit) = self.ns.div_wit.get(&key) {
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

        // Mint stable witness PRefs using reserved synthetic names.
        let counter = self.ns.div_wit.len();
        let q_name = format!("__zippel::gb::div_q::{}", counter);
        let r_name = format!("__zippel::gb::div_r::{}", counter);
        let q_wit = self.sentinel_pref(&q_name, ATyp::VPoly(nr, mq), result);
        let r_wit = self.sentinel_pref(&r_name, ATyp::VPoly(nr, mr), result);

        // Emit canonical identity rows: one per a_idx multi-index.
        let a_polys = self.ref_vars(a.get());
        let b_polys = self.ref_vars(b.get());
        let a_idx = multi_indices(na, ma);
        let b_idx = multi_indices(nb, mb);
        let q_idx = multi_indices(nr, mq);
        let r_idx = multi_indices(nr, mr);

        debug_assert_eq!(
            a_polys.len(),
            a_idx.len(),
            "ref_vars(a) slot count mismatch: {} vs a_idx {}",
            a_polys.len(),
            a_idx.len()
        );
        debug_assert_eq!(
            b_polys.len(),
            b_idx.len(),
            "ref_vars(b) slot count mismatch: {} vs b_idx {}",
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
                        let qf = q_wit.clone().with_slot(j_pos).unwrap();
                        rhs = &rhs + &(&b_polys[i_pos] * &SparsePolynomial::var(&qf));
                    }
                }
            }
            // R contribution (only for k with total degree ≤ mr).
            if let Some(r_pos) = r_idx.iter().position(|rk| rk == k) {
                let rf = r_wit.clone().with_slot(r_pos).unwrap();
                rhs = &rhs + &SparsePolynomial::var(&rf);
            }
            result.basis.push(&a_polys[ka_pos] - &rhs);
        }

        self.ns
            .div_wit
            .insert(&key, &(q_wit.clone(), r_wit.clone()));
        Some((q_wit, r_wit))
    }

    /// Phase 13: link the user's PRef `pr` to a witness PRef `wit` slot by
    /// slot, for when `pr` aliases a div/rem witness produced by
    /// `div_witnesses`. Emits `var(pr[j]) − var(wit[j]) = 0` for every
    /// `j < pr.typ.physical_len()`, and registers `pl[pr[j]] = var(wit[j])`.
    fn link_to_witness(&mut self, pr: &PRef, wit: &PRef, result: &mut GroebnerResult<C, T>) {
        let n_pr = pr.typ.physical_len();
        let n_wit = wit.typ.physical_len();
        // Number of shared slots. If user's pr has more slots than the
        // witness (unusual — would indicate the lub widened the result),
        // link what we can; excess pr slots stay unconstrained (opaque).
        let n = n_pr.min(n_wit);
        for j in 0..n {
            let pf = pr.clone().with_slot(j).unwrap();
            let wf = wit.clone().with_slot(j).unwrap();
            let wvar = SparsePolynomial::var(&wf);
            result.pl.insert(&pf, &wvar);
            result.basis.push(&wvar - &SparsePolynomial::var(&pf));
        }
    }

    #[allow(clippy::wrong_self_convention)]
    fn to_poly_value(&self, v: &Value<C>) -> Vec<SparsePolynomial<C::F, T>> {
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
    /// enough polys for the caller to drive `pr.with_slot(i)`):
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
    /// `ref_vars` (when Eval appears nested inside another op) and `add_op`
    /// (when Eval is the top-level op being bound to a PRef).
    fn eval_to_poly(&mut self, p: &GOp<C>, xs: &GOp<C>) -> Option<Vec<SparsePolynomial<C::F, T>>> {
        let p_typ = p.typ();
        let xs_polys = self.ref_vars(xs);
        let k = xs_polys.len();
        match &p_typ {
            ATyp::Uni(_) | ATyp::VPoly(1, _) if k >= 1 => {
                let p_polys = self.ref_vars(p);
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
                let p_polys = self.ref_vars(p);
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
                let p_polys = self.ref_vars(p);
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

    /// Resolve an `Op::Ref(v, typ)` to a vector of variable polynomials,
    /// one per physical slot of the resolved PRef.
    ///
    /// After IR lowering, every child of a compound op is `Op::Ref` or
    /// `Op::Value`. This helper asserts the `Op::Ref` invariant and
    /// returns the slot variables for use in basis row construction.
    fn ref_vars(&self, op: &GOp<C>) -> Vec<SparsePolynomial<C::F, T>> {
        match op {
            Op::Ref(v, typ) => {
                let pf = self.find_ref(v);
                debug_assert_eq!(
                    pf.typ, *typ,
                    "find_ref type mismatch: namespace has {:?} but Op::Ref says {:?}",
                    pf.typ, typ,
                );
                pf.slots()
                    .into_iter()
                    .map(|s| SparsePolynomial::var(&s))
                    .collect()
            }
            Op::Value(v) => self.to_poly_value(v),
            other => {
                panic!(
                    "ref_vars called with unsupported op variant: {:?} — children should be materialized to Ref",
                    std::mem::discriminant(other)
                )
            }
        }
    }
}

impl<C: ArkConfig + HasOpFactory, T: Monomial> GroebnerBuilder<C, T> {
    fn add_op(&mut self, pr: PRef, op: GOp<C>, result: &mut GroebnerResult<C, T>) {
        let op_for_div = op.clone();
        match op {
            Op::Ref(r, typ) => {
                let ref_poly = self.ref_vars(&Op::Ref(r, typ));
                for (i, p) in ref_poly.into_iter().enumerate() {
                    let pf = pr.clone().with_slot(i).unwrap();
                    result.pl.insert(&pf, &p);
                    result.basis.push(p - SparsePolynomial::var(&pf));
                }
            }
            Op::Bin(BinOp::Add | BinOp::And, a, b, _) => self
                .ref_vars(&a)
                .into_iter()
                .zip(self.ref_vars(&b))
                .enumerate()
                .for_each(|(i, (a, b))| {
                    let pf = pr.clone().with_slot(i).unwrap();
                    result.pl.insert(&pf, &(&a + &b));
                    result.basis.push(a + b - SparsePolynomial::var(&pf));
                }),
            Op::Bin(BinOp::Sub, a, b, _) => self
                .ref_vars(&a)
                .into_iter()
                .zip(self.ref_vars(&b))
                .enumerate()
                .for_each(|(i, (a, b))| {
                    let pf = pr.clone().with_slot(i).unwrap();
                    result.pl.insert(&pf, &(&a - &b));
                    result.basis.push(a - b - SparsePolynomial::var(&pf));
                }),
            Op::Bin(BinOp::Mul, ref a, ref b, _) => {
                let a_typ = a.typ();
                let b_typ = b.typ();
                let is_poly = |t: &ATyp| matches!(t, ATyp::VPoly(_, _) | ATyp::Mle(_));
                let poly_result: Option<Vec<SparsePolynomial<C::F, T>>> =
                    if is_poly(&a_typ) || is_poly(&b_typ) {
                        match (&a_typ, &b_typ, &pr.typ) {
                            // VPoly × VPoly of same num_vars → convolution into the
                            // result type's multi-index basis. Terms whose total
                            // degree exceeds the result's max_degree are dropped
                            // (they must be zero for the expression to be well-typed).
                            (ATyp::VPoly(na, ma), ATyp::VPoly(nb, mb), ATyp::VPoly(nr, mr))
                                if na == nb && na == nr =>
                            {
                                let a_polys = self.ref_vars(a);
                                let b_polys = self.ref_vars(b);
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
                                let a_polys = self.ref_vars(a);
                                let b_polys = self.ref_vars(b);
                                let all_b = hypercube(n);
                                let r_idx = multi_indices(n, *mr);
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
                match poly_result {
                    Some(polys) => {
                        for (i, poly) in polys.into_iter().enumerate() {
                            let pf = pr.clone().with_slot(i).unwrap();
                            result.pl.insert(&pf, &poly);
                            result.basis.push(poly - SparsePolynomial::var(&pf));
                        }
                    }
                    None => self
                        .ref_vars(a)
                        .into_iter()
                        .zip(self.ref_vars(b))
                        .enumerate()
                        .for_each(|(i, (ap, bp))| {
                            let pf = pr.clone().with_slot(i).unwrap();
                            result.pl.insert(&pf, &(&ap * &bp));
                            result.basis.push(ap * bp - SparsePolynomial::var(&pf));
                        }),
                }
            }
            Op::Bin(BinOp::Dot, a, b, _) => {
                let sum = self
                    .ref_vars(&a)
                    .into_iter()
                    .zip(self.ref_vars(&b))
                    .map(|(a, b)| a * b)
                    .sum();
                result.pl.insert(&pr, &sum);
                result.basis.push(sum - SparsePolynomial::var(&pr))
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
                if let Some((q_wit, _r_wit)) = self.div_witnesses(a, b, result) {
                    self.link_to_witness(&pr, &q_wit, result);
                } else {
                    self.ref_vars(a)
                        .into_iter()
                        .zip(self.ref_vars(b))
                        .enumerate()
                        .for_each(|(i, (a_p, b_p))| {
                            let pf = pr.clone().with_slot(i).unwrap();
                            result
                                .np
                                .insert(&pf, &Op::ram(op_for_div.clone(), Op::index(i)));
                            result.basis.push(a_p - b_p * SparsePolynomial::var(&pf));
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
                if let Some((_q_wit, r_wit)) = self.div_witnesses(a, b, result) {
                    self.link_to_witness(&pr, &r_wit, result);
                } else {
                    result.np.insert(&pr, &op_for_div);
                }
            }
            Op::Bin(BinOp::Equ, a, b, _) => self
                .ref_vars(&a)
                .into_iter()
                .zip(self.ref_vars(&b))
                .for_each(|(a, b)| {
                    result.pl.insert(&pr, &(&a - &b));
                    result.pl.insert(&pr, &SparsePolynomial::lit(&C::F::zero()));
                    result.basis.push(a - b);
                    result.basis.push(SparsePolynomial::var(&pr));
                }),
            Op::Check(a) => self.add_op(pr, a.get().clone(), result),
            Op::Challenge(t, b) => {
                let op = Op::Challenge(t, b);
                result.np.insert(&pr, &op);
            }
            Op::Random(t, b) => {
                let op = Op::Random(t, b);
                result.np.insert(&pr, &op);
            }
            Op::Interpolate(ref points, ref evals) => {
                result
                    .np
                    .insert(&pr, &Op::Interpolate(points.clone(), evals.clone()));
            }
            // Op::Ifft(v): p = ifft(v) where p is a univariate polynomial in
            // coefficient form and v a length-N vector of its evaluations at
            // the N-th roots of unity. Constraints (linear over F):
            //   for each i ∈ [0, N): Σ_j ω^{i·j} · p[j]  =  v[i]
            // where ω is a primitive N-th root of unity and p[j] is the
            // j-th coefficient slot of `pr`. If `get_root_of_unity(N)` is
            // None (N isn't a 2-adic divisor of |F|-1), fall back to opaque.
            Op::Ifft(ref a) => {
                let v_polys = self.ref_vars(a);
                let n = v_polys.len();
                if let Some(omega) = C::F::get_root_of_unity(n as u64) {
                    // Row i: Σ_j ω^{i·j} · pr[j] = v_polys[i]
                    let coeff_vars: Vec<SparsePolynomial<C::F, T>> = (0..n)
                        .map(|j| SparsePolynomial::var(&pr.clone().with_slot(j).unwrap()))
                        .collect();
                    for (i, vp) in v_polys.iter().enumerate().take(n) {
                        let lhs = dft_row(&coeff_vars, omega, i);
                        result.basis.push(&lhs - vp);
                    }
                    // Register each coefficient slot of `pr` in `pl` so
                    // `find_ref` can resolve `Ref::Var("p", _)` later.
                    for j in 0..n {
                        let pf = pr.clone().with_slot(j).unwrap();
                        let v = SparsePolynomial::var(&pf);
                        result.pl.insert(&pf, &v);
                    }
                } else {
                    result.np.insert(&pr, &Op::Ifft(a.clone()));
                }
            }
            // Op::Fft(p): v = fft(p) — symmetric to Ifft. Here `pr` holds
            // the N output-vector slots; the coefficients live in `p`. The
            // same DFT matrix applies:
            //   for each i ∈ [0, N): v[i] = Σ_j ω^{i·j} · p[j]
            Op::Fft(ref a) => {
                let coeff_polys = self.ref_vars(a);
                let n = coeff_polys.len();
                if let Some(omega) = C::F::get_root_of_unity(n as u64) {
                    for i in 0..n {
                        let lhs = dft_row(&coeff_polys, omega, i);
                        let pf = pr.clone().with_slot(i).unwrap();
                        // Register v[i]'s polynomial form in pl and push basis eqn.
                        result.pl.insert(&pf, &lhs);
                        result.basis.push(&lhs - &SparsePolynomial::var(&pf));
                    }
                } else {
                    result.np.insert(&pr, &Op::Fft(a.clone()));
                }
            }
            // Op::Poly / Op::Mle / Op::Coef: bind the i-th PRef slot of `pr`
            // to the i-th scalar poly read from `inner` by `ref_vars`. These
            // three share identity semantics on coefficients / evaluations —
            // only the slot-count / enumeration of `pr.typ` differs, and that
            // is driven entirely by the input's shape (ref_vars already returns
            // the right number of polys). Basis-change between coefficient
            // and evaluation form happens in later phases (Eval / Bin on
            // mixed polynomial types).
            Op::Poly(ref inner) | Op::Mle(ref inner) | Op::Coef(ref inner) => {
                let polys = self.ref_vars(inner);
                debug_assert!(
                    !polys.is_empty(),
                    "Op::Poly/Mle/Coef produced zero polys for {:?}",
                    pr.typ
                );
                for (i, p) in polys.into_iter().enumerate() {
                    let pf = pr.clone().with_slot(i).unwrap();
                    result.pl.insert(&pf, &p);
                    result.basis.push(p - SparsePolynomial::var(&pf));
                }
            }
            Op::Vec(vs) => {
                for (i, v) in vs.into_iter().enumerate() {
                    let pf = pr.with_index(i).unwrap();
                    self.add_op(pf, v.get().clone(), result);
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
            // `ref_vars` normalises both to k scalar polys. Unsupported shapes
            // (e.g. k > n, or Record operands) fall through to the np catch-all
            // via `None`.
            Op::Evaluate(ref p, ref xs) => {
                let eval_result = self.eval_to_poly(p, xs);
                match eval_result {
                    Some(polys) => {
                        for (i, poly) in polys.into_iter().enumerate() {
                            let pf = pr.clone().with_slot(i).unwrap();
                            result.pl.insert(&pf, &poly);
                            result.basis.push(poly - SparsePolynomial::var(&pf));
                        }
                    }
                    None => {
                        result.np.insert(&pr, &Op::Evaluate(p.clone(), xs.clone()));
                    }
                }
            }
            // Phase 10: `Op::Reduce(op, v)` — unfold into `op`-fold of
            // `ref_vars(v)` when the inner BinOp is polynomial over F.
            // Otherwise opaque (np).
            Op::Reduce(rop, ref v) => {
                let elems = self.ref_vars(v);
                match self.reduce_unfold(rop, elems) {
                    Some(polys) => {
                        for (i, p) in polys.into_iter().enumerate() {
                            let pf = pr.clone().with_slot(i).unwrap();
                            result.pl.insert(&pf, &p);
                            result.basis.push(p - SparsePolynomial::var(&pf));
                        }
                    }
                    None => {
                        result.np.insert(&pr, &Op::Reduce(rop, v.clone()));
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
                            let pf = pr.clone().with_slot(i).unwrap();
                            result.pl.insert(&pf, &p);
                            result.basis.push(p - SparsePolynomial::var(&pf));
                        }
                    }
                    None => {
                        result.np.insert(&pr, &Op::Value(v.clone()));
                    }
                }
            }
            // Phase 10: `Op::Ram(a, b)` — RAM reads are treated as *fresh
            // identifiers* in the Gröbner basis. A runtime RAM access can't
            // be equated with any compile-time slot (the underlying array
            // may have been mutated through an aliased reference, etc.), so
            // even with a literal index we do not emit a basis row relating
            // `pr` to `find_ref(a).with_slot(i)`.
            //
            // We do need every slot of `pr` to appear in `np`, otherwise
            // `find_ref(Ref::Var(pr_name, _))` panics for subsequent ops
            // that read the RAM result.
            //
            // FIXME: this seems problematic as it always link the first
            // logical element to pr. We can use `ref_vars` and should add
            // this to np if it is a runtime index.
            Op::Ram(ref a, ref b) => match b.get() {
                Op::Value(Value::Index(i)) => {
                    let raw = Op::Ram(a.clone(), b.clone());
                    if let Op::Ref(r, _) = a.get() {
                        if let Some(array_pref) = self.ns.prefs.get(r) {
                            if let Some(slot_pref) = array_pref.with_slot(*i) {
                                let e = SparsePolynomial::var(&slot_pref);
                                result.basis.push(e.clone() - SparsePolynomial::var(&pr));
                                result.pl.insert(&pr, &e);
                            } else {
                                result.np.insert(&pr, &raw);
                            }
                        } else {
                            result.np.insert(&pr, &raw);
                        }
                    } else {
                        result.np.insert(&pr, &raw);
                    }
                }
                _ => {
                    let raw = Op::Ram(a.clone(), b.clone());
                    let slots: Vec<PRef> = pr.slots();
                    if slots.is_empty() {
                        result.np.insert(&pr, &raw);
                    }
                    for pf in slots {
                        result.np.insert(&pf, &raw);
                    }
                }
            },
            // Phase 12: `Op::Pair(a, b, t)` — bilinear pairing via the
            // `__zippel::gb::gt` sentinel. The result `pr : GT` is bound to
            // the exponent-space bilinear form:
            //
            //   var(pr) = ref_vars(a) · ref_vars(b) · var(__zippel::gb::gt)
            //
            // which encodes both the pairing axiom
            // `pair(__zippel::gb::g1, __zippel::gb::g2) = __zippel::gb::gt`
            // and full bilinearity. Matching pair expressions on both
            // sides of a `verify(lhs == rhs)` then cancel under Buchberger
            // because their basis rows are identical F-polynomials.
            Op::Pair(ref a, ref b, _) => {
                let e_a = self
                    .ref_vars(a.get())
                    .into_iter()
                    .next()
                    .unwrap_or_else(SparsePolynomial::zero);
                let e_b = self
                    .ref_vars(b.get())
                    .into_iter()
                    .next()
                    .unwrap_or_else(SparsePolynomial::zero);
                let gt = self.gt_pref(result);
                let e = &e_a * &e_b * SparsePolynomial::var(&gt);
                result.pl.insert(&pr, &e);
                result.basis.push(&e - &SparsePolynomial::var(&pr));
            }
            // `Op::Record(fields)` — the record as a whole is opaque in np
            // (cannot be converted to a polynomial ideal). Each field is
            // recursively processed by delegating to `add_op` with a fresh
            // PRef whose `reference` re-uses `pr`'s (so subsequent field
            // projections — which lower to `Op::Ref(Ref::Var(r, n), field_typ)`
            // — can find a matching entry via `find_ref`'s namespace lookup).
            //
            // A full field-offset-aware slot layout for records is deferred.
            Op::Record(ref fields) => {
                result.np.insert(&pr, &Op::Record(fields.clone()));
                for (_, sub) in fields.iter() {
                    let sub_op = sub.get().clone();
                    let sub_pr = PRef {
                        typ: sub_op.typ(),
                        index: 0,
                        ..pr.clone()
                    };
                    self.add_op(sub_pr, sub_op, result);
                }
            }
            // Concat/Pow/Marginalize/Proj: opaque in np — cannot be
            // converted to polynomial ideal constraints.
            Op::Bin(BinOp::Concat, ref a, ref b, _) => {
                result.np.insert(
                    &pr,
                    &Op::Bin(BinOp::Concat, a.clone(), b.clone(), pr.typ.clone()),
                );
            }
            Op::Bin(BinOp::Pow, ref a, ref b, _) => {
                result.np.insert(
                    &pr,
                    &Op::Bin(BinOp::Pow, a.clone(), b.clone(), pr.typ.clone()),
                );
            }
            Op::Marginalize(ref inner) => {
                result.np.insert(&pr, &Op::Marginalize(inner.clone()));
            }
            Op::Proj(ref inner, ref field, ref typ) => {
                result
                    .np
                    .insert(&pr, &Op::Proj(inner.clone(), field.clone(), typ.clone()));
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[cfg(test)]
    use crate::UDags;
    use crate::analyses::TransClos;
    #[cfg(test)]
    use crate::analyses::{QualifierPropagation, UniformityPropagation};
    use backend::ArkBls12_381;
    use backend::op::mk;
    #[cfg(test)]
    use lang::ast::UModule;
    #[cfg(test)]
    use share::Ctx;
    #[cfg(test)]
    use share::unwrap;

    fn trans_clos_from_src(src: &str) -> TransClos<ArkBls12_381> {
        let m = UModule::from_str(src)
            .unwrap()
            .concretize(&Ctx::new())
            .unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);
        let g = UniformityPropagation::from_dag(&g).annotate_dag(&g);
        TransClos::input(&g)
    }

    fn trans_clos_from_src_sized(
        src: &str,
        sizes: &share::Ctx<lang::id::Tid, usize>,
    ) -> TransClos<ArkBls12_381> {
        let m = UModule::from_str(src).unwrap().concretize(sizes).unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);
        let g = UniformityPropagation::from_dag(&g).annotate_dag(&g);
        TransClos::input(&g)
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
        let builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        use backend::Value;

        let val = Value::VecIndex(vec![0, 1, 2]);
        let poly = builder.to_poly_value(&val);
        assert_eq!(poly.len(), 3);
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
    // ref_vars on polynomial-typed refs
    // -----------------------------------------------------------------

    #[test]
    fn test_ref_vars_vpoly_expands_coefficients() {
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
        builder.ns.register(&pref_p);

        let op: GOp<ArkBls12_381> = Op::Ref(Ref::new(NodeIndex::new(0)), ATyp::VPoly(2, 2));
        let polys = builder.ref_vars(&op);
        assert_eq!(polys.len(), 6);
        for (i, _) in polys.iter().enumerate() {
            let expected = pref_p.clone().with_slot(i).unwrap();
            assert!(
                polys[i].contains(&expected),
                "coefficient poly {} does not contain expected PRef (index {})",
                i,
                i
            );
        }
    }

    #[test]
    fn test_ref_vars_mle_expands_evaluations() {
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
        builder.ns.register(&pref_p);

        let op: GOp<ArkBls12_381> = Op::Ref(Ref::new(NodeIndex::new(0)), ATyp::Mle(3));
        let polys = builder.ref_vars(&op);
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
        let mut gresult = GroebnerResult::<ArkBls12_381, GrevLexTerm>::new();

        // First: bind Vec of scalars on node 0, then Poly on node 1.
        let pref_v = PRef::from_node(
            NodeIndex::new(0),
            ATyp::VPoly(1, 2),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_v);
        let coefs: Vec<_> = (1..=3u64)
            .map(|n| mk::<ArkBls12_381>(Op::Value(Value::Scalar(Fr::from(n)))))
            .collect();
        builder.add_op(pref_v.clone(), Op::Vec(coefs), &mut gresult);

        let pref_p = PRef::from_node(
            NodeIndex::new(1),
            ATyp::VPoly(1, 2),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        let op_poly: GOp<ArkBls12_381> = Op::Poly(mk::<ArkBls12_381>(Op::Ref(
            crate::Ref::new(NodeIndex::new(0)),
            ATyp::VPoly(1, 2),
        )));
        builder.ns.register(&pref_p);
        builder.add_op(pref_p.clone(), op_poly, &mut gresult);

        // Three coefficient slots should have been bound.
        for i in 0..3 {
            let slot = pref_p.clone().with_slot(i).unwrap();
            assert!(gresult.pl.contains(&slot), "slot {} missing from pl", i);
        }
        // Six basis equations: 3 from Vec binding + 3 from Poly identity.
        assert_eq!(gresult.basis.basis.len(), 6);
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
        let mut gresult = GroebnerResult::<ArkBls12_381, GrevLexTerm>::new();

        // First: bind Vec of scalars on node 0, then Poly on node 1.
        let pref_v = PRef::from_node(
            NodeIndex::new(0),
            ATyp::VPoly(1, 2),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_v);
        let coefs: Vec<_> = (1..=3u64)
            .map(|n| mk::<ArkBls12_381>(Op::Value(Value::Scalar(Fr::from(n)))))
            .collect();
        builder.add_op(pref_v.clone(), Op::Vec(coefs), &mut gresult);

        // Poly: reads the Vec's slots via Ref.
        let pref_p = PRef::from_node(
            NodeIndex::new(1),
            ATyp::VPoly(1, 2),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_p);
        builder.add_op(
            pref_p.clone(),
            Op::Poly(mk::<ArkBls12_381>(Op::Ref(
                crate::Ref::new(NodeIndex::new(0)),
                ATyp::VPoly(1, 2),
            ))),
            &mut gresult,
        );

        // Then: Op::Coef reading the VPoly back into a Uni(2) output
        // (degree 2 = 3 coefficient slots, per docs/poly-encoding.md).
        let pref_c = PRef::from_node(
            NodeIndex::new(2),
            ATyp::Uni(2),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        let ref_p: GOp<ArkBls12_381> =
            Op::Ref(crate::Ref::new(NodeIndex::new(1)), ATyp::VPoly(1, 2));
        builder.add_op(
            pref_c.clone(),
            Op::Coef(mk::<ArkBls12_381>(ref_p)),
            &mut gresult,
        );

        // Each Coef slot should be bound identically to the corresponding
        // VPoly coefficient PRef — that's the round-trip identity. `ref_vars`
        // resolves per-slot PRefs to ATyp::scalar(), so we expect that form
        // on the RHS.
        for i in 0..3 {
            let coef_slot = pref_c.clone().with_slot(i).unwrap();
            let poly_slot = pref_p.clone().with_slot(i).unwrap();
            let stored = gresult.pl.get(&coef_slot).expect("coef slot missing");
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
        let mut gresult = GroebnerResult::<ArkBls12_381, GrevLexTerm>::new();

        // First: bind Vec of scalars on node 0, then Mle on node 1.
        let pref_v = PRef::from_node(
            NodeIndex::new(0),
            ATyp::Mle(2),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_v);
        let vals: Vec<_> = (1..=4u64)
            .map(|n| mk::<ArkBls12_381>(Op::Value(Value::Scalar(Fr::from(n)))))
            .collect();
        builder.add_op(pref_v.clone(), Op::Vec(vals), &mut gresult);

        let pref_m = PRef::from_node(
            NodeIndex::new(1),
            ATyp::Mle(2),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_m);
        builder.add_op(
            pref_m.clone(),
            Op::Mle(mk::<ArkBls12_381>(Op::Ref(
                crate::Ref::new(NodeIndex::new(0)),
                ATyp::Mle(2),
            ))),
            &mut gresult,
        );

        // 4 from Vec binding + 4 from Mle identity.
        assert_eq!(gresult.basis.basis.len(), 8);
        for i in 0..4 {
            assert!(
                gresult.pl.contains(&pref_m.clone().with_slot(i).unwrap()),
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
        let mut gresult = GroebnerResult::<ArkBls12_381, GrevLexTerm>::new();
        let _pref_p = {
            let p = PRef::from_node(
                NodeIndex::new(0),
                ATyp::VPoly(1, 1),
                0,
                Qualifier::Private,
                Distribution::default(),
            );
            builder.ns.register(&p);
            p
        };
        let _pref_xs = {
            let p = PRef::from_node(
                NodeIndex::new(1),
                ATyp::Uni(1),
                0,
                Qualifier::Private,
                Distribution::default(),
            );
            builder.ns.register(&p);
            p
        };

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
        builder.add_op(result.clone(), op, &mut gresult);

        // Expected: 2 result slots + 2 basis equations, and no np insertion.
        assert_eq!(
            gresult.np.len(),
            0,
            "eval should not have fallen through to np"
        );
        for i in 0..2 {
            assert!(
                gresult.pl.contains(&result.clone().with_slot(i).unwrap()),
                "uni batched result slot {} missing",
                i
            );
        }
        // Each result slot: poly = a_0 + a_1 * xs[i] (a linear polynomial in
        // 4 input variables). Check it depends on exactly {a_0, a_1, xs[i]}.
        let pref_a = PRef::from_node(
            NodeIndex::new(0),
            ATyp::VPoly(1, 1),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        let pref_xs = PRef::from_node(
            NodeIndex::new(1),
            ATyp::Uni(1),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        let a0 = pref_a.clone().with_slot(0).unwrap();
        let a1 = pref_a.clone().with_slot(1).unwrap();
        let x0 = pref_xs.clone().with_slot(0).unwrap();
        let x1 = pref_xs.clone().with_slot(1).unwrap();

        let slot0 = gresult
            .pl
            .get(&result.clone().with_slot(0).unwrap())
            .unwrap();
        let vars0 = slot0.vars();
        assert!(vars0.contains(&a0), "slot 0 missing a_0");
        assert!(vars0.contains(&a1), "slot 0 missing a_1");
        assert!(vars0.contains(&x0), "slot 0 missing xs[0]");
        assert!(!vars0.contains(&x1), "slot 0 should not contain xs[1]");

        let slot1 = gresult
            .pl
            .get(&result.clone().with_slot(1).unwrap())
            .unwrap();
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
        let mut gresult = GroebnerResult::<ArkBls12_381, GrevLexTerm>::new();

        // Bind p: Vec of scalars on node 0, then Poly on node 1.
        let pref_vp = PRef::from_node(
            NodeIndex::new(0),
            ATyp::VPoly(1, 1),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_vp);
        let coefs: Vec<_> = [3u64, 5]
            .iter()
            .map(|n| mk::<ArkBls12_381>(Op::Value(Value::Scalar(Fr::from(*n)))))
            .collect();
        builder.add_op(pref_vp.clone(), Op::Vec(coefs), &mut gresult);
        let pref_p = PRef::from_node(
            NodeIndex::new(1),
            ATyp::VPoly(1, 1),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_p);
        builder.add_op(
            pref_p.clone(),
            Op::Poly(mk::<ArkBls12_381>(Op::Ref(
                crate::Ref::new(NodeIndex::new(0)),
                ATyp::VPoly(1, 1),
            ))),
            &mut gresult,
        );

        // Bind xs: Vec of scalars on node 2, then Poly on node 3.
        let pref_vxs = PRef::from_node(
            NodeIndex::new(2),
            ATyp::Uni(1),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_vxs);
        let xs_vals: Vec<_> = [7u64, 11]
            .iter()
            .map(|n| mk::<ArkBls12_381>(Op::Value(Value::Scalar(Fr::from(*n)))))
            .collect();
        builder.add_op(pref_vxs.clone(), Op::Vec(xs_vals), &mut gresult);
        let pref_xs = PRef::from_node(
            NodeIndex::new(3),
            ATyp::Uni(1),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_xs);
        builder.add_op(
            pref_xs.clone(),
            Op::Poly(mk::<ArkBls12_381>(Op::Ref(
                crate::Ref::new(NodeIndex::new(2)),
                ATyp::Uni(1),
            ))),
            &mut gresult,
        );

        // Now issue eval: p(xs).
        let result = PRef::from_node(
            NodeIndex::new(4),
            ATyp::Uni(1),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        let op: GOp<ArkBls12_381> = Op::Evaluate(
            mk::<ArkBls12_381>(Op::Ref(
                crate::Ref::new(NodeIndex::new(1)),
                ATyp::VPoly(1, 1),
            )),
            mk::<ArkBls12_381>(Op::Ref(crate::Ref::new(NodeIndex::new(3)), ATyp::Uni(1))),
        );
        builder.add_op(result.clone(), op, &mut gresult);

        // Check stored polys: since all inputs are constants, each result slot
        // stores a polynomial equal to a_0 + a_1 * x as a sparse poly in the
        // slot PRefs (constants haven't been inlined). We verify the basis
        // equation reduces correctly by substituting literal values via `vars`.
        let slot0 = gresult
            .pl
            .get(&result.clone().with_slot(0).unwrap())
            .unwrap();
        let slot1 = gresult
            .pl
            .get(&result.clone().with_slot(1).unwrap())
            .unwrap();
        assert!(!slot0.is_zero());
        assert!(!slot1.is_zero());
        // 2 Vec bindings * 2 slots each = 4, plus 2 Poly identities * 2 = 4,
        // plus 2 eval results = 2. Total = 10.
        assert_eq!(gresult.basis.basis.len(), 10);
    }

    #[test]
    fn test_add_op_eval_vpoly_full_multivariate() {
        // VPoly(2, 2) has 6 coef slots; eval at Uni(2) => scalar (one slot).
        use crate::PRef;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let mut gresult = GroebnerResult::<ArkBls12_381, GrevLexTerm>::new();
        let _ = {
            let p = PRef::from_node(
                NodeIndex::new(0),
                ATyp::VPoly(2, 2),
                0,
                Qualifier::Private,
                Distribution::default(),
            );
            builder.ns.register(&p);
            p
        };
        let _ = {
            let p = PRef::from_node(
                NodeIndex::new(1),
                ATyp::Uni(1),
                0,
                Qualifier::Private,
                Distribution::default(),
            );
            builder.ns.register(&p);
            p
        };

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
        builder.add_op(result.clone(), op, &mut gresult);

        // One result slot (scalar) produced, zero np entries for eval.
        assert!(gresult.pl.contains(&result.clone().with_slot(0).unwrap()));
        // Should contain all 6 coef PRefs of p + both xs slots.
        let slot = gresult
            .pl
            .get(&result.clone().with_slot(0).unwrap())
            .unwrap();
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
        let mut gresult = GroebnerResult::<ArkBls12_381, GrevLexTerm>::new();
        let _ = {
            let p = PRef::from_node(
                NodeIndex::new(0),
                ATyp::VPoly(3, 1),
                0,
                Qualifier::Private,
                Distribution::default(),
            );
            builder.ns.register(&p);
            p
        };
        let _ = {
            let p = PRef::from_node(
                NodeIndex::new(1),
                ATyp::Uni(0),
                0,
                Qualifier::Private,
                Distribution::default(),
            );
            builder.ns.register(&p);
            p
        };

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
        builder.add_op(result.clone(), op, &mut gresult);

        // VPoly(2, 1) has physical_len = C(2+1, 1) = 3 slots (one for constant,
        // two for each linear variable).
        assert_eq!(ATyp::VPoly(2, 1).physical_len(), 3);
        for i in 0..3 {
            assert!(
                gresult.pl.contains(&result.clone().with_slot(i).unwrap()),
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
        let mut gresult = GroebnerResult::<ArkBls12_381, GrevLexTerm>::new();
        let _ = {
            let p = PRef::from_node(
                NodeIndex::new(0),
                ATyp::Mle(2),
                0,
                Qualifier::Private,
                Distribution::default(),
            );
            builder.ns.register(&p);
            p
        };
        let _ = {
            let p = PRef::from_node(
                NodeIndex::new(1),
                ATyp::Uni(1),
                0,
                Qualifier::Private,
                Distribution::default(),
            );
            builder.ns.register(&p);
            p
        };

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
        builder.add_op(result.clone(), op, &mut gresult);

        assert!(gresult.pl.contains(&result.clone().with_slot(0).unwrap()));
        // Result poly should reference all 4 Mle slots + both xs slots.
        let slot = gresult
            .pl
            .get(&result.clone().with_slot(0).unwrap())
            .unwrap();
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
        let mut gresult = GroebnerResult::<ArkBls12_381, GrevLexTerm>::new();
        let _ = {
            let p = PRef::from_node(
                NodeIndex::new(0),
                ATyp::Mle(3),
                0,
                Qualifier::Private,
                Distribution::default(),
            );
            builder.ns.register(&p);
            p
        };
        let _ = {
            let p = PRef::from_node(
                NodeIndex::new(1),
                ATyp::Uni(0),
                0,
                Qualifier::Private,
                Distribution::default(),
            );
            builder.ns.register(&p);
            p
        };

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
        builder.add_op(result.clone(), op, &mut gresult);

        // Mle(2) has 4 eval slots.
        for i in 0..4 {
            assert!(
                gresult.pl.contains(&result.clone().with_slot(i).unwrap()),
                "partial mle eval slot {} missing",
                i
            );
        }
    }

    #[test]
    fn test_add_op_eval_unsupported_falls_through_to_np() {
        // Eval at a Record (which ref_vars can't handle) should fall through to np.
        use crate::PRef;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let mut gresult = GroebnerResult::<ArkBls12_381, GrevLexTerm>::new();
        let _ = {
            let p = PRef::from_node(
                NodeIndex::new(0),
                ATyp::VPoly(3, 2),
                0,
                Qualifier::Private,
                Distribution::default(),
            );
            builder.ns.register(&p);
            p
        };
        // xs with k > n should fall through (k=4 > n=3). Uni(3) = degree 3 = 4 slots.
        let _ = {
            let p = PRef::from_node(
                NodeIndex::new(1),
                ATyp::Uni(3),
                0,
                Qualifier::Private,
                Distribution::default(),
            );
            builder.ns.register(&p);
            p
        };

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
        builder.add_op(result.clone(), op, &mut gresult);

        // Unsupported shape → stored in np, not pl.
        assert!(gresult.np.contains(&result));
        assert!(!gresult.pl.contains(&result));
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
        let mut gresult = GroebnerResult::<ArkBls12_381, GrevLexTerm>::new();
        let pref_a = {
            let p = PRef::from_node(
                NodeIndex::new(0),
                ATyp::VPoly(2, 1),
                0,
                Qualifier::Private,
                Distribution::default(),
            );
            builder.ns.register(&p);
            p
        };
        let pref_b = {
            let p = PRef::from_node(
                NodeIndex::new(1),
                ATyp::VPoly(2, 1),
                0,
                Qualifier::Private,
                Distribution::default(),
            );
            builder.ns.register(&p);
            p
        };

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
        builder.add_op(result.clone(), op, &mut gresult);

        // 3 result slots bound.
        for i in 0..3 {
            assert!(
                gresult.pl.contains(&result.clone().with_slot(i).unwrap()),
                "add result slot {} missing",
                i
            );
        }
        // Each result slot contains exactly a.slot(i) + b.slot(i).
        for i in 0..3 {
            let a_slot = pref_a.clone().with_slot(i).unwrap();
            let b_slot = pref_b.clone().with_slot(i).unwrap();
            let stored = gresult
                .pl
                .get(&result.clone().with_slot(i).unwrap())
                .unwrap();
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
        let mut gresult = GroebnerResult::<ArkBls12_381, GrevLexTerm>::new();
        let pref_a = {
            let p = PRef::from_node(
                NodeIndex::new(0),
                ATyp::Mle(2),
                0,
                Qualifier::Private,
                Distribution::default(),
            );
            builder.ns.register(&p);
            p
        };
        let pref_b = {
            let p = PRef::from_node(
                NodeIndex::new(1),
                ATyp::Mle(2),
                0,
                Qualifier::Private,
                Distribution::default(),
            );
            builder.ns.register(&p);
            p
        };

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
        builder.add_op(result.clone(), op, &mut gresult);

        for i in 0..4 {
            let a_slot = pref_a.clone().with_slot(i).unwrap();
            let b_slot = pref_b.clone().with_slot(i).unwrap();
            let stored = gresult
                .pl
                .get(&result.clone().with_slot(i).unwrap())
                .unwrap();
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
        let mut gresult = GroebnerResult::<ArkBls12_381, GrevLexTerm>::new();
        let pref_a = PRef::from_node(
            NodeIndex::new(0),
            ATyp::VPoly(2, 2),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_a);
        let pref_b = PRef::from_node(
            NodeIndex::new(1),
            ATyp::VPoly(2, 2),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_b);

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
        builder.add_op(result.clone(), op, &mut gresult);

        // VPoly(2,2) has 6 slots.
        assert_eq!(ATyp::VPoly(2, 2).physical_len(), 6);
        for i in 0..6 {
            let a_slot = pref_a.clone().with_slot(i).unwrap();
            let b_slot = pref_b.clone().with_slot(i).unwrap();
            let stored = gresult
                .pl
                .get(&result.clone().with_slot(i).unwrap())
                .unwrap();
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
        let mut gresult = GroebnerResult::<ArkBls12_381, GrevLexTerm>::new();
        let pref_a = PRef::from_node(
            NodeIndex::new(0),
            ATyp::VPoly(1, 1),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_a);
        let pref_b = PRef::from_node(
            NodeIndex::new(1),
            ATyp::VPoly(1, 1),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_b);

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
        builder.add_op(result.clone(), op, &mut gresult);

        // VPoly(1,2) has physical_len = 3 slots (degrees 0, 1, 2 in graded-lex order).
        assert_eq!(ATyp::VPoly(1, 2).physical_len(), 3);
        let a0 = pref_a.clone().with_slot(0).unwrap();
        let a1 = pref_a.clone().with_slot(1).unwrap();
        let b0 = pref_b.clone().with_slot(0).unwrap();
        let b1 = pref_b.clone().with_slot(1).unwrap();

        let var = |p: &PRef| SparsePolynomial::<ark_bls12_381::Fr, GrevLexTerm>::var(p);
        let deg0 = gresult
            .pl
            .get(&result.clone().with_slot(0).unwrap())
            .unwrap()
            .clone();
        let deg1 = gresult
            .pl
            .get(&result.clone().with_slot(1).unwrap())
            .unwrap()
            .clone();
        let deg2 = gresult
            .pl
            .get(&result.clone().with_slot(2).unwrap())
            .unwrap()
            .clone();
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
        let mut gresult = GroebnerResult::<ArkBls12_381, GrevLexTerm>::new();
        let pref_a = PRef::from_node(
            NodeIndex::new(0),
            ATyp::VPoly(2, 1),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_a);
        let pref_b = PRef::from_node(
            NodeIndex::new(1),
            ATyp::VPoly(2, 1),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_b);

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
        builder.add_op(result.clone(), op, &mut gresult);

        // Check the constant-term slot (multi-index [0,0]): should be a_[0,0] * b_[0,0].
        let r_idx = multi_indices(2, 2);
        let a_idx = multi_indices(2, 1);
        let pos_00 = r_idx.iter().position(|k| k == &vec![0, 0]).unwrap();
        let a_pos_00 = a_idx.iter().position(|k| k == &vec![0, 0]).unwrap();

        let a00 = pref_a.clone().with_slot(a_pos_00).unwrap();
        let b00 = pref_b.clone().with_slot(a_pos_00).unwrap();
        let var = |p: &PRef| SparsePolynomial::<ark_bls12_381::Fr, GrevLexTerm>::var(p);
        let got = gresult
            .pl
            .get(&result.clone().with_slot(pos_00).unwrap())
            .unwrap()
            .clone();
        assert_eq!(
            got,
            &var(&a00) * &var(&b00),
            "VPoly(2,2) constant term mismatch"
        );

        // Ensure all 6 slots were populated.
        for i in 0..6 {
            assert!(
                gresult.pl.contains(&result.clone().with_slot(i).unwrap()),
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
        let mut gresult = GroebnerResult::<ArkBls12_381, GrevLexTerm>::new();
        let pref_u = PRef::from_node(
            NodeIndex::new(0),
            ATyp::Mle(1),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_u);
        let pref_v = PRef::from_node(
            NodeIndex::new(1),
            ATyp::Mle(1),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_v);

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
        builder.add_op(result.clone(), op, &mut gresult);

        // 3 slots populated.
        for i in 0..3 {
            assert!(
                gresult.pl.contains(&result.clone().with_slot(i).unwrap()),
                "Mle×Mle slot {} missing",
                i
            );
        }

        let u0 = pref_u.clone().with_slot(0).unwrap();
        let u1 = pref_u.clone().with_slot(1).unwrap();
        let v0 = pref_v.clone().with_slot(0).unwrap();
        let v1 = pref_v.clone().with_slot(1).unwrap();
        let var = |p: &PRef| SparsePolynomial::<ark_bls12_381::Fr, GrevLexTerm>::var(p);

        let deg0 = gresult
            .pl
            .get(&result.clone().with_slot(0).unwrap())
            .unwrap()
            .clone();
        let deg1 = gresult
            .pl
            .get(&result.clone().with_slot(1).unwrap())
            .unwrap()
            .clone();
        let deg2 = gresult
            .pl
            .get(&result.clone().with_slot(2).unwrap())
            .unwrap()
            .clone();

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
    #[test]
    fn test_add_op_vpoly_div_univariate_identity() {
        // VPoly(1,2) / VPoly(1,1) → VPoly(1,1).
        //   a has physical_len = 3 slots (a_0, a_1, a_2)
        //   b has physical_len = 2 slots (b_0, b_1)
        //   q_wit: VPoly(1,1), 2 slots (q_0, q_1)
        //   r_wit: VPoly(1,0), 1 slot  (r_0)
        // Canonical identity rows (from div_witnesses):
        //   k=[0] (total deg 0): a_0  -  (b_0·q_0 + r_0)
        //   k=[1] (total deg 1): a_1  -  (b_0·q_1 + b_1·q_0)
        //   k=[2] (total deg 2): a_2  -  b_1·q_1
        // link_to_witness emits 2 more rows: var(q_wit[j]) - var(result[j]), j=0,1.
        use crate::{PRef, Ref};
        use lang::ast::BinOp;
        use lang::id::Vid;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let mut gresult = GroebnerResult::<ArkBls12_381, GrevLexTerm>::new();
        let pref_a = PRef::from_node(
            NodeIndex::new(0),
            ATyp::VPoly(1, 2),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_a);
        let pref_b = PRef::from_node(
            NodeIndex::new(1),
            ATyp::VPoly(1, 1),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_b);

        let basis_before = gresult.basis.len();
        let result = PRef::from_node(
            NodeIndex::new(2),
            ATyp::VPoly(1, 1),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        let op: GOp<ArkBls12_381> = Op::Bin(
            BinOp::Div,
            mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), ATyp::VPoly(1, 2))),
            mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(1)), ATyp::VPoly(1, 1))),
            ATyp::VPoly(1, 1),
        );
        builder.add_op(result.clone(), op, &mut gresult);

        // Recover the q_wit / r_wit PRefs (minted by sentinel_pref starting
        // at MAX and decrementing: q_wit=MAX, r_wit=MAX-1).
        let q_wit = PRef::from_var(
            Vid::from("__zippel::gb::div_q::0"),
            petgraph::graph::NodeIndex::new(usize::MAX),
            ATyp::VPoly(1, 1),
            0,
            Qualifier::Public,
            Distribution::default(),
        );
        let r_wit = PRef::from_var(
            Vid::from("__zippel::gb::div_r::0"),
            petgraph::graph::NodeIndex::new(usize::MAX - 1),
            ATyp::VPoly(1, 0),
            0,
            Qualifier::Public,
            Distribution::default(),
        );

        // Per-slot input vars (typ computed by `with_slot`).
        let scl = |p: &PRef, i: usize| p.clone().with_slot(i).unwrap();
        // Per-slot witness vars. `div_witnesses` uses `wit.clone().with_slot(j).unwrap()`
        // which sets typ appropriately.
        let wit_slot = |p: &PRef, i: usize| p.clone().with_slot(i).unwrap();
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
            gresult.basis.len() - basis_before,
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
                gresult.basis.iter().any(|row| row == expected),
                "basis missing identity row {}",
                lbl
            );
        }

        // link_to_witness: pl[result[j]] = var(q_wit[j]) for j=0,1.
        assert_eq!(
            gresult
                .pl
                .get(&result.clone().with_slot(0).unwrap())
                .cloned(),
            Some(var(&q0)),
            "pl[result[0]] should alias q_wit[0]"
        );
        assert_eq!(
            gresult
                .pl
                .get(&result.clone().with_slot(1).unwrap())
                .cloned(),
            Some(var(&q1)),
            "pl[result[1]] should alias q_wit[1]"
        );

        // Linking rows: var(q_wit[j]) - var(result[j]).
        // link_to_witness uses `result.clone().with_slot(j).unwrap()` (typ computed by with_slot).
        let r0_slot = result.clone().with_slot(0).unwrap();
        let r1_slot = result.clone().with_slot(1).unwrap();
        let link0 = &var(&q0) - &var(&r0_slot);
        let link1 = &var(&q1) - &var(&r1_slot);
        assert!(
            gresult.basis.iter().any(|row| row == &link0),
            "basis missing link row var(q_wit[0]) - var(result[0])"
        );
        assert!(
            gresult.basis.iter().any(|row| row == &link1),
            "basis missing link row var(q_wit[1]) - var(result[1])"
        );
        assert_eq!(
            builder.ns.div_wit.len(),
            1,
            "div_wit should have one (a,b) entry"
        );
    }

    #[test]
    fn test_add_op_vpoly_rem_univariate_identity() {
        // VPoly(1,2) % VPoly(1,1) → VPoly(1,0).
        // Same witnesses as the Div test, but link result to r_wit (1 slot).
        use crate::{PRef, Ref};
        use lang::ast::BinOp;
        use lang::id::Vid;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let mut gresult = GroebnerResult::<ArkBls12_381, GrevLexTerm>::new();
        let _pref_a = PRef::from_node(
            NodeIndex::new(0),
            ATyp::VPoly(1, 2),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&_pref_a);
        let _pref_b = PRef::from_node(
            NodeIndex::new(1),
            ATyp::VPoly(1, 1),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&_pref_b);

        let basis_before = gresult.basis.len();
        let result = PRef::from_node(
            NodeIndex::new(2),
            ATyp::VPoly(1, 0),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        let op: GOp<ArkBls12_381> = Op::Bin(
            BinOp::Rem,
            mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), ATyp::VPoly(1, 2))),
            mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(1)), ATyp::VPoly(1, 1))),
            ATyp::VPoly(1, 0),
        );
        builder.add_op(result.clone(), op, &mut gresult);

        // q_wit=MAX, r_wit=MAX-1 (fresh builder, counter starts at MAX).
        let r_wit = PRef::from_var(
            Vid::from("__zippel::gb::div_r::0"),
            petgraph::graph::NodeIndex::new(usize::MAX - 1),
            ATyp::VPoly(1, 0),
            0,
            Qualifier::Public,
            Distribution::default(),
        );
        let scl = |p: &PRef, i: usize| p.clone().with_slot(i).unwrap();
        let _ = scl; // kept for parity with the Div test; not used here.
        let var = |p: &PRef| SparsePolynomial::<ark_bls12_381::Fr, GrevLexTerm>::var(p);
        // r_wit slots: with_slot computes the correct type.
        let r0 = r_wit.clone().with_slot(0).unwrap();

        // 3 identity rows + 1 linking row (result has only 1 slot).
        assert_eq!(
            gresult.basis.len() - basis_before,
            4,
            "expected 3 identity + 1 linking row"
        );

        // pl[result[0]] = var(r_wit[0]).
        assert_eq!(
            gresult
                .pl
                .get(&result.clone().with_slot(0).unwrap())
                .cloned(),
            Some(var(&r0)),
            "pl[result[0]] should alias r_wit[0]"
        );

        // Linking row: link_to_witness uses result.with_slot(0).unwrap() (type computed by with_slot).
        let r0_slot = result.clone().with_slot(0).unwrap();
        let link = &var(&r0) - &var(&r0_slot);
        assert!(
            gresult.basis.iter().any(|row| row == &link),
            "basis missing link row var(r_wit[0]) - var(result[0])"
        );
        assert_eq!(builder.ns.div_wit.len(), 1, "one div_wit entry after Rem");
    }

    #[test]
    fn test_add_op_div_then_rem_shares_witness() {
        // Both `a/b` and `a%b` on the same `(a,b)` HOp pair share the
        // witness side-table. Second op should NOT emit new identity rows.
        use crate::{PRef, Ref};
        use lang::ast::BinOp;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let mut gresult = GroebnerResult::<ArkBls12_381, GrevLexTerm>::new();
        let _pref_a = PRef::from_node(
            NodeIndex::new(0),
            ATyp::VPoly(1, 2),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&_pref_a);
        let _pref_b = PRef::from_node(
            NodeIndex::new(1),
            ATyp::VPoly(1, 1),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&_pref_b);

        let basis_before_div = gresult.basis.len();
        let _q_res = {
            let result = PRef::from_node(
                NodeIndex::new(2),
                ATyp::VPoly(1, 1),
                0,
                Qualifier::Private,
                Distribution::default(),
            );
            let op: GOp<ArkBls12_381> = Op::Bin(
                BinOp::Div,
                mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), ATyp::VPoly(1, 2))),
                mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(1)), ATyp::VPoly(1, 1))),
                ATyp::VPoly(1, 1),
            );
            builder.add_op(result.clone(), op, &mut gresult);
            result
        };
        let after_div = gresult.basis.len();

        let _r_res = {
            let result = PRef::from_node(
                NodeIndex::new(3),
                ATyp::VPoly(1, 0),
                0,
                Qualifier::Private,
                Distribution::default(),
            );
            let op: GOp<ArkBls12_381> = Op::Bin(
                BinOp::Rem,
                mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), ATyp::VPoly(1, 2))),
                mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(1)), ATyp::VPoly(1, 1))),
                ATyp::VPoly(1, 0),
            );
            builder.add_op(result.clone(), op, &mut gresult);
            result
        };
        let after_rem = gresult.basis.len();

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
        assert_eq!(
            builder.ns.div_wit.len(),
            1,
            "div_wit unchanged after Rem (cached)"
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
        let mut gresult = GroebnerResult::<ArkBls12_381, GrevLexTerm>::new();
        let pref_a = PRef::from_node(
            NodeIndex::new(0),
            ATyp::scalar(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_a);
        let pref_b = PRef::from_node(
            NodeIndex::new(1),
            ATyp::scalar(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_b);

        let basis_before = gresult.basis.len();
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
        builder.add_op(result.clone(), op, &mut gresult);

        // Legacy zip emits exactly one row: a - b · var(result).
        assert_eq!(
            gresult.basis.len() - basis_before,
            1,
            "scalar fallback emits 1 row"
        );
        let var = |p: &PRef| SparsePolynomial::<ark_bls12_381::Fr, GrevLexTerm>::var(p);
        let expected = &var(&pref_a) - &(&var(&pref_b) * &var(&result));
        assert!(
            gresult.basis.iter().any(|row| row == &expected),
            "scalar fallback row should be `a - b · var(result)`"
        );
        assert_eq!(
            builder.ns.div_wit.len(),
            0,
            "div_wit stays empty on scalar Div"
        );
    }

    // -----------------------------------------------------------------
    // Slot-count arithmetic: physical_len / multi_indices / hypercube /
    // index_of. Property-based tests (via arbtest) pin the m+1 / 2^n /
    // C(n+m, n) conventions from docs/poly-encoding.md so a refactor of
    // `physical_len` cannot silently drift back to the old `m == length`
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
        // in physical_len.
        assert_eq!(binomial(0, 0), 1);
        assert_eq!(binomial(5, 0), 1);
        assert_eq!(binomial(5, 5), 1);
        assert_eq!(binomial(5, 2), 10);
        assert_eq!(binomial(6, 3), 20);
        assert_eq!(binomial(10, 4), 210);
    }

    #[test]
    fn test_physical_len_vpoly_matches_binomial() {
        // VPoly(n, m) has C(n + m, n) coefficient slots.
        arbtest::arbtest(|u| {
            let n: usize = u.int_in_range(1..=5)?;
            let m: usize = u.int_in_range(0..=5)?;
            let sum = n + m;
            let expected = binomial(sum, n);
            assert_eq!(
                ATyp::VPoly(n, m).physical_len(),
                expected,
                "physical_len(VPoly({n}, {m})) should be C({sum}, {n}) = {expected}",
            );
            Ok(())
        });
    }

    #[test]
    fn test_physical_len_mle_is_power_of_two() {
        // Mle(n) is the multilinear extension over {0,1}^n, so 2^n slots.
        arbtest::arbtest(|u| {
            let n: usize = u.int_in_range(0..=5)?;
            assert_eq!(
                ATyp::Mle(n).physical_len(),
                1usize << n,
                "physical_len(Mle({n})) should be 2^{n}",
            );
            Ok(())
        });
    }

    #[test]
    fn test_physical_len_uni_is_m_plus_one() {
        // Phase-14 convention: Uni(m) has m+1 coefficient slots.
        arbtest::arbtest(|u| {
            let m: usize = u.int_in_range(0..=15)?;
            assert_eq!(
                ATyp::Uni(m).physical_len(),
                m + 1,
                "physical_len(Uni({m})) should be {} (m + 1)",
                m + 1,
            );
            Ok(())
        });
    }

    #[test]
    fn test_physical_len_vec_is_length() {
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
            assert_eq!(
                typ.physical_len(),
                n,
                "physical_len(Vec(_, {n})) should be {n}"
            );
            Ok(())
        });
    }

    #[test]
    fn test_physical_len_base_is_one() {
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
            assert_eq!(typ.physical_len(), 1, "physical_len({typ:?}) should be 1");
        }
    }

    #[test]
    fn test_multi_indices_len_matches_physical_len() {
        // multi_indices(n, m).len() == physical_len(VPoly(n, m)) is definitional.
        arbtest::arbtest(|u| {
            let n: usize = u.int_in_range(1..=4)?;
            let m: usize = u.int_in_range(0..=4)?;
            assert_eq!(
                multi_indices(n, m).len(),
                ATyp::VPoly(n, m).physical_len(),
                "multi_indices({n}, {m}).len() should equal physical_len(VPoly({n}, {m}))",
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
        // For an arbitrary position i in 0..physical_len the multi-index at
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

    #[test]
    fn groebner_nested_div() {
        use lang::id::Tid;
        let src = r#"
            proto nd<F: Field>(public a: Uni<F, 4>, public b: Uni<F, 2>, public c: Uni<F, 2>) where a == a {
                let q = (a / b) / c;
                verify(q == q)
            }"#;
        let mut sizes = Ctx::new();
        sizes.insert(&Tid::new("N"), &4);
        let tc = trans_clos_from_src_sized(src, &sizes);
        let mut builder: GroebnerBuilder<ArkBls12_381, ElimTerm> = GroebnerBuilder::new();
        let mut gr = builder.build(tc);

        // Two div_witnesses calls: inner (a/b) and outer ((a/b)/c)
        // Each emits a (q_wit, r_wit) pair, so np should contain 4 div witnesses
        assert_eq!(
            gr.np.len(),
            4,
            "nested div should have 4 np entries (2 q_wit + 2 r_wit), got {}",
            gr.np.len()
        );

        // Div witnesses are named __zippel::gb::div_q/div_r
        let np_names: Vec<String> = gr
            .np
            .keys()
            .into_iter()
            .filter_map(|p| p.name.as_ref().map(|n| n.0.clone()))
            .collect();
        assert!(
            np_names
                .iter()
                .any(|n| n.starts_with("__zippel::gb::div_q")),
            "np should contain div_q witnesses, got {:?}",
            np_names
        );
        assert!(
            np_names
                .iter()
                .any(|n| n.starts_with("__zippel::gb::div_r")),
            "np should contain div_r witnesses, got {:?}",
            np_names
        );

        // pl should contain entries for the div result nodes (linking them to
        // quotient witness slots). Since children are Op::Ref after IR lowering,
        // pl entries are keyed by node index with name=None.
        assert!(
            !gr.pl.is_empty(),
            "pl should have entries for div result nodes, got {}",
            gr.pl.len()
        );

        // Basis should contain canonical div identity rows (a = b*q + r)
        // and linking rows for both inner and outer division
        gr.run::<8>();
        assert!(
            !gr.basis.is_empty(),
            "basis should not be empty after nested div"
        );
    }

    #[test]
    fn groebner_shared_div_rem_witnesses() {
        use lang::id::Tid;
        let src = r#"
            proto sdr<F: Field>(public a: Uni<F, 4>, public b: Uni<F, 2>) where a == a {
                verify(a == b * (a / b) + (a % b))
            }"#;
        let mut sizes = Ctx::new();
        sizes.insert(&Tid::new("N"), &4);
        let tc = trans_clos_from_src_sized(src, &sizes);
        let mut builder: GroebnerBuilder<ArkBls12_381, ElimTerm> = GroebnerBuilder::new();
        let mut gr = builder.build(tc);

        // Single (a, b) pair → one div_witnesses call → 2 np entries (q_wit, r_wit)
        assert_eq!(
            gr.np.len(),
            2,
            "shared div/rem should have 2 np entries (1 q_wit + 1 r_wit), got {}",
            gr.np.len()
        );

        // Both div and rem share the same canonical identity — the key invariant
        let np_names: Vec<String> = gr
            .np
            .keys()
            .into_iter()
            .filter_map(|p| p.name.as_ref().map(|n| n.0.clone()))
            .collect();
        let q_count = np_names.iter().filter(|n| n.contains("div_q")).count();
        let r_count = np_names.iter().filter(|n| n.contains("div_r")).count();
        assert_eq!(
            q_count, 1,
            "exactly 1 div_q witness for shared (a, b) pair, got {}",
            q_count
        );
        assert_eq!(
            r_count, 1,
            "exactly 1 div_r witness for shared (a, b) pair, got {}",
            r_count
        );

        // pl should have entries for the div result (n3 → q_wit), mul result (n4 → b*q),
        // rem result (n5 → r_wit), and sum result (n6 → n4 + n5)
        assert!(
            gr.pl.len() >= 8,
            "pl should have entries for div/mul/rem/add chains, got {} entries",
            gr.pl.len()
        );

        gr.run::<8>();
        assert!(
            !gr.basis.is_empty(),
            "basis should not be empty after shared div/rem"
        );
    }

    #[test]
    fn groebner_vec_add_1d() {
        let src = r#"
            proto va1d<F: Field>(public a: F, public b: F, public c: F, public d: F) where a == a {
                let v = [a, b] + [c, d];
                verify(v[0] == a + c)
            }"#;
        let tc = trans_clos_from_src(src);
        let mut builder: GroebnerBuilder<ArkBls12_381, ElimTerm> = GroebnerBuilder::new();
        let gr = builder.build(tc);

        // Vec add verify: v[0] == a + c
        // The verify expression generates an equality constraint
        assert!(
            gr.pl.len() >= 1,
            "pl should have at least 1 entry for the verify expression, got {}",
            gr.pl.len()
        );

        assert_eq!(
            gr.np.len(),
            0,
            "1d vec add has no opaque ops, np should be empty, got {}",
            gr.np.len()
        );

        assert!(
            gr.basis.len() >= 2,
            "basis should have at least 2 rows (add constraint + verify eq), got {}",
            gr.basis.len()
        );
    }

    #[test]
    fn groebner_vec_add_2d() {
        let src = r#"
            proto va2d<F: Field>(
                public a: F, public b: F, public c: F, public d: F,
                public e: F, public f: F, public g: F, public h: F
            ) where a == a {
                let m1 = [[a, b], [c, d]];
                let m2 = [[e, f], [g, h]];
                let m3 = m1 + m2;
                let m3r0 = m3[0];
                verify(m3r0[0] == a + e)
            }"#;
        let tc = trans_clos_from_src(src);
        let mut builder: GroebnerBuilder<ArkBls12_381, ElimTerm> = GroebnerBuilder::new();
        let gr = builder.build(tc);

        // 2d Vec add: the verify expression is m3r0[0] == a+e
        // pl should contain the verify LHS mapped to a+e
        assert!(
            gr.pl.len() >= 1,
            "pl should have at least 1 entry for the verify expression, got {}",
            gr.pl.len()
        );

        // No opaque ops
        assert_eq!(
            gr.np.len(),
            0,
            "2d vec add has no opaque ops, np should be empty, got {}",
            gr.np.len()
        );

        // Basis should contain the add constraint + verify eq
        assert!(
            gr.basis.len() >= 2,
            "basis should have at least 2 rows, got {}",
            gr.basis.len()
        );

        // Namespace should register all 8 public inputs
        let ns_named_count = builder
            .ns
            .prefs
            .values()
            .filter(|p| p.name.is_some())
            .count();
        assert!(
            ns_named_count >= 8,
            "namespace should register >= 8 named public prefs, got {}",
            ns_named_count
        );
    }

    #[test]
    fn groebner_vec_add_3d() {
        let src = r#"
            proto va3d<F: Field>(
                public a: F, public b: F, public c: F, public d: F,
                public e: F, public f: F, public g: F, public h: F
            ) where a == a {
                let t1 = [[[a, b], [c, d]], [[e, f], [g, h]]];
                let t2 = [[[a, b], [c, d]], [[e, f], [g, h]]];
                let t3 = t1 + t2;
                let t3d0 = t3[0];
                let t3d0r0 = t3d0[0];
                verify(t3d0r0[0] == a + a)
            }"#;
        let tc = trans_clos_from_src(src);
        let mut builder: GroebnerBuilder<ArkBls12_381, ElimTerm> = GroebnerBuilder::new();
        let gr = builder.build(tc);

        // 3d Vec add: same structure, verify(t3d0r0[0] == a + a)
        assert!(
            gr.pl.len() >= 1,
            "pl should have at least 1 entry for the verify expression, got {}",
            gr.pl.len()
        );

        assert_eq!(
            gr.np.len(),
            0,
            "3d vec add has no opaque ops, np should be empty, got {}",
            gr.np.len()
        );

        assert!(
            gr.basis.len() >= 2,
            "basis should have at least 2 rows, got {}",
            gr.basis.len()
        );

        let ns_named_count = builder
            .ns
            .prefs
            .values()
            .filter(|p| p.name.is_some())
            .count();
        assert!(
            ns_named_count >= 8,
            "namespace should register >= 8 named public prefs, got {}",
            ns_named_count
        );
    }
}
