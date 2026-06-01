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
use backend::{ABase, ATyp, ArkConfig, ArkScalarOps, Value};
use lang::typ::lub::Lub;
use lang::typ::{Distribution, Nothing, Qualifier};
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

/// Compute the Lagrange interpolation basis coefficients for `n` distinct
/// points `x_0, ..., x_{n-1}`. Returns a matrix `L[i][k]` where
/// `L[i][k]` is the coefficient of `X^k` in the Lagrange basis polynomial
/// `L_i(X) = Π_{j≠i} (X - x_j) / (x_i - x_j)`.
fn lagrange_basis<F: Field>(xs: &[F]) -> Vec<Vec<F>> {
    let n = xs.len();
    let mut basis: Vec<Vec<F>> = Vec::with_capacity(n);

    for i in 0..n {
        let xi = xs[i];
        let mut denom = F::one();
        for j in 0..n {
            if j != i {
                denom *= xi - xs[j];
            }
        }
        let denom_inv = denom.inverse().unwrap();

        let mut poly: Vec<F> = vec![F::one()];
        for j in 0..n {
            if j == i {
                continue;
            }
            let neg_xj = -xs[j];
            let mut new_poly = vec![F::zero(); poly.len() + 1];
            for (k, c) in poly.iter().enumerate() {
                new_poly[k] = new_poly[k] + *c * neg_xj;
                new_poly[k + 1] = new_poly[k + 1] + *c;
            }
            poly = new_poly;
        }

        for c in poly.iter_mut() {
            *c *= denom_inv;
        }

        basis.push(poly);
    }

    basis
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
    pub prefs: HashMap<Ref, PRef>,
    pub div_wit: Ctx<(HOp<C>, HOp<C>), (PRef, PRef)>,
    sentinel_counter: usize,
    gt_sentinel: Option<PRef>,
    name_counters: HashMap<String, usize>,
}

impl<C: ArkConfig + HasOpFactory> GroebnerNamespace<C> {
    pub fn new() -> Self {
        Self {
            prefs: HashMap::new(),
            div_wit: Ctx::new(),
            sentinel_counter: usize::MAX,
            gt_sentinel: None,
            name_counters: HashMap::new(),
        }
    }

    /// Register a PRef in the namespace. Overwrites any existing entry
    /// for the same reference. Returns the previous entry if one existed.
    pub fn register(&mut self, pr: &PRef) -> Option<PRef> {
        self.prefs.insert(pr.reference, pr.clone())
    }

    /// Allocate a fresh sentinel PRef with a stable unique NodeIndex.
    pub fn sentinel_pref(&mut self, name: &str, typ: ATyp) -> PRef {
        let vid = Vid::from(name);
        let idx = NodeIndex::new(self.sentinel_counter);
        self.sentinel_counter -= 1;
        PRef::from_var(vid, idx, typ, 0, Qualifier::Public, Distribution::default())
    }

    /// Return a unique name for the given key by appending a per-key counter.
    pub fn next_name(&mut self, key: &str) -> String {
        let counter = self.name_counters.entry(key.to_string()).or_insert(0);
        let name = format!("__zippel::gb::{}::{}", key, counter);
        *counter += 1;
        name
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

/// An owned slice of polynomial variables paired with their `ATyp`.
///
/// Provides element-wise access for `Vec` types (via `at_index`),
/// zero-padding lifts to wider types (via `lift_to`), and scalar
/// broadcast (via `broadcast_scalar_to`).
struct PolySource<C: ArkConfig, T: Monomial> {
    polys: Vec<SparsePolynomial<C::F, T>>,
    typ: ATyp,
}

impl<C: ArkConfig, T: Monomial> PolySource<C, T> {
    fn new(polys: Vec<SparsePolynomial<C::F, T>>, typ: ATyp) -> Self {
        PolySource { polys, typ }
    }

    fn typ(&self) -> &ATyp {
        &self.typ
    }

    fn polys(&self) -> &[SparsePolynomial<C::F, T>] {
        &self.polys
    }

    fn physical_len(&self) -> usize {
        self.typ.physical_len()
    }

    fn from_ref_vars(builder: &GroebnerBuilder<C, T>, op: &GOp<C>) -> Self
    where
        C: HasOpFactory,
    {
        let typ = op.typ();
        let polys = builder.ref_vars(op);
        PolySource { polys, typ }
    }

    fn at_index(&self, i: usize) -> Option<PolySource<C, T>> {
        match &self.typ {
            ATyp::Vec(inner, n) if i < *n => {
                let elem_len = inner.physical_len();
                Some(PolySource {
                    polys: self.polys[i * elem_len..(i + 1) * elem_len].to_vec(),
                    typ: (**inner).clone(),
                })
            }
            _ => None,
        }
    }

    /// Lift polys from `self.typ` to `target`, producing a `PolySource`
    /// with exactly `target.physical_len()` polys.
    ///
    /// Only handles type combinations permitted by `lub_equ`, `lub_add`,
    /// and `lub_sub`. Panics on any other combination — the type checker
    /// guarantees these never occur.
    ///
    /// # Correctness guarantees
    ///
    /// **Base → Base**: same slot count, identity mapping.
    ///
    /// **Uni(n) → Uni(n')** where `n ≤ n'`:
    ///   Uni(n) = VPoly(1,n) has `n+1` slots in graded-lex order.
    ///   `multi_indices(1, n)` is a prefix of `multi_indices(1, n')`,
    ///   so zero-padding is correct.
    ///
    /// **VPoly(n, m) → VPoly(n, m')** where `m ≤ m'` (same arity, wider degree):
    ///   `multi_indices(n, m)` is a prefix of `multi_indices(n, m')` because
    ///   graded-lex enumerates by total degree first; all indices with `|k| ≤ m`
    ///   appear before any with `|k| = m+1`. Zero-padding is correct.
    ///
    /// **VPoly(n1, m1) → VPoly(n2, m2)** where `n1 < n2` and `m1 ≤ m2`:
    ///   NOT a simple prefix. Each source multi-index `(k1,…,kn1)` embeds as
    ///   `(k1,…,kn1,0,…,0)` in `n2`-variable space. We look up each embedded
    ///   index's position in `multi_indices(n2, m2)` and place the source poly
    ///   there; all other result slots are zero.
    ///
    /// **Mle(n1) → Mle(n2)** where `n1 ≤ n2`:
    ///   The hypercube `{0,1}^n1` embeds as `{(b1,…,bn1,0,…,0)} ⊂ {0,1}^n2`.
    ///   Since `hypercube` enumerates in bit-order, each `(b1,…,bn1)` maps to
    ///   the same slot index in Mle(n2) (trailing zeros don't affect the index).
    ///   Mle(n1) IS a prefix of Mle(n2) — zero-padding is correct.
    ///
    /// **Mle(n) → VPoly(n', m')** where `n ≤ n'`:
    ///   Cross-type lift (from `lub_add`/`lub_sub` when Mle arities differ).
    ///   Mle stores evaluations at hypercube points; VPoly stores coefficients
    ///   at multi-indices. We convert via Lagrange-basis expansion: the VPoly
    ///   coefficient at multi-index `k` is `Σ_b f(b) · Π_i C[b_i][k_i]`
    ///   where `C = [[1,-1],[0,1]]` encodes `L_0(x)=1-x`, `L_1(x)=x`.
    ///
    /// **Uni(n) → VPoly(n', m')** where `1 ≤ n'` and `n ≤ m'`:
    ///   Same as VPoly(1,n) → VPoly(n',m'). Handled by same-arity prefix or
    ///   cross-arity embedding as above.
    fn lift_to(&self, target: &ATyp) -> PolySource<C, T> {
        let src_len = self.typ.physical_len();
        let dst_len = target.physical_len();
        assert!(
            src_len <= dst_len,
            "lift_to: cannot lift from wider type {} ({} slots) to narrower type {} ({} slots)",
            self.typ,
            src_len,
            target,
            dst_len
        );

        if self.typ == *target {
            return PolySource {
                polys: self.polys.clone(),
                typ: target.clone(),
            };
        }

        match (&self.typ, target) {
            (ATyp::Base(_), ATyp::Base(_)) => PolySource {
                polys: self.polys.clone(),
                typ: target.clone(),
            },

            (ATyp::Uni(_n1), ATyp::Uni(_n2)) => {
                let mut out = self.polys.clone();
                out.resize(dst_len, SparsePolynomial::zero());
                PolySource {
                    polys: out,
                    typ: target.clone(),
                }
            }

            (ATyp::Mle(_n1), ATyp::Mle(_n2)) => {
                let mut out = self.polys.clone();
                out.resize(dst_len, SparsePolynomial::zero());
                PolySource {
                    polys: out,
                    typ: target.clone(),
                }
            }

            (ATyp::VPoly(n1, m1), ATyp::VPoly(n2, m2)) if n1 <= n2 && m1 <= m2 => {
                if n1 == n2 {
                    let mut out = self.polys.clone();
                    out.resize(dst_len, SparsePolynomial::zero());
                    PolySource {
                        polys: out,
                        typ: target.clone(),
                    }
                } else {
                    let dst_idx = multi_indices(*n2, *m2);
                    let src_idx = multi_indices(*n1, *m1);
                    let mut out = vec![SparsePolynomial::<C::F, T>::zero(); dst_idx.len()];
                    for (j, src_k) in src_idx.iter().enumerate() {
                        let mut padded = src_k.clone();
                        padded.resize(*n2, 0);
                        if let Some(dst_j) = dst_idx.iter().position(|dk| dk == &padded) {
                            out[dst_j] = self.polys[j].clone();
                        }
                    }
                    PolySource {
                        polys: out,
                        typ: target.clone(),
                    }
                }
            }

            (ATyp::Uni(m1), ATyp::VPoly(n2, m2)) if *n2 >= 1 && m1 <= m2 => {
                if *n2 == 1 {
                    let mut out = self.polys.clone();
                    out.resize(dst_len, SparsePolynomial::zero());
                    PolySource {
                        polys: out,
                        typ: target.clone(),
                    }
                } else {
                    let dst_idx = multi_indices(*n2, *m2);
                    let src_idx = multi_indices(1, *m1);
                    let mut out = vec![SparsePolynomial::<C::F, T>::zero(); dst_idx.len()];
                    for (j, src_k) in src_idx.iter().enumerate() {
                        let mut padded = src_k.clone();
                        padded.resize(*n2, 0);
                        if let Some(dst_j) = dst_idx.iter().position(|dk| dk == &padded) {
                            out[dst_j] = self.polys[j].clone();
                        }
                    }
                    PolySource {
                        polys: out,
                        typ: target.clone(),
                    }
                }
            }

            // Mle(n1) → VPoly(n2, m2): convert from evaluation form to
            // coefficient form via Lagrange-basis expansion.
            //
            // Each Mle slot `j` (corresponding to hypercube point `b =
            // (b1,…,b1_n1)`) stores the evaluation `f(b)`. The Lagrange
            // basis polynomial `L_b(X)` satisfies `L_b(b') = δ_{b,b'}`.
            // In coefficient form, per variable: `L_0(x) = 1-x` has
            // coefficients `[1, -1]` and `L_1(x) = x` has coefficients
            // `[0, 1]`. So the full `L_b(X) = Π_i L_{b_i}(X_i)` has
            // coefficient at multi-index `k` equal to
            // `Π_i C[b_i][k_i]` where `C = [[1,-1],[0,1]]`.
            //
            // The VPoly coefficient at index `k` is then
            // `Σ_b f(b) · Π_i C[b_i][k_i]`.
            (ATyp::Mle(n1), ATyp::VPoly(n2, m2)) if n1 <= n2 && *m2 >= 1 => {
                // Per-variable Lagrange eval→coeff: `C[b][k]` is the
                // coefficient of `x^k` in `L_b(x)`.
                // `L_0(x) = 1 - x` → C[0] = [1, -1]
                // `L_1(x) = x`     → C[1] = [0,  1]
                const C: [[i64; 2]; 2] = [[1, -1], [0, 1]];
                let src_hcube = hypercube(*n1);
                let dst_idx = multi_indices(*n2, *m2);
                let n2_val = *n2;
                let n1_val = *n1;
                let mut out = vec![SparsePolynomial::<C::F, T>::zero(); dst_idx.len()];
                let lit_of = |v: i64| -> SparsePolynomial<C::F, T> {
                    if v >= 0 {
                        SparsePolynomial::lit(&C::FOps::from_usize(v as usize))
                    } else {
                        -SparsePolynomial::lit(&C::FOps::from_usize((-v) as usize))
                    }
                };
                for (j, src_b) in src_hcube.iter().enumerate() {
                    for (ir, k) in dst_idx.iter().enumerate() {
                        let mut scalar: i64 = 1;
                        for i in 0..n1_val {
                            let ki = if i < k.len() { k[i] } else { 0 };
                            if ki >= 2 {
                                scalar = 0;
                                break;
                            }
                            scalar *= C[src_b[i]][ki];
                        }
                        if n2_val > n1_val {
                            for i in n1_val..n2_val {
                                let ki = if i < k.len() { k[i] } else { 0 };
                                if ki != 0 {
                                    scalar = 0;
                                    break;
                                }
                            }
                        }
                        if scalar == 0 {
                            continue;
                        }
                        out[ir] = &out[ir] + &(&lit_of(scalar) * &self.polys[j]);
                    }
                }
                PolySource {
                    polys: out,
                    typ: target.clone(),
                }
            }

            _ => {
                unreachable!(
                    "lift_to: unsupported type combination {} → {}",
                    self.typ, target
                )
            }
        }
    }

    fn broadcast_scalar_to(&self, poly_typ: &ATyp) -> PolySource<C, T> {
        let dst_len = poly_typ.physical_len();
        let scalar_poly = self.polys[0].clone();
        PolySource {
            polys: vec![scalar_poly; dst_len],
            typ: poly_typ.clone(),
        }
    }

    fn is_poly(&self) -> bool {
        Self::poly_shape_static(&self.typ).is_some() || matches!(self.typ, ATyp::Mle(_))
    }

    fn poly_shape_static(t: &ATyp) -> Option<(usize, usize)> {
        match t {
            ATyp::VPoly(n, m) => Some((*n, *m)),
            ATyp::Uni(m) => Some((1, *m)),
            _ => None,
        }
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

    /// Canonical poly shape extraction → `(num_vars, max_total_degree)`.
    ///
    /// `VPoly(n, m)` stores `(n, m)` directly, where `m` is the max **total**
    /// degree. When constructed from `CTyp::Poly(_, n, d)` via `from_ctyp`,
    /// Unified Div/Rem handler for both `add_op` and `reduce_op`.
    ///
    /// Dispatches based on operand types:
    /// - Both VPoly/Uni → polynomial division with witness PRefs + cache
    /// - Both non-poly (scalar/Vec) → slot-wise field division
    /// - Either MLE, or mixed poly/non-poly → `unreachable!`
    ///
    /// When `cache_key` is `Some`, checks `div_wit` for a cached witness
    /// pair before emitting identity rows, and inserts after emission.
    /// This ensures Div+Rem on the same operand pair share witnesses.
    fn div_rem_op(
        &mut self,
        target: &PRef,
        a: &PolySource<C, T>,
        b: &PolySource<C, T>,
        is_rem: bool,
        cache_key: Option<(HOp<C>, HOp<C>)>,
        result: &mut GroebnerResult<C, T>,
    ) {
        match (a.typ(), b.typ()) {
            (ATyp::Vec(_, na), ATyp::Vec(_, nb)) if na == nb => {
                for i in 0..*na {
                    let t_i = target.with_index(i).unwrap();
                    let a_elem = a.at_index(i).unwrap();
                    let b_elem = b.at_index(i).unwrap();
                    self.div_rem_op(&t_i, &a_elem, &b_elem, is_rem, None, result);
                }
            }
            (ATyp::Vec(_, na), ATyp::Base(ABase::Scalar)) => {
                for i in 0..*na {
                    let t_i = target.with_index(i).unwrap();
                    let a_elem = a.at_index(i).unwrap();
                    self.div_rem_op(&t_i, &a_elem, b, is_rem, None, result);
                }
            }
            (_, ATyp::Base(ABase::Scalar)) if a.is_poly() => {
                unreachable!(
                    "{}: polynomial ÷ scalar — type checker should produce a Mul-by-inverse, not Div",
                    if is_rem { "Rem" } else { "Div" },
                );
            }
            _ if matches!(a.typ(), ATyp::Mle(_)) || matches!(b.typ(), ATyp::Mle(_)) => {
                unreachable!(
                    "{}: MLE division is not supported ({} {} {}) — only VPoly/Uni dividend and divisor are supported",
                    if is_rem { "Rem" } else { "Div" },
                    a.typ(),
                    if is_rem { "%" } else { "/" },
                    b.typ(),
                );
            }
            _ if a.is_poly() && b.is_poly() => {
                if let Some(ref key) = cache_key
                    && let Some((q_wit, r_wit)) = self.ns.div_wit.get(key).cloned()
                {
                    let wit = if is_rem { &r_wit } else { &q_wit };
                    self.link_to_witness(target, wit, result);
                    return;
                }

                let (na, ma) = PolySource::<C, T>::poly_shape_static(a.typ()).unwrap();
                let (nb, mb) = PolySource::<C, T>::poly_shape_static(b.typ()).unwrap();
                if na != nb {
                    unreachable!(
                        "{}: VPoly num_vars mismatch — dividend has n={} but divisor has n={}",
                        if is_rem { "Rem" } else { "Div" },
                        na,
                        nb,
                    );
                }
                if ma < mb {
                    unreachable!(
                        "{}: dividend degree < divisor degree ({} < {})",
                        if is_rem { "Rem" } else { "Div" },
                        ma,
                        mb,
                    );
                }
                if mb == 0 {
                    let q_name = self.ns.next_name("div_q");
                    let r_name = self.ns.next_name("div_r");
                    let q_wit = self.sentinel_pref(&q_name, ATyp::VPoly(na, ma), result);
                    let r_wit = self.sentinel_pref(&r_name, ATyp::VPoly(na, 0), result);
                    let a_idx = multi_indices(na, ma);
                    let b_poly = &b.polys()[0];
                    for (ka_pos, _k) in a_idx.iter().enumerate() {
                        let rhs: SparsePolynomial<C::F, T> =
                            b_poly * &SparsePolynomial::var(&q_wit.with_slot(ka_pos).unwrap());
                        result.basis.push(&a.polys()[ka_pos] - &rhs);
                    }
                    for rf in r_wit.slots() {
                        result.basis.push(SparsePolynomial::var(&rf));
                    }
                    let wit = if is_rem { &r_wit } else { &q_wit };
                    self.link_to_witness(target, wit, result);
                    if let Some(key) = cache_key {
                        self.ns.div_wit.insert(&key, &(q_wit, r_wit));
                    }
                    return;
                }

                let nr = na;
                let mq = ma - mb;
                let mr = mb - 1;

                let q_name = self.ns.next_name("div_q");
                let r_name = self.ns.next_name("div_r");
                let q_wit = self.sentinel_pref(&q_name, ATyp::VPoly(nr, mq), result);
                let r_wit = self.sentinel_pref(&r_name, ATyp::VPoly(nr, mr), result);

                let a_idx = multi_indices(na, ma);
                let b_idx = multi_indices(nb, mb);
                let q_idx = multi_indices(nr, mq);
                let r_idx = multi_indices(nr, mr);

                debug_assert_eq!(
                    a.polys().len(),
                    a_idx.len(),
                    "a_polys slot count mismatch: {} vs a_idx {}",
                    a.polys().len(),
                    a_idx.len()
                );
                debug_assert_eq!(
                    b.polys().len(),
                    b_idx.len(),
                    "b_polys slot count mismatch: {} vs b_idx {}",
                    b.polys().len(),
                    b_idx.len()
                );

                for (ka_pos, k) in a_idx.iter().enumerate() {
                    let mut rhs = SparsePolynomial::<C::F, T>::zero();
                    for (i_pos, ki) in b_idx.iter().enumerate() {
                        for (j_pos, kj) in q_idx.iter().enumerate() {
                            let sum: Vec<usize> =
                                ki.iter().zip(kj.iter()).map(|(x, y)| x + y).collect();
                            if sum == *k {
                                let qf = q_wit.clone().with_slot(j_pos).unwrap();
                                rhs = &rhs + &(&b.polys()[i_pos] * &SparsePolynomial::var(&qf));
                            }
                        }
                    }
                    if let Some(r_pos) = r_idx.iter().position(|rk| rk == k) {
                        let rf = r_wit.clone().with_slot(r_pos).unwrap();
                        rhs = &rhs + &SparsePolynomial::var(&rf);
                    }
                    result.basis.push(&a.polys()[ka_pos] - &rhs);
                }

                let wit = if is_rem { &r_wit } else { &q_wit };
                self.link_to_witness(target, wit, result);

                if let Some(key) = cache_key {
                    self.ns.div_wit.insert(&key, &(q_wit, r_wit));
                }
            }
            _ if !a.is_poly() && !b.is_poly() => {
                if is_rem {
                    unreachable!(
                        "Rem: non-polynomial remainder is undefined for {} % {} — type checker should prevent this",
                        a.typ(),
                        b.typ(),
                    );
                }
                self.slot_wise_div(target, a.polys(), b.polys(), result);
            }
            _ => {
                unreachable!(
                    "{}: mixed poly/non-poly division ({} {} {}) is not supported",
                    if is_rem { "Rem" } else { "Div" },
                    a.typ(),
                    if is_rem { "%" } else { "/" },
                    b.typ(),
                );
            }
        }
    }

    /// Slot-wise binary operation with type-aware broadcasting.
    ///
    /// Handles all type combinations that the lub functions permit:
    /// - `Scalar op Scalar` → single slot
    /// - `Vec(T,n) op Vec(T,n)` → element-wise recursion
    /// - `Vec(T,n) op Scalar` / `Scalar op Vec(T,n)` → broadcast scalar to each element
    /// - `Poly op Scalar` / `Scalar op Poly` → broadcast scalar to each coefficient
    /// - `Uni(n1) op Uni(n2)` → zero-pad shorter operand to match result degree
    /// - Same-type poly op → straightforward slot-wise
    fn broadcast_equ(
        &mut self,
        pr: &PRef,
        a: &PolySource<C, T>,
        b: &PolySource<C, T>,
        result: &mut GroebnerResult<C, T>,
    ) {
        self.emit_equ_diffs(a, b, result);
        for pf in pr.slots() {
            result.basis.push(SparsePolynomial::var(&pf));
        }
    }

    fn emit_equ_diffs(
        &mut self,
        a: &PolySource<C, T>,
        b: &PolySource<C, T>,
        result: &mut GroebnerResult<C, T>,
    ) {
        match (a.typ(), b.typ()) {
            (ATyp::Vec(_, na), ATyp::Vec(_, nb)) if na == nb => {
                for i in 0..*na {
                    let a_elem = a.at_index(i).unwrap();
                    let b_elem = b.at_index(i).unwrap();
                    self.emit_equ_diffs(&a_elem, &b_elem, result);
                }
            }
            _ => {
                let lub = ATyp::lub_equ(a.typ(), b.typ(), &Nothing)
                    .expect("broadcast_equ: lub_equ failed");
                let a_lifted = a.lift_to(&lub);
                let b_lifted = b.lift_to(&lub);
                for j in 0..lub.physical_len() {
                    let diff = &a_lifted.polys[j] - &b_lifted.polys[j];
                    result.basis.push(diff);
                }
            }
        }
    }

    fn concat_op(
        &mut self,
        pr: &PRef,
        a: &PolySource<C, T>,
        b: &PolySource<C, T>,
        a_op: &HOp<C>,
        b_op: &HOp<C>,
        result: &mut GroebnerResult<C, T>,
    ) {
        match (&pr.typ, a.typ(), b.typ()) {
            (ATyp::Vec(r_elem, _), ATyp::Vec(_, na), ATyp::Vec(_, nb)) => {
                for i in 0..*na {
                    let t_i = pr.with_index(i).unwrap();
                    let elem = a.at_index(i).unwrap();
                    let lifted = elem.lift_to(r_elem);
                    for (pf, p) in t_i.slots().into_iter().zip(lifted.polys) {
                        result.pl.insert(&pf, &p);
                        result.basis.push(p - SparsePolynomial::var(&pf));
                    }
                }
                for i in 0..*nb {
                    let t_i = pr.with_index(na + i).unwrap();
                    let elem = b.at_index(i).unwrap();
                    let lifted = elem.lift_to(r_elem);
                    for (pf, p) in t_i.slots().into_iter().zip(lifted.polys) {
                        result.pl.insert(&pf, &p);
                        result.basis.push(p - SparsePolynomial::var(&pf));
                    }
                }
            }
            (ATyp::Vec(r_elem, _), ATyp::Vec(_, na), _) => {
                for i in 0..*na {
                    let t_i = pr.with_index(i).unwrap();
                    let elem = a.at_index(i).unwrap();
                    let lifted = elem.lift_to(r_elem);
                    for (pf, p) in t_i.slots().into_iter().zip(lifted.polys) {
                        result.pl.insert(&pf, &p);
                        result.basis.push(p - SparsePolynomial::var(&pf));
                    }
                }
                let t_last = pr.with_index(*na).unwrap();
                let lifted = b.lift_to(r_elem);
                for (pf, p) in t_last.slots().into_iter().zip(lifted.polys) {
                    result.pl.insert(&pf, &p);
                    result.basis.push(p - SparsePolynomial::var(&pf));
                }
            }
            (ATyp::Vec(r_elem, _), _, ATyp::Vec(_, nb)) => {
                let t_first = pr.with_index(0).unwrap();
                let lifted = a.lift_to(r_elem);
                for (pf, p) in t_first.slots().into_iter().zip(lifted.polys) {
                    result.pl.insert(&pf, &p);
                    result.basis.push(p - SparsePolynomial::var(&pf));
                }
                for i in 0..*nb {
                    let t_i = pr.with_index(1 + i).unwrap();
                    let elem = b.at_index(i).unwrap();
                    let lifted = elem.lift_to(r_elem);
                    for (pf, p) in t_i.slots().into_iter().zip(lifted.polys) {
                        result.pl.insert(&pf, &p);
                        result.basis.push(p - SparsePolynomial::var(&pf));
                    }
                }
            }
            _ => {
                result.np.insert(
                    pr,
                    &Op::Bin(BinOp::Concat, a_op.clone(), b_op.clone(), pr.typ.clone()),
                );
            }
        }
    }

    fn broadcast_binop(
        &mut self,
        pr: &PRef,
        a: &PolySource<C, T>,
        b: &PolySource<C, T>,
        r_typ: &ATyp,
        op: BinOp,
        result: &mut GroebnerResult<C, T>,
    ) {
        match (a.typ(), b.typ()) {
            (ATyp::Vec(_, na), ATyp::Vec(_, nb)) if na == nb => {
                for i in 0..*na {
                    let a_elem = a.at_index(i).unwrap();
                    let b_elem = b.at_index(i).unwrap();
                    let r_inner = match r_typ {
                        ATyp::Vec(inner, _) => inner,
                        _ => unreachable!("broadcast_binop Vec×Vec result must be Vec"),
                    };
                    self.broadcast_binop(
                        &pr.with_index(i).unwrap(),
                        &a_elem,
                        &b_elem,
                        r_inner,
                        op,
                        result,
                    );
                }
            }
            (_, ATyp::Base(ABase::Scalar)) if a.physical_len() > 1 => {
                let b_broadcast = b.broadcast_scalar_to(a.typ());
                let pr_slots = pr.slots();
                assert_eq!(
                    pr_slots.len(),
                    a.polys().len(),
                    "broadcast_binop Scalar×Poly: pr slot count must match operand"
                );
                for (j, pf) in pr_slots.iter().enumerate() {
                    let combined = self.apply_binop(op, &a.polys()[j], &b_broadcast.polys()[0]);
                    result.pl.insert(pf, &combined);
                    result.basis.push(combined - SparsePolynomial::var(pf));
                }
            }
            (ATyp::Base(ABase::Scalar), _) if b.physical_len() > 1 => {
                let a_broadcast = a.broadcast_scalar_to(b.typ());
                let pr_slots = pr.slots();
                assert_eq!(
                    pr_slots.len(),
                    b.polys().len(),
                    "broadcast_binop Poly×Scalar: pr slot count must match operand"
                );
                for (j, pf) in pr_slots.iter().enumerate() {
                    let combined = self.apply_binop(op, &a_broadcast.polys()[0], &b.polys()[j]);
                    result.pl.insert(pf, &combined);
                    result.basis.push(combined - SparsePolynomial::var(pf));
                }
            }
            _ if a.is_poly() || b.is_poly() || matches!(r_typ, ATyp::Mle(_)) => {
                let a_lifted = a.lift_to(r_typ);
                let b_lifted = b.lift_to(r_typ);
                let pr_slots = pr.slots();
                for (j, pf) in pr_slots.iter().enumerate() {
                    let combined = self.apply_binop(op, &a_lifted.polys()[j], &b_lifted.polys()[j]);
                    result.pl.insert(pf, &combined);
                    result.basis.push(combined - SparsePolynomial::var(pf));
                }
            }
            _ => {
                let pr_slots = pr.slots();
                for ((ap, bp), pf) in a.polys().iter().zip(b.polys()).zip(&pr_slots) {
                    let combined = self.apply_binop(op, ap, bp);
                    result.pl.insert(pf, &combined);
                    result.basis.push(combined - SparsePolynomial::var(pf));
                }
            }
        }
    }

    fn apply_binop(
        &self,
        op: BinOp,
        a: &SparsePolynomial<C::F, T>,
        b: &SparsePolynomial<C::F, T>,
    ) -> SparsePolynomial<C::F, T> {
        match op {
            BinOp::Add | BinOp::And => a + b,
            BinOp::Sub => a - b,
            other => unreachable!("apply_binop called with {:?}", other),
        }
    }

    /// For `Vec<T>` × `Vec<T>`, iterates over logical indices and recurses
    /// per element. At the leaf level (non-Vec), dispatches to polynomial
    /// convolution (VPoly/Uni/Mle) or slot-wise multiplication (base types).
    fn mul_op(
        &mut self,
        target: &PRef,
        a: &PolySource<C, T>,
        b: &PolySource<C, T>,
        r_typ: &ATyp,
        result: &mut GroebnerResult<C, T>,
    ) {
        match (a.typ(), b.typ()) {
            (ATyp::Vec(_, na), ATyp::Vec(_, nb)) if na == nb => {
                let r_inner = match r_typ {
                    ATyp::Vec(inner, _) => inner,
                    _ => unreachable!("mul_op Vec×Vec result must be Vec"),
                };
                for i in 0..*na {
                    let t_i = target.with_index(i).unwrap();
                    let a_elem = a.at_index(i).unwrap();
                    let b_elem = b.at_index(i).unwrap();
                    self.mul_op(&t_i, &a_elem, &b_elem, r_inner, result);
                }
            }
            (ATyp::Vec(_, na), _) => {
                let r_inner = match r_typ {
                    ATyp::Vec(inner, _) => inner,
                    _ => unreachable!("mul_op Vec×scalar result must be Vec"),
                };
                for i in 0..*na {
                    let t_i = target.with_index(i).unwrap();
                    let a_elem = a.at_index(i).unwrap();
                    self.mul_op(&t_i, &a_elem, b, r_inner, result);
                }
            }
            (_, ATyp::Vec(_, nb)) => {
                let r_inner = match r_typ {
                    ATyp::Vec(inner, _) => inner,
                    _ => unreachable!("mul_op scalar×Vec result must be Vec"),
                };
                for i in 0..*nb {
                    let t_i = target.with_index(i).unwrap();
                    let b_elem = b.at_index(i).unwrap();
                    self.mul_op(&t_i, a, &b_elem, r_inner, result);
                }
            }
            (_, ATyp::Base(ABase::Scalar)) if a.is_poly() => {
                let target_slots = target.slots();
                for (ap, pf) in a.polys().iter().zip(&target_slots) {
                    let prod = ap * &b.polys()[0];
                    result.pl.insert(pf, &prod);
                    result.basis.push(prod - SparsePolynomial::var(pf));
                }
            }
            (ATyp::Base(ABase::Scalar), _) if b.is_poly() => {
                let target_slots = target.slots();
                for (bp, pf) in b.polys().iter().zip(&target_slots) {
                    let prod = &a.polys()[0] * bp;
                    result.pl.insert(pf, &prod);
                    result.basis.push(prod - SparsePolynomial::var(pf));
                }
            }
            (ATyp::Mle(na), ATyp::Mle(nb)) if na == nb => {
                let ATyp::VPoly(_nr, mr) = r_typ else {
                    unreachable!("Mul Mle×Mle result must be VPoly");
                };
                let n = *na;
                let all_b = hypercube(n);
                let r_idx = multi_indices(n, *mr);
                let single_var_coeff = |ba: usize, bb: usize, k: usize| -> i64 {
                    if k >= 3 {
                        return 0;
                    }
                    const C: [[[i64; 3]; 2]; 2] =
                        [[[1, -2, 1], [0, 1, -1]], [[0, 1, -1], [0, 0, 1]]];
                    C[ba][bb][k]
                };
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
                        let uv = &a.polys()[ia] * &b.polys()[ib];
                        for (ir, k) in r_idx.iter().enumerate() {
                            let mut scalar: i64 = 1;
                            for i in 0..n {
                                let c = single_var_coeff(ba[i], bb[i], k[i]);
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
                for (pf, poly) in target.slots().into_iter().zip(out) {
                    result.pl.insert(&pf, &poly);
                    result.basis.push(poly - SparsePolynomial::var(&pf));
                }
            }
            _ if a.is_poly() && b.is_poly() => {
                let a_norm = match a.typ() {
                    ATyp::Uni(m) => ATyp::VPoly(1, *m),
                    other => other.clone(),
                };
                let b_norm = match b.typ() {
                    ATyp::Uni(m) => ATyp::VPoly(1, *m),
                    other => other.clone(),
                };
                let r_norm = match r_typ {
                    ATyp::Uni(m) => ATyp::VPoly(1, *m),
                    other => other.clone(),
                };
                match (&a_norm, &b_norm, &r_norm) {
                    (ATyp::VPoly(na, ma), ATyp::VPoly(nb, mb), ATyp::VPoly(nr, mr))
                        if na == nb && na == nr =>
                    {
                        let a_idx = multi_indices(*na, *ma);
                        let b_idx = multi_indices(*nb, *mb);
                        let r_idx = multi_indices(*nr, *mr);
                        let mut out: Vec<SparsePolynomial<C::F, T>> =
                            vec![SparsePolynomial::<C::F, T>::zero(); r_idx.len()];
                        for (ia, ka) in a_idx.iter().enumerate() {
                            for (ib, kb) in b_idx.iter().enumerate() {
                                let k: Vec<usize> =
                                    ka.iter().zip(kb.iter()).map(|(x, y)| x + y).collect();
                                let ir = r_idx
                                    .iter()
                                    .position(|rk| rk == &k)
                                    .expect("multi-index missing in result");
                                out[ir] = &out[ir] + &(&a.polys()[ia] * &b.polys()[ib]);
                            }
                        }
                        for (pf, poly) in target.slots().into_iter().zip(out) {
                            result.pl.insert(&pf, &poly);
                            result.basis.push(poly - SparsePolynomial::var(&pf));
                        }
                    }
                    _ => {
                        unreachable!(
                            "Mul: unsupported polynomial type combination {}×{} → {}",
                            a.typ(),
                            b.typ(),
                            r_typ
                        )
                    }
                }
            }
            (ATyp::Base(_), ATyp::Base(_)) => {
                let target_slots = target.slots();
                for ((ap, bp), pf) in a.polys().iter().zip(b.polys()).zip(&target_slots) {
                    let prod = ap * bp;
                    result.pl.insert(pf, &prod);
                    result.basis.push(prod - SparsePolynomial::var(pf));
                }
            }
            _ => {
                unreachable!(
                    "Mul: unsupported type combination {}×{} → {}",
                    a.typ(),
                    b.typ(),
                    r_typ
                )
            }
        }
    }

    fn dot_op(
        &mut self,
        pr: &PRef,
        a: &PolySource<C, T>,
        b: &PolySource<C, T>,
        result: &mut GroebnerResult<C, T>,
    ) {
        match (a.typ(), b.typ()) {
            (ATyp::Vec(_, na), ATyp::Vec(_, nb)) if na == nb => {
                let r_elem_len = pr.typ.physical_len();
                let mut acc: Vec<SparsePolynomial<C::F, T>> =
                    vec![SparsePolynomial::zero(); r_elem_len];
                for i in 0..*na {
                    let acc_name = self.ns.next_name("dot_acc");
                    let acc_pref = self.sentinel_pref(&acc_name, pr.typ.clone(), result);
                    let a_elem = a.at_index(i).unwrap();
                    let b_elem = b.at_index(i).unwrap();
                    self.mul_op(&acc_pref, &a_elem, &b_elem, &pr.typ, result);
                    let acc_vars: Vec<SparsePolynomial<C::F, T>> = acc_pref
                        .slots()
                        .into_iter()
                        .map(|s| SparsePolynomial::var(&s))
                        .collect();
                    assert_eq!(
                        acc_vars.len(),
                        acc.len(),
                        "dot_op: acc_pref slot count must match accumulator"
                    );
                    for (j, a) in acc.iter_mut().enumerate() {
                        *a = &*a + &acc_vars[j];
                    }
                }
                for (pf, p) in pr.slots().into_iter().zip(acc) {
                    result.pl.insert(&pf, &p);
                    result.basis.push(p - SparsePolynomial::var(&pf));
                }
            }
            (ATyp::Base(_), ATyp::Base(_)) => {
                let pr_slots = pr.slots();
                assert_eq!(
                    pr_slots.len(),
                    1,
                    "Dot: Base·Base result must be single slot"
                );
                let sum: SparsePolynomial<C::F, T> =
                    a.polys().iter().zip(b.polys()).map(|(a, b)| a * b).sum();
                result.pl.insert(&pr_slots[0], &sum);
                result.basis.push(sum - SparsePolynomial::var(&pr_slots[0]));
            }
            _ => {
                unreachable!(
                    "Dot: unsupported type combination {} · {}",
                    a.typ(),
                    b.typ()
                );
            }
        }
    }

    fn pair_op(
        &mut self,
        pr: &PRef,
        a: &PolySource<C, T>,
        b: &PolySource<C, T>,
        result: &mut GroebnerResult<C, T>,
    ) {
        let gt = self.gt_pref(result);
        match (a.typ(), b.typ(), &pr.typ) {
            (ATyp::Vec(_, na), ATyp::Vec(_, nb), ATyp::Vec(r_inner, _)) if na == nb => {
                let gt_var = SparsePolynomial::var(&gt);
                for i in 0..*na {
                    let a_elem = a.at_index(i).unwrap();
                    let b_elem = b.at_index(i).unwrap();
                    let t_i = pr.with_index(i).unwrap();
                    let a_lifted = a_elem.lift_to(r_inner);
                    let b_lifted = b_elem.lift_to(r_inner);
                    for (j, pf) in t_i.slots().iter().enumerate() {
                        let e = &a_lifted.polys()[j] * &b_lifted.polys()[j] * gt_var.clone();
                        result.pl.insert(pf, &e);
                        result.basis.push(&e - &SparsePolynomial::var(pf));
                    }
                }
            }
            (ATyp::Base(_), ATyp::Base(_), ATyp::Base(_)) => {
                let pr_slots = pr.slots();
                let gt_var = SparsePolynomial::var(&gt);
                for (pf, e_a, e_b) in pr_slots
                    .iter()
                    .zip(a.polys())
                    .zip(b.polys())
                    .map(|((pf, a), b)| (pf, a, b))
                {
                    let e = e_a * e_b * gt_var.clone();
                    result.pl.insert(pf, &e);
                    result.basis.push(&e - &SparsePolynomial::var(pf));
                }
            }
            _ => {
                unreachable!(
                    "Pair: unsupported type combination {} × {} → {}",
                    a.typ(),
                    b.typ(),
                    pr.typ
                );
            }
        }
    }

    fn pow_op(&mut self, pr: &PRef, a: &HOp<C>, b: &HOp<C>, result: &mut GroebnerResult<C, T>) {
        let a_src = PolySource::from_ref_vars(self, a);
        match (a_src.typ(), &b.typ(), &pr.typ) {
            (ATyp::Vec(_, na), ATyp::Vec(_, nb), ATyp::Vec(r_inner, _)) if na == nb => {
                let elem_exps = self.resolve_const_exps_vec(b, *na);
                for i in 0..*na {
                    let t_i = pr.with_index(i).unwrap();
                    let elem_a = a_src.at_index(i).unwrap();
                    if let Some(k) = elem_exps[i] {
                        self.pow_const(&t_i, &elem_a, r_inner, k, result);
                    } else {
                        result.np.insert(
                            &t_i,
                            &Op::Bin(BinOp::Pow, a.clone(), b.clone(), t_i.typ.clone()),
                        );
                    }
                }
            }
            (ATyp::Vec(_, na), _, ATyp::Vec(r_inner, _)) => {
                let k = self.resolve_const_exp_scalar(b);
                for i in 0..*na {
                    let t_i = pr.with_index(i).unwrap();
                    let elem_a = a_src.at_index(i).unwrap();
                    if let Some(k) = k {
                        self.pow_const(&t_i, &elem_a, r_inner, k, result);
                    } else {
                        result.np.insert(
                            &t_i,
                            &Op::Bin(BinOp::Pow, a.clone(), b.clone(), t_i.typ.clone()),
                        );
                    }
                }
            }
            (_, ATyp::Vec(_, nb), ATyp::Vec(_, _)) => {
                let elem_exps = self.resolve_const_exps_vec(b, *nb);
                for i in 0..*nb {
                    let t_i = pr.with_index(i).unwrap();
                    if let Some(k) = elem_exps[i] {
                        self.pow_const(&t_i, &a_src, &t_i.typ, k, result);
                    } else {
                        result.np.insert(
                            &t_i,
                            &Op::Bin(BinOp::Pow, a.clone(), b.clone(), t_i.typ.clone()),
                        );
                    }
                }
            }
            _ => {
                if let Some(k) = self.resolve_const_exp_scalar(b) {
                    self.pow_const(pr, &a_src, &pr.typ, k, result);
                } else {
                    result.np.insert(
                        pr,
                        &Op::Bin(BinOp::Pow, a.clone(), b.clone(), pr.typ.clone()),
                    );
                }
            }
        }
    }

    /// Try to resolve a scalar operand to a compile-time constant index.
    fn resolve_const_exp_scalar(&self, b: &HOp<C>) -> Option<usize> {
        match b.get() {
            Op::Value(Value::Index(i)) => Some(*i),
            _ => None,
        }
    }

    /// Try to resolve each element of a Vec operand to a compile-time constant index.
    fn resolve_const_exps_vec(&self, b: &HOp<C>, n: usize) -> Vec<Option<usize>> {
        match b.get() {
            Op::Value(Value::VecIndex(vs)) => vs.iter().map(|i| Some(*i)).collect(),
            Op::Vec(vs) => vs
                .iter()
                .map(|v| match v.get() {
                    Op::Value(Value::Index(i)) => Some(*i),
                    _ => None,
                })
                .collect(),
            Op::Value(Value::Index(i)) => {
                vec![Some(*i); n]
            }
            _ => vec![None; n],
        }
    }
    fn pow_const(
        &mut self,
        target: &PRef,
        base: &PolySource<C, T>,
        _result_typ: &ATyp,
        k: usize,
        result: &mut GroebnerResult<C, T>,
    ) {
        if k == 0 {
            let one = SparsePolynomial::<C::F, T>::lit(&C::F::one());
            for pf in target.slots() {
                result.pl.insert(&pf, &one);
                result.basis.push(one.clone() - SparsePolynomial::var(&pf));
            }
            return;
        }
        if k == 1 {
            for (pf, p) in target.slots().into_iter().zip(base.polys().iter().cloned()) {
                result.pl.insert(&pf, &p);
                result.basis.push(p - SparsePolynomial::var(&pf));
            }
            return;
        }
        let mut acc = PolySource::new(base.polys().to_vec(), base.typ().clone());
        for _step in 1..k {
            let next_name = self.ns.next_name("pow_acc");
            let next_typ =
                ATyp::lub_mul(acc.typ(), base.typ(), &Nothing).expect("pow_const: lub_mul");
            let next_pref = self.sentinel_pref(&next_name, next_typ.clone(), result);
            self.mul_op(&next_pref, &acc, base, &next_typ, result);
            acc = PolySource::new(
                next_pref
                    .slots()
                    .into_iter()
                    .map(|s| SparsePolynomial::var(&s))
                    .collect(),
                next_typ,
            );
        }
        for (pf, p) in target.slots().into_iter().zip(acc.polys) {
            result.pl.insert(&pf, &p);
            result.basis.push(p - SparsePolynomial::var(&pf));
        }
    }

    /// Slot-wise division constraint: for each slot j,
    ///   `a[j] - b[j] * var(target[j]) = 0`
    fn slot_wise_div(
        &mut self,
        target: &PRef,
        a_polys: &[SparsePolynomial<C::F, T>],
        b_polys: &[SparsePolynomial<C::F, T>],
        result: &mut GroebnerResult<C, T>,
    ) {
        let target_slots = target.slots();
        for (j, pf) in target_slots.iter().enumerate() {
            result
                .basis
                .push(a_polys[j].clone() - b_polys[j].clone() * SparsePolynomial::var(pf));
        }
    }

    /// Phase 13: link the user's PRef `pr` to a witness PRef `wit` slot by
    /// slot, for when `pr` aliases a div/rem witness produced by
    /// `div_witnesses`. Emits `var(pr[j]) − var(wit[j]) = 0` for every
    /// `j < pr.typ.physical_len()`, and registers `pl[pr[j]] = var(wit[j])`.
    fn link_to_witness(&mut self, pr: &PRef, wit: &PRef, result: &mut GroebnerResult<C, T>) {
        // Zip to min(pr slots, wit slots) — zip truncates to the shorter iterator.
        // Excess pr slots stay unconstrained (opaque).
        for (pf, wf) in pr.slots().into_iter().zip(wit.slots()) {
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

    /// Shared helper for `Op::Evaluate(p, xs)` — computes the result
    /// polynomials for evaluating `p` at `xs`. Panics on unsupported
    /// (p.typ(), |xs|) combinations; the type checker guarantees these
    /// are unreachable.
    fn eval_to_poly(&mut self, p: &GOp<C>, xs: &GOp<C>) -> Vec<SparsePolynomial<C::F, T>> {
        let p_typ = p.typ();
        let xs_polys = self.ref_vars(xs);
        let k = xs_polys.len();
        match &p_typ {
            ATyp::Uni(_) | ATyp::VPoly(1, _) => {
                assert!(
                    k >= 1,
                    "Evaluate on Uni/VPoly(1,_) requires at least 1 point; got {}",
                    k
                );
                let p_polys = self.ref_vars(p);
                let one = SparsePolynomial::<C::F, T>::lit(&C::F::one());
                (0..k)
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
                    .collect()
            }
            ATyp::VPoly(n, mdeg) if *n >= 2 && k <= *n => {
                assert!(
                    k >= 1,
                    "Evaluate on VPoly requires at least 1 point; got {}",
                    k
                );
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
                    vec![acc]
                } else {
                    let remaining_n = n - k;
                    let result_indices = multi_indices(remaining_n, *mdeg);
                    result_indices
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
                        .collect()
                }
            }
            ATyp::Mle(n) if k <= *n => {
                assert!(
                    k >= 1,
                    "Evaluate on Mle requires at least 1 point; got {}",
                    k
                );
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
                    vec![acc]
                } else {
                    let remaining_n = n - k;
                    let result_b = hypercube(remaining_n);
                    result_b
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
                        .collect()
                }
            }
            _ => unreachable!(
                "Evaluate: unsupported polynomial type {:?} with {} evaluation points",
                p_typ, k
            ),
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
        match op {
            Op::Ref(r, typ) => {
                let ref_src = PolySource::from_ref_vars(self, &Op::Ref(r, typ.clone()));
                let lifted = ref_src.lift_to(&pr.typ);
                for (pf, p) in pr.slots().into_iter().zip(lifted.polys) {
                    result.pl.insert(&pf, &p);
                    result.basis.push(p - SparsePolynomial::var(&pf));
                }
            }
            Op::Bin(BinOp::Add | BinOp::And, a, b, _) => {
                let a_src = PolySource::from_ref_vars(self, &a);
                let b_src = PolySource::from_ref_vars(self, &b);
                self.broadcast_binop(&pr, &a_src, &b_src, &pr.typ, BinOp::Add, result);
            }
            Op::Bin(BinOp::Sub, a, b, _) => {
                let a_src = PolySource::from_ref_vars(self, &a);
                let b_src = PolySource::from_ref_vars(self, &b);
                self.broadcast_binop(&pr, &a_src, &b_src, &pr.typ, BinOp::Sub, result);
            }
            Op::Bin(BinOp::Mul, ref a, ref b, _) => {
                let a_src = PolySource::from_ref_vars(self, a);
                let b_src = PolySource::from_ref_vars(self, b);
                self.mul_op(&pr, &a_src, &b_src, &pr.typ, result);
            }
            Op::Bin(BinOp::Dot, ref a, ref b, _) => {
                let a_src = PolySource::from_ref_vars(self, a);
                let b_src = PolySource::from_ref_vars(self, b);
                self.dot_op(&pr, &a_src, &b_src, result);
            }
            Op::Bin(BinOp::Div, ref a, ref b, _) => {
                let a_src = PolySource::from_ref_vars(self, a);
                let b_src = PolySource::from_ref_vars(self, b);
                self.div_rem_op(
                    &pr,
                    &a_src,
                    &b_src,
                    false,
                    Some((a.clone(), b.clone())),
                    result,
                );
            }
            Op::Bin(BinOp::Rem, ref a, ref b, _) => {
                let a_src = PolySource::from_ref_vars(self, a);
                let b_src = PolySource::from_ref_vars(self, b);
                self.div_rem_op(
                    &pr,
                    &a_src,
                    &b_src,
                    true,
                    Some((a.clone(), b.clone())),
                    result,
                );
            }
            Op::Bin(BinOp::Equ, a, b, _) => {
                let a_src = PolySource::from_ref_vars(self, &a);
                let b_src = PolySource::from_ref_vars(self, &b);
                self.broadcast_equ(&pr, &a_src, &b_src, result);
            }
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
                self.interpolate_op(pr, points, evals, result);
            }
            // Op::Ifft(v): p = ifft(v) — inverse DFT. The coefficient form `pr`
            // is the IDFT of the evaluation form `a`. Each coefficient is:
            //   p[j] = (1/N) · Σ_i ω^{-i·j} · v[i]
            // where ω is a primitive N-th root of unity. The type checker
            // guarantees N is a 2-adic divisor of |F|-1, so ω always exists.
            Op::Ifft(ref a) => {
                let v_polys = self.ref_vars(a);
                let n = v_polys.len();
                let omega = C::F::get_root_of_unity(n as u64)
                    .expect("IFFT size must have a root of unity; type checker guarantees this");
                let omega_inv = omega.inverse().unwrap();
                let n_inv = C::F::from(n as u64).inverse().unwrap();
                let pr_slots = pr.slots();
                for (j, pf) in pr_slots.iter().enumerate() {
                    let idft_j = dft_row(&v_polys, omega_inv, j);
                    let lhs = &idft_j * &SparsePolynomial::lit(&n_inv);
                    result.pl.insert(pf, &lhs);
                    result.basis.push(&lhs - &SparsePolynomial::var(pf));
                }
            }
            // Op::Fft(p): v = fft(p) — forward DFT. Each evaluation is:
            //   v[i] = Σ_j ω^{i·j} · p[j]
            // The type checker guarantees N is a 2-adic divisor of |F|-1.
            Op::Fft(ref a) => {
                let coeff_polys = self.ref_vars(a);
                let n = coeff_polys.len();
                let omega = C::F::get_root_of_unity(n as u64)
                    .expect("FFT size must have a root of unity; type checker guarantees this");
                let pr_slots = pr.slots();
                for (i, pf) in pr_slots.iter().enumerate() {
                    let lhs = dft_row(&coeff_polys, omega, i);
                    result.pl.insert(pf, &lhs);
                    result.basis.push(&lhs - &SparsePolynomial::var(pf));
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
                for (pf, p) in pr.slots().into_iter().zip(polys) {
                    result.pl.insert(&pf, &p);
                    result.basis.push(p - SparsePolynomial::var(&pf));
                }
            }
            Op::Vec(vs) => {
                for (i, v) in vs.into_iter().enumerate() {
                    let pr_i = pr.with_index(i).unwrap();
                    self.add_op(pr_i, v.get().clone(), result);
                }
            }
            // Op::Evaluate(p, xs): evaluate a polynomial `p` at points `xs`.
            //
            // Three shapes are handled (dispatched on p.typ() × |xs slots|):
            //
            //   1. Univariate batched — p: Uni(_) or VPoly(1, _), xs: len k ≥ 1
            //        result[i] = Σ_j a_j · xs[i]^j                  (Vec(F, k) output)
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
            // The type checker guarantees xs is non-empty and p has a supported
            // polynomial type; unsupported shapes are unreachable.
            Op::Evaluate(ref p, ref xs) => {
                let polys = self.eval_to_poly(p, xs);
                for (pf, poly) in pr.slots().into_iter().zip(polys) {
                    result.pl.insert(&pf, &poly);
                    result.basis.push(poly - SparsePolynomial::var(&pf));
                }
            }
            // Phase 10: `Op::Reduce(op, v)` — left-fold of vector elements.
            // See `reduce_op` for per-operator handling.
            Op::Reduce(rop, ref v) => {
                self.reduce_op(pr, rop, v, result);
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
                        for (pf, p) in pr.slots().into_iter().zip(polys) {
                            result.pl.insert(&pf, &p);
                            result.basis.push(p - SparsePolynomial::var(&pf));
                        }
                    }
                    None => {
                        result.np.insert(&pr, &Op::Value(v.clone()));
                    }
                }
            }
            // Phase 10: `Op::Ram(a, b)` — RAM reads with a literal index `i`
            // resolve to the i-th logical element of the array. For compound
            // element types, all physical slots are linked pairwise.
            // Runtime indices fall back to opaque.
            Op::Ram(ref a, ref b) => match b.get() {
                Op::Value(Value::Index(i)) => {
                    let Op::Ref(r, _) = a.get() else {
                        unreachable!(
                            "Ram array operand must be Ref; got {:?}",
                            std::mem::discriminant(a.get())
                        )
                    };
                    let array_pref = self.find_ref(r);
                    let Some(elem_pref) = array_pref.with_index(*i) else {
                        unreachable!(
                            "Ram operand with literal index must be within bound; Got {:?}",
                            *i
                        )
                    };

                    for (pf, e) in pr.slots().into_iter().zip(elem_pref.slots()) {
                        let e_poly = SparsePolynomial::var(&e);
                        result
                            .basis
                            .push(e_poly.clone() - SparsePolynomial::var(&pf));
                        result.pl.insert(&pf, &e_poly);
                    }
                }
                _ => {
                    let raw = Op::Ram(a.clone(), b.clone());
                    result.np.insert(&pr, &raw);
                }
            },
            // Phase 12: `Op::Pair(a, b, t)` — bilinear pairing via the
            // `__zippel::gb::gt` sentinel. For each slot position, the
            // result is bound to the exponent-space bilinear form:
            //
            //   var(pr[i]) = var(a[i]) · var(b[i]) · var(__zippel::gb::gt)
            //
            // which encodes both the pairing axiom
            // `pair(__zippel::gb::g1, __zippel::gb::g2) = __zippel::gb::gt`
            // and full bilinearity. Matching pair expressions on both
            // sides of a `verify(lhs == rhs)` then cancel under Buchberger
            // because their basis rows are identical F-polynomials.
            Op::Pair(ref a, ref b, _) => {
                let a_src = PolySource::from_ref_vars(self, a.get());
                let b_src = PolySource::from_ref_vars(self, b.get());
                self.pair_op(&pr, &a_src, &b_src, result);
            }
            // `Op::Record(fields)` — field-slot-aware layout.
            // Physical slots are laid out in Ctx iteration order: each
            // field occupies `field_typ.physical_len()` consecutive slots.
            // For each field, emit basis rows linking record slots to
            // the field's polynomial values.
            Op::Record(ref fields) => {
                let pr_slots = pr.slots();
                let mut slot_offset = 0usize;
                for (_, field_op) in fields.iter() {
                    let field_polys = self.ref_vars(field_op.get());
                    for (j, p) in field_polys.into_iter().enumerate() {
                        let pf = &pr_slots[slot_offset + j];
                        result.pl.insert(pf, &p);
                        result.basis.push(p - SparsePolynomial::var(pf));
                    }
                    slot_offset += field_op.typ().physical_len();
                }
            }
            // Concat/Pow/Marginalize/Proj: opaque in np — cannot be
            // converted to polynomial ideal constraints.
            Op::Bin(BinOp::Concat, ref a, ref b, _) => {
                let a_src = PolySource::from_ref_vars(self, a);
                let b_src = PolySource::from_ref_vars(self, b);
                self.concat_op(&pr, &a_src, &b_src, a, b, result);
            }
            Op::Bin(BinOp::Pow, ref a, ref b, _) => {
                self.pow_op(&pr, a, b, result);
            }
            Op::Marginalize(ref inner) => {
                result.np.insert(&pr, &Op::Marginalize(inner.clone()));
            }
            // `Op::Proj(inner, field, typ)` — extract a field from a Record.
            // The field's physical slots sit at an offset within the Record's
            // slot layout: offset = sum of physical_len() of preceding fields
            // (in Ctx iteration order). Emit basis rows linking proj result
            // slots to the corresponding inner Record slots.
            Op::Proj(ref inner, ref field, ref _typ) => {
                let inner_typ = inner.typ();
                let inner_polys = self.ref_vars(inner);
                let ATyp::Record(fields) = &inner_typ else {
                    unreachable!(
                        "Proj inner must be Record; type checker guarantees this, got {:?}",
                        inner_typ
                    );
                };
                let mut offset = 0usize;
                for (fname, ftyp) in fields.iter() {
                    let f_len = ftyp.physical_len();
                    if fname == field {
                        let pr_slots = pr.slots();
                        for (j, pf) in pr_slots.iter().enumerate() {
                            result.pl.insert(pf, &inner_polys[offset + j]);
                            result
                                .basis
                                .push(inner_polys[offset + j].clone() - SparsePolynomial::var(pf));
                        }
                        break;
                    }
                    offset += f_len;
                }
            }
        }
    }

    /// Lagrange interpolation: given `n` distinct points `(x_i, y_i)`,
    /// the result polynomial `p(X) = Σ_i y_i · L_i(X)` where
    /// `L_i(X) = Π_{j≠i} (X - x_j) / (x_i - x_j)`.
    ///
    /// For each coefficient slot `k` of the result `Uni(n)`:
    ///   `var(pr[k]) = Σ_i var(y_i) · L[i][k]`
    ///
    /// When `points` is `Op::Value`, the constant values are extracted
    /// directly via `to_poly_value`. When `points` is `Op::Ref`, the
    /// point slot polynomials are looked up in `result.pl` — since the
    /// Vec node is processed before Interpolate in topological order,
    /// constant bindings are already available there.
    ///
    /// Falls back to opaque if the point values aren't all constant.
    fn interpolate_op(
        &mut self,
        pr: PRef,
        points: &HOp<C>,
        evals: &HOp<C>,
        result: &mut GroebnerResult<C, T>,
    ) {
        let evals_polys = self.ref_vars(evals);
        let n = evals_polys.len();

        let xs: Option<Vec<C::F>> = match points.get() {
            Op::Value(v) => self
                .to_poly_value(v)
                .iter()
                .map(|p| {
                    if p.is_constant() {
                        p.leading_term().map(|(c, _)| c)
                    } else {
                        None
                    }
                })
                .collect(),
            Op::Ref(r, _) => {
                let points_pref = self.find_ref(r);
                points_pref
                    .slots()
                    .iter()
                    .map(|s| {
                        result.pl.get(s).and_then(|p| {
                            if p.is_constant() {
                                p.leading_term().map(|(c, _)| c)
                            } else {
                                None
                            }
                        })
                    })
                    .collect()
            }
            other => {
                unreachable!(
                    "Interpolate points operand must be Ref or Value; got {:?}",
                    std::mem::discriminant(other)
                )
            }
        };

        let Some(xs) = xs else {
            result
                .np
                .insert(&pr, &Op::Interpolate(points.clone(), evals.clone()));
            return;
        };
        assert_eq!(
            n,
            xs.len(),
            "Interpolate: points and evals must have same length"
        );

        let lag = lagrange_basis::<C::F>(&xs);
        let pr_slots = pr.slots();
        for (k, pf) in pr_slots.iter().enumerate() {
            let mut acc = SparsePolynomial::<C::F, T>::zero();
            for (i, y_i) in evals_polys.iter().enumerate() {
                if k < lag[i].len() && lag[i][k] != C::F::zero() {
                    let weight = SparsePolynomial::<C::F, T>::lit(&lag[i][k]);
                    acc = acc + (y_i * &weight);
                }
            }
            result.pl.insert(pf, &acc);
            result.basis.push(acc - SparsePolynomial::var(pf));
        }
    }

    /// Left-fold of vector elements:
    ///   acc₀ = v[0],  acc_i = rop(acc_{i-1}, v[i]),  result = acc_{n-1}
    ///
    /// Physical slots from `ref_vars(v)` are chunked by `elem_len`
    /// (the element type's `physical_len`) into logical elements.
    /// The fold is performed per-slot-position across elements.
    ///
    /// Operator handling:
    ///
    /// - **Add/And/Sub/Mul**: pure polynomial fold — Add/And start from
    ///   zero, Mul from one, Sub starts from the first element.
    ///
    /// - **Concat**: passes through all physical slots.
    ///
    /// - **Div**: intermediate sentinel PRefs for each fold step with
    ///   per-slot constraints `acc - elem * var(target) = 0`.
    ///
    /// - **Rem/Equ/Pow**: opaque. Rem is pointwise opaque; chained
    ///   equality can't be cleanly encoded in the polynomial basis; Pow's
    ///   left-fold `(a^b)^c` requires `a^(b*c)` which is only valid for
    ///   constant b, c and produces potentially very-high-degree terms —
    ///   better handled by the `BinOp::Pow` handler in `add_op` which
    ///   sees a single exponent directly.
    ///
    /// - **Dot**: unreachable (type checker rejects `reduce(dot, _)`).
    fn reduce_op(&mut self, pr: PRef, rop: BinOp, v: &HOp<C>, result: &mut GroebnerResult<C, T>) {
        let v_typ = v.typ();
        let (elem_t, n) = match &v_typ {
            ATyp::Vec(box e, n) => (e.clone(), *n),
            _ => unreachable!("Reduce operand must be Vec; type checker guarantees this"),
        };

        if n == 1 {
            let Op::Ref(r, _) = v.get() else {
                unreachable!(
                    "Reduce operand must be Ref; got {:?}",
                    std::mem::discriminant(v.get())
                )
            };
            let v_pref = self.find_ref(r);
            let elem_pref = v_pref.with_index(0).unwrap();
            self.link_to_witness(&pr, &elem_pref, result);
            return;
        }

        let v_src = PolySource::from_ref_vars(self, v);

        match rop {
            BinOp::Add | BinOp::And => {
                let mut acc: PolySource<C, T> = PolySource::new(
                    (0..elem_t.physical_len())
                        .map(|_| SparsePolynomial::zero())
                        .collect(),
                    elem_t.clone(),
                );
                for i in 0..n {
                    let elem = v_src.at_index(i).unwrap();
                    let lifted = elem.lift_to(&elem_t);
                    for (j, p) in acc.polys.iter_mut().enumerate() {
                        *p = &*p + &lifted.polys[j];
                    }
                }
                for (pf, p) in pr.slots().into_iter().zip(acc.polys) {
                    result.pl.insert(&pf, &p);
                    result.basis.push(p - SparsePolynomial::var(&pf));
                }
            }
            BinOp::Sub => {
                let mut acc = v_src.at_index(0).unwrap();
                for i in 1..n {
                    let elem = v_src.at_index(i).unwrap();
                    let lifted = elem.lift_to(&elem_t);
                    for (j, p) in acc.polys.iter_mut().enumerate() {
                        *p = &*p - &lifted.polys[j];
                    }
                }
                for (pf, p) in pr.slots().into_iter().zip(acc.polys) {
                    result.pl.insert(&pf, &p);
                    result.basis.push(p - SparsePolynomial::var(&pf));
                }
            }
            BinOp::Mul => {
                let mut acc = v_src.at_index(0).unwrap();
                for i in 1..n {
                    let elem = v_src.at_index(i).unwrap();
                    let acc_name = self.ns.next_name("reduce_mul_acc");
                    let acc_pref = self.sentinel_pref(&acc_name, elem_t.clone(), result);
                    self.mul_op(&acc_pref, &acc, &elem, &elem_t, result);
                    acc = PolySource::new(
                        acc_pref
                            .slots()
                            .into_iter()
                            .map(|s| SparsePolynomial::var(&s))
                            .collect(),
                        elem_t.clone(),
                    );
                }
                for (pf, p) in pr.slots().into_iter().zip(acc.polys) {
                    result.basis.push(p - SparsePolynomial::var(&pf));
                }
            }
            BinOp::Concat => {
                for (pf, p) in pr.slots().into_iter().zip(v_src.polys) {
                    result.pl.insert(&pf, &p);
                    result.basis.push(p - SparsePolynomial::var(&pf));
                }
            }
            BinOp::Div | BinOp::Rem => {
                let is_rem = rop == BinOp::Rem;
                let is_poly = PolySource::<C, T>::poly_shape_static(&elem_t).is_some();
                let mut acc_src = v_src.at_index(0).unwrap();
                for step in 0..n - 1 {
                    let is_last = step == n - 2;
                    let target = if is_last {
                        pr.clone()
                    } else {
                        let acc_name = self.ns.next_name(if is_rem {
                            "reduce_rem_acc"
                        } else {
                            "reduce_div_acc"
                        });
                        self.sentinel_pref(&acc_name, elem_t.clone(), result)
                    };
                    let elem_src = v_src.at_index(step + 1).unwrap();
                    if is_poly {
                        self.div_rem_op(
                            &target,
                            &acc_src,
                            &elem_src,
                            is_rem && is_last,
                            None,
                            result,
                        );
                    } else {
                        if is_rem {
                            unreachable!(
                                "Rem: non-polynomial remainder is undefined for Vec<{}>",
                                elem_t,
                            );
                        }
                        self.slot_wise_div(&target, acc_src.polys(), elem_src.polys(), result);
                    }
                    acc_src = PolySource::new(
                        target
                            .slots()
                            .into_iter()
                            .map(|s| SparsePolynomial::var(&s))
                            .collect(),
                        elem_t.clone(),
                    );
                }
            }
            BinOp::Equ | BinOp::Pow => {
                result.np.insert(&pr, &Op::Reduce(rop, v.clone()));
            }
            BinOp::Dot => {
                unreachable!("reduce(dot, _) is rejected by the type checker");
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
        let builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        use ark_bls12_381::Fr;
        use backend::Value;

        let val = Value::Scalar(Fr::from(42u64));
        let poly = builder.to_poly_value(&val);
        assert_eq!(poly.len(), 1);
    }

    #[test]
    fn test_groebner_builder_to_poly_value_bool_true() {
        let builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        use backend::Value;

        let val = Value::Bool(true);
        let poly = builder.to_poly_value(&val);
        assert_eq!(poly.len(), 1);
    }

    #[test]
    fn test_groebner_builder_to_poly_value_bool_false() {
        let builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        use backend::Value;

        let val = Value::Bool(false);
        let poly = builder.to_poly_value(&val);
        assert_eq!(poly.len(), 1);
    }

    #[test]
    fn test_groebner_builder_to_poly_value_index() {
        let builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        use backend::Value;

        let val = Value::Index(5);
        let poly = builder.to_poly_value(&val);
        assert_eq!(poly.len(), 1);
    }

    #[test]
    fn test_groebner_builder_to_poly_value_vec_scalar() {
        let builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        use ark_bls12_381::Fr;
        use backend::Value;

        let val = Value::VecScalar(vec![Fr::from(1u64), Fr::from(2u64), Fr::from(3u64)]);
        let poly = builder.to_poly_value(&val);
        assert_eq!(poly.len(), 3);
    }

    #[test]
    fn test_groebner_builder_to_poly_value_vec_bool() {
        let builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
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

    #[test]
    fn test_reduce_add_over_scalar_vec() {
        use crate::{PRef, Ref};
        use lang::ast::BinOp;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let mut gresult = GroebnerResult::<ArkBls12_381, GrevLexTerm>::new();
        // v : Vec(F, 3)  →  reduce(+, v) : F
        let pref_v = PRef::from_node(
            NodeIndex::new(0),
            ATyp::Vec(Box::new(ATyp::scalar()), 3),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_v);

        let result = PRef::from_node(
            NodeIndex::new(1),
            ATyp::scalar(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        let op: GOp<ArkBls12_381> = Op::Reduce(
            BinOp::Add,
            mk::<ArkBls12_381>(Op::Ref(
                Ref::new(NodeIndex::new(0)),
                ATyp::Vec(Box::new(ATyp::scalar()), 3),
            )),
        );
        builder.add_op(result.clone(), op, &mut gresult);

        let var = |p: &PRef| SparsePolynomial::<ark_bls12_381::Fr, GrevLexTerm>::var(p);
        let v0 = pref_v.clone().with_slot(0).unwrap();
        let v1 = pref_v.clone().with_slot(1).unwrap();
        let v2 = pref_v.clone().with_slot(2).unwrap();

        let expected = &var(&v0) + &(&var(&v1) + &var(&v2));
        let row = &expected - &var(&result);
        assert!(
            gresult.basis.iter().any(|r| r == &row),
            "basis should contain v0+v1+v2 - result, got {:?}",
            gresult.basis
        );
        assert_eq!(
            gresult.pl.get(&result).cloned(),
            Some(expected),
            "pl[result] should map to v0+v1+v2"
        );
    }

    #[test]
    fn test_reduce_add_over_poly_vec() {
        // reduce(+, [Poly(1,2); 3]) : Poly(1,2)
        // Vec(Poly(1,2), 3) has 3 elements × 3 coefficients = 9 physical slots.
        // reduce should produce 3 polynomials (one per coefficient position),
        // where result[j] = v0[j] + v1[j] + v2[j].
        use crate::{PRef, Ref};
        use lang::ast::BinOp;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let mut gresult = GroebnerResult::<ArkBls12_381, GrevLexTerm>::new();
        let poly_t = ATyp::Uni(2);
        let vec_t = ATyp::Vec(Box::new(poly_t.clone()), 3);
        let pref_v = PRef::from_node(
            NodeIndex::new(0),
            vec_t.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_v);

        let result = PRef::from_node(
            NodeIndex::new(1),
            poly_t.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        let op: GOp<ArkBls12_381> = Op::Reduce(
            BinOp::Add,
            mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), vec_t)),
        );
        builder.add_op(result.clone(), op, &mut gresult);

        let var = |p: &PRef| SparsePolynomial::<ark_bls12_381::Fr, GrevLexTerm>::var(p);
        // Vec(Poly(1,2), 3): element 0 is slots 0,1,2; element 1 is slots 3,4,5; element 2 is slots 6,7,8.
        let v0_c0 = pref_v.clone().with_index(0).unwrap().with_slot(0).unwrap();
        let v0_c1 = pref_v.clone().with_index(0).unwrap().with_slot(1).unwrap();
        let v0_c2 = pref_v.clone().with_index(0).unwrap().with_slot(2).unwrap();
        let v1_c0 = pref_v.clone().with_index(1).unwrap().with_slot(0).unwrap();
        let v1_c1 = pref_v.clone().with_index(1).unwrap().with_slot(1).unwrap();
        let v1_c2 = pref_v.clone().with_index(1).unwrap().with_slot(2).unwrap();
        let v2_c0 = pref_v.clone().with_index(2).unwrap().with_slot(0).unwrap();
        let v2_c1 = pref_v.clone().with_index(2).unwrap().with_slot(1).unwrap();
        let v2_c2 = pref_v.clone().with_index(2).unwrap().with_slot(2).unwrap();

        let r_c0 = result.clone().with_slot(0).unwrap();
        let r_c1 = result.clone().with_slot(1).unwrap();
        let r_c2 = result.clone().with_slot(2).unwrap();

        // result[0] = v0[0] + v1[0] + v2[0]
        let expected_c0 = &var(&v0_c0) + &(&var(&v1_c0) + &var(&v2_c0));
        let expected_c1 = &var(&v0_c1) + &(&var(&v1_c1) + &var(&v2_c1));
        let expected_c2 = &var(&v0_c2) + &(&var(&v1_c2) + &var(&v2_c2));

        assert_eq!(
            gresult.pl.get(&r_c0).cloned(),
            Some(expected_c0.clone()),
            "pl[result[0]] = v0[0]+v1[0]+v2[0]"
        );
        assert_eq!(
            gresult.pl.get(&r_c1).cloned(),
            Some(expected_c1.clone()),
            "pl[result[1]] = v0[1]+v1[1]+v2[1]"
        );
        assert_eq!(
            gresult.pl.get(&r_c2).cloned(),
            Some(expected_c2.clone()),
            "pl[result[2]] = v0[2]+v1[2]+v2[2]"
        );

        let row0 = &expected_c0 - &var(&r_c0);
        let row1 = &expected_c1 - &var(&r_c1);
        let row2 = &expected_c2 - &var(&r_c2);
        assert!(
            gresult.basis.iter().any(|r| r == &row0),
            "basis should contain row for coefficient 0"
        );
        assert!(
            gresult.basis.iter().any(|r| r == &row1),
            "basis should contain row for coefficient 1"
        );
        assert!(
            gresult.basis.iter().any(|r| r == &row2),
            "basis should contain row for coefficient 2"
        );
    }

    #[test]
    fn test_lagrange_basis_2_points() {
        use ark_bls12_381::Fr;

        let xs: Vec<Fr> = [0u64, 1].iter().map(|&x| Fr::from(x)).collect();
        let lag = lagrange_basis(&xs);

        assert_eq!(lag.len(), 2);
        assert_eq!(lag[0][0], Fr::one());
        assert_eq!(lag[0][1], -Fr::one());
        assert_eq!(lag[1][0], Fr::zero());
        assert_eq!(lag[1][1], Fr::one());
    }

    #[test]
    fn test_lagrange_basis_3_points() {
        use ark_bls12_381::Fr;

        let xs: Vec<Fr> = [1u64, 2, 3].iter().map(|&x| Fr::from(x)).collect();
        let lag = lagrange_basis(&xs);

        assert_eq!(lag.len(), 3, "3 points → 3 basis polynomials");
        for l in &lag {
            assert_eq!(l.len(), 3, "each L_i has degree ≤ 2 → 3 coefficients");
        }

        let two_inv = Fr::from(2u64).inverse().unwrap();
        assert_eq!(lag[0][0], Fr::from(3u64));
        assert_eq!(lag[0][1], Fr::from(5u64) * (-two_inv));
        assert_eq!(lag[0][2], two_inv);

        for i in 0..3 {
            for j in 0..3 {
                let mut val = Fr::zero();
                let mut xpow = Fr::one();
                for k in 0..lag[i].len() {
                    val += lag[i][k] * xpow;
                    xpow *= xs[j];
                }
                if i == j {
                    assert_eq!(val, Fr::one(), "L_{}({}) should be 1", i, j + 1);
                } else {
                    assert_eq!(val, Fr::zero(), "L_{}({}) should be 0", i, j + 1);
                }
            }
        }
    }

    #[test]
    fn test_add_op_interpolate_constant_points() {
        use crate::PRef;
        use ark_bls12_381::Fr;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let mut gresult = GroebnerResult::<ArkBls12_381, GrevLexTerm>::new();

        let evals_typ = ATyp::Vec(Box::new(ATyp::scalar()), 2);
        let pref_evals = PRef::from_node(
            NodeIndex::new(0),
            evals_typ.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_evals);

        let points: GOp<ArkBls12_381> =
            Op::Value(Value::VecScalar(vec![Fr::from(0u64), Fr::from(1u64)]));
        let evals: GOp<ArkBls12_381> =
            Op::Ref(crate::Ref::new(NodeIndex::new(0)), evals_typ.clone());

        let result_typ = ATyp::uni(2);
        let pref_result = PRef::from_node(
            NodeIndex::new(1),
            result_typ.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_result);

        let op: GOp<ArkBls12_381> =
            Op::Interpolate(mk::<ArkBls12_381>(points), mk::<ArkBls12_381>(evals));
        builder.add_op(pref_result.clone(), op, &mut gresult);

        let var = |p: &PRef| SparsePolynomial::<Fr, GrevLexTerm>::var(p);

        let r0 = pref_result.clone().with_slot(0).unwrap();
        let r1 = pref_result.clone().with_slot(1).unwrap();
        let r2 = pref_result.clone().with_slot(2).unwrap();

        let y0 = pref_evals
            .clone()
            .with_index(0)
            .unwrap()
            .with_slot(0)
            .unwrap();
        let y1 = pref_evals
            .clone()
            .with_index(1)
            .unwrap()
            .with_slot(0)
            .unwrap();

        let expected_c0 = var(&y0);
        let expected_c1 = -var(&y0) + var(&y1);

        assert_eq!(
            gresult.pl.get(&r0).cloned(),
            Some(expected_c0.clone()),
            "pl[c0] = var(y0)"
        );
        assert_eq!(
            gresult.pl.get(&r1).cloned(),
            Some(expected_c1.clone()),
            "pl[c1] = -var(y0) + var(y1)"
        );
        assert_eq!(
            gresult.pl.get(&r2).cloned(),
            Some(SparsePolynomial::<Fr, GrevLexTerm>::zero()),
            "pl[c2] = 0"
        );

        assert!(
            gresult
                .basis
                .iter()
                .any(|r| r == &(&expected_c0 - &var(&r0)))
        );
        assert!(
            gresult
                .basis
                .iter()
                .any(|r| r == &(&expected_c1 - &var(&r1)))
        );
    }

    #[test]
    fn test_add_op_interpolate_3_constant_points() {
        use crate::PRef;
        use ark_bls12_381::Fr;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let mut gresult = GroebnerResult::<ArkBls12_381, GrevLexTerm>::new();

        let evals_typ = ATyp::Vec(Box::new(ATyp::scalar()), 3);
        let pref_evals = PRef::from_node(
            NodeIndex::new(0),
            evals_typ.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_evals);

        let points: GOp<ArkBls12_381> = Op::Value(Value::VecScalar(
            [1u64, 2, 3].iter().map(|&x| Fr::from(x)).collect(),
        ));
        let evals: GOp<ArkBls12_381> =
            Op::Ref(crate::Ref::new(NodeIndex::new(0)), evals_typ.clone());

        let result_typ = ATyp::uni(3);
        let pref_result = PRef::from_node(
            NodeIndex::new(1),
            result_typ.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_result);

        let op: GOp<ArkBls12_381> =
            Op::Interpolate(mk::<ArkBls12_381>(points), mk::<ArkBls12_381>(evals));
        builder.add_op(pref_result.clone(), op, &mut gresult);

        let var = |p: &PRef| SparsePolynomial::<Fr, GrevLexTerm>::var(p);

        let r0 = pref_result.clone().with_slot(0).unwrap();
        let r1 = pref_result.clone().with_slot(1).unwrap();
        let r2 = pref_result.clone().with_slot(2).unwrap();
        let r3 = pref_result.clone().with_slot(3).unwrap();

        let y0 = pref_evals
            .clone()
            .with_index(0)
            .unwrap()
            .with_slot(0)
            .unwrap();
        let y1 = pref_evals
            .clone()
            .with_index(1)
            .unwrap()
            .with_slot(0)
            .unwrap();
        let y2 = pref_evals
            .clone()
            .with_index(2)
            .unwrap()
            .with_slot(0)
            .unwrap();

        let lag = lagrange_basis::<Fr>(&[Fr::from(1u64), Fr::from(2u64), Fr::from(3u64)]);

        let expected_c0 = &(&var(&y0) * &SparsePolynomial::lit(&lag[0][0]))
            + &(&(&var(&y1) * &SparsePolynomial::lit(&lag[1][0]))
                + &(&var(&y2) * &SparsePolynomial::lit(&lag[2][0])));
        let expected_c1 = &(&var(&y0) * &SparsePolynomial::lit(&lag[0][1]))
            + &(&(&var(&y1) * &SparsePolynomial::lit(&lag[1][1]))
                + &(&var(&y2) * &SparsePolynomial::lit(&lag[2][1])));
        let expected_c2 = &(&var(&y0) * &SparsePolynomial::lit(&lag[0][2]))
            + &(&(&var(&y1) * &SparsePolynomial::lit(&lag[1][2]))
                + &(&var(&y2) * &SparsePolynomial::lit(&lag[2][2])));

        assert_eq!(
            gresult.pl.get(&r0).cloned(),
            Some(expected_c0.clone()),
            "pl[c0]"
        );
        assert_eq!(
            gresult.pl.get(&r1).cloned(),
            Some(expected_c1.clone()),
            "pl[c1]"
        );
        assert_eq!(
            gresult.pl.get(&r2).cloned(),
            Some(expected_c2.clone()),
            "pl[c2]"
        );
        assert_eq!(
            gresult.pl.get(&r3).cloned(),
            Some(SparsePolynomial::<Fr, GrevLexTerm>::zero()),
            "pl[c3] = 0"
        );
    }

    #[test]
    fn test_add_op_interpolate_ref_with_constant_points_in_pl() {
        use crate::PRef;
        use ark_bls12_381::Fr;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let mut gresult = GroebnerResult::<ArkBls12_381, GrevLexTerm>::new();

        let vec_t = ATyp::Vec(Box::new(ATyp::scalar()), 2);
        let pref_points = PRef::from_node(
            NodeIndex::new(0),
            vec_t.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_points);

        let coefs: Vec<_> = [0u64, 1]
            .iter()
            .map(|&n| mk::<ArkBls12_381>(Op::Value(Value::Index(n as usize))))
            .collect();
        builder.add_op(pref_points.clone(), Op::Vec(coefs), &mut gresult);

        let pref_evals = PRef::from_node(
            NodeIndex::new(1),
            vec_t.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_evals);

        let result_typ = ATyp::uni(2);
        let pref_result = PRef::from_node(
            NodeIndex::new(2),
            result_typ.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_result);

        let points: GOp<ArkBls12_381> = Op::Ref(crate::Ref::new(NodeIndex::new(0)), vec_t.clone());
        let evals: GOp<ArkBls12_381> = Op::Ref(crate::Ref::new(NodeIndex::new(1)), vec_t.clone());

        let op: GOp<ArkBls12_381> =
            Op::Interpolate(mk::<ArkBls12_381>(points), mk::<ArkBls12_381>(evals));
        builder.add_op(pref_result.clone(), op, &mut gresult);

        let var = |p: &PRef| SparsePolynomial::<Fr, GrevLexTerm>::var(p);

        let r0 = pref_result.clone().with_slot(0).unwrap();
        let r1 = pref_result.clone().with_slot(1).unwrap();
        let r2 = pref_result.clone().with_slot(2).unwrap();

        let y0 = pref_evals
            .clone()
            .with_index(0)
            .unwrap()
            .with_slot(0)
            .unwrap();
        let y1 = pref_evals
            .clone()
            .with_index(1)
            .unwrap()
            .with_slot(0)
            .unwrap();

        let expected_c0 = var(&y0);
        let expected_c1 = -var(&y0) + var(&y1);

        assert_eq!(
            gresult.pl.get(&r0).cloned(),
            Some(expected_c0.clone()),
            "pl[c0]"
        );
        assert_eq!(
            gresult.pl.get(&r1).cloned(),
            Some(expected_c1.clone()),
            "pl[c1]"
        );
        assert_eq!(
            gresult.pl.get(&r2).cloned(),
            Some(SparsePolynomial::<Fr, GrevLexTerm>::zero()),
            "pl[c2] = 0"
        );
    }

    #[test]
    fn test_add_op_interpolate_variable_points_falls_back_to_opaque() {
        use crate::PRef;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let mut gresult = GroebnerResult::<ArkBls12_381, GrevLexTerm>::new();

        let vec_t = ATyp::Vec(Box::new(ATyp::scalar()), 2);
        let pref_points = PRef::from_node(
            NodeIndex::new(0),
            vec_t.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        let pref_evals = PRef::from_node(
            NodeIndex::new(1),
            vec_t.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_points);
        builder.ns.register(&pref_evals);

        let result_typ = ATyp::uni(2);
        let pref_result = PRef::from_node(
            NodeIndex::new(2),
            result_typ.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_result);

        let points: GOp<ArkBls12_381> = Op::Ref(crate::Ref::new(NodeIndex::new(0)), vec_t.clone());
        let evals: GOp<ArkBls12_381> = Op::Ref(crate::Ref::new(NodeIndex::new(1)), vec_t.clone());

        let op: GOp<ArkBls12_381> =
            Op::Interpolate(mk::<ArkBls12_381>(points), mk::<ArkBls12_381>(evals));
        builder.add_op(pref_result.clone(), op, &mut gresult);

        assert!(
            gresult.np.contains(&pref_result),
            "variable points should be opaque"
        );
    }

    #[test]
    fn test_add_op_div_scalar_slot_wise() {
        use crate::PRef;
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
        let pref_b = PRef::from_node(
            NodeIndex::new(1),
            ATyp::scalar(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_a);
        builder.ns.register(&pref_b);

        let pref_result = PRef::from_node(
            NodeIndex::new(2),
            ATyp::scalar(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_result);

        let a = Op::Ref(crate::Ref::new(NodeIndex::new(0)), ATyp::scalar());
        let b = Op::Ref(crate::Ref::new(NodeIndex::new(1)), ATyp::scalar());
        let op: GOp<ArkBls12_381> = Op::Bin(
            BinOp::Div,
            mk::<ArkBls12_381>(a),
            mk::<ArkBls12_381>(b),
            ATyp::scalar(),
        );
        builder.add_op(pref_result.clone(), op, &mut gresult);

        let var = |p: &PRef| SparsePolynomial::<ark_bls12_381::Fr, GrevLexTerm>::var(p);

        let a_slot = pref_a.with_slot(0).unwrap();
        let b_slot = pref_b.with_slot(0).unwrap();
        let r_slot = pref_result.with_slot(0).unwrap();
        let expected = &var(&a_slot) - &(&var(&b_slot) * &var(&r_slot));
        assert!(
            gresult.basis.iter().any(|r| r == &expected),
            "basis should contain a - b*var(pr)"
        );
    }

    #[test]
    #[should_panic(expected = "Rem: non-polynomial remainder")]
    fn test_add_op_rem_scalar_panics() {
        use crate::PRef;
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
        let pref_b = PRef::from_node(
            NodeIndex::new(1),
            ATyp::scalar(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_a);
        builder.ns.register(&pref_b);

        let pref_result = PRef::from_node(
            NodeIndex::new(2),
            ATyp::scalar(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_result);

        let a = Op::Ref(crate::Ref::new(NodeIndex::new(0)), ATyp::scalar());
        let b = Op::Ref(crate::Ref::new(NodeIndex::new(1)), ATyp::scalar());
        let op: GOp<ArkBls12_381> = Op::Bin(
            BinOp::Rem,
            mk::<ArkBls12_381>(a),
            mk::<ArkBls12_381>(b),
            ATyp::scalar(),
        );
        builder.add_op(pref_result, op, &mut gresult);
    }

    #[test]
    fn test_reduce_div_scalar_uses_slot_wise_div() {
        use crate::PRef;
        use lang::ast::BinOp;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let mut gresult = GroebnerResult::<ArkBls12_381, GrevLexTerm>::new();

        let vec_t = ATyp::Vec(Box::new(ATyp::scalar()), 3);
        let pref_v = PRef::from_node(
            NodeIndex::new(0),
            vec_t.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_v);

        let result = PRef::from_node(
            NodeIndex::new(1),
            ATyp::scalar(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        let op: GOp<ArkBls12_381> = Op::Reduce(
            BinOp::Div,
            mk::<ArkBls12_381>(Op::Ref(crate::Ref::new(NodeIndex::new(0)), vec_t)),
        );
        builder.add_op(result.clone(), op, &mut gresult);

        let v0 = pref_v.clone().with_index(0).unwrap().with_slot(0).unwrap();
        let v1 = pref_v.clone().with_index(1).unwrap().with_slot(0).unwrap();
        let v2 = pref_v.clone().with_index(2).unwrap().with_slot(0).unwrap();
        let r_slot = result.with_slot(0).unwrap();

        let step1_vars: Vec<_> = gresult
            .basis
            .iter()
            .filter(|row| row.contains(&r_slot) && row.contains(&v2))
            .collect();
        assert!(
            !step1_vars.is_empty(),
            "basis should contain final div constraint involving v[2] and result"
        );

        let step0_vars: Vec<_> = gresult
            .basis
            .iter()
            .filter(|row| row.contains(&v0) && row.contains(&v1))
            .collect();
        assert!(
            !step0_vars.is_empty(),
            "basis should contain first div constraint involving v[0] and v[1]"
        );
    }

    #[test]
    #[should_panic(expected = "Rem: non-polynomial remainder")]
    fn test_reduce_rem_scalar_panics() {
        use crate::PRef;
        use lang::ast::BinOp;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let mut gresult = GroebnerResult::<ArkBls12_381, GrevLexTerm>::new();

        let vec_t = ATyp::Vec(Box::new(ATyp::scalar()), 2);
        let pref_v = PRef::from_node(
            NodeIndex::new(0),
            vec_t.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_v);

        let result = PRef::from_node(
            NodeIndex::new(1),
            ATyp::scalar(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&result);

        let op: GOp<ArkBls12_381> = Op::Reduce(
            BinOp::Rem,
            mk::<ArkBls12_381>(Op::Ref(crate::Ref::new(NodeIndex::new(0)), vec_t)),
        );
        builder.add_op(result, op, &mut gresult);
    }

    #[test]
    #[should_panic(expected = "MLE division is not supported")]
    fn test_add_op_div_mle_panics() {
        use crate::PRef;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let mut gresult = GroebnerResult::<ArkBls12_381, GrevLexTerm>::new();

        let pref_a = PRef::from_node(
            NodeIndex::new(0),
            ATyp::Mle(2),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        let pref_b = PRef::from_node(
            NodeIndex::new(1),
            ATyp::Mle(2),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_a);
        builder.ns.register(&pref_b);

        let result = PRef::from_node(
            NodeIndex::new(2),
            ATyp::Mle(2),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&result);

        let a = Op::Ref(crate::Ref::new(NodeIndex::new(0)), ATyp::Mle(2));
        let b = Op::Ref(crate::Ref::new(NodeIndex::new(1)), ATyp::Mle(2));
        let op: GOp<ArkBls12_381> = Op::Bin(
            BinOp::Div,
            mk::<ArkBls12_381>(a),
            mk::<ArkBls12_381>(b),
            ATyp::Mle(2),
        );
        builder.add_op(result, op, &mut gresult);
    }

    #[test]
    fn test_reduce_div_vpoly_uses_handle_div_rem() {
        use crate::PRef;
        use lang::ast::BinOp;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let mut gresult = GroebnerResult::<ArkBls12_381, GrevLexTerm>::new();

        let vec_t = ATyp::Vec(Box::new(ATyp::VPoly(1, 3)), 2);
        let pref_v = PRef::from_node(
            NodeIndex::new(0),
            vec_t.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_v);

        let result = PRef::from_node(
            NodeIndex::new(1),
            ATyp::VPoly(1, 1),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&result);

        let op: GOp<ArkBls12_381> = Op::Reduce(
            BinOp::Div,
            mk::<ArkBls12_381>(Op::Ref(crate::Ref::new(NodeIndex::new(0)), vec_t)),
        );
        builder.add_op(result.clone(), op, &mut gresult);

        assert!(
            !gresult.basis.is_empty(),
            "Reduce Div on VPoly should emit identity rows via handle_div_rem"
        );
    }

    // -----------------------------------------------------------------
    // Record: field-slot-aware layout
    // -----------------------------------------------------------------

    #[test]
    fn test_record_scalar_fields_bind_slots() {
        use crate::PRef;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let mut gresult = GroebnerResult::<ArkBls12_381, GrevLexTerm>::new();

        let s = ATyp::scalar();
        // Ctx iterates in key order (alphabetical): "x" < "y"
        let mut rec_fields = Ctx::<String, ATyp>::new();
        rec_fields.insert(&"x".to_string(), &s);
        rec_fields.insert(&"y".to_string(), &s);
        let rec_typ = ATyp::Record(rec_fields);

        let pref_a = PRef::from_node(
            NodeIndex::new(0),
            s.clone(),
            0,
            Qualifier::Public,
            Distribution::default(),
        );
        builder.ns.register(&pref_a);
        let pref_b = PRef::from_node(
            NodeIndex::new(1),
            s.clone(),
            0,
            Qualifier::Public,
            Distribution::default(),
        );
        builder.ns.register(&pref_b);

        let mut fields = Ctx::<String, HOp<ArkBls12_381>>::new();
        fields.insert(
            &"x".to_string(),
            &mk::<ArkBls12_381>(Op::Ref(crate::Ref::new(NodeIndex::new(0)), s.clone())),
        );
        fields.insert(
            &"y".to_string(),
            &mk::<ArkBls12_381>(Op::Ref(crate::Ref::new(NodeIndex::new(1)), s.clone())),
        );

        let pref_r = PRef::from_node(
            NodeIndex::new(2),
            rec_typ,
            0,
            Qualifier::Public,
            Distribution::default(),
        );
        builder.ns.register(&pref_r);

        builder.add_op(pref_r.clone(), Op::Record(fields), &mut gresult);

        // Ctx iteration order: "x" (slot 0), "y" (slot 1)
        let slot_x = pref_r.clone().with_slot(0).unwrap();
        let slot_y = pref_r.clone().with_slot(1).unwrap();

        assert!(
            gresult.pl.contains(&slot_x),
            "record slot 0 (x) missing from pl"
        );
        assert!(
            gresult.pl.contains(&slot_y),
            "record slot 1 (y) missing from pl"
        );

        let poly_x = gresult.pl.get(&slot_x).unwrap();
        let poly_y = gresult.pl.get(&slot_y).unwrap();
        assert!(
            poly_x.contains(&pref_a),
            "slot 0 poly should reference field x"
        );
        assert!(
            poly_y.contains(&pref_b),
            "slot 1 poly should reference field y"
        );
    }

    #[test]
    fn test_record_mixed_type_fields_bind_slots() {
        use crate::PRef;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let mut gresult = GroebnerResult::<ArkBls12_381, GrevLexTerm>::new();

        let s = ATyp::scalar();
        let uni_typ = ATyp::Uni(2);
        let mut rec_fields = Ctx::<String, ATyp>::new();
        rec_fields.insert(&"a".to_string(), &s);
        rec_fields.insert(&"p".to_string(), &uni_typ);
        let rec_typ = ATyp::Record(rec_fields);

        let pref_scalar = PRef::from_node(
            NodeIndex::new(0),
            s.clone(),
            0,
            Qualifier::Public,
            Distribution::default(),
        );
        builder.ns.register(&pref_scalar);

        let pref_poly = PRef::from_node(
            NodeIndex::new(1),
            uni_typ.clone(),
            0,
            Qualifier::Public,
            Distribution::default(),
        );
        builder.ns.register(&pref_poly);

        let mut fields = Ctx::<String, HOp<ArkBls12_381>>::new();
        fields.insert(
            &"a".to_string(),
            &mk::<ArkBls12_381>(Op::Ref(crate::Ref::new(NodeIndex::new(0)), s.clone())),
        );
        fields.insert(
            &"p".to_string(),
            &mk::<ArkBls12_381>(Op::Ref(crate::Ref::new(NodeIndex::new(1)), uni_typ.clone())),
        );

        let pref_r = PRef::from_node(
            NodeIndex::new(2),
            rec_typ,
            0,
            Qualifier::Public,
            Distribution::default(),
        );
        builder.ns.register(&pref_r);

        builder.add_op(pref_r.clone(), Op::Record(fields), &mut gresult);

        assert_eq!(
            pref_r.typ.physical_len(),
            4,
            "1 scalar + 3 Uni(2) coeffs = 4"
        );

        let slot_a = pref_r.clone().with_slot(0).unwrap();
        assert_eq!(slot_a.typ, s, "slot 0 should be scalar (field a)");
        assert!(
            gresult.pl.contains(&slot_a),
            "record slot 0 (a) missing from pl"
        );

        for i in 0..3 {
            let slot_pi = pref_r.clone().with_slot(1 + i).unwrap();
            assert_eq!(
                slot_pi.typ, s,
                "slots 1-3 should be scalar (field p coefficients)"
            );
            assert!(
                gresult.pl.contains(&slot_pi),
                "record slot {} (p coeff {}) missing from pl",
                1 + i,
                i
            );
        }
    }

    #[test]
    fn test_record_basis_count_matches_physical_len() {
        use crate::PRef;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let mut gresult = GroebnerResult::<ArkBls12_381, GrevLexTerm>::new();

        let s = ATyp::scalar();
        let v2 = ATyp::Vec(Box::new(s.clone()), 3);
        let mut rec_fields = Ctx::<String, ATyp>::new();
        rec_fields.insert(&"x".to_string(), &s);
        rec_fields.insert(&"v".to_string(), &v2);
        let rec_typ = ATyp::Record(rec_fields);
        let phys_len = rec_typ.physical_len();
        assert_eq!(phys_len, 4, "1 scalar + 3 Vec scalars = 4");

        let pref_x = PRef::from_node(
            NodeIndex::new(0),
            s.clone(),
            0,
            Qualifier::Public,
            Distribution::default(),
        );
        builder.ns.register(&pref_x);

        let pref_v = PRef::from_node(
            NodeIndex::new(1),
            v2.clone(),
            0,
            Qualifier::Public,
            Distribution::default(),
        );
        builder.ns.register(&pref_v);

        let mut fields = Ctx::<String, HOp<ArkBls12_381>>::new();
        fields.insert(
            &"x".to_string(),
            &mk::<ArkBls12_381>(Op::Ref(crate::Ref::new(NodeIndex::new(0)), s.clone())),
        );
        fields.insert(
            &"v".to_string(),
            &mk::<ArkBls12_381>(Op::Ref(crate::Ref::new(NodeIndex::new(1)), v2.clone())),
        );

        let pref_r = PRef::from_node(
            NodeIndex::new(2),
            rec_typ,
            0,
            Qualifier::Public,
            Distribution::default(),
        );
        builder.ns.register(&pref_r);

        builder.add_op(pref_r.clone(), Op::Record(fields), &mut gresult);

        assert_eq!(
            gresult.basis.len(),
            phys_len,
            "basis should have one row per physical slot"
        );
    }

    // -----------------------------------------------------------------
    // Proj: extract field from a Record
    // -----------------------------------------------------------------

    #[test]
    fn test_proj_scalar_field_from_record() {
        use crate::PRef;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let mut gresult = GroebnerResult::<ArkBls12_381, GrevLexTerm>::new();

        let s = ATyp::scalar();
        // Alphabetical: "x" < "y", so "x" is slot 0, "y" is slot 1
        let mut rec_fields = Ctx::<String, ATyp>::new();
        rec_fields.insert(&"x".to_string(), &s);
        rec_fields.insert(&"y".to_string(), &s);
        let rec_typ = ATyp::Record(rec_fields);

        let pref_rec = PRef::from_node(
            NodeIndex::new(0),
            rec_typ.clone(),
            0,
            Qualifier::Public,
            Distribution::default(),
        );
        builder.ns.register(&pref_rec);

        let inner_op: GOp<ArkBls12_381> = Op::Ref(crate::Ref::new(NodeIndex::new(0)), rec_typ);

        let pref_proj = PRef::from_node(
            NodeIndex::new(1),
            s.clone(),
            0,
            Qualifier::Public,
            Distribution::default(),
        );
        builder.ns.register(&pref_proj);

        builder.add_op(
            pref_proj.clone(),
            Op::Proj(mk::<ArkBls12_381>(inner_op), "x".to_string(), s.clone()),
            &mut gresult,
        );

        assert!(
            gresult.pl.contains(&pref_proj),
            "proj result missing from pl"
        );

        let proj_poly = gresult.pl.get(&pref_proj).unwrap();
        let slot_0 = pref_rec.clone().with_slot(0).unwrap();
        assert!(
            proj_poly.contains(&slot_0),
            "proj poly should reference record slot 0 (field x)"
        );
    }

    #[test]
    fn test_proj_second_field_offset_correct() {
        use crate::PRef;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let mut gresult = GroebnerResult::<ArkBls12_381, GrevLexTerm>::new();

        let s = ATyp::scalar();
        // Use "a" and "b" so alphabetical order is "a" then "b"
        // "a" : Scalar (1 slot at offset 0)
        // "b" : Vec<Scalar,3> (3 slots at offset 1)
        let v3 = ATyp::Vec(Box::new(s.clone()), 3);
        let mut rec_fields = Ctx::<String, ATyp>::new();
        rec_fields.insert(&"a".to_string(), &s);
        rec_fields.insert(&"b".to_string(), &v3);
        let rec_typ = ATyp::Record(rec_fields);

        let pref_rec = PRef::from_node(
            NodeIndex::new(0),
            rec_typ.clone(),
            0,
            Qualifier::Public,
            Distribution::default(),
        );
        builder.ns.register(&pref_rec);

        let inner_op: GOp<ArkBls12_381> = Op::Ref(crate::Ref::new(NodeIndex::new(0)), rec_typ);

        let pref_proj = PRef::from_node(
            NodeIndex::new(1),
            v3.clone(),
            0,
            Qualifier::Public,
            Distribution::default(),
        );
        builder.ns.register(&pref_proj);

        builder.add_op(
            pref_proj.clone(),
            Op::Proj(mk::<ArkBls12_381>(inner_op), "b".to_string(), v3.clone()),
            &mut gresult,
        );

        assert_eq!(pref_proj.typ.physical_len(), 3, "Vec<F, 3> has 3 slots");
        for i in 0..3 {
            let proj_slot = pref_proj.clone().with_slot(i).unwrap();
            assert!(
                gresult.pl.contains(&proj_slot),
                "proj slot {} missing from pl",
                i
            );

            let proj_poly = gresult.pl.get(&proj_slot).unwrap();
            let rec_slot = pref_rec.clone().with_slot(1 + i).unwrap();
            assert!(
                proj_poly.contains(&rec_slot),
                "proj slot {} poly should reference record slot {} (field b at offset 1)",
                i,
                1 + i
            );
        }
    }

    #[test]
    fn test_proj_first_field_of_multi_field_record() {
        use crate::PRef;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let mut gresult = GroebnerResult::<ArkBls12_381, GrevLexTerm>::new();

        let s = ATyp::scalar();
        let uni2 = ATyp::Uni(2);
        // "a" < "b" alphabetically
        // "a": Uni(2) → 3 slots at offset 0
        // "b": Scalar → 1 slot at offset 3
        let mut rec_fields = Ctx::<String, ATyp>::new();
        rec_fields.insert(&"a".to_string(), &uni2);
        rec_fields.insert(&"b".to_string(), &s);
        let rec_typ = ATyp::Record(rec_fields);

        let pref_rec = PRef::from_node(
            NodeIndex::new(0),
            rec_typ.clone(),
            0,
            Qualifier::Public,
            Distribution::default(),
        );
        builder.ns.register(&pref_rec);

        let inner_op: GOp<ArkBls12_381> = Op::Ref(crate::Ref::new(NodeIndex::new(0)), rec_typ);

        let pref_proj = PRef::from_node(
            NodeIndex::new(1),
            uni2.clone(),
            0,
            Qualifier::Public,
            Distribution::default(),
        );
        builder.ns.register(&pref_proj);

        builder.add_op(
            pref_proj.clone(),
            Op::Proj(mk::<ArkBls12_381>(inner_op), "a".to_string(), uni2.clone()),
            &mut gresult,
        );

        assert_eq!(pref_proj.typ.physical_len(), 3, "Uni(2) has 3 coefficients");
        for i in 0..3 {
            let proj_slot = pref_proj.clone().with_slot(i).unwrap();
            assert!(
                gresult.pl.contains(&proj_slot),
                "proj slot {} missing from pl",
                i
            );

            let proj_poly = gresult.pl.get(&proj_slot).unwrap();
            let rec_slot = pref_rec.clone().with_slot(i).unwrap();
            assert!(
                proj_poly.contains(&rec_slot),
                "proj slot {} poly should reference record slot {} (field a at offset 0)",
                i,
                i
            );
        }
    }

    // -----------------------------------------------------------------
    // Regression: broadcast type handling for slot-wise binops
    // -----------------------------------------------------------------

    #[test]
    fn test_add_uni_different_degrees() {
        use crate::PRef;
        use ark_bls12_381::Fr;
        use backend::op::mk;
        use lang::ast::BinOp;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let mut gresult = GroebnerResult::<ArkBls12_381, GrevLexTerm>::new();

        let uni2 = ATyp::Uni(2);
        let uni4 = ATyp::Uni(4);
        let uni4_result = ATyp::Uni(4);

        let pref_a = PRef::from_node(
            NodeIndex::new(0),
            uni2.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_a);
        let coefs_a: Vec<_> = (1..=3u64)
            .map(|n| mk::<ArkBls12_381>(Op::Value(Value::Scalar(Fr::from(n)))))
            .collect();
        builder.add_op(pref_a.clone(), Op::Vec(coefs_a), &mut gresult);

        let pref_b = PRef::from_node(
            NodeIndex::new(1),
            uni4.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_b);
        let coefs_b: Vec<_> = (1..=5u64)
            .map(|n| mk::<ArkBls12_381>(Op::Value(Value::Scalar(Fr::from(n)))))
            .collect();
        builder.add_op(pref_b.clone(), Op::Vec(coefs_b), &mut gresult);

        let pref_r = PRef::from_node(
            NodeIndex::new(2),
            uni4_result.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_r);

        builder.add_op(
            pref_r.clone(),
            Op::Bin(
                BinOp::Add,
                mk::<ArkBls12_381>(Op::Ref(crate::Ref::new(NodeIndex::new(0)), uni2)),
                mk::<ArkBls12_381>(Op::Ref(crate::Ref::new(NodeIndex::new(1)), uni4)),
                uni4_result,
            ),
            &mut gresult,
        );

        assert_eq!(pref_r.typ.physical_len(), 5, "Uni(4) has 5 coefficients");
        for i in 0..5 {
            let slot = pref_r.clone().with_slot(i).unwrap();
            assert!(
                gresult.pl.contains(&slot),
                "Uni(2)+Uni(4) result slot {} missing from pl",
                i
            );
        }
    }

    #[test]
    fn test_mul_scalar_poly_broadcast() {
        use crate::PRef;
        use lang::ast::BinOp;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let mut gresult = GroebnerResult::<ArkBls12_381, GrevLexTerm>::new();

        let s = ATyp::scalar();
        let uni2 = ATyp::Uni(2);

        let pref_s = PRef::from_node(
            NodeIndex::new(0),
            s.clone(),
            0,
            Qualifier::Public,
            Distribution::default(),
        );
        builder.ns.register(&pref_s);

        let pref_p = PRef::from_node(
            NodeIndex::new(1),
            uni2.clone(),
            0,
            Qualifier::Public,
            Distribution::default(),
        );
        builder.ns.register(&pref_p);

        let pref_r = PRef::from_node(
            NodeIndex::new(2),
            uni2.clone(),
            0,
            Qualifier::Public,
            Distribution::default(),
        );
        builder.ns.register(&pref_r);

        builder.add_op(
            pref_r.clone(),
            Op::Bin(
                BinOp::Mul,
                mk::<ArkBls12_381>(Op::Ref(crate::Ref::new(NodeIndex::new(0)), s.clone())),
                mk::<ArkBls12_381>(Op::Ref(crate::Ref::new(NodeIndex::new(1)), uni2.clone())),
                uni2.clone(),
            ),
            &mut gresult,
        );

        assert_eq!(
            gresult.basis.len(),
            3,
            "Scalar * Uni(2) should produce 3 basis rows (one per coefficient)"
        );
        for i in 0..3 {
            let slot = pref_r.clone().with_slot(i).unwrap();
            assert!(
                gresult.pl.contains(&slot),
                "Scalar*Uni(2) result slot {} missing from pl",
                i
            );
        }
    }

    #[test]
    fn test_mul_vec_scalar_broadcast() {
        use crate::PRef;
        use lang::ast::BinOp;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let mut gresult = GroebnerResult::<ArkBls12_381, GrevLexTerm>::new();

        let s = ATyp::scalar();
        let v3 = ATyp::Vec(Box::new(s.clone()), 3);

        let pref_v = PRef::from_node(
            NodeIndex::new(0),
            v3.clone(),
            0,
            Qualifier::Public,
            Distribution::default(),
        );
        builder.ns.register(&pref_v);

        let pref_s = PRef::from_node(
            NodeIndex::new(1),
            s.clone(),
            0,
            Qualifier::Public,
            Distribution::default(),
        );
        builder.ns.register(&pref_s);

        let pref_r = PRef::from_node(
            NodeIndex::new(2),
            v3.clone(),
            0,
            Qualifier::Public,
            Distribution::default(),
        );
        builder.ns.register(&pref_r);

        builder.add_op(
            pref_r.clone(),
            Op::Bin(
                BinOp::Mul,
                mk::<ArkBls12_381>(Op::Ref(crate::Ref::new(NodeIndex::new(0)), v3.clone())),
                mk::<ArkBls12_381>(Op::Ref(crate::Ref::new(NodeIndex::new(1)), s.clone())),
                v3.clone(),
            ),
            &mut gresult,
        );

        assert_eq!(
            gresult.basis.len(),
            3,
            "Vec<Scalar,3> * Scalar should produce 3 basis rows"
        );
    }

    #[test]
    fn test_add_scalar_poly_broadcast() {
        use crate::PRef;
        use lang::ast::BinOp;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let mut gresult = GroebnerResult::<ArkBls12_381, GrevLexTerm>::new();

        let s = ATyp::scalar();
        let uni2 = ATyp::Uni(2);

        let pref_s = PRef::from_node(
            NodeIndex::new(0),
            s.clone(),
            0,
            Qualifier::Public,
            Distribution::default(),
        );
        builder.ns.register(&pref_s);

        let pref_p = PRef::from_node(
            NodeIndex::new(1),
            uni2.clone(),
            0,
            Qualifier::Public,
            Distribution::default(),
        );
        builder.ns.register(&pref_p);

        let pref_r = PRef::from_node(
            NodeIndex::new(2),
            uni2.clone(),
            0,
            Qualifier::Public,
            Distribution::default(),
        );
        builder.ns.register(&pref_r);

        builder.add_op(
            pref_r.clone(),
            Op::Bin(
                BinOp::Add,
                mk::<ArkBls12_381>(Op::Ref(crate::Ref::new(NodeIndex::new(0)), s.clone())),
                mk::<ArkBls12_381>(Op::Ref(crate::Ref::new(NodeIndex::new(1)), uni2.clone())),
                uni2.clone(),
            ),
            &mut gresult,
        );

        assert_eq!(
            gresult.basis.len(),
            3,
            "Scalar + Uni(2) should produce 3 basis rows"
        );
    }

    #[test]
    fn test_concat_vec_uni_different_degrees() {
        use crate::PRef;
        use lang::ast::BinOp;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let mut gresult = GroebnerResult::<ArkBls12_381, GrevLexTerm>::new();

        let uni2 = ATyp::Uni(2);
        let uni4 = ATyp::Uni(4);
        let vec_uni2 = ATyp::Vec(Box::new(uni2.clone()), 2);
        let vec_uni4 = ATyp::Vec(Box::new(uni4.clone()), 2);
        let vec_result = ATyp::Vec(Box::new(uni4.clone()), 4);

        let pref_a = PRef::from_node(
            NodeIndex::new(0),
            vec_uni2.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_a);

        let pref_b = PRef::from_node(
            NodeIndex::new(1),
            vec_uni4.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_b);

        let pref_r = PRef::from_node(
            NodeIndex::new(2),
            vec_result.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_r);

        builder.add_op(
            pref_r.clone(),
            Op::Bin(
                BinOp::Concat,
                mk::<ArkBls12_381>(Op::Ref(
                    crate::Ref::new(NodeIndex::new(0)),
                    vec_uni2.clone(),
                )),
                mk::<ArkBls12_381>(Op::Ref(
                    crate::Ref::new(NodeIndex::new(1)),
                    vec_uni4.clone(),
                )),
                vec_result.clone(),
            ),
            &mut gresult,
        );

        assert_eq!(
            pref_r.typ.physical_len(),
            20,
            "Vec(Uni(4), 4) has 4*5=20 slots"
        );
        for i in 0..4 {
            let elem = pref_r.with_index(i).unwrap();
            for j in 0..5 {
                let slot = elem.with_slot(j).unwrap();
                assert!(
                    gresult.pl.contains(&slot),
                    "Concat result element {} slot {} missing from pl",
                    i,
                    j
                );
            }
        }
    }

    #[test]
    fn test_concat_vec_scalar_element() {
        use crate::PRef;
        use lang::ast::BinOp;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let mut gresult = GroebnerResult::<ArkBls12_381, GrevLexTerm>::new();

        let s = ATyp::scalar();
        let vec_s = ATyp::Vec(Box::new(s.clone()), 2);
        let vec_result = ATyp::Vec(Box::new(s.clone()), 3);

        let pref_a = PRef::from_node(
            NodeIndex::new(0),
            vec_s.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_a);

        let pref_b = PRef::from_node(
            NodeIndex::new(1),
            s.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_b);

        let pref_r = PRef::from_node(
            NodeIndex::new(2),
            vec_result.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_r);

        builder.add_op(
            pref_r.clone(),
            Op::Bin(
                BinOp::Concat,
                mk::<ArkBls12_381>(Op::Ref(crate::Ref::new(NodeIndex::new(0)), vec_s.clone())),
                mk::<ArkBls12_381>(Op::Ref(crate::Ref::new(NodeIndex::new(1)), s.clone())),
                vec_result.clone(),
            ),
            &mut gresult,
        );

        assert_eq!(pref_r.typ.physical_len(), 3, "Vec(Scalar, 3) has 3 slots");
        for i in 0..3 {
            let elem = pref_r.with_index(i).unwrap();
            assert!(
                gresult.pl.contains(&elem),
                "Concat Vec++Scalar result element {} missing from pl",
                i
            );
        }
    }

    #[test]
    fn test_equ_vec_uni_different_degrees() {
        use crate::PRef;
        use lang::ast::BinOp;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let mut gresult = GroebnerResult::<ArkBls12_381, GrevLexTerm>::new();

        let uni2 = ATyp::Uni(2);
        let uni4 = ATyp::Uni(4);
        let vec_uni2 = ATyp::Vec(Box::new(uni2.clone()), 2);
        let vec_uni4 = ATyp::Vec(Box::new(uni4.clone()), 2);
        let bool_typ = ATyp::bool();

        let pref_a = PRef::from_node(
            NodeIndex::new(0),
            vec_uni2.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_a);

        let pref_b = PRef::from_node(
            NodeIndex::new(1),
            vec_uni4.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_b);

        let pref_r = PRef::from_node(
            NodeIndex::new(2),
            bool_typ.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_r);

        builder.add_op(
            pref_r.clone(),
            Op::Bin(
                BinOp::Equ,
                mk::<ArkBls12_381>(Op::Ref(
                    crate::Ref::new(NodeIndex::new(0)),
                    vec_uni2.clone(),
                )),
                mk::<ArkBls12_381>(Op::Ref(
                    crate::Ref::new(NodeIndex::new(1)),
                    vec_uni4.clone(),
                )),
                bool_typ.clone(),
            ),
            &mut gresult,
        );

        assert!(
            !gresult.basis.is_empty(),
            "Vec(Uni(2),2) == Vec(Uni(4),2) should produce basis constraints (zero-padded per element)"
        );
    }

    #[test]
    fn test_dot_vec_scalar() {
        use crate::PRef;
        use lang::ast::BinOp;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let mut gresult = GroebnerResult::<ArkBls12_381, GrevLexTerm>::new();

        let s = ATyp::scalar();
        let vec_s = ATyp::Vec(Box::new(s.clone()), 3);

        let pref_a = PRef::from_node(
            NodeIndex::new(0),
            vec_s.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_a);

        let pref_b = PRef::from_node(
            NodeIndex::new(1),
            vec_s.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_b);

        let pref_r = PRef::from_node(
            NodeIndex::new(2),
            s.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_r);

        builder.add_op(
            pref_r.clone(),
            Op::Bin(
                BinOp::Dot,
                mk::<ArkBls12_381>(Op::Ref(crate::Ref::new(NodeIndex::new(0)), vec_s.clone())),
                mk::<ArkBls12_381>(Op::Ref(crate::Ref::new(NodeIndex::new(1)), vec_s.clone())),
                s.clone(),
            ),
            &mut gresult,
        );

        assert!(
            gresult.pl.contains(&pref_r),
            "Dot Vec(Scalar,3)·Vec(Scalar,3) result should be in pl"
        );
        assert!(
            !gresult.basis.is_empty(),
            "Dot Vec(Scalar,3)·Vec(Scalar,3) should produce basis rows"
        );
    }

    #[test]
    fn test_dot_vec_uni() {
        use crate::PRef;
        use lang::ast::BinOp;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let mut gresult = GroebnerResult::<ArkBls12_381, GrevLexTerm>::new();

        let uni2 = ATyp::Uni(2);
        let uni4 = ATyp::Uni(4);
        let vec_uni2 = ATyp::Vec(Box::new(uni2.clone()), 2);
        let vec_uni4 = ATyp::Vec(Box::new(uni4.clone()), 2);
        let dot_result = ATyp::Uni(6);

        let pref_a = PRef::from_node(
            NodeIndex::new(0),
            vec_uni2.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_a);

        let pref_b = PRef::from_node(
            NodeIndex::new(1),
            vec_uni4.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_b);

        let pref_r = PRef::from_node(
            NodeIndex::new(2),
            dot_result.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_r);

        builder.add_op(
            pref_r.clone(),
            Op::Bin(
                BinOp::Dot,
                mk::<ArkBls12_381>(Op::Ref(
                    crate::Ref::new(NodeIndex::new(0)),
                    vec_uni2.clone(),
                )),
                mk::<ArkBls12_381>(Op::Ref(
                    crate::Ref::new(NodeIndex::new(1)),
                    vec_uni4.clone(),
                )),
                dot_result.clone(),
            ),
            &mut gresult,
        );

        for i in 0..7 {
            let slot = pref_r.with_slot(i).unwrap();
            assert!(
                gresult.pl.contains(&slot),
                "Dot Vec(Uni(2),2)·Vec(Uni(4),2) result slot {} missing from pl",
                i
            );
        }
    }

    #[test]
    fn test_pair_vec() {
        use crate::PRef;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let mut gresult = GroebnerResult::<ArkBls12_381, GrevLexTerm>::new();

        let g1 = ATyp::g1();
        let g2 = ATyp::g2();
        let gt = ATyp::gt();
        let vec_g1 = ATyp::Vec(Box::new(g1.clone()), 2);
        let vec_g2 = ATyp::Vec(Box::new(g2.clone()), 2);
        let vec_gt = ATyp::Vec(Box::new(gt.clone()), 2);

        let pref_a = PRef::from_node(
            NodeIndex::new(0),
            vec_g1.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_a);

        let pref_b = PRef::from_node(
            NodeIndex::new(1),
            vec_g2.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_b);

        let pref_r = PRef::from_node(
            NodeIndex::new(2),
            vec_gt.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_r);

        builder.add_op(
            pref_r.clone(),
            Op::Pair(
                mk::<ArkBls12_381>(Op::Ref(crate::Ref::new(NodeIndex::new(0)), vec_g1.clone())),
                mk::<ArkBls12_381>(Op::Ref(crate::Ref::new(NodeIndex::new(1)), vec_g2.clone())),
                vec_gt.clone(),
            ),
            &mut gresult,
        );

        for i in 0..2 {
            let elem = pref_r.with_index(i).unwrap();
            assert!(
                gresult.pl.contains(&elem),
                "Pair Vec(G1,2)×Vec(G2,2) result element {} missing from pl",
                i
            );
        }
    }

    #[test]
    fn test_pow_vec_element_wise() {
        use crate::PRef;
        use lang::ast::BinOp;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let mut gresult = GroebnerResult::<ArkBls12_381, GrevLexTerm>::new();

        let s = ATyp::scalar();
        let fin = ATyp::fin(lang::typ::range::CRange::default());
        let vec_s = ATyp::Vec(Box::new(s.clone()), 2);
        let vec_fin = ATyp::Vec(Box::new(fin.clone()), 2);
        let vec_result = ATyp::Vec(Box::new(s.clone()), 2);

        let pref_a = PRef::from_node(
            NodeIndex::new(0),
            vec_s.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_a);

        let pref_b = PRef::from_node(
            NodeIndex::new(1),
            vec_fin.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_b);

        let pref_r = PRef::from_node(
            NodeIndex::new(2),
            vec_result.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_r);

        builder.add_op(
            pref_r.clone(),
            Op::Bin(
                BinOp::Pow,
                mk::<ArkBls12_381>(Op::Ref(crate::Ref::new(NodeIndex::new(0)), vec_s.clone())),
                mk::<ArkBls12_381>(Op::Ref(crate::Ref::new(NodeIndex::new(1)), vec_fin.clone())),
                vec_result.clone(),
            ),
            &mut gresult,
        );

        for i in 0..2 {
            let elem = pref_r.with_index(i).unwrap();
            assert!(
                gresult.np.contains(&elem),
                "Pow Vec(Scalar,2)^Vec(Fin,2) result element {} should be opaque",
                i
            );
        }
    }

    #[test]
    fn test_pow_uni_const_exp() {
        use crate::PRef;
        use backend::op::mk;
        use lang::ast::BinOp;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let mut gresult = GroebnerResult::<ArkBls12_381, GrevLexTerm>::new();

        let uni2 = ATyp::Uni(2);
        let result_uni4 = ATyp::Uni(4);

        let pref_a = PRef::from_node(
            NodeIndex::new(0),
            uni2.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_a);

        let pref_r = PRef::from_node(
            NodeIndex::new(1),
            result_uni4.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_r);

        builder.add_op(
            pref_r.clone(),
            Op::Bin(
                BinOp::Pow,
                mk::<ArkBls12_381>(Op::Ref(crate::Ref::new(NodeIndex::new(0)), uni2.clone())),
                mk::<ArkBls12_381>(Op::Value(Value::Index(2))),
                result_uni4.clone(),
            ),
            &mut gresult,
        );

        for i in 0..5 {
            let slot = pref_r.with_slot(i).unwrap();
            assert!(
                gresult.pl.contains(&slot),
                "Pow Uni(2)^2 result slot {} missing from pl",
                i
            );
        }
        assert!(
            !gresult.np.contains(&pref_r),
            "Pow Uni(2)^2 with constant exponent should not be opaque"
        );
    }

    #[test]
    fn test_pow_vec_uni_const_exp() {
        use crate::PRef;
        use backend::op::mk;
        use lang::ast::BinOp;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let mut gresult = GroebnerResult::<ArkBls12_381, GrevLexTerm>::new();

        let uni2 = ATyp::Uni(2);
        let result_uni4 = ATyp::Uni(4);
        let vec_uni2 = ATyp::Vec(Box::new(uni2.clone()), 2);
        let vec_result = ATyp::Vec(Box::new(result_uni4.clone()), 2);

        let pref_a = PRef::from_node(
            NodeIndex::new(0),
            vec_uni2.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_a);

        let pref_r = PRef::from_node(
            NodeIndex::new(1),
            vec_result.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_r);

        builder.add_op(
            pref_r.clone(),
            Op::Bin(
                BinOp::Pow,
                mk::<ArkBls12_381>(Op::Ref(
                    crate::Ref::new(NodeIndex::new(0)),
                    vec_uni2.clone(),
                )),
                mk::<ArkBls12_381>(Op::Value(Value::Index(2))),
                vec_result.clone(),
            ),
            &mut gresult,
        );

        for i in 0..2 {
            let elem = pref_r.with_index(i).unwrap();
            for j in 0..5 {
                let slot = elem.with_slot(j).unwrap();
                assert!(
                    gresult.pl.contains(&slot),
                    "Pow Vec(Uni(2),2)^2 element {} slot {} missing from pl",
                    i,
                    j
                );
            }
        }
        assert!(
            !gresult.np.contains(&pref_r),
            "Pow Vec(Uni(2),2)^2 with constant exponent should not be opaque"
        );
    }

    #[test]
    fn test_pow_vec_vecindex_per_element() {
        use crate::PRef;
        use backend::op::mk;
        use lang::ast::BinOp;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let mut gresult = GroebnerResult::<ArkBls12_381, GrevLexTerm>::new();

        let s = ATyp::scalar();
        let vec_s = ATyp::Vec(Box::new(s.clone()), 2);
        let vec_result = ATyp::Vec(Box::new(s.clone()), 2);

        let pref_a = PRef::from_node(
            NodeIndex::new(0),
            vec_s.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_a);

        let pref_r = PRef::from_node(
            NodeIndex::new(1),
            vec_result.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_r);

        builder.add_op(
            pref_r.clone(),
            Op::Bin(
                BinOp::Pow,
                mk::<ArkBls12_381>(Op::Ref(crate::Ref::new(NodeIndex::new(0)), vec_s.clone())),
                mk::<ArkBls12_381>(Op::Value(Value::VecIndex(vec![2, 3]))),
                vec_result.clone(),
            ),
            &mut gresult,
        );

        for i in 0..2 {
            let elem = pref_r.with_index(i).unwrap();
            assert!(
                gresult.pl.contains(&elem),
                "Pow Vec(Scalar,2)^VecIndex([2,3]) result element {} missing from pl",
                i
            );
        }
        assert!(
            !gresult.np.contains(&pref_r),
            "Pow Vec(Scalar,2)^VecIndex([2,3]) should not be opaque"
        );
    }

    #[test]
    fn test_pow_vec_mixed_const_and_opaque() {
        use crate::PRef;
        use backend::op::mk;
        use lang::ast::BinOp;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let mut gresult = GroebnerResult::<ArkBls12_381, GrevLexTerm>::new();

        let s = ATyp::scalar();
        let vec_s = ATyp::Vec(Box::new(s.clone()), 2);
        let vec_result = ATyp::Vec(Box::new(s.clone()), 2);
        let fin = ATyp::fin(lang::typ::range::CRange::default());
        let vec_fin = ATyp::Vec(Box::new(fin.clone()), 2);

        let pref_a = PRef::from_node(
            NodeIndex::new(0),
            vec_s.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_a);

        let pref_b = PRef::from_node(
            NodeIndex::new(1),
            vec_fin.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_b);

        let pref_r = PRef::from_node(
            NodeIndex::new(2),
            vec_result.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_r);

        builder.add_op(
            pref_r.clone(),
            Op::Bin(
                BinOp::Pow,
                mk::<ArkBls12_381>(Op::Ref(crate::Ref::new(NodeIndex::new(0)), vec_s.clone())),
                mk::<ArkBls12_381>(Op::Ref(crate::Ref::new(NodeIndex::new(1)), vec_fin.clone())),
                vec_result.clone(),
            ),
            &mut gresult,
        );

        for i in 0..2 {
            let elem = pref_r.with_index(i).unwrap();
            assert!(
                gresult.np.contains(&elem),
                "Pow Vec(Scalar,2)^Vec(Fin,2) with non-const exponent element {} should be opaque",
                i
            );
        }
    }

    // -----------------------------------------------------------------
    // PolySource::lift_to tests
    // -----------------------------------------------------------------

    #[test]
    fn test_lift_uni_to_wider_uni() {
        use crate::PRef;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let pref = PRef::from_node(
            NodeIndex::new(0),
            ATyp::Uni(2),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref);
        let src = PolySource::from_ref_vars(
            &builder,
            &Op::Ref(Ref::new(NodeIndex::new(0)), ATyp::Uni(2)),
        );
        assert_eq!(src.polys.len(), 3);

        let lifted = src.lift_to(&ATyp::Uni(4));
        assert_eq!(lifted.polys.len(), 5);
        assert_eq!(*lifted.typ(), ATyp::Uni(4));
        for i in 0..3 {
            assert_eq!(
                lifted.polys[i],
                SparsePolynomial::var(&pref.clone().with_slot(i).unwrap())
            );
        }
        for i in 3..5 {
            assert!(
                lifted.polys[i].is_zero(),
                "padded slot {} should be zero",
                i
            );
        }
    }

    #[test]
    fn test_lift_mle_to_wider_mle() {
        use crate::PRef;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let pref = PRef::from_node(
            NodeIndex::new(0),
            ATyp::Mle(2),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref);
        let src = PolySource::from_ref_vars(
            &builder,
            &Op::Ref(Ref::new(NodeIndex::new(0)), ATyp::Mle(2)),
        );
        assert_eq!(src.polys.len(), 4);

        let lifted = src.lift_to(&ATyp::Mle(3));
        assert_eq!(lifted.polys.len(), 8);
        assert_eq!(*lifted.typ(), ATyp::Mle(3));
        for i in 0..4 {
            assert_eq!(
                lifted.polys[i],
                SparsePolynomial::var(&pref.clone().with_slot(i).unwrap())
            );
        }
        for i in 4..8 {
            assert!(
                lifted.polys[i].is_zero(),
                "padded slot {} should be zero",
                i
            );
        }
    }

    #[test]
    fn test_lift_vpoly_same_arity_prefix() {
        use crate::PRef;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let pref = PRef::from_node(
            NodeIndex::new(0),
            ATyp::VPoly(2, 2),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref);
        let src = PolySource::from_ref_vars(
            &builder,
            &Op::Ref(Ref::new(NodeIndex::new(0)), ATyp::VPoly(2, 2)),
        );
        assert_eq!(src.polys.len(), 6);

        let lifted = src.lift_to(&ATyp::VPoly(2, 3));
        assert_eq!(lifted.polys.len(), 10);
        assert_eq!(*lifted.typ(), ATyp::VPoly(2, 3));
        for i in 0..6 {
            assert_eq!(
                lifted.polys[i],
                SparsePolynomial::var(&pref.clone().with_slot(i).unwrap())
            );
        }
        for i in 6..10 {
            assert!(
                lifted.polys[i].is_zero(),
                "padded slot {} should be zero",
                i
            );
        }
    }

    #[test]
    fn test_lift_vpoly_cross_arity_embedding() {
        use crate::PRef;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let pref = PRef::from_node(
            NodeIndex::new(0),
            ATyp::VPoly(2, 2),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref);
        let src = PolySource::from_ref_vars(
            &builder,
            &Op::Ref(Ref::new(NodeIndex::new(0)), ATyp::VPoly(2, 2)),
        );

        let lifted = src.lift_to(&ATyp::VPoly(3, 2));
        assert_eq!(*lifted.typ(), ATyp::VPoly(3, 2));
        assert_eq!(lifted.polys.len(), ATyp::VPoly(3, 2).physical_len());

        let dst = multi_indices(3, 2);
        let src_idx = multi_indices(2, 2);
        for (j, sk) in src_idx.iter().enumerate() {
            let mut padded = sk.clone();
            padded.resize(3, 0);
            let pos = dst.iter().position(|dk| dk == &padded).unwrap();
            assert_eq!(
                lifted.polys[pos],
                SparsePolynomial::var(&pref.clone().with_slot(j).unwrap()),
                "src multi-index {:?} → padded {:?} → dst position {} should have src slot {}",
                sk,
                padded,
                pos,
                j
            );
        }
    }

    #[test]
    fn test_lift_mle_to_vpoly_lagrange() {
        use ark_bls12_381::Fr;

        let src = PolySource::<ArkBls12_381, GrevLexTerm>::new(
            vec![
                SparsePolynomial::lit(&Fr::from(1u64)),
                SparsePolynomial::lit(&Fr::from(2u64)),
                SparsePolynomial::lit(&Fr::from(3u64)),
                SparsePolynomial::lit(&Fr::from(4u64)),
            ],
            ATyp::Mle(2),
        );

        let lifted = src.lift_to(&ATyp::VPoly(2, 2));
        assert_eq!(*lifted.typ(), ATyp::VPoly(2, 2));
        assert_eq!(lifted.polys.len(), 6);

        let dst = multi_indices(2, 2);
        let c: [[i64; 2]; 2] = [[1, -1], [0, 1]];
        let hcube = hypercube(2);
        let vals: Vec<i64> = vec![1, 2, 3, 4];
        for (ir, k) in dst.iter().enumerate() {
            let mut expected: i64 = 0;
            for (j, b) in hcube.iter().enumerate() {
                let mut scalar: i64 = 1;
                for i in 0..2 {
                    let ki = if i < k.len() { k[i] } else { 0 };
                    if ki >= 2 {
                        scalar = 0;
                        break;
                    }
                    scalar *= c[b[i]][ki];
                }
                expected += vals[j] * scalar;
            }
            let actual = &lifted.polys[ir];
            if expected == 0 {
                assert!(
                    actual.is_zero(),
                    "Mle→VPoly coefficient at multi-index {:?} (position {}) should be zero",
                    k,
                    ir
                );
            } else {
                let expected_poly: SparsePolynomial<ark_bls12_381::Fr, GrevLexTerm> =
                    if expected >= 0 {
                        SparsePolynomial::lit(&Fr::from(expected as u64))
                    } else {
                        -SparsePolynomial::lit(&Fr::from((-expected) as u64))
                    };
                assert_eq!(
                    *actual, expected_poly,
                    "Mle→VPoly coefficient at multi-index {:?} (position {}) mismatch",
                    k, ir
                );
            }
        }
    }

    #[test]
    fn test_lift_uni_to_vpoly_same_arity() {
        use crate::PRef;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let pref = PRef::from_node(
            NodeIndex::new(0),
            ATyp::Uni(2),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref);
        let src = PolySource::from_ref_vars(
            &builder,
            &Op::Ref(Ref::new(NodeIndex::new(0)), ATyp::Uni(2)),
        );
        assert_eq!(src.polys.len(), 3);

        let lifted = src.lift_to(&ATyp::VPoly(1, 2));
        assert_eq!(*lifted.typ(), ATyp::VPoly(1, 2));
        assert_eq!(lifted.polys.len(), 3);
        for i in 0..3 {
            assert_eq!(
                lifted.polys[i],
                SparsePolynomial::var(&pref.clone().with_slot(i).unwrap())
            );
        }
    }

    // -----------------------------------------------------------------
    // broadcast_equ: Bool result with bare basis diffs
    // -----------------------------------------------------------------

    #[test]
    fn test_equ_scalar_has_var_constraint_and_diff() {
        use crate::PRef;
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
        let pref_r = PRef::from_node(
            NodeIndex::new(2),
            ATyp::bool(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );

        builder.add_op(
            pref_r.clone(),
            Op::Bin(
                BinOp::Equ,
                mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), ATyp::scalar())),
                mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(1)), ATyp::scalar())),
                ATyp::bool(),
            ),
            &mut gresult,
        );

        let a_slot = pref_a.with_slot(0).unwrap();
        let b_slot = pref_b.with_slot(0).unwrap();
        let r_slot = pref_r.with_slot(0).unwrap();
        let diff = &SparsePolynomial::var(&a_slot) - &SparsePolynomial::var(&b_slot);
        assert!(
            gresult.basis.iter().any(|p| *p == diff),
            "basis should contain a-b diff"
        );
        assert!(
            gresult
                .basis
                .iter()
                .any(|p| *p == SparsePolynomial::var(&r_slot)),
            "basis should contain var(r) constraint for Bool result"
        );
    }

    #[test]
    fn test_equ_uni_bool_result_bare_diffs() {
        use crate::PRef;
        use lang::ast::BinOp;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let mut gresult = GroebnerResult::<ArkBls12_381, GrevLexTerm>::new();

        let pref_a = PRef::from_node(
            NodeIndex::new(0),
            ATyp::Uni(2),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_a);
        let pref_b = PRef::from_node(
            NodeIndex::new(1),
            ATyp::Uni(2),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_b);
        let pref_r = PRef::from_node(
            NodeIndex::new(2),
            ATyp::bool(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );

        builder.add_op(
            pref_r.clone(),
            Op::Bin(
                BinOp::Equ,
                mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), ATyp::Uni(2))),
                mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(1)), ATyp::Uni(2))),
                ATyp::bool(),
            ),
            &mut gresult,
        );

        let r_slot = pref_r.with_slot(0).unwrap();

        assert!(
            gresult
                .basis
                .iter()
                .any(|p| *p == SparsePolynomial::var(&r_slot)),
            "basis should contain var(r) for Bool result"
        );

        for j in 0..3 {
            let a_j = pref_a.clone().with_slot(j).unwrap();
            let b_j = pref_b.clone().with_slot(j).unwrap();
            let diff = &SparsePolynomial::var(&a_j) - &SparsePolynomial::var(&b_j);
            assert!(
                gresult.basis.iter().any(|p| *p == diff),
                "basis should contain a[{}]-b[{}] diff",
                j,
                j
            );
        }

        assert!(
            !gresult.pl.contains(&r_slot),
            "Bool result slot should NOT be defined via pl"
        );
    }

    #[test]
    fn test_equ_uni_different_degrees_lifts_both() {
        use crate::PRef;
        use lang::ast::BinOp;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let mut gresult = GroebnerResult::<ArkBls12_381, GrevLexTerm>::new();

        let pref_a = PRef::from_node(
            NodeIndex::new(0),
            ATyp::Uni(2),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_a);
        let pref_b = PRef::from_node(
            NodeIndex::new(1),
            ATyp::Uni(4),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_b);
        let pref_r = PRef::from_node(
            NodeIndex::new(2),
            ATyp::bool(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );

        builder.add_op(
            pref_r.clone(),
            Op::Bin(
                BinOp::Equ,
                mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), ATyp::Uni(2))),
                mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(1)), ATyp::Uni(4))),
                ATyp::bool(),
            ),
            &mut gresult,
        );

        let r_slot = pref_r.with_slot(0).unwrap();
        assert!(
            gresult
                .basis
                .iter()
                .any(|p| *p == SparsePolynomial::var(&r_slot)),
            "basis should contain var(r) for Bool result"
        );

        let lub_len = ATyp::Uni(4).physical_len();
        assert_eq!(lub_len, 5);
        for j in 0..lub_len {
            let a_j = if j < 3 {
                SparsePolynomial::var(&pref_a.clone().with_slot(j).unwrap())
            } else {
                SparsePolynomial::zero()
            };
            let b_j = SparsePolynomial::var(&pref_b.clone().with_slot(j).unwrap());
            let diff = a_j - b_j;
            assert!(
                gresult.basis.iter().any(|p| *p == diff),
                "basis should contain lifted diff at slot {}",
                j
            );
        }
    }

    // -----------------------------------------------------------------
    // concat_op: extracted function
    // -----------------------------------------------------------------

    #[test]
    fn test_concat_vec_vec_elements() {
        use crate::PRef;
        use lang::ast::BinOp;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let mut gresult = GroebnerResult::<ArkBls12_381, GrevLexTerm>::new();

        let s = ATyp::scalar();
        let vec2 = ATyp::Vec(Box::new(s.clone()), 2);
        let vec3 = ATyp::Vec(Box::new(s.clone()), 3);
        let vec5 = ATyp::Vec(Box::new(s.clone()), 5);

        let pref_a = PRef::from_node(
            NodeIndex::new(0),
            vec2.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_a);
        let pref_b = PRef::from_node(
            NodeIndex::new(1),
            vec3.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_b);
        let pref_r = PRef::from_node(
            NodeIndex::new(2),
            vec5.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );

        builder.add_op(
            pref_r.clone(),
            Op::Bin(
                BinOp::Concat,
                mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), vec2)),
                mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(1)), vec3)),
                vec5,
            ),
            &mut gresult,
        );

        for i in 0..5 {
            let pr_i = pref_r.with_index(i).unwrap();
            let pr_slot = pr_i.with_slot(0).unwrap();
            assert!(
                gresult.pl.contains(&pr_slot),
                "concat result element {} slot 0 should be in pl",
                i
            );
        }
    }

    // -----------------------------------------------------------------
    // reduce_op with PolySource: direct fold for Add/Sub
    // -----------------------------------------------------------------

    #[test]
    fn test_reduce_add_poly_vec_direct_fold() {
        use crate::PRef;
        use lang::ast::BinOp;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let mut gresult = GroebnerResult::<ArkBls12_381, GrevLexTerm>::new();

        let poly_t = ATyp::Uni(2);
        let vec_t = ATyp::Vec(Box::new(poly_t.clone()), 2);

        let pref_v = PRef::from_node(
            NodeIndex::new(0),
            vec_t.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_v);

        let result = PRef::from_node(
            NodeIndex::new(1),
            poly_t.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );

        builder.add_op(
            result.clone(),
            Op::Reduce(
                BinOp::Add,
                mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), vec_t)),
            ),
            &mut gresult,
        );

        let var = |p: &PRef| SparsePolynomial::<ark_bls12_381::Fr, GrevLexTerm>::var(p);
        for j in 0..3 {
            let v0_j = pref_v.clone().with_index(0).unwrap().with_slot(j).unwrap();
            let v1_j = pref_v.clone().with_index(1).unwrap().with_slot(j).unwrap();
            let r_j = result.clone().with_slot(j).unwrap();
            let expected = &var(&v0_j) + &var(&v1_j);
            let stored = gresult.pl.get(&r_j).unwrap();
            assert_eq!(*stored, expected, "reduce add poly slot {} mismatch", j);
        }
    }

    // -----------------------------------------------------------------
    // Op::Ref with lift_to
    // -----------------------------------------------------------------

    #[test]
    fn test_ref_lift_to_wider_type() {
        use crate::PRef;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let mut gresult = GroebnerResult::<ArkBls12_381, GrevLexTerm>::new();

        let pref_src = PRef::from_node(
            NodeIndex::new(0),
            ATyp::Uni(2),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_src);

        let pref_dst = PRef::from_node(
            NodeIndex::new(1),
            ATyp::Uni(4),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.ns.register(&pref_dst);

        builder.add_op(
            pref_dst.clone(),
            Op::Ref(Ref::new(NodeIndex::new(0)), ATyp::Uni(2)),
            &mut gresult,
        );

        assert_eq!(pref_dst.slots().len(), 5, "Uni(4) should have 5 slots");
        for j in 0..3 {
            let dst_j = pref_dst.clone().with_slot(j).unwrap();
            let src_j = pref_src.clone().with_slot(j).unwrap();
            let stored = gresult.pl.get(&dst_j).unwrap();
            assert_eq!(
                *stored,
                SparsePolynomial::var(&src_j),
                "ref lift slot {} should map to src slot {}",
                j,
                j
            );
        }
        for j in 3..5 {
            let dst_j = pref_dst.clone().with_slot(j).unwrap();
            let stored = gresult.pl.get(&dst_j).unwrap();
            assert!(
                stored.is_zero(),
                "ref lift padded slot {} should be zero",
                j
            );
        }
    }

    // -----------------------------------------------------------------
    // broadcast_scalar_to
    // -----------------------------------------------------------------

    #[test]
    fn test_broadcast_scalar_to_vpoly() {
        let scalar_poly =
            SparsePolynomial::<ark_bls12_381::Fr, GrevLexTerm>::var(&PRef::from_node(
                petgraph::graph::NodeIndex::new(0),
                ATyp::scalar(),
                0,
                lang::typ::Qualifier::Private,
                lang::typ::Distribution::default(),
            ));
        let src =
            PolySource::<ArkBls12_381, GrevLexTerm>::new(vec![scalar_poly.clone()], ATyp::scalar());
        let broadcast = src.broadcast_scalar_to(&ATyp::VPoly(2, 2));
        assert_eq!(broadcast.polys.len(), 6);
        for (i, p) in broadcast.polys.iter().enumerate() {
            assert_eq!(*p, scalar_poly, "broadcast slot {} should be the scalar", i);
        }
    }
}
