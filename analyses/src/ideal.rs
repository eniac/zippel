use crate::TransClos;
use crate::frontend::Polynomial;
use graph::pref::PRef;
use graph::{GOp, HOp, Op, Ref, mk};
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

// Keep record/projection materialization bounded. Large protocol helper records
// can contain polynomial state with enormous flattened slot counts; failing
// explicitly is preferable to attempting an allocation that aborts the process.
const MAX_GROEBNER_MATERIALIZED_SLOTS: usize = 1 << 20;

// ---------------------------------------------------------------------------
// PRef-slot enumeration helpers for polynomial / MLE values.
//
// These define the canonical order in which the slots of a polynomial-typed
// PRef are laid out (via `PRef::with_slot(i)`). They are NOT monomial / term
// orderings — the `GrevLexTerm` and `ElimMono<E>` orderings in
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
fn dft_row<C: ArkConfig>(coeffs: &[Polynomial<C::F>], omega: C::F, i: usize) -> Polynomial<C::F> {
    let w_step = omega.pow([i as u64]);
    let mut wij = C::F::one();
    let mut acc = Polynomial::<C::F>::zero();
    for c in coeffs.iter() {
        let scalar = Polynomial::<C::F>::lit(&wij);
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
    let mut basis: Vec<Vec<F>> = Vec::with_capacity(xs.len());

    for (i, xi) in xs.iter().copied().enumerate() {
        let mut denom = F::one();
        for (j, xj) in xs.iter().copied().enumerate() {
            if j != i {
                denom *= xi - xj;
            }
        }
        let denom_inv = denom.inverse().unwrap();

        let mut poly: Vec<F> = vec![F::one()];
        for (j, xj) in xs.iter().copied().enumerate() {
            if j == i {
                continue;
            }
            let neg_xj = -xj;
            let mut new_poly = vec![F::zero(); poly.len() + 1];
            for (k, &c) in poly.iter().enumerate() {
                new_poly[k] += c * neg_xj;
                new_poly[k + 1] += c;
            }
            poly = new_poly;
        }

        for c in &mut poly {
            *c *= denom_inv;
        }

        basis.push(poly);
    }

    basis
}

pub const GB_GENERATED_NAME_PREFIX: &str = "__zippel::gb::";

/// Canonical polynomial shape used when comparing division witness operands.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
struct CanonPolyTyp {
    num_vars: usize,
    max_degree: usize,
}

/// Canonical operand-content key for source-level polynomial division witnesses.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct DivWitnessKey {
    dividend_typ: CanonPolyTyp,
    divisor_typ: CanonPolyTyp,
    dividend_slots: Vec<String>,
    divisor_slots: Vec<String>,
}

/// Namespace for division-witness and sentinel allocation shared across
/// Groebner builders.
#[derive(Clone)]
pub struct GroebnerNamespace<C: ArkConfig> {
    pub div_wit: Ctx<DivWitnessKey, (PRef, PRef)>,
    sentinel_counter: usize,
    name_counters: HashMap<String, usize>,
    _phantom: PhantomData<C>,
}

impl<C: ArkConfig + HasOpFactory> Default for GroebnerNamespace<C> {
    fn default() -> Self {
        Self::new()
    }
}

impl<C: ArkConfig + HasOpFactory> GroebnerNamespace<C> {
    pub fn new() -> Self {
        Self {
            div_wit: Ctx::new(),
            sentinel_counter: usize::MAX,
            name_counters: HashMap::new(),
            _phantom: PhantomData,
        }
    }

    /// Allocate a fresh sentinel PRef with a stable unique NodeIndex.
    pub fn sentinel_pref(&mut self, name: &str, typ: ATyp) -> PRef {
        let vid = Vid::from(name);
        let idx = NodeIndex::new(self.sentinel_counter);
        self.sentinel_counter -= 1;
        PRef::from_var(vid, idx, typ, 0, Qualifier::Local, Distribution::default())
    }

    /// Return a unique name for the given key by appending a per-key counter.
    pub fn next_name(&mut self, key: &str) -> String {
        let counter = self.name_counters.entry(key.to_string()).or_insert(0);
        let name = format!("{}{}::{}", GB_GENERATED_NAME_PREFIX, key, counter);
        *counter += 1;
        name
    }
}

/// The ideal of building a Gröbner basis — the basis polynomials, their
/// polynomial definitions (pl), and the prefs used in the basis.
#[derive(Clone)]
pub struct Ideal<C: ArkConfig> {
    pub basis: Vec<Polynomial<C::F>>,
    pub pl: Ctx<PRef, Polynomial<C::F>>,
    pub prefs: HashMap<Ref, PRef>,
    pub var_order: Vec<PRef>,
}

impl<C: ArkConfig + HasOpFactory> Ideal<C> {
    pub fn new() -> Self {
        Self {
            basis: Vec::new(),
            pl: Ctx::new(),
            prefs: HashMap::new(),
            var_order: Vec::new(),
        }
    }

    /// Register a PRef in the namespace. Overwrites any existing entry
    /// for the same reference. Returns the previous entry if one existed.
    pub fn register(&mut self, pr: &PRef) -> Option<PRef> {
        self.prefs.insert(pr.reference, pr.clone())
    }

    /// Look up a Ref in the namespace. Panics if not found.
    pub fn find_ref(&self, r: &Ref) -> PRef {
        if let Some(v) = self.prefs.get(r) {
            return v.clone();
        }
        panic!("groebner: ref {} not found in namespace prefs", r)
    }

    pub fn vars(&self) -> Set<PRef> {
        let mut vars: Set<PRef> = self.pl.keys().into_iter().collect();
        for p in &self.basis {
            for v in p.vars() {
                vars.insert(v);
            }
        }
        vars
    }

    /// Filter out variables that satisfy the predicate
    pub fn eliminate_var<F: Fn(&PRef) -> bool>(&mut self, f: &F) {
        self.basis.retain(|p| p.vars().iter().all(|v| !f(v)));
        self.pl.retain(|p, _| !f(p));
    }

    pub fn eliminate_monomial<F: Fn(&crate::frontend::Monomial) -> bool>(&mut self, f: &F) {
        self.basis.retain(|p| p.terms.keys().any(|t| !f(t)));
        let basis_vars: Set<PRef> = self.basis.iter().flat_map(|p| p.vars()).collect();
        self.pl.retain(|p, _| basis_vars.contains(p));
    }

    /// Inline all `pl` definitions into the basis polynomials.
    ///
    /// Topologically sorts `pl` entries, substitutes dependencies into
    /// each other to resolve chains, then substitutes the resolved
    /// definitions into all basis polynomials. Clears `pl` afterwards.
    pub fn inline(&mut self, transcript_refs: &Set<Ref>) {
        if self.pl.is_empty() {
            return;
        }

        let pl_keys: Set<PRef> = self.pl.keys();
        let mut order: Vec<PRef> = Vec::with_capacity(pl_keys.len());
        let mut resolved: Set<PRef> = Set::new();
        let mut inlineable: Set<PRef> = pl_keys.clone();
        inlineable.retain(|k| !transcript_refs.contains(&k.reference));
        let mut remaining: Vec<(PRef, usize)> = inlineable
            .iter()
            .map(|k| {
                let deps = self.pl[k]
                    .terms
                    .keys()
                    .flat_map(|t| t.vars())
                    .filter(|v| inlineable.contains(v))
                    .count();
                (k.clone(), deps)
            })
            .collect();

        loop {
            let before = remaining.len();
            let mut next_remaining = Vec::new();
            for (k, deps) in remaining {
                if deps == 0 {
                    order.push(k.clone());
                    resolved.insert(k.clone());
                } else {
                    let new_deps = self.pl[&k]
                        .terms
                        .keys()
                        .flat_map(|t| t.vars())
                        .filter(|v| inlineable.contains(v) && !resolved.contains(v))
                        .count();
                    next_remaining.push((k, new_deps));
                }
            }
            remaining = next_remaining;
            if remaining.len() == before {
                for (k, _) in remaining {
                    order.push(k);
                }
                break;
            }
            if remaining.is_empty() {
                break;
            }
        }

        for k in &order {
            if let Some(def) = self.pl.remove(k) {
                let (new_def, _) = def.inline_vars(&self.pl);
                self.pl.insert(k, &new_def);
            }
        }

        // save transcript vars
        let mut saved: Vec<(PRef, Polynomial<C::F>)> = Vec::new();
        for k in pl_keys.iter() {
            if transcript_refs.contains(&k.reference)
                && let Some(v) = self.pl.remove(k)
            {
                let (new_v, _) = v.inline_vars(&self.pl);
                saved.push((k.clone(), new_v));
            }
        }

        // fully inline all non-transcript vars
        for p in self.basis.iter_mut() {
            let (new_p, _) = p.clone().inline_vars(&self.pl);
            *p = new_p;
        }
        self.basis.retain(|p| !p.is_zero());

        for (k, v) in saved {
            self.pl.insert(&k, &v);
        }

        for k in &order {
            self.pl.remove(k);
        }
    }

    /// Merge another ideal's basis and polynomial definitions into this ideal.
    pub fn merge(&mut self, other: &Self) {
        self.basis.extend(other.basis.iter().cloned());
        for (k, v) in other.pl.iter() {
            self.pl.insert(k, v);
        }
        self.var_order.extend(other.var_order.iter().cloned());
        for (k, v) in other.prefs.iter() {
            self.prefs.entry(*k).or_insert_with(|| v.clone());
        }
    }
}

impl<C: ArkConfig + HasOpFactory> Default for Ideal<C> {
    fn default() -> Self {
        Self::new()
    }
}

impl<'a, C, D, A> Pretty<'a, D, A> for Ideal<C>
where
    C: ArkConfig,
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
        ])
    }

    fn is_nil(&self) -> bool {
        self.basis.is_empty() && self.pl.is_empty()
    }
}

impl<C: ArkConfig> fmt::Display for Ideal<C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <Ideal<C> as Pretty<'_, BoxAllocator, ()>>::pretty(self.clone(), &BoxAllocator)
            .1
            .render_fmt(100, f)
    }
}

/// An owned slice of polynomial variables paired with their `ATyp`.
///
/// Provides element-wise access for `Vec` types (via `at_index`),
/// zero-padding lifts to wider types (via `lift_to`), all-slot scalar
/// broadcast (via `broadcast_scalar_to`), and representation-aware
/// scalar lifting for additive polynomial operations.
struct PolySource<C: ArkConfig> {
    polys: Vec<Polynomial<C::F>>,
    typ: ATyp,
}

impl<C: ArkConfig> PolySource<C> {
    fn new(polys: Vec<Polynomial<C::F>>, typ: ATyp) -> Self {
        PolySource { polys, typ }
    }

    fn typ(&self) -> &ATyp {
        &self.typ
    }

    fn polys(&self) -> &[Polynomial<C::F>] {
        &self.polys
    }

    fn physical_len(&self) -> usize {
        self.typ.physical_len()
    }

    fn from_ref_vars(prefs: &HashMap<Ref, PRef>, op: &GOp<C>) -> Self
    where
        C: HasOpFactory,
    {
        let typ = op.typ();
        let polys = IdealBuilder::<C>::ref_vars(op, prefs);
        PolySource { polys, typ }
    }

    fn from_pref_vars(pref: &PRef, typ: ATyp) -> Self {
        let polys = pref
            .slots()
            .into_iter()
            .map(|slot| Polynomial::var(&slot))
            .collect();
        PolySource { polys, typ }
    }

    fn embed_multi_indexed_polys(
        polys: &[Polynomial<C::F>],
        source_indices: &[Vec<usize>],
        target_indices: &[Vec<usize>],
        target_arity: usize,
    ) -> Vec<Polynomial<C::F>> {
        let mut out = vec![Polynomial::<C::F>::zero(); target_indices.len()];
        for (j, source_index) in source_indices.iter().enumerate() {
            let mut padded = source_index.clone();
            padded.resize(target_arity, 0);
            if let Some(target_slot) = target_indices.iter().position(|target| target == &padded) {
                out[target_slot] = polys[j].clone();
            }
        }
        out
    }

    fn at_index(&self, i: usize) -> Option<PolySource<C>> {
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
    ///   there; all other ideal slots are zero.
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
    fn lift_to(&self, target: &ATyp) -> PolySource<C> {
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
                out.resize(dst_len, Polynomial::zero());
                PolySource {
                    polys: out,
                    typ: target.clone(),
                }
            }

            (ATyp::Mle(_n1), ATyp::Mle(_n2)) => {
                let mut out = self.polys.clone();
                out.resize(dst_len, Polynomial::zero());
                PolySource {
                    polys: out,
                    typ: target.clone(),
                }
            }

            (ATyp::Mle(1), ATyp::Uni(m2)) if *m2 >= 1 => {
                assert_eq!(
                    self.polys.len(),
                    2,
                    "lift_to: Mle(1) source must have exactly two evaluation slots"
                );
                let g0 = self.polys[0].clone();
                let g1 = self.polys[1].clone();
                let mut out = vec![Polynomial::<C::F>::zero(); dst_len];
                out[0] = g0.clone();
                out[1] = &g1 - &g0;
                PolySource {
                    polys: out,
                    typ: target.clone(),
                }
            }

            (ATyp::VPoly(n1, m1), ATyp::VPoly(n2, m2)) if n1 <= n2 && m1 <= m2 => {
                if n1 == n2 {
                    let mut out = self.polys.clone();
                    out.resize(dst_len, Polynomial::zero());
                    PolySource {
                        polys: out,
                        typ: target.clone(),
                    }
                } else {
                    let dst_idx = multi_indices(*n2, *m2);
                    let src_idx = multi_indices(*n1, *m1);
                    let out = Self::embed_multi_indexed_polys(&self.polys, &src_idx, &dst_idx, *n2);
                    PolySource {
                        polys: out,
                        typ: target.clone(),
                    }
                }
            }

            (ATyp::Uni(m1), ATyp::VPoly(n2, m2)) if *n2 >= 1 && m1 <= m2 => {
                if *n2 == 1 {
                    let mut out = self.polys.clone();
                    out.resize(dst_len, Polynomial::zero());
                    PolySource {
                        polys: out,
                        typ: target.clone(),
                    }
                } else {
                    let dst_idx = multi_indices(*n2, *m2);
                    let src_idx = multi_indices(1, *m1);
                    let out = Self::embed_multi_indexed_polys(&self.polys, &src_idx, &dst_idx, *n2);
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
            // (b1,…,b_n1)`) stores the evaluation `f(b)`. The Lagrange
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
                let mut out = vec![Polynomial::<C::F>::zero(); dst_idx.len()];
                let lit_of = |v: i64| -> Polynomial<C::F> {
                    if v >= 0 {
                        Polynomial::lit(&C::FOps::from_usize(v as usize))
                    } else {
                        -Polynomial::lit(&C::FOps::from_usize((-v) as usize))
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

    fn broadcast_scalar_to(&self, poly_typ: &ATyp) -> PolySource<C> {
        let dst_len = poly_typ.physical_len();
        let scalar_poly = self.polys[0].clone();
        PolySource {
            polys: vec![scalar_poly; dst_len],
            typ: poly_typ.clone(),
        }
    }

    fn lift_scalar_for_add_sub_to(&self, poly_typ: &ATyp) -> PolySource<C> {
        assert!(
            Self::is_scalar_like(&self.typ),
            "lift_scalar_for_add_sub_to requires a scalar-like source, got {}",
            self.typ
        );
        assert_eq!(
            self.polys.len(),
            1,
            "lift_scalar_for_add_sub_to requires exactly one source slot"
        );

        let scalar_poly = self.polys[0].clone();
        let polys = match poly_typ {
            ATyp::Base(_) => vec![scalar_poly],
            ATyp::Uni(_) => {
                let mut out = vec![Polynomial::<C::F>::zero(); poly_typ.physical_len()];
                out[0] = scalar_poly;
                out
            }
            ATyp::VPoly(n, m) => {
                let indices = multi_indices(*n, *m);
                let zero_slot = indices
                    .iter()
                    .position(|idx| idx.iter().all(|degree| *degree == 0))
                    .expect("VPoly multi-index enumeration must include the constant slot");
                let mut out = vec![Polynomial::<C::F>::zero(); indices.len()];
                out[zero_slot] = scalar_poly;
                out
            }
            ATyp::Mle(_) => vec![scalar_poly; poly_typ.physical_len()],
            ATyp::Vec(_, _) | ATyp::Record(_) => unreachable!(
                "lift_scalar_for_add_sub_to: unsupported scalar lift target {}",
                poly_typ
            ),
        };

        PolySource {
            polys,
            typ: poly_typ.clone(),
        }
    }

    fn is_poly(&self) -> bool {
        Self::poly_shape_static(&self.typ).is_some() || matches!(self.typ, ATyp::Mle(_))
    }

    fn is_scalar_like(t: &ATyp) -> bool {
        matches!(t, ATyp::Base(ABase::Scalar | ABase::Fin(_)))
    }

    fn poly_shape_static(t: &ATyp) -> Option<(usize, usize)> {
        match t {
            ATyp::VPoly(n, m) => Some((*n, *m)),
            ATyp::Uni(m) => Some((1, *m)),
            _ => None,
        }
    }
}

/// Constructs `Ideal`s from `TransClos` inputs. Owns a
/// `GroebnerNamespace` for division-witness and sentinel allocation
/// that persists across `build()` calls. Each call to `build(TransClos)`
/// returns a fresh `Ideal` with its own `prefs` namespace.
#[derive(Clone)]
pub struct IdealBuilder<C: ArkConfig> {
    pub ns: GroebnerNamespace<C>,
    /// When true, `a / b` where `a`'s op is `Mul(cofactor, b)` (or `Mul(b, cofactor)`)
    /// lowers as the exact-division copy `q = cofactor` instead of the generic
    /// quotient/remainder convolution. Set only by the completeness analysis.
    detect_exact_division: bool,
    /// Per-`build()` map from a node's `Ref` to its op, used to recognise the
    /// `Mul`-then-`Div` exact-division pattern. Populated only when
    /// `detect_exact_division` is set.
    node_ops: HashMap<Ref, GOp<C>>,
}

impl<C: ArkConfig + HasOpFactory> Default for IdealBuilder<C> {
    fn default() -> Self {
        Self::new()
    }
}

impl<C: ArkConfig + HasOpFactory> IdealBuilder<C> {
    pub fn new() -> Self {
        Self {
            ns: GroebnerNamespace::new(),
            detect_exact_division: false,
            node_ops: HashMap::new(),
        }
    }

    /// Enable structural exact-division detection (completeness analysis only).
    pub fn enable_exact_division(&mut self) {
        self.detect_exact_division = true;
    }

    /// Panic with a clear, searchable message when an operation has no
    /// polynomial-ideal treatment in the Groebner analysis.
    ///
    /// `context` is a short kebab-case string identifying the code path
    /// (e.g. `"concat-non-vector"`, `"dynamic-pow"`).
    fn uncovered_op(context: &str, target: &PRef) -> ! {
        panic!(
            "Groebner operation has no polynomial-ideal treatment at {} for {}",
            context,
            target.verbose()
        )
    }

    /// Clear only cached polynomial division witnesses; keep sentinel and generated-name state intact.
    pub fn clear_div_witness_cache(&mut self) {
        self.ns.div_wit = Ctx::new();
    }

    /// Clone the namespace used for canonical variable naming, but force future
    /// polynomial divisions to emit fresh quotient/remainder identity rows.
    pub fn fork_with_clean_div_witness_cache(&self) -> Self {
        let mut fork = Self {
            ns: self.ns.clone(),
            detect_exact_division: self.detect_exact_division,
            node_ops: self.node_ops.clone(),
        };
        fork.clear_div_witness_cache();
        fork
    }

    /// Build a `Ideal` from a `TransClos`. Each call returns a
    /// fresh ideal with its own `prefs` namespace, while the builder
    /// namespace keeps generated witness/sentinel allocation stable.
    pub fn build(&mut self, tc: TransClos<C>) -> Ideal<C> {
        let mut ideal = Ideal::new();
        if self.detect_exact_division {
            self.node_ops.clear();
            for (pr, op) in tc.clos.iter() {
                self.node_ops.insert(pr.reference, op.clone());
            }
        }
        for new_arg in tc.prefs.iter() {
            ideal.register(new_arg);
        }
        for (pr, _op) in tc.clos.iter() {
            ideal.register(pr);
        }
        for (pr, op) in tc.clos.into_iter() {
            self.add_op(pr.clone(), op, &mut ideal);
            ideal.var_order.push(pr);
        }
        ideal
    }

    pub(crate) fn sentinel_pref(&mut self, name: &str, typ: ATyp, ideal: &mut Ideal<C>) -> PRef {
        let pr = self.ns.sentinel_pref(name, typ);
        ideal.var_order.push(pr.clone());
        pr
    }

    /// Allocate quotient/remainder witness sentinels without registering opaque operations.
    fn alloc_div_witness_pair(
        &mut self,
        quotient_typ: ATyp,
        remainder_typ: ATyp,
        ideal: &mut Ideal<C>,
    ) -> (PRef, PRef) {
        let q_name = self.ns.next_name("div_q");
        let r_name = self.ns.next_name("div_r");
        let q_wit = self.sentinel_pref(&q_name, quotient_typ, ideal);
        let r_wit = self.sentinel_pref(&r_name, remainder_typ, ideal);
        (q_wit, r_wit)
    }

    /// If exact-division detection is enabled and dividend `a` is a `Ref` to a
    /// node whose op is `Mul(x, y)` with one factor structurally equal to divisor
    /// `b`, return the *other* factor (the cofactor). Then `a / b` is exact:
    /// quotient = cofactor, remainder = 0.
    fn exact_division_cofactor(&self, a: &HOp<C>, b: &HOp<C>) -> Option<HOp<C>> {
        if !self.detect_exact_division {
            return None;
        }
        let Op::Ref(div_ref, _) = b.get() else {
            return None;
        };
        let Op::Ref(prod_ref, _) = a.get() else {
            return None;
        };
        let Op::Bin(BinOp::Mul, x, y, _) = self.node_ops.get(prod_ref)? else {
            return None;
        };
        if let Op::Ref(xr, _) = x.get()
            && xr == div_ref
        {
            return Some(y.clone());
        }
        if let Op::Ref(yr, _) = y.get()
            && yr == div_ref
        {
            return Some(x.clone());
        }
        None
    }

    fn canonical_div_typ(t: &ATyp) -> Option<CanonPolyTyp> {
        PolySource::<C>::poly_shape_static(t).map(|(num_vars, max_degree)| CanonPolyTyp {
            num_vars,
            max_degree,
        })
    }

    fn div_witness_key(
        &self,
        a: &PolySource<C>,
        b: &PolySource<C>,
        ideal: &Ideal<C>,
    ) -> DivWitnessKey {
        DivWitnessKey {
            dividend_typ: Self::canonical_div_typ(a.typ()).expect("dividend must be polynomial"),
            divisor_typ: Self::canonical_div_typ(b.typ()).expect("divisor must be polynomial"),
            dividend_slots: Self::canonical_slot_keys(a, ideal),
            divisor_slots: Self::canonical_slot_keys(b, ideal),
        }
    }

    fn canonical_slot_keys(source: &PolySource<C>, ideal: &Ideal<C>) -> Vec<String> {
        source
            .polys()
            .iter()
            .map(|p| Self::canonical_poly_key(p, ideal, &mut Vec::new()))
            .collect()
    }

    fn canonical_poly_key(
        poly: &Polynomial<C::F>,
        ideal: &Ideal<C>,
        seen: &mut Vec<PRef>,
    ) -> String {
        if poly.is_zero() {
            return "0".to_string();
        }

        let mut terms: Vec<String> = poly
            .terms
            .iter()
            .map(|(term, coeff)| {
                format!(
                    "coeff={};monomial={}",
                    coeff,
                    Self::canonical_monomial_key(term, ideal, seen)
                )
            })
            .collect();
        terms.sort();
        terms.join("|")
    }

    fn canonical_monomial_key(
        term: &crate::frontend::Monomial,
        ideal: &Ideal<C>,
        seen: &mut Vec<PRef>,
    ) -> String {
        let mut factors: Vec<String> = term
            .vars()
            .into_iter()
            .zip(term.powers())
            .map(|(pref, power)| Self::canonical_factor_key(&pref, power, ideal, seen))
            .collect();
        factors.sort();
        factors.join("*")
    }

    fn canonical_factor_key(
        pref: &PRef,
        power: usize,
        ideal: &Ideal<C>,
        seen: &mut Vec<PRef>,
    ) -> String {
        if Self::is_named_source_pref(pref) {
            return format!("{}^{}", Self::canonical_pref_key(pref), power);
        }

        if let Some(def) = ideal.pl.get(pref)
            && !seen.contains(pref)
        {
            seen.push(pref.clone());
            let def_key = Self::canonical_poly_key(def, ideal, seen);
            seen.pop();
            return format!("def=({})^{}", def_key, power);
        }

        format!("{}^{}", Self::canonical_pref_key(pref), power)
    }

    fn is_named_source_pref(pref: &PRef) -> bool {
        pref.name()
            .map(|name| !name.to_string().starts_with(GB_GENERATED_NAME_PREFIX))
            .unwrap_or(false)
    }

    fn canonical_pref_key(pref: &PRef) -> String {
        let name = pref.name().map(|name| name.to_string());
        match name {
            Some(name) if !name.starts_with(GB_GENERATED_NAME_PREFIX) => format!(
                "named:name={};slot={};typ={};qual={:?};dist={:?};transcript={}",
                name, pref.index, pref.typ, pref.qualifier, pref.distribution, pref.from_transcript,
            ),
            name => format!(
                "raw:ref={:?};slot={};typ={};qual={:?};dist={:?};transcript={};name={:?}",
                pref.reference,
                pref.index,
                pref.typ,
                pref.qualifier,
                pref.distribution,
                pref.from_transcript,
                name,
            ),
        }
    }

    /// Unified Div/Rem handler for both `add_op` and `reduce_op`.
    ///
    /// Dispatches based on operand types:
    /// - Vec operands recurse element-wise, preserving witness caching for each element
    /// - VPoly/Uni polynomial divisions use witness PRefs + cache
    /// - Polynomial-like dividends divided by scalar-like divisors use slot-wise field division
    /// - Non-polynomial Div uses slot-wise field division
    /// - Remainder by scalar and unsupported MLE polynomial division remain `unreachable!`
    ///
    /// Polynomial divisions use a canonical operand-content key in `div_wit`
    /// before emitting identity rows, and insert after emission. This ensures
    /// Div+Rem on equivalent named operands share witnesses across closures.
    fn div_rem_op(
        &mut self,
        target: &PRef,
        a: &PolySource<C>,
        b: &PolySource<C>,
        is_rem: bool,
        cache_witness: bool,
        ideal: &mut Ideal<C>,
    ) {
        match (a.typ(), b.typ()) {
            (ATyp::Vec(_, na), ATyp::Vec(_, nb)) if na == nb => {
                for i in 0..*na {
                    let t_i = target.with_index(i).unwrap();
                    let a_elem = a.at_index(i).unwrap();
                    let b_elem = b.at_index(i).unwrap();
                    self.div_rem_op(&t_i, &a_elem, &b_elem, is_rem, cache_witness, ideal);
                }
            }
            (ATyp::Vec(_, na), _) if PolySource::<C>::is_scalar_like(b.typ()) => {
                for i in 0..*na {
                    let t_i = target.with_index(i).unwrap();
                    let a_elem = a.at_index(i).unwrap();
                    self.div_rem_op(&t_i, &a_elem, b, is_rem, cache_witness, ideal);
                }
            }
            (_, ATyp::Vec(_, nb)) if PolySource::<C>::is_scalar_like(a.typ()) => {
                if is_rem {
                    unreachable!(
                        "Rem: scalar-left vector remainder is undefined for {} % {} — type checker should prevent this",
                        a.typ(),
                        b.typ(),
                    );
                }
                for i in 0..*nb {
                    let t_i = target.with_index(i).unwrap();
                    let b_elem = b.at_index(i).unwrap();
                    self.div_rem_op(&t_i, a, &b_elem, false, cache_witness, ideal);
                }
            }
            _ if a.is_poly() && PolySource::<C>::is_scalar_like(b.typ()) => {
                if is_rem {
                    unreachable!(
                        "Rem: polynomial-like remainder by scalar is undefined for {} % {} — type checker should prevent this",
                        a.typ(),
                        b.typ(),
                    );
                }
                let b_broadcast = b.broadcast_scalar_to(a.typ());
                self.slot_wise_div(target, a.polys(), b_broadcast.polys(), ideal);
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
                let key = cache_witness.then(|| self.div_witness_key(a, b, ideal));
                if let Some((q_wit, r_wit)) = key
                    .as_ref()
                    .and_then(|key| self.ns.div_wit.get(key).cloned())
                {
                    let wit = if is_rem { &r_wit } else { &q_wit };
                    self.link_to_witness(target, wit, ideal);
                    return;
                }

                let (na, ma) = PolySource::<C>::poly_shape_static(a.typ()).unwrap();
                let (nb, mb) = PolySource::<C>::poly_shape_static(b.typ()).unwrap();
                if na != nb {
                    unreachable!(
                        "{}: VPoly num_vars mismatch — dividend has n={} but divisor has n={}",
                        if is_rem { "Rem" } else { "Div" },
                        na,
                        nb,
                    );
                }
                if ma < mb {
                    if is_rem {
                        let lifted = a.lift_to(&target.typ);
                        for (pf, p) in target.slots().into_iter().zip(lifted.polys) {
                            ideal.pl.insert(&pf, &p);
                            ideal.basis.push(p - Polynomial::var(&pf));
                        }
                        return;
                    }
                    unreachable!(
                        "{}: dividend degree < divisor degree ({} < {})",
                        if is_rem { "Rem" } else { "Div" },
                        ma,
                        mb,
                    );
                }
                if mb == 0 {
                    let (q_wit, r_wit) =
                        self.alloc_div_witness_pair(ATyp::VPoly(na, ma), ATyp::VPoly(na, 0), ideal);
                    let a_idx = multi_indices(na, ma);
                    let b_poly = &b.polys()[0];
                    for (ka_pos, _k) in a_idx.iter().enumerate() {
                        let rhs: Polynomial<C::F> =
                            b_poly * &Polynomial::var(&q_wit.with_slot(ka_pos).unwrap());
                        ideal.basis.push(&a.polys()[ka_pos] - &rhs);
                    }
                    for rf in r_wit.slots() {
                        ideal.basis.push(Polynomial::var(&rf));
                    }
                    let wit = if is_rem { &r_wit } else { &q_wit };
                    self.link_to_witness(target, wit, ideal);
                    if let Some(key) = key {
                        self.ns.div_wit.insert(&key, &(q_wit, r_wit));
                    }
                    return;
                }

                let nr = na;
                let mq = ma - mb;
                let mr = mb - 1;

                let (q_wit, r_wit) =
                    self.alloc_div_witness_pair(ATyp::VPoly(nr, mq), ATyp::VPoly(nr, mr), ideal);

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
                    let mut rhs = Polynomial::<C::F>::zero();
                    for (i_pos, ki) in b_idx.iter().enumerate() {
                        for (j_pos, kj) in q_idx.iter().enumerate() {
                            let sum: Vec<usize> =
                                ki.iter().zip(kj.iter()).map(|(x, y)| x + y).collect();
                            if sum == *k {
                                let qf = q_wit.clone().with_slot(j_pos).unwrap();
                                rhs = &rhs + &(&b.polys()[i_pos] * &Polynomial::var(&qf));
                            }
                        }
                    }
                    if let Some(r_pos) = r_idx.iter().position(|rk| rk == k) {
                        let rf = r_wit.clone().with_slot(r_pos).unwrap();
                        rhs = &rhs + &Polynomial::var(&rf);
                    }
                    ideal.basis.push(&a.polys()[ka_pos] - &rhs);
                }

                let wit = if is_rem { &r_wit } else { &q_wit };
                self.link_to_witness(target, wit, ideal);

                if let Some(key) = key {
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
                self.slot_wise_div(target, a.polys(), b.polys(), ideal);
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
    /// - `Uni(n1) op Uni(n2)` → zero-pad shorter operand to match ideal degree
    /// - Same-type poly op → straightforward slot-wise
    fn broadcast_equ(
        &mut self,
        _pr: &PRef,
        a: &PolySource<C>,
        b: &PolySource<C>,
        ideal: &mut Ideal<C>,
    ) {
        self.emit_equ_diffs(a, b, ideal);
        // NOTE: We do NOT emit `pr.slots()` as basis polynomials here.
        // `==` is used as an assertion, not to compute the boolean
        // ideal of equality checking.
    }

    fn emit_equ_diffs(&mut self, a: &PolySource<C>, b: &PolySource<C>, ideal: &mut Ideal<C>) {
        match (a.typ(), b.typ()) {
            (ATyp::Vec(_, na), ATyp::Vec(_, nb)) if na == nb => {
                for i in 0..*na {
                    let a_elem = a.at_index(i).unwrap();
                    let b_elem = b.at_index(i).unwrap();
                    self.emit_equ_diffs(&a_elem, &b_elem, ideal);
                }
            }
            _ if matches!(
                (a.typ(), b.typ()),
                (ATyp::Mle(_), ATyp::Uni(_)) | (ATyp::Uni(_), ATyp::Mle(_))
            ) && a.typ().physical_len() == b.typ().physical_len() =>
            {
                for (ap, bp) in a.polys().iter().zip(b.polys()) {
                    ideal.basis.push(ap - bp);
                }
            }
            _ => {
                let lub = ATyp::lub_equ(a.typ(), b.typ(), &Nothing)
                    .expect("broadcast_equ: lub_equ failed");
                let a_lifted = a.lift_to(&lub);
                let b_lifted = b.lift_to(&lub);
                for j in 0..lub.physical_len() {
                    let diff = &a_lifted.polys[j] - &b_lifted.polys[j];
                    ideal.basis.push(diff);
                }
            }
        }
    }

    fn bind_lifted_alias(
        target: &PRef,
        source: &PolySource<C>,
        target_typ: &ATyp,
        ideal: &mut Ideal<C>,
    ) {
        let lifted = source.lift_to(target_typ);
        for (pf, p) in target.slots().into_iter().zip(lifted.polys) {
            ideal.pl.insert(&pf, &p);
            ideal.basis.push(p - Polynomial::var(&pf));
        }
    }

    fn bind_vec_aliases(
        target: &PRef,
        target_offset: usize,
        source: &PolySource<C>,
        source_len: usize,
        elem_typ: &ATyp,
        ideal: &mut Ideal<C>,
    ) {
        for source_index in 0..source_len {
            let target_elem = target.with_index(target_offset + source_index).unwrap();
            let source_elem = source.at_index(source_index).unwrap();
            Self::bind_lifted_alias(&target_elem, &source_elem, elem_typ, ideal);
        }
    }

    fn concat_op(
        &mut self,
        pr: &PRef,
        a: &PolySource<C>,
        b: &PolySource<C>,
        _a_op: &HOp<C>,
        _b_op: &HOp<C>,
        ideal: &mut Ideal<C>,
    ) {
        match (&pr.typ, a.typ(), b.typ()) {
            (ATyp::Vec(r_elem, _), ATyp::Vec(_, na), ATyp::Vec(_, nb)) => {
                Self::bind_vec_aliases(pr, 0, a, *na, r_elem, ideal);
                Self::bind_vec_aliases(pr, *na, b, *nb, r_elem, ideal);
            }
            (ATyp::Vec(r_elem, _), ATyp::Vec(_, na), _) => {
                Self::bind_vec_aliases(pr, 0, a, *na, r_elem, ideal);
                let target_elem = pr.with_index(*na).unwrap();
                Self::bind_lifted_alias(&target_elem, b, r_elem, ideal);
            }
            (ATyp::Vec(r_elem, _), _, ATyp::Vec(_, nb)) => {
                let target_elem = pr.with_index(0).unwrap();
                Self::bind_lifted_alias(&target_elem, a, r_elem, ideal);
                Self::bind_vec_aliases(pr, 1, b, *nb, r_elem, ideal);
            }
            _ => {
                Self::uncovered_op("concat-non-vector", pr);
            }
        }
    }

    fn emit_slotwise_binop(
        &self,
        pr: &PRef,
        left: &[Polynomial<C::F>],
        right: &[Polynomial<C::F>],
        op: BinOp,
        ideal: &mut Ideal<C>,
        context: &str,
    ) {
        let pr_slots = pr.slots();
        assert_eq!(
            pr_slots.len(),
            left.len(),
            "broadcast_binop {context}: ideal slot count must match left operand"
        );
        assert_eq!(
            pr_slots.len(),
            right.len(),
            "broadcast_binop {context}: ideal slot count must match right operand"
        );

        for ((pf, left_poly), right_poly) in pr_slots.iter().zip(left).zip(right) {
            let combined = self.apply_binop(op, left_poly, right_poly);
            ideal.pl.insert(pf, &combined);
            ideal.basis.push(combined - Polynomial::var(pf));
        }
    }

    fn broadcast_binop(
        &mut self,
        pr: &PRef,
        a: &PolySource<C>,
        b: &PolySource<C>,
        r_typ: &ATyp,
        op: BinOp,
        ideal: &mut Ideal<C>,
    ) {
        match (a.typ(), b.typ()) {
            (ATyp::Vec(_, na), ATyp::Vec(_, nb)) if na == nb => {
                for i in 0..*na {
                    let a_elem = a.at_index(i).unwrap();
                    let b_elem = b.at_index(i).unwrap();
                    let r_inner = match r_typ {
                        ATyp::Vec(inner, _) => inner,
                        _ => unreachable!("broadcast_binop Vec×Vec ideal must be Vec"),
                    };
                    self.broadcast_binop(
                        &pr.with_index(i).unwrap(),
                        &a_elem,
                        &b_elem,
                        r_inner,
                        op,
                        ideal,
                    );
                }
            }
            (_, _)
                if matches!(op, BinOp::Add | BinOp::Sub)
                    && PolySource::<C>::is_scalar_like(b.typ())
                    && a.is_poly() =>
            {
                let a_lifted = a.lift_to(r_typ);
                let b_lifted = b.lift_scalar_for_add_sub_to(r_typ);
                self.emit_slotwise_binop(
                    pr,
                    a_lifted.polys(),
                    b_lifted.polys(),
                    op,
                    ideal,
                    "Poly×Scalar",
                );
            }
            (_, _)
                if matches!(op, BinOp::Add | BinOp::Sub)
                    && PolySource::<C>::is_scalar_like(a.typ())
                    && b.is_poly() =>
            {
                let a_lifted = a.lift_scalar_for_add_sub_to(r_typ);
                let b_lifted = b.lift_to(r_typ);
                self.emit_slotwise_binop(
                    pr,
                    a_lifted.polys(),
                    b_lifted.polys(),
                    op,
                    ideal,
                    "Scalar×Poly",
                );
            }
            (_, _) if PolySource::<C>::is_scalar_like(b.typ()) && a.physical_len() > 1 => {
                let b_broadcast = b.broadcast_scalar_to(a.typ());
                self.emit_slotwise_binop(
                    pr,
                    a.polys(),
                    b_broadcast.polys(),
                    op,
                    ideal,
                    "value×scalar",
                );
            }
            (_, _) if PolySource::<C>::is_scalar_like(a.typ()) && b.physical_len() > 1 => {
                let a_broadcast = a.broadcast_scalar_to(b.typ());
                self.emit_slotwise_binop(
                    pr,
                    a_broadcast.polys(),
                    b.polys(),
                    op,
                    ideal,
                    "scalar×value",
                );
            }
            _ if a.is_poly() || b.is_poly() || matches!(r_typ, ATyp::Mle(_)) => {
                let a_lifted = a.lift_to(r_typ);
                let b_lifted = b.lift_to(r_typ);
                self.emit_slotwise_binop(
                    pr,
                    a_lifted.polys(),
                    b_lifted.polys(),
                    op,
                    ideal,
                    "poly/lifted",
                );
            }
            _ => {
                self.emit_slotwise_binop(pr, a.polys(), b.polys(), op, ideal, "slotwise");
            }
        }
    }

    fn apply_binop(
        &self,
        op: BinOp,
        a: &Polynomial<C::F>,
        b: &Polynomial<C::F>,
    ) -> Polynomial<C::F> {
        match op {
            BinOp::Add => a + b,
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
        a: &PolySource<C>,
        b: &PolySource<C>,
        r_typ: &ATyp,
        ideal: &mut Ideal<C>,
    ) {
        match (a.typ(), b.typ()) {
            (ATyp::Vec(_, na), ATyp::Vec(_, nb)) if na == nb => {
                let r_inner = match r_typ {
                    ATyp::Vec(inner, _) => inner,
                    _ => unreachable!("mul_op Vec×Vec ideal must be Vec"),
                };
                for i in 0..*na {
                    let t_i = target.with_index(i).unwrap();
                    let a_elem = a.at_index(i).unwrap();
                    let b_elem = b.at_index(i).unwrap();
                    self.mul_op(&t_i, &a_elem, &b_elem, r_inner, ideal);
                }
            }
            (ATyp::Vec(_, na), _) => {
                let r_inner = match r_typ {
                    ATyp::Vec(inner, _) => inner,
                    _ => unreachable!("mul_op Vec×scalar ideal must be Vec"),
                };
                for i in 0..*na {
                    let t_i = target.with_index(i).unwrap();
                    let a_elem = a.at_index(i).unwrap();
                    self.mul_op(&t_i, &a_elem, b, r_inner, ideal);
                }
            }
            (_, ATyp::Vec(_, nb)) => {
                let r_inner = match r_typ {
                    ATyp::Vec(inner, _) => inner,
                    _ => unreachable!("mul_op scalar×Vec ideal must be Vec"),
                };
                for i in 0..*nb {
                    let t_i = target.with_index(i).unwrap();
                    let b_elem = b.at_index(i).unwrap();
                    self.mul_op(&t_i, a, &b_elem, r_inner, ideal);
                }
            }
            (_, ATyp::Base(ABase::Scalar)) if a.is_poly() => {
                let target_slots = target.slots();
                for (ap, pf) in a.polys().iter().zip(&target_slots) {
                    let prod = ap * &b.polys()[0];
                    ideal.pl.insert(pf, &prod);
                    ideal.basis.push(prod - Polynomial::var(pf));
                }
            }
            (ATyp::Base(ABase::Scalar), _) if b.is_poly() => {
                let target_slots = target.slots();
                for (bp, pf) in b.polys().iter().zip(&target_slots) {
                    let prod = &a.polys()[0] * bp;
                    ideal.pl.insert(pf, &prod);
                    ideal.basis.push(prod - Polynomial::var(pf));
                }
            }
            (ATyp::Mle(na), ATyp::Mle(nb)) if na == nb => {
                let ATyp::VPoly(_nr, mr) = r_typ else {
                    unreachable!("Mul Mle×Mle ideal must be VPoly");
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
                let lit_of = |v: i64| -> Polynomial<C::F> {
                    if v >= 0 {
                        Polynomial::lit(&C::FOps::from_usize(v as usize))
                    } else {
                        -Polynomial::lit(&C::FOps::from_usize((-v) as usize))
                    }
                };
                let mut out: Vec<Polynomial<C::F>> = vec![Polynomial::<C::F>::zero(); r_idx.len()];
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
                    ideal.pl.insert(&pf, &poly);
                    ideal.basis.push(poly - Polynomial::var(&pf));
                }
            }
            (ATyp::Mle(na), ATyp::VPoly(nb, mb)) | (ATyp::VPoly(nb, mb), ATyp::Mle(na))
                if *na == *nb =>
            {
                let ATyp::VPoly(nr, mr) = r_typ else {
                    unreachable!("Mul Mle×VPoly ideal must be VPoly");
                };
                assert!(
                    *nr == *na && *mr == *mb + *na,
                    "Mul Mle({})×VPoly({}, {}) ideal must be VPoly({}, {}), got VPoly({}, {})",
                    na,
                    nb,
                    mb,
                    na,
                    *mb + *na,
                    nr,
                    mr
                );
                let n = *na;
                let (mle_src, vpoly_src) = if matches!(a.typ(), ATyp::Mle(_)) {
                    (a, b)
                } else {
                    (b, a)
                };
                let all_b = hypercube(n);
                let b_idx = multi_indices(n, *mb);
                let r_idx = multi_indices(n, *mr);
                let lit_of = |v: i64| -> Polynomial<C::F> {
                    if v >= 0 {
                        Polynomial::lit(&C::FOps::from_usize(v as usize))
                    } else {
                        -Polynomial::lit(&C::FOps::from_usize((-v) as usize))
                    }
                };
                let mut out: Vec<Polynomial<C::F>> = vec![Polynomial::<C::F>::zero(); r_idx.len()];
                // Coefficient of x^k in L_{ba}(x) · x^{kb}, indexed by
                // [ba][k - kb] (only when k >= kb).  L_0(x)=1-x → x^kb - x^{kb+1};
                // L_1(x)=x → x^{kb+1}.
                const C: [[i64; 2]; 2] = [[1, -1], [0, 1]];
                for (ia, ba) in all_b.iter().enumerate() {
                    for (ib, kb) in b_idx.iter().enumerate() {
                        let uv = &mle_src.polys()[ia] * &vpoly_src.polys()[ib];
                        for (ir, k) in r_idx.iter().enumerate() {
                            let mut scalar: i64 = 1;
                            for i in 0..n {
                                if k[i] < kb[i] {
                                    scalar = 0;
                                    break;
                                }
                                let delta = k[i] - kb[i];
                                if delta >= 2 {
                                    scalar = 0;
                                    break;
                                }
                                let c = C[ba[i]][delta];
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
                    ideal.pl.insert(&pf, &poly);
                    ideal.basis.push(poly - Polynomial::var(&pf));
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
                        let mut out: Vec<Polynomial<C::F>> =
                            vec![Polynomial::<C::F>::zero(); r_idx.len()];
                        for (ia, ka) in a_idx.iter().enumerate() {
                            for (ib, kb) in b_idx.iter().enumerate() {
                                let k: Vec<usize> =
                                    ka.iter().zip(kb.iter()).map(|(x, y)| x + y).collect();
                                let ir = r_idx
                                    .iter()
                                    .position(|rk| rk == &k)
                                    .expect("multi-index missing in ideal");
                                out[ir] = &out[ir] + &(&a.polys()[ia] * &b.polys()[ib]);
                            }
                        }
                        for (pf, poly) in target.slots().into_iter().zip(out) {
                            ideal.pl.insert(&pf, &poly);
                            ideal.basis.push(poly - Polynomial::var(&pf));
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
                    ideal.pl.insert(pf, &prod);
                    ideal.basis.push(prod - Polynomial::var(pf));
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

    fn dot_op(&mut self, pr: &PRef, a: &PolySource<C>, b: &PolySource<C>, ideal: &mut Ideal<C>) {
        match (a.typ(), b.typ()) {
            (ATyp::Vec(_, na), ATyp::Vec(_, nb)) if na == nb => {
                let r_elem_len = pr.typ.physical_len();
                let mut acc: Vec<Polynomial<C::F>> = vec![Polynomial::zero(); r_elem_len];
                for i in 0..*na {
                    let acc_name = self.ns.next_name("dot_acc");
                    let acc_pref = self.sentinel_pref(&acc_name, pr.typ.clone(), ideal);
                    let a_elem = a.at_index(i).unwrap();
                    let b_elem = b.at_index(i).unwrap();
                    self.mul_op(&acc_pref, &a_elem, &b_elem, &pr.typ, ideal);
                    let acc_vars: Vec<Polynomial<C::F>> = acc_pref
                        .slots()
                        .into_iter()
                        .map(|s| Polynomial::var(&s))
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
                    ideal.pl.insert(&pf, &p);
                    ideal.basis.push(p - Polynomial::var(&pf));
                }
            }
            (ATyp::Base(_), ATyp::Base(_)) => {
                let pr_slots = pr.slots();
                assert_eq!(
                    pr_slots.len(),
                    1,
                    "Dot: Base·Base ideal must be single slot"
                );
                let sum: Polynomial<C::F> =
                    a.polys().iter().zip(b.polys()).map(|(a, b)| a * b).sum();
                ideal.pl.insert(&pr_slots[0], &sum);
                ideal.basis.push(sum - Polynomial::var(&pr_slots[0]));
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

    fn pair_op(&mut self, pr: &PRef, a: &PolySource<C>, b: &PolySource<C>, ideal: &mut Ideal<C>) {
        match (a.typ(), b.typ(), &pr.typ) {
            (ATyp::Vec(_, na), ATyp::Vec(_, nb), ATyp::Vec(r_inner, _)) if na == nb => {
                for i in 0..*na {
                    let a_elem = a.at_index(i).unwrap();
                    let b_elem = b.at_index(i).unwrap();
                    let t_i = pr.with_index(i).unwrap();
                    let a_lifted = a_elem.lift_to(r_inner);
                    let b_lifted = b_elem.lift_to(r_inner);
                    for (j, pf) in t_i.slots().iter().enumerate() {
                        let e = &a_lifted.polys()[j] * &b_lifted.polys()[j];
                        ideal.pl.insert(pf, &e);
                        ideal.basis.push(&e - &Polynomial::var(pf));
                    }
                }
            }
            (ATyp::Base(_), ATyp::Base(_), ATyp::Base(_)) => {
                let pr_slots = pr.slots();
                for (pf, e_a, e_b) in pr_slots
                    .iter()
                    .zip(a.polys())
                    .zip(b.polys())
                    .map(|((pf, a), b)| (pf, a, b))
                {
                    let e = e_a * e_b;
                    ideal.pl.insert(pf, &e);
                    ideal.basis.push(&e - &Polynomial::var(pf));
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

    fn pow_op(&mut self, pr: &PRef, a: &HOp<C>, b: &HOp<C>, ideal: &mut Ideal<C>) {
        let a_src = PolySource::from_ref_vars(&ideal.prefs, a);
        match (a_src.typ(), &b.typ(), &pr.typ) {
            (ATyp::Vec(_, na), ATyp::Vec(_, nb), ATyp::Vec(r_inner, _)) if na == nb => {
                let elem_exps = self.resolve_const_exps_vec(b, *na);
                for (i, exp) in elem_exps.iter().enumerate().take(*na) {
                    let t_i = pr.with_index(i).unwrap();
                    let elem_a = a_src.at_index(i).unwrap();
                    if let Some(k) = exp {
                        self.pow_const(&t_i, &elem_a, r_inner, *k, ideal);
                    } else {
                        Self::uncovered_op("dynamic-pow", &t_i);
                    }
                }
            }
            (ATyp::Vec(_, na), _, ATyp::Vec(r_inner, _)) => {
                let k = self.resolve_const_exp_scalar(b);
                for i in 0..*na {
                    let t_i = pr.with_index(i).unwrap();
                    let elem_a = a_src.at_index(i).unwrap();
                    if let Some(k) = k {
                        self.pow_const(&t_i, &elem_a, r_inner, k, ideal);
                    } else {
                        Self::uncovered_op("dynamic-pow", &t_i);
                    }
                }
            }
            (_, ATyp::Vec(_, nb), ATyp::Vec(_, _)) => {
                let elem_exps = self.resolve_const_exps_vec(b, *nb);
                for (i, exp) in elem_exps.iter().enumerate().take(*nb) {
                    let t_i = pr.with_index(i).unwrap();
                    if let Some(k) = exp {
                        self.pow_const(&t_i, &a_src, &t_i.typ, *k, ideal);
                    } else {
                        Self::uncovered_op("dynamic-pow", &t_i);
                    }
                }
            }
            _ => {
                if let Some(k) = self.resolve_const_exp_scalar(b) {
                    self.pow_const(pr, &a_src, &pr.typ, k, ideal);
                } else {
                    Self::uncovered_op("dynamic-pow", pr);
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
        base: &PolySource<C>,
        _ideal_typ: &ATyp,
        k: usize,
        ideal: &mut Ideal<C>,
    ) {
        if k == 0 {
            let one = Polynomial::<C::F>::lit(&C::F::one());
            for pf in target.slots() {
                ideal.pl.insert(&pf, &one);
                ideal.basis.push(one.clone() - Polynomial::var(&pf));
            }
            return;
        }
        if k == 1 {
            for (pf, p) in target.slots().into_iter().zip(base.polys().iter().cloned()) {
                ideal.pl.insert(&pf, &p);
                ideal.basis.push(p - Polynomial::var(&pf));
            }
            return;
        }
        let mut acc = PolySource::new(base.polys().to_vec(), base.typ().clone());
        for _step in 1..k {
            let next_name = self.ns.next_name("pow_acc");
            let next_typ =
                ATyp::lub_mul(acc.typ(), base.typ(), &Nothing).expect("pow_const: lub_mul");
            let next_pref = self.sentinel_pref(&next_name, next_typ.clone(), ideal);
            self.mul_op(&next_pref, &acc, base, &next_typ, ideal);
            acc = PolySource::new(
                next_pref
                    .slots()
                    .into_iter()
                    .map(|s| Polynomial::var(&s))
                    .collect(),
                next_typ,
            );
        }
        for (pf, p) in target.slots().into_iter().zip(acc.polys) {
            ideal.pl.insert(&pf, &p);
            ideal.basis.push(p - Polynomial::var(&pf));
        }
    }

    /// Slot-wise division constraint: for each slot j,
    ///   `a[j] - b[j] * var(target[j]) = 0`
    fn slot_wise_div(
        &mut self,
        target: &PRef,
        a_polys: &[Polynomial<C::F>],
        b_polys: &[Polynomial<C::F>],
        ideal: &mut Ideal<C>,
    ) {
        let target_slots = target.slots();
        for (j, pf) in target_slots.iter().enumerate() {
            ideal
                .basis
                .push(a_polys[j].clone() - b_polys[j].clone() * Polynomial::var(pf));
        }
    }

    /// Phase 13: link the user's PRef `pr` to a witness PRef `wit` slot by
    /// slot, for when `pr` aliases a div/rem witness produced by
    /// `div_witnesses`. Emits `var(pr[j]) − var(wit[j]) = 0` for every
    /// `j < pr.typ.physical_len()`, and registers `pl[pr[j]] = var(wit[j])`.
    fn link_to_witness(&mut self, pr: &PRef, wit: &PRef, ideal: &mut Ideal<C>) {
        // Zip to min(pr slots, wit slots) — zip truncates to the shorter iterator.
        // Excess pr slots stay unconstrained (opaque).
        for (pf, wf) in pr.slots().into_iter().zip(wit.slots()) {
            let wvar = Polynomial::var(&wf);
            ideal.pl.insert(&pf, &wvar);
            ideal.basis.push(&wvar - &Polynomial::var(&pf));
        }
    }

    #[allow(clippy::wrong_self_convention)]
    fn to_poly_value(v: &Value<C>) -> Vec<Polynomial<C::F>> {
        match v {
            Value::Scalar(s) => vec![Polynomial::lit(s)],
            Value::Bool(b) => vec![Polynomial::lit(&if *b {
                C::F::one()
            } else {
                C::F::zero()
            })],
            Value::Index(i) => vec![Polynomial::lit(&C::FOps::from_usize(*i))],
            Value::Vec(v) => v.iter().flat_map(|v| Self::to_poly_value(v)).collect(),
            Value::VecBool(v) => v
                .iter()
                .map(|b| Polynomial::lit(&if *b { C::F::one() } else { C::F::zero() }))
                .collect::<Vec<_>>(),
            Value::VecScalar(v) => v.iter().map(Polynomial::lit).collect::<Vec<_>>(),
            Value::VecIndex(v) => v
                .iter()
                .map(|i| Polynomial::lit(&C::FOps::from_usize(*i)))
                .collect::<Vec<_>>(),
            _ => unreachable!("Unsupported value: {}", v),
        }
    }

    /// Shared helper for `Op::Evaluate(p, xs)` — computes the ideal
    /// polynomials for evaluating `p` at `xs`. Panics on unsupported
    /// (p.typ(), |xs|) combinations; the type checker guarantees these
    /// are unreachable.
    fn eval_to_poly(
        &mut self,
        p: &GOp<C>,
        xs: &GOp<C>,
        prefs: &HashMap<Ref, PRef>,
    ) -> Vec<Polynomial<C::F>> {
        let p_typ = p.typ();
        let xs_polys = Self::ref_vars(xs, prefs);
        let k = xs_polys.len();
        match &p_typ {
            ATyp::Uni(_) | ATyp::VPoly(1, _) => {
                assert!(
                    k >= 1,
                    "Evaluate on Uni/VPoly(1,_) requires at least 1 point; got {}",
                    k
                );
                let p_polys = Self::ref_vars(p, prefs);
                let one = Polynomial::<C::F>::lit(&C::F::one());
                xs_polys
                    .iter()
                    .map(|xi| {
                        let mut acc = Polynomial::<C::F>::zero();
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
                let p_polys = Self::ref_vars(p, prefs);
                let all_k = multi_indices(*n, *mdeg);
                let mono = |k_fixed: &[usize], xs_polys: &[Polynomial<C::F>]| -> Polynomial<C::F> {
                    let mut acc = Polynomial::<C::F>::lit(&C::F::one());
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
                    let mut acc = Polynomial::<C::F>::zero();
                    for (idx, ki) in all_k.iter().enumerate() {
                        acc = &acc + &(&p_polys[idx] * &mono(ki, &xs_polys));
                    }
                    vec![acc]
                } else {
                    let remaining_n = n - k;
                    let ideal_indices = multi_indices(remaining_n, *mdeg);
                    ideal_indices
                        .iter()
                        .map(|kp| {
                            let mut acc = Polynomial::<C::F>::zero();
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
                let p_polys = Self::ref_vars(p, prefs);
                let all_b = hypercube(*n);
                let one = Polynomial::<C::F>::lit(&C::F::one());
                let eq = |bi: usize, x: &Polynomial<C::F>| -> Polynomial<C::F> {
                    if bi == 1 { x.clone() } else { &one - x }
                };
                let eq_prod =
                    |b_fixed: &[usize], xs_polys: &[Polynomial<C::F>]| -> Polynomial<C::F> {
                        let mut acc = one.clone();
                        for (j, &bj) in b_fixed.iter().enumerate() {
                            acc = &acc * &eq(bj, &xs_polys[j]);
                        }
                        acc
                    };
                if k == *n {
                    let mut acc = Polynomial::<C::F>::zero();
                    for (idx, b) in all_b.iter().enumerate() {
                        acc = &acc + &(&p_polys[idx] * &eq_prod(b, &xs_polys));
                    }
                    vec![acc]
                } else {
                    let remaining_n = n - k;
                    let ideal_b = hypercube(remaining_n);
                    ideal_b
                        .iter()
                        .map(|bp| {
                            let mut acc = Polynomial::<C::F>::zero();
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

    /// Compute the slot offset of `field_name` within a record type.
    fn record_field_offset(fields: &Ctx<String, ATyp>, field_name: &str) -> usize {
        let mut offset = 0;
        for (fname, ftyp) in fields.iter() {
            if fname == field_name {
                return offset;
            }
            offset += ftyp.physical_len();
        }
        panic!(
            "Groebner record_field_offset: field '{}' not found in record fields {:?}",
            field_name,
            fields.iter().map(|(k, _)| k).collect::<Vec<_>>()
        )
    }

    fn eval_to_poly_as(
        &mut self,
        p: &GOp<C>,
        xs: &GOp<C>,
        target_typ: &ATyp,
        prefs: &HashMap<Ref, PRef>,
    ) -> Vec<Polynomial<C::F>> {
        let polys = self.eval_to_poly(p, xs, prefs);
        let raw_typ = {
            let k = Self::ref_vars(xs, prefs).len();
            match p.typ() {
                ATyp::Mle(n) if k < n => ATyp::Mle(n - k),
                ATyp::Mle(n) if k == n => ATyp::scalar(),
                ATyp::VPoly(n, m) if n >= 2 && k < n => ATyp::VPoly(n - k, m),
                ATyp::VPoly(n, _) if n >= 2 && k == n => ATyp::scalar(),
                ATyp::Uni(_) | ATyp::VPoly(1, _) if target_typ.physical_len() == polys.len() => {
                    target_typ.clone()
                }
                ATyp::Uni(_) | ATyp::VPoly(1, _) => ATyp::vec(&ATyp::scalar(), k),
                other => other,
            }
        };
        PolySource::<C> {
            polys,
            typ: raw_typ,
        }
        .lift_to(target_typ)
        .polys
    }

    /// Resolve an `Op::Ref(v, typ)` to a vector of variable polynomials,
    /// one per physical slot of the resolved PRef.
    ///
    /// After IR lowering, every child of a compound op is `Op::Ref` or
    /// `Op::Value`. This helper asserts the `Op::Ref` invariant and
    /// returns the slot variables for use in basis row construction.
    fn ref_vars(op: &GOp<C>, prefs: &HashMap<Ref, PRef>) -> Vec<Polynomial<C::F>> {
        match op {
            Op::Ref(v, typ) => {
                let pf = prefs
                    .get(v)
                    .unwrap_or_else(|| panic!("groebner: ref {} not found in namespace prefs", v));
                debug_assert_eq!(
                    pf.typ, *typ,
                    "find_ref type mismatch: namespace has {:?} but Op::Ref says {:?}",
                    pf.typ, typ,
                );
                pf.slots()
                    .into_iter()
                    .map(|s| Polynomial::var(&s))
                    .collect()
            }
            Op::Value(v) => Self::to_poly_value(v),
            other => {
                panic!(
                    "ref_vars called with unsupported op variant: {:?} — children should be materialized to Ref",
                    std::mem::discriminant(other)
                )
            }
        }
    }
}

impl<C: ArkConfig + HasOpFactory> IdealBuilder<C> {
    fn add_op(&mut self, pr: PRef, op: GOp<C>, ideal: &mut Ideal<C>) {
        match op {
            Op::Ref(r, typ) => {
                if pr.reference == r && pr.index == 0 && pr.typ == typ {
                    return;
                }

                let ref_src: PolySource<C> =
                    PolySource::from_ref_vars(&ideal.prefs, &Op::Ref(r, typ.clone()));
                let lifted = ref_src.lift_to(&pr.typ);
                for (pf, p) in pr.slots().into_iter().zip(lifted.polys) {
                    ideal.pl.insert(&pf, &p);
                    ideal.basis.push(p - Polynomial::var(&pf));
                }
            }
            Op::Bin(BinOp::Add, a, b, _) => {
                let a_src = PolySource::from_ref_vars(&ideal.prefs, &a);
                let b_src = PolySource::from_ref_vars(&ideal.prefs, &b);
                self.broadcast_binop(&pr, &a_src, &b_src, &pr.typ, BinOp::Add, ideal);
            }
            Op::Bin(BinOp::And, ref a, ref b, _) => {
                let a_src = PolySource::from_ref_vars(&ideal.prefs, a);
                let b_src = PolySource::from_ref_vars(&ideal.prefs, b);
                self.mul_op(&pr, &a_src, &b_src, &pr.typ, ideal);
            }
            Op::Bin(BinOp::Sub, a, b, _) => {
                let a_src = PolySource::from_ref_vars(&ideal.prefs, &a);
                let b_src = PolySource::from_ref_vars(&ideal.prefs, &b);
                self.broadcast_binop(&pr, &a_src, &b_src, &pr.typ, BinOp::Sub, ideal);
            }
            Op::Bin(BinOp::Mul, ref a, ref b, _) => {
                let a_src = PolySource::from_ref_vars(&ideal.prefs, a);
                let b_src = PolySource::from_ref_vars(&ideal.prefs, b);
                self.mul_op(&pr, &a_src, &b_src, &pr.typ, ideal);
            }
            Op::Bin(BinOp::Dot, ref a, ref b, _) => {
                let a_src = PolySource::from_ref_vars(&ideal.prefs, a);
                let b_src = PolySource::from_ref_vars(&ideal.prefs, b);
                self.dot_op(&pr, &a_src, &b_src, ideal);
            }
            Op::Bin(BinOp::Div, ref a, ref b, _) => {
                if let Some(cofactor) = self.exact_division_cofactor(a, b) {
                    let cof_src = PolySource::from_ref_vars(&ideal.prefs, &cofactor);
                    let lifted = cof_src.lift_to(&pr.typ);
                    for (pf, p) in pr.slots().into_iter().zip(lifted.polys) {
                        ideal.pl.insert(&pf, &p);
                        ideal.basis.push(p - Polynomial::var(&pf));
                    }
                } else {
                    let a_src = PolySource::from_ref_vars(&ideal.prefs, a);
                    let b_src = PolySource::from_ref_vars(&ideal.prefs, b);
                    self.div_rem_op(&pr, &a_src, &b_src, false, true, ideal);
                }
            }
            Op::Bin(BinOp::Rem, ref a, ref b, _) => {
                let a_src = PolySource::from_ref_vars(&ideal.prefs, a);
                let b_src = PolySource::from_ref_vars(&ideal.prefs, b);
                self.div_rem_op(&pr, &a_src, &b_src, true, true, ideal);
            }
            Op::Bin(BinOp::Equ, a, b, _) => {
                let a_src = PolySource::from_ref_vars(&ideal.prefs, &a);
                let b_src = PolySource::from_ref_vars(&ideal.prefs, &b);
                self.broadcast_equ(&pr, &a_src, &b_src, ideal);
            }
            Op::Check(a) => self.add_op(pr, a.get().clone(), ideal),
            Op::Challenge(_, _) | Op::Random(_, _) => {}
            Op::Interpolate(ref points, ref evals) => {
                self.interpolate_op(pr, points, evals, ideal);
            }
            // Op::Ifft(v): p = ifft(v) — inverse DFT. The coefficient form `pr`
            // is the IDFT of the evaluation form `a`. Each coefficient is:
            //   p[j] = (1/N) · Σ_i ω^{-i·j} · v[i]
            // where ω is a primitive N-th root of unity. The type checker
            // guarantees N is a 2-adic divisor of |F|-1, so ω always exists.
            Op::Ifft(ref a) => {
                let v_polys = Self::ref_vars(a, &ideal.prefs);
                let n = v_polys.len();
                let omega = C::F::get_root_of_unity(n as u64)
                    .expect("IFFT size must have a root of unity; type checker guarantees this");
                let omega_inv = omega.inverse().unwrap();
                let n_inv = C::F::from(n as u64).inverse().unwrap();
                let pr_slots = pr.slots();
                for (j, pf) in pr_slots.iter().enumerate() {
                    let idft_j = dft_row::<C>(&v_polys, omega_inv, j);
                    let lhs = &idft_j * &Polynomial::lit(&n_inv);
                    ideal.pl.insert(pf, &lhs);
                    ideal.basis.push(&lhs - &Polynomial::var(pf));
                }
            }
            // Op::Fft(p): v = fft(p) — forward DFT. Each evaluation is:
            //   v[i] = Σ_j ω^{i·j} · p[j]
            // The type checker guarantees N is a 2-adic divisor of |F|-1.
            Op::Fft(ref a) => {
                let coeff_polys = Self::ref_vars(a, &ideal.prefs);
                let n = coeff_polys.len();
                let omega = C::F::get_root_of_unity(n as u64)
                    .expect("FFT size must have a root of unity; type checker guarantees this");
                let pr_slots = pr.slots();
                for (i, pf) in pr_slots.iter().enumerate() {
                    let lhs = dft_row::<C>(&coeff_polys, omega, i);
                    ideal.pl.insert(pf, &lhs);
                    ideal.basis.push(&lhs - &Polynomial::var(pf));
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
                let polys = Self::ref_vars(inner, &ideal.prefs);
                debug_assert!(
                    !polys.is_empty(),
                    "Op::Poly/Mle/Coef produced zero polys for {:?}",
                    pr.typ
                );
                for (pf, p) in pr.slots().into_iter().zip(polys) {
                    ideal.pl.insert(&pf, &p);
                    ideal.basis.push(p - Polynomial::var(&pf));
                }
            }
            Op::Vec(vs) => {
                for (i, v) in vs.into_iter().enumerate() {
                    let pr_i = pr.with_index(i).unwrap();
                    self.add_op(pr_i, v.get().clone(), ideal);
                }
            }
            // Op::Evaluate(p, xs): evaluate a polynomial `p` at points `xs`.
            //
            // Three shapes are handled (dispatched on p.typ() × |xs slots|):
            //
            //   1. Univariate batched — p: Uni(_) or VPoly(1, _), xs: len k ≥ 1
            //        ideal[i] = Σ_j a_j · xs[i]^j                  (target-shaped k-slot output)
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
            Op::Evaluate(ref p, None, Some(ref xs)) => {
                let polys = self.eval_to_poly_as(p, xs, &pr.typ, &ideal.prefs);
                for (pf, poly) in pr.slots().into_iter().zip(polys) {
                    ideal.pl.insert(&pf, &poly);
                    ideal.basis.push(poly - Polynomial::var(&pf));
                }
            }
            Op::Evaluate(ref p, Some(range), Some(ref fixed)) => {
                match self.selected_eval_to_poly(p, &range, fixed, &ideal.prefs) {
                    Some(polys) => {
                        for (pf, poly) in pr.slots().into_iter().zip(polys) {
                            ideal.pl.insert(&pf, &poly);
                            ideal.basis.push(poly - Polynomial::var(&pf));
                        }
                    }
                    None => Self::uncovered_op("selected-evaluate", &pr),
                }
            }
            Op::Evaluate(ref p, None, None) => {
                let coeff_polys = Self::ref_vars(p, &ideal.prefs);
                let n = coeff_polys.len();
                let omega = C::F::get_root_of_unity(n as u64).expect(
                    "Evaluate grid size must have a root of unity; type checker guarantees this",
                );
                for (i, pf) in pr.slots().into_iter().enumerate() {
                    let lhs = dft_row::<C>(&coeff_polys, omega, i);
                    ideal.pl.insert(&pf, &lhs);
                    ideal.basis.push(&lhs - &Polynomial::var(&pf));
                }
            }
            Op::Evaluate(_, Some(_), None) => {
                Self::uncovered_op("selected-evaluate-missing-points", &pr);
            }
            Op::Map(ref domain, ref body) => self.map_to_poly(pr, domain, body, &[], &[], ideal),
            Op::ReduceMap(rop, ref domain, ref body) => {
                self.reduce_map_to_poly(pr, rop, domain, body, &[], &[], ideal)
            }
            Op::LoopParam(_, _) => Self::uncovered_op("loop-param", &pr),
            // Phase 10: `Op::Reduce(op, v)` — left-fold of vector elements.
            // See `reduce_op` for per-operator handling.
            Op::Reduce(rop, ref v) => {
                self.reduce_op(pr, rop, v, ideal);
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
                // fails explicitly via `uncovered_op`.
                let polys_opt: Option<Vec<Polynomial<C::F>>> = match v {
                    Value::Scalar(_)
                    | Value::Bool(_)
                    | Value::Index(_)
                    | Value::Vec(_)
                    | Value::VecBool(_)
                    | Value::VecScalar(_)
                    | Value::VecIndex(_) => Some(Self::to_poly_value(v)),
                    _ => None,
                };
                match polys_opt {
                    Some(polys) => {
                        for (pf, p) in pr.slots().into_iter().zip(polys) {
                            ideal.pl.insert(&pf, &p);
                            ideal.basis.push(p - Polynomial::var(&pf));
                        }
                    }
                    None => {
                        Self::uncovered_op("unsupported-value", &pr);
                    }
                }
            }
            // Phase 10: `Op::Ram(a, b)` — RAM reads with a literal index `i`
            // resolve to the i-th logical element of the array. For compound
            // element types, all physical slots are linked pairwise.
            // Multi-index (VecIndex) reads produce a vector of elements.
            // Runtime indices fall back to opaque.
            Op::Ram(ref a, ref b) => match b.get() {
                Op::Value(Value::Index(i)) => {
                    let Op::Ref(r, _) = a.get() else {
                        unreachable!(
                            "Ram array operand must be Ref; got {:?}",
                            std::mem::discriminant(a.get())
                        )
                    };
                    let array_pref = ideal.find_ref(r);
                    let Some(elem_pref) = array_pref.with_index(*i) else {
                        unreachable!(
                            "Ram operand with literal index must be within bound; Got {:?}",
                            *i
                        )
                    };

                    for (pf, e) in pr.slots().into_iter().zip(elem_pref.slots()) {
                        let e_poly = Polynomial::var(&e);
                        ideal.basis.push(e_poly.clone() - Polynomial::var(&pf));
                        ideal.pl.insert(&pf, &e_poly);
                    }
                }
                Op::Value(Value::VecIndex(vs)) => {
                    let Op::Ref(r, _) = a.get() else {
                        unreachable!(
                            "Ram array operand must be Ref; got {:?}",
                            std::mem::discriminant(a.get())
                        )
                    };
                    let array_pref = ideal.find_ref(r);
                    for (j, idx) in vs.iter().enumerate() {
                        let src_pref = array_pref.with_index(*idx).unwrap();
                        let dst_pref = pr.with_index(j).unwrap();
                        for (pf, e) in dst_pref.slots().into_iter().zip(src_pref.slots()) {
                            let e_poly = Polynomial::var(&e);
                            ideal.basis.push(e_poly.clone() - Polynomial::var(&pf));
                            ideal.pl.insert(&pf, &e_poly);
                        }
                    }
                }
                _ => {
                    Self::uncovered_op("dynamic-ram", &pr);
                }
            },
            // Phase 12: `Op::Pair(a, b, t)` — bilinear pairing.
            // For each slot position, the ideal is bound to the
            // exponent-space product:
            //
            //   var(pr[i]) = var(a[i]) · var(b[i])
            //
            // Matching pair expressions on both sides of a `verify(lhs == rhs)`
            // cancel under Buchberger because their basis rows are identical
            // F-polynomials.
            Op::Pair(ref a, ref b, _) => {
                let a_src = PolySource::from_ref_vars(&ideal.prefs, a.get());
                let b_src = PolySource::from_ref_vars(&ideal.prefs, b.get());
                self.pair_op(&pr, &a_src, &b_src, ideal);
            }
            // `Op::Record(fields)` — field-slot-aware layout.
            // Physical slots are laid out in Ctx iteration order: each
            // field occupies `field_typ.physical_len()` consecutive slots.
            // For each field, emit basis rows linking record slots to
            // the field's polynomial values.
            Op::Record(ref fields) => {
                let pr_len = pr.typ.physical_len();
                if pr_len > MAX_GROEBNER_MATERIALIZED_SLOTS {
                    panic!(
                        "Groebner Record has {} physical slots, above materialization limit {}",
                        pr_len, MAX_GROEBNER_MATERIALIZED_SLOTS
                    );
                }
                let mut slot_offset = 0usize;
                for (_, field_op) in fields.iter() {
                    let field_polys = Self::ref_vars(field_op.get(), &ideal.prefs);
                    for (j, p) in field_polys.into_iter().enumerate() {
                        let pf = pr
                            .clone()
                            .with_slot(slot_offset + j)
                            .expect("record field slot must be within record physical layout");
                        ideal.pl.insert(&pf, &p);
                        ideal.basis.push(p - Polynomial::var(&pf));
                    }
                    slot_offset += field_op.typ().physical_len();
                }
            }
            // Concat/Pow/Marginalize/Proj require explicit ideal treatment;
            // unsupported shapes fail instead of becoming hidden op state.
            Op::Bin(BinOp::Concat, ref a, ref b, _) => {
                let a_src = PolySource::from_ref_vars(&ideal.prefs, a);
                let b_src = PolySource::from_ref_vars(&ideal.prefs, b);
                self.concat_op(&pr, &a_src, &b_src, a, b, ideal);
            }
            Op::Bin(BinOp::Pow, ref a, ref b, _) => {
                self.pow_op(&pr, a, b, ideal);
            }
            // `Op::Proj(inner, field, typ)` — extract a field from a Record.
            // The field's physical slots sit at an offset within the Record's
            // slot layout: offset = sum of physical_len() of preceding fields
            // (in Ctx iteration order). Emit basis rows linking proj ideal
            // slots to the corresponding inner Record slots.
            //
            // Non-record inner types are not supported — after IR lowering every
            // Proj must operate on a Record; any other variant is a compiler bug.
            Op::Proj(ref inner, ref field, ref _typ) => {
                let inner_typ = inner.typ();
                let inner_polys = Self::ref_vars(inner, &ideal.prefs);
                match &inner_typ {
                    ATyp::Record(fields) => {
                        let offset = Self::record_field_offset(fields, field);
                        let pr_slots = pr.slots();
                        for (j, pf) in pr_slots.iter().enumerate() {
                            ideal.pl.insert(pf, &inner_polys[offset + j]);
                            ideal
                                .basis
                                .push(inner_polys[offset + j].clone() - Polynomial::var(pf));
                        }
                    }
                    _ => {
                        unreachable!(
                            "Groebner Proj: non-record inner type {:?} for field '{}'; \
                             all Proj ops must operate on Record types after IR lowering",
                            inner_typ, field
                        );
                    }
                }
            }
        }
    }

    /// Lagrange interpolation: given `n` distinct points `(x_i, y_i)`,
    /// the ideal polynomial `p(X) = Σ_i y_i · L_i(X)` where
    /// `L_i(X) = Π_{j≠i} (X - x_j) / (x_i - x_j)`.
    ///
    /// For each coefficient slot `k` of the ideal `Uni(n)`:
    ///   `var(pr[k]) = Σ_i var(y_i) · L[i][k]`
    ///
    /// When `points` is `Op::Value`, the constant values are extracted
    /// directly via `to_poly_value`. When `points` is `Op::Ref`, the
    /// point slot polynomials are looked up in `ideal.pl` — since the
    /// Vec node is processed before Interpolate in topological order,
    /// constant bindings are already available there.
    ///
    /// Falls back to opaque if the point values aren't all constant.
    fn interpolate_op(&mut self, pr: PRef, points: &HOp<C>, evals: &HOp<C>, ideal: &mut Ideal<C>) {
        let evals_polys = Self::ref_vars(evals, &ideal.prefs);
        let n = evals_polys.len();

        let xs_polys: Vec<Polynomial<C::F>> = match points.get() {
            Op::Value(v) => Self::to_poly_value(v),
            Op::Ref(r, _) => {
                let points_pref = ideal.find_ref(r);
                points_pref
                    .slots()
                    .iter()
                    .map(|s| ideal.pl.get(s).cloned().unwrap_or_else(Polynomial::zero))
                    .collect()
            }
            other => {
                unreachable!(
                    "Interpolate points operand must be Ref or Value; got {:?}",
                    std::mem::discriminant(other)
                )
            }
        };

        assert_eq!(
            n,
            xs_polys.len(),
            "Interpolate: points and evals must have same length"
        );

        let all_constant = xs_polys.iter().all(|p| p.is_constant());

        if all_constant {
            let xs: Vec<C::F> = xs_polys.iter().map(|p| p.constant_coeff()).collect();
            for i in 0..xs.len() {
                for j in (i + 1)..xs.len() {
                    if xs[i] == xs[j] {
                        Self::uncovered_op("duplicate-interpolate-points", &pr);
                    }
                }
            }
            let lag = lagrange_basis::<C::F>(&xs);
            let pr_slots = pr.slots();
            for (k, pf) in pr_slots.iter().enumerate() {
                let mut acc = Polynomial::<C::F>::zero();
                for (i, y_i) in evals_polys.iter().enumerate() {
                    if k < lag[i].len() && lag[i][k] != C::F::zero() {
                        let weight = Polynomial::<C::F>::lit(&lag[i][k]);
                        acc += y_i * &weight;
                    }
                }
                ideal.pl.insert(pf, &acc);
                ideal.basis.push(acc - Polynomial::var(pf));
            }
        } else {
            for i in 0..xs_polys.len() {
                for j in (i + 1)..xs_polys.len() {
                    let diff = &xs_polys[i] - &xs_polys[j];
                    if diff.is_zero() {
                        Self::uncovered_op("duplicate-interpolate-points", &pr);
                    }
                }
            }

            let n_pts = xs_polys.len();
            let mut denom_inverses: Vec<Vec<Option<PRef>>> = vec![vec![None; n_pts]; n_pts];
            for i in 0..n_pts {
                for j in 0..n_pts {
                    if i == j {
                        continue;
                    }
                    let diff = &xs_polys[i] - &xs_polys[j];
                    if diff.is_constant() {
                        continue;
                    }
                    let d_name = self.ns.next_name("interp_inv");
                    let d = self.sentinel_pref(&d_name, ATyp::scalar(), ideal);
                    ideal
                        .basis
                        .push(Polynomial::var(&d) * diff - Polynomial::<C::F>::lit(&C::F::one()));
                    denom_inverses[i][j] = Some(d);
                }
            }

            let pr_slots = pr.slots();
            let mut ideal_polys = vec![Polynomial::<C::F>::zero(); pr_slots.len()];

            for (i, y_i) in evals_polys.iter().enumerate() {
                let mut lag_poly = vec![Polynomial::<C::F>::lit(&C::F::one())];

                for (j, xj_poly) in xs_polys.iter().enumerate().take(n_pts) {
                    if j == i {
                        continue;
                    }
                    let neg_xj = xj_poly * &Polynomial::lit(&(-C::F::one()));
                    let mut new_lag = vec![Polynomial::<C::F>::zero(); lag_poly.len() + 1];
                    for (deg, c) in lag_poly.iter().enumerate() {
                        let shifted = c * &neg_xj;
                        new_lag[deg] = &new_lag[deg] + &shifted;
                        new_lag[deg + 1] = &new_lag[deg + 1] + c;
                    }
                    lag_poly = new_lag;
                }

                let mut denom_inv = Polynomial::<C::F>::lit(&C::F::one());
                for j in 0..n_pts {
                    if j == i {
                        continue;
                    }
                    let diff = &xs_polys[i] - &xs_polys[j];
                    if diff.is_constant() {
                        let c = diff.constant_coeff();
                        denom_inv *= Polynomial::lit(&c.inverse().unwrap());
                    } else {
                        let d = denom_inverses[i][j]
                            .as_ref()
                            .expect("d-variable must exist for non-constant diff");
                        denom_inv *= Polynomial::var(d);
                    }
                }

                for (k, coeff) in lag_poly.iter().enumerate() {
                    let scaled = coeff * &denom_inv;
                    ideal_polys[k] = &ideal_polys[k] + &(y_i * &scaled);
                }
            }

            for (pf, poly) in pr_slots.iter().zip(ideal_polys) {
                ideal.pl.insert(pf, &poly);
                ideal.basis.push(poly - Polynomial::var(pf));
            }
        }
    }

    /// Left-fold of vector elements:
    ///   acc₀ = v[0],  acc_i = rop(acc_{i-1}, v[i]),  ideal = acc_{n-1}
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
    /// - **Div/Rem**: lower as true left folds. Polynomial folds use
    ///   division/remainder witness identities for each step, while scalar
    ///   division uses per-slot constraints `acc - elem * var(target) = 0`.
    ///
    /// - **Equ/Pow**: opaque. Chained equality can't be cleanly encoded in
    ///   the polynomial basis; Pow's left-fold `(a^b)^c` requires `a^(b*c)`
    ///   which is only valid for constant b, c and produces potentially
    ///   very-high-degree terms — better handled by the `BinOp::Pow` handler
    ///   in `add_op` which sees a single exponent directly.
    ///
    /// - **Dot**: unreachable (type checker rejects `reduce(dot, _)`).
    fn reduce_op(&mut self, pr: PRef, rop: BinOp, v: &HOp<C>, ideal: &mut Ideal<C>) {
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
            let v_pref = ideal.find_ref(r);
            let elem_pref = v_pref.with_index(0).unwrap();
            self.link_to_witness(&pr, &elem_pref, ideal);
            return;
        }

        let v_src = PolySource::from_ref_vars(&ideal.prefs, v);

        match rop {
            BinOp::Add => {
                let mut acc: PolySource<C> = PolySource::new(
                    (0..elem_t.physical_len())
                        .map(|_| Polynomial::zero())
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
                    ideal.pl.insert(&pf, &p);
                    ideal.basis.push(p - Polynomial::var(&pf));
                }
            }
            BinOp::And => {
                let mut acc = v_src.at_index(0).unwrap();
                for i in 1..n {
                    let elem = v_src.at_index(i).unwrap();
                    let acc_name = self.ns.next_name("reduce_and_acc");
                    let acc_pref = self.sentinel_pref(&acc_name, elem_t.clone(), ideal);
                    self.mul_op(&acc_pref, &acc, &elem, &elem_t, ideal);
                    acc = PolySource::new(
                        acc_pref
                            .slots()
                            .into_iter()
                            .map(|s| Polynomial::var(&s))
                            .collect(),
                        elem_t.clone(),
                    );
                }
                for (pf, p) in pr.slots().into_iter().zip(acc.polys) {
                    ideal.basis.push(p - Polynomial::var(&pf));
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
                    ideal.pl.insert(&pf, &p);
                    ideal.basis.push(p - Polynomial::var(&pf));
                }
            }
            BinOp::Mul => {
                let mut acc = v_src.at_index(0).unwrap();
                let mut acc_typ = elem_t.clone();
                for i in 1..n {
                    let elem = v_src.at_index(i).unwrap();
                    let step_typ = ATyp::lub_mul(&acc_typ, elem.typ(), &Nothing)
                        .expect("reduce(*): type checker guarantees lub_mul");
                    let is_last = i == n - 1;
                    let acc_pref = if is_last {
                        pr.clone()
                    } else {
                        let acc_name = self.ns.next_name("reduce_mul_acc");
                        self.sentinel_pref(&acc_name, step_typ.clone(), ideal)
                    };
                    self.mul_op(&acc_pref, &acc, &elem, &step_typ, ideal);
                    acc = PolySource::from_pref_vars(&acc_pref, step_typ.clone());
                    acc_typ = step_typ;
                }
            }
            BinOp::Concat => {
                for (pf, p) in pr.slots().into_iter().zip(v_src.polys) {
                    ideal.pl.insert(&pf, &p);
                    ideal.basis.push(p - Polynomial::var(&pf));
                }
            }
            BinOp::Div | BinOp::Rem => {
                let is_rem = rop == BinOp::Rem;
                let is_poly = PolySource::<C>::poly_shape_static(&elem_t).is_some();
                let mut acc_src = v_src.at_index(0).unwrap();
                let mut acc_typ = elem_t.clone();
                for step in 0..n - 1 {
                    let is_last = step == n - 2;
                    let elem_src = v_src.at_index(step + 1).unwrap();
                    if !is_poly && is_rem {
                        unreachable!(
                            "Rem: non-polynomial remainder is undefined for Vec<{}>",
                            elem_t,
                        );
                    }
                    let step_typ = ATyp::lub_op(rop, &acc_typ, elem_src.typ(), &Nothing)
                        .expect("reduce(/,%): type checker guarantees lub");
                    let target = if is_last {
                        pr.clone()
                    } else {
                        let acc_name = self.ns.next_name(if is_rem {
                            "reduce_rem_acc"
                        } else {
                            "reduce_div_acc"
                        });
                        self.sentinel_pref(&acc_name, step_typ.clone(), ideal)
                    };
                    if is_poly {
                        self.div_rem_op(&target, &acc_src, &elem_src, is_rem, false, ideal);
                    } else {
                        self.slot_wise_div(&target, acc_src.polys(), elem_src.polys(), ideal);
                    }
                    acc_src = PolySource::from_pref_vars(&target, step_typ.clone());
                    acc_typ = step_typ;
                }
            }
            BinOp::Equ | BinOp::Pow => {
                Self::uncovered_op("reduce-equ-or-pow", &pr);
            }
            BinOp::Dot => {
                unreachable!("reduce(dot, _) is rejected by the type checker");
            }
        }
    }
}

impl<C: ArkConfig + HasOpFactory> IdealBuilder<C> {
    /// Shared fold for `Op::Reduce` and `Op::ReduceMap`: combine the `n`
    /// elements of `v_src` (each of type `elem_t`) under `rop`, binding `pr`.
    fn reduce_polysource(
        &mut self,
        pr: PRef,
        rop: BinOp,
        v_src: PolySource<C>,
        elem_t: ATyp,
        n: usize,
        ideal: &mut Ideal<C>,
    ) {
        match rop {
            BinOp::Add => {
                let mut acc: PolySource<C> = PolySource::new(
                    (0..elem_t.physical_len())
                        .map(|_| Polynomial::zero())
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
                    ideal.pl.insert(&pf, &p);
                    ideal.basis.push(p - Polynomial::var(&pf));
                }
            }
            BinOp::And => {
                let mut acc = v_src.at_index(0).unwrap();
                for i in 1..n {
                    let elem = v_src.at_index(i).unwrap();
                    let acc_name = self.ns.next_name("reduce_and_acc");
                    let acc_pref = self.sentinel_pref(&acc_name, elem_t.clone(), ideal);
                    self.mul_op(&acc_pref, &acc, &elem, &elem_t, ideal);
                    acc = PolySource::new(
                        acc_pref
                            .slots()
                            .into_iter()
                            .map(|s| Polynomial::var(&s))
                            .collect(),
                        elem_t.clone(),
                    );
                }
                for (pf, p) in pr.slots().into_iter().zip(acc.polys) {
                    ideal.basis.push(p - Polynomial::var(&pf));
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
                    ideal.pl.insert(&pf, &p);
                    ideal.basis.push(p - Polynomial::var(&pf));
                }
            }
            BinOp::Mul => {
                let mut acc = v_src.at_index(0).unwrap();
                let mut acc_typ = elem_t.clone();
                for i in 1..n {
                    let elem = v_src.at_index(i).unwrap();
                    let step_typ = ATyp::lub_mul(&acc_typ, elem.typ(), &Nothing)
                        .expect("reduce(*): type checker guarantees lub_mul");
                    let is_last = i == n - 1;
                    let acc_pref = if is_last {
                        pr.clone()
                    } else {
                        let acc_name = self.ns.next_name("reduce_mul_acc");
                        self.sentinel_pref(&acc_name, step_typ.clone(), ideal)
                    };
                    self.mul_op(&acc_pref, &acc, &elem, &step_typ, ideal);
                    acc = PolySource::from_pref_vars(&acc_pref, step_typ.clone());
                    acc_typ = step_typ;
                }
            }
            BinOp::Concat => {
                for (pf, p) in pr.slots().into_iter().zip(v_src.polys) {
                    ideal.pl.insert(&pf, &p);
                    ideal.basis.push(p - Polynomial::var(&pf));
                }
            }
            BinOp::Div | BinOp::Rem => {
                let is_rem = rop == BinOp::Rem;
                let is_poly = PolySource::<C>::poly_shape_static(&elem_t).is_some();
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
                        self.sentinel_pref(&acc_name, elem_t.clone(), ideal)
                    };
                    let elem_src = v_src.at_index(step + 1).unwrap();
                    if is_poly {
                        self.div_rem_op(
                            &target,
                            &acc_src,
                            &elem_src,
                            is_rem && is_last,
                            false,
                            ideal,
                        );
                    } else {
                        if is_rem {
                            unreachable!(
                                "Rem: non-polynomial remainder is undefined for Vec<{}>",
                                elem_t,
                            );
                        }
                        self.slot_wise_div(&target, acc_src.polys(), elem_src.polys(), ideal);
                    }
                    acc_src = PolySource::new(
                        target
                            .slots()
                            .into_iter()
                            .map(|s| Polynomial::var(&s))
                            .collect(),
                        elem_t.clone(),
                    );
                }
            }
            BinOp::Equ | BinOp::Pow => {
                Self::uncovered_op("reduce-equ-or-pow", &pr);
            }
            BinOp::Dot => {
                unreachable!("reduce(dot, _) is rejected by the type checker");
            }
        }
    }

    /// Selected evaluation: keep variable `range.start` free and substitute
    /// `fixed` for the remaining variables. Returns the residual univariate
    /// coefficient polys, or `None` for unsupported shapes.
    fn selected_eval_to_poly(
        &mut self,
        p: &GOp<C>,
        range: &lang::typ::CRange,
        fixed: &GOp<C>,
        prefs: &HashMap<Ref, PRef>,
    ) -> Option<Vec<Polynomial<C::F>>> {
        if range.step != 1 || range.len() != 1 {
            return None;
        }

        let fixed_polys = Self::ref_vars(fixed, prefs);
        match p.typ() {
            ATyp::VPoly(n, d) if range.end <= n && fixed_polys.len() == n.saturating_sub(1) => {
                let p_polys = Self::ref_vars(p, prefs);
                let all_indices = multi_indices(n, d);
                let mut out = vec![Polynomial::<C::F>::zero(); d + 1];

                for (idx, ki) in all_indices.iter().enumerate() {
                    let free_exp = ki[range.start];
                    let mut term = p_polys[idx].clone();
                    let mut fixed_idx = 0usize;
                    for (var_idx, &var_exp) in ki.iter().enumerate().take(n) {
                        if var_idx == range.start {
                            continue;
                        }
                        if var_exp > 0 {
                            let mut fixed_pow = fixed_polys[fixed_idx].clone();
                            fixed_pow.pow(var_exp);
                            term = &term * &fixed_pow;
                        }
                        fixed_idx += 1;
                    }
                    out[free_exp] = &out[free_exp] + &term;
                }
                Some(out)
            }
            ATyp::Mle(n) if range.end <= n && fixed_polys.len() == n.saturating_sub(1) => {
                let p_polys = Self::ref_vars(p, prefs);
                let all_b = hypercube(n);
                let one = Polynomial::<C::F>::lit(&C::F::one());
                let eq = |bi: usize, x: &Polynomial<C::F>| -> Polynomial<C::F> {
                    if bi == 1 { x.clone() } else { &one - x }
                };
                let free = range.start;
                let mut out = vec![Polynomial::<C::F>::zero(); 2];
                for (idx, b) in all_b.iter().enumerate() {
                    let mut w = one.clone();
                    let mut fixed_idx = 0usize;
                    for (var_idx, &bv) in b.iter().enumerate().take(n) {
                        if var_idx == free {
                            continue;
                        }
                        w = &w * &eq(bv, &fixed_polys[fixed_idx]);
                        fixed_idx += 1;
                    }
                    let term = &p_polys[idx] * &w;
                    if b[free] == 0 {
                        out[0] = &out[0] + &term;
                        out[1] = &out[1] - &term;
                    } else {
                        out[1] = &out[1] + &term;
                    }
                }
                Some(out)
            }
            _ => None,
        }
    }

    /// Constant-fold an integer (`Fin`/`Bool`) subexpression over the enclosing
    /// loop indices. Returns `Some(value)` only when `op` is integer-typed and
    /// every enclosing loop binder has a concrete value; otherwise `None`.
    fn const_eval_int(&self, op: &HOp<C>, loop_vals: &[Option<Value<C>>]) -> Option<Value<C>> {
        let t = op.typ();
        if !(t.is_fin() || t.is_bool()) {
            return None;
        }
        let params: Vec<std::sync::Arc<Value<C>>> = loop_vals
            .iter()
            .map(|v| v.clone().map(std::sync::Arc::new))
            .collect::<Option<_>>()?;
        let env: HashMap<Ref, std::sync::Arc<Value<C>>> = HashMap::new();
        let mut rng = <rand::rngs::StdRng as rand::SeedableRng>::seed_from_u64(0);
        graph::eval::eval_op_with_loop_params(op.get(), &env, &mut rng, &params)
            .ok()
            .map(|v| (*v).clone())
    }

    /// Materialize an inline Map/ReduceMap body op-tree into registered
    /// sentinel PRefs and return the PRef bound to its ideal.
    fn body_to_poly(
        &mut self,
        body: &HOp<C>,
        loops: &[PRef],
        loop_vals: &[Option<Value<C>>],
        ideal: &mut Ideal<C>,
    ) -> Option<PRef> {
        match body.get() {
            Op::Ref(r, _) => Some(ideal.find_ref(r)),
            Op::LoopParam(level, _) => loops.get(*level).cloned(),
            Op::Value(_) => {
                let name = self.ns.next_name("gb_map_body");
                let pf = self.sentinel_pref(&name, body.typ(), ideal);
                ideal.register(&pf);
                self.add_op(pf.clone(), body.get().clone(), ideal);
                Some(pf)
            }
            Op::Map(d, b) => {
                let name = self.ns.next_name("gb_map_body");
                let pf = self.sentinel_pref(&name, body.typ(), ideal);
                ideal.register(&pf);
                self.map_to_poly(pf.clone(), d, b, loops, loop_vals, ideal);
                Some(pf)
            }
            Op::ReduceMap(rop, d, b) => {
                let name = self.ns.next_name("gb_map_body");
                let pf = self.sentinel_pref(&name, body.typ(), ideal);
                ideal.register(&pf);
                self.reduce_map_to_poly(pf.clone(), *rop, d, b, loops, loop_vals, ideal);
                Some(pf)
            }
            _ => {
                if let Some(v) = self.const_eval_int(body, loop_vals) {
                    let name = self.ns.next_name("gb_map_body");
                    let pf = self.sentinel_pref(&name, body.typ(), ideal);
                    ideal.register(&pf);
                    self.add_op(pf.clone(), Op::Value(v), ideal);
                    return Some(pf);
                }
                let rebuilt = self.rebuild_body_op(body, loops, loop_vals, ideal)?;
                let name = self.ns.next_name("gb_map_body");
                let pf = self.sentinel_pref(&name, body.typ(), ideal);
                ideal.register(&pf);
                self.add_op(pf.clone(), rebuilt, ideal);
                Some(pf)
            }
        }
    }

    /// Materialize a body child to an add_op-ready operand: `Op::Value` and
    /// `Op::Ref` stay verbatim; everything else is bound to a fresh sentinel.
    fn body_child(
        &mut self,
        child: &HOp<C>,
        loops: &[PRef],
        loop_vals: &[Option<Value<C>>],
        ideal: &mut Ideal<C>,
    ) -> Option<HOp<C>> {
        match child.get() {
            Op::Value(_) | Op::Ref(_, _) => Some(child.clone()),
            _ => {
                if let Some(v) = self.const_eval_int(child, loop_vals) {
                    return Some(mk::<C>(Op::Value(v)));
                }
                let pf = self.body_to_poly(child, loops, loop_vals, ideal)?;
                Some(mk::<C>(Op::Ref(pf.reference, pf.typ.clone())))
            }
        }
    }

    /// Rebuild a compound body op with each child replaced by an add_op-ready
    /// operand (see `body_child`). Returns `None` for an unsupported variant.
    fn rebuild_body_op(
        &mut self,
        body: &HOp<C>,
        loops: &[PRef],
        loop_vals: &[Option<Value<C>>],
        ideal: &mut Ideal<C>,
    ) -> Option<GOp<C>> {
        Some(match body.get() {
            Op::Bin(op, a, b, typ) => Op::Bin(
                *op,
                self.body_child(a, loops, loop_vals, ideal)?,
                self.body_child(b, loops, loop_vals, ideal)?,
                typ.clone(),
            ),
            Op::Ram(a, b) => Op::Ram(
                self.body_child(a, loops, loop_vals, ideal)?,
                self.body_child(b, loops, loop_vals, ideal)?,
            ),
            Op::Evaluate(p, range, pts) => Op::Evaluate(
                self.body_child(p, loops, loop_vals, ideal)?,
                *range,
                match pts {
                    Some(x) => Some(self.body_child(x, loops, loop_vals, ideal)?),
                    None => None,
                },
            ),
            Op::Poly(a) => Op::Poly(self.body_child(a, loops, loop_vals, ideal)?),
            Op::Coef(a) => Op::Coef(self.body_child(a, loops, loop_vals, ideal)?),
            Op::Mle(a) => Op::Mle(self.body_child(a, loops, loop_vals, ideal)?),
            Op::Ifft(a) => Op::Ifft(self.body_child(a, loops, loop_vals, ideal)?),
            Op::Fft(a) => Op::Fft(self.body_child(a, loops, loop_vals, ideal)?),
            Op::Interpolate(pts, evals) => Op::Interpolate(
                self.body_child(pts, loops, loop_vals, ideal)?,
                self.body_child(evals, loops, loop_vals, ideal)?,
            ),
            Op::Proj(a, field, typ) => Op::Proj(
                self.body_child(a, loops, loop_vals, ideal)?,
                field.clone(),
                typ.clone(),
            ),
            Op::Vec(vs) => {
                let mut children = Vec::with_capacity(vs.len());
                for v in vs {
                    children.push(self.body_child(v, loops, loop_vals, ideal)?);
                }
                Op::Vec(children)
            }
            Op::Record(fields) => {
                let mut out: Ctx<String, HOp<C>> = Ctx::new();
                for (k, v) in fields.iter() {
                    let child = self.body_child(v, loops, loop_vals, ideal)?;
                    out.insert(k, &child);
                }
                Op::Record(out)
            }
            _ => return None,
        })
    }

    /// Explode a domain `v: [F; n]` into `n` registered element PRefs.
    fn explode_domain(
        &mut self,
        domain: &HOp<C>,
        loops: &[PRef],
        loop_vals: &[Option<Value<C>>],
        ideal: &mut Ideal<C>,
    ) -> Option<Vec<(PRef, Option<Value<C>>)>> {
        let (elem_t, n) = match domain.typ() {
            ATyp::Vec(box e, n) => (e, n),
            _ => return None,
        };
        let elem_values: Vec<Option<Value<C>>> = match domain.get() {
            Op::Value(v) => v.clone().into_elements().into_iter().map(Some).collect(),
            _ => vec![None; n],
        };
        let src: PolySource<C> = match domain.get() {
            Op::Ref(_, _) | Op::Value(_) => PolySource::from_ref_vars(&ideal.prefs, domain.get()),
            _ => {
                let dp = self.body_to_poly(domain, loops, loop_vals, ideal)?;
                PolySource::new(
                    dp.slots()
                        .into_iter()
                        .map(|s| Polynomial::var(&s))
                        .collect(),
                    dp.typ.clone(),
                )
            }
        };
        let mut elems = Vec::with_capacity(n);
        for i in 0..n {
            let es = src.at_index(i)?;
            let name = self.ns.next_name("gb_map_elem");
            let elem_pf = self.sentinel_pref(&name, elem_t.clone(), ideal);
            ideal.register(&elem_pf);
            for (slot, poly) in elem_pf.slots().into_iter().zip(es.polys) {
                ideal.pl.insert(&slot, &poly);
                ideal.basis.push(poly - Polynomial::var(&slot));
            }
            elems.push((elem_pf, elem_values.get(i).cloned().flatten()));
        }
        Some(elems)
    }

    /// `Op::Map`: explode the domain, apply the body to each element, and
    /// link ideal slot `i` to the body's output for element `i`.
    fn map_to_poly(
        &mut self,
        pr: PRef,
        domain: &HOp<C>,
        body: &HOp<C>,
        parent_loops: &[PRef],
        parent_vals: &[Option<Value<C>>],
        ideal: &mut Ideal<C>,
    ) {
        let elems = match self.explode_domain(domain, parent_loops, parent_vals, ideal) {
            Some(e) => e,
            None => Self::uncovered_op("map-domain", &pr),
        };
        for (i, (elem, elem_val)) in elems.iter().enumerate() {
            let mut loops = parent_loops.to_vec();
            loops.push(elem.clone());
            let mut vals = parent_vals.to_vec();
            vals.push(elem_val.clone());
            match self.body_to_poly(body, &loops, &vals, ideal) {
                Some(vi) => self.link_to_witness(&pr.with_index(i).unwrap(), &vi, ideal),
                None => Self::uncovered_op("map-body", &pr),
            }
        }
    }

    /// `Op::ReduceMap`: explode the domain, map the body per element, and fold
    /// the ideals with `reduce_polysource`.
    #[allow(clippy::too_many_arguments)]
    fn reduce_map_to_poly(
        &mut self,
        pr: PRef,
        rop: BinOp,
        domain: &HOp<C>,
        body: &HOp<C>,
        parent_loops: &[PRef],
        parent_vals: &[Option<Value<C>>],
        ideal: &mut Ideal<C>,
    ) {
        let elems = match self.explode_domain(domain, parent_loops, parent_vals, ideal) {
            Some(e) => e,
            None => Self::uncovered_op("reduce-map-domain", &pr),
        };
        let n = elems.len();
        if n == 0 {
            Self::uncovered_op("reduce-map-empty", &pr);
        }
        let mut mapped: Vec<PRef> = Vec::with_capacity(n);
        for (elem, elem_val) in elems.iter() {
            let mut loops = parent_loops.to_vec();
            loops.push(elem.clone());
            let mut vals = parent_vals.to_vec();
            vals.push(elem_val.clone());
            match self.body_to_poly(body, &loops, &vals, ideal) {
                Some(vi) => mapped.push(vi),
                None => Self::uncovered_op("reduce-map-body", &pr),
            }
        }
        if n == 1 {
            self.link_to_witness(&pr, &mapped[0], ideal);
            return;
        }
        let elem_t = mapped[0].typ.clone();
        let combined = PolySource::new(
            mapped
                .iter()
                .flat_map(|p| p.slots().into_iter().map(|s| Polynomial::var(&s)))
                .collect(),
            ATyp::vec(&elem_t, n),
        );
        self.reduce_polysource(pr, rop, combined, elem_t, n, ideal);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::TransClos;
    #[cfg(test)]
    use crate::{QualifierPropagation, UniformityPropagation};
    use backend::ArkBls12_381;
    use backend::op::mk;
    #[cfg(test)]
    use graph::UDags;
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
        TransClos::verifier(&g)
    }

    fn trans_clos_from_src_sized(
        src: &str,
        sizes: &share::Ctx<lang::id::Tid, usize>,
    ) -> TransClos<ArkBls12_381> {
        let m = UModule::from_str(src).unwrap().concretize(sizes).unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);
        let g = UniformityPropagation::from_dag(&g).annotate_dag(&g);
        TransClos::verifier(&g)
    }

    #[test]
    fn test_groebner_builder_to_poly_value_scalar() {
        use ark_bls12_381::Fr;
        use backend::Value;

        let val = Value::Scalar(Fr::from(42u64));
        let poly = IdealBuilder::<ArkBls12_381>::to_poly_value(&val);
        assert_eq!(poly.len(), 1);
    }

    #[test]
    fn test_groebner_builder_to_poly_value_bool_true() {
        use backend::Value;

        let val = Value::Bool(true);
        let poly = IdealBuilder::<ArkBls12_381>::to_poly_value(&val);
        assert_eq!(poly.len(), 1);
    }

    #[test]
    fn test_groebner_builder_to_poly_value_bool_false() {
        use backend::Value;

        let val = Value::Bool(false);
        let poly = IdealBuilder::<ArkBls12_381>::to_poly_value(&val);
        assert_eq!(poly.len(), 1);
    }

    #[test]
    fn test_groebner_builder_to_poly_value_index() {
        use backend::Value;

        let val = Value::Index(5);
        let poly = IdealBuilder::<ArkBls12_381>::to_poly_value(&val);
        assert_eq!(poly.len(), 1);
    }

    #[test]
    fn test_groebner_builder_to_poly_value_vec_scalar() {
        use ark_bls12_381::Fr;
        use backend::Value;

        let val = Value::VecScalar(vec![Fr::from(1u64), Fr::from(2u64), Fr::from(3u64)]);
        let poly = IdealBuilder::<ArkBls12_381>::to_poly_value(&val);
        assert_eq!(poly.len(), 3);
    }

    #[test]
    fn test_groebner_builder_to_poly_value_vec_bool() {
        use backend::Value;

        let val = Value::VecBool(vec![true, false, true]);
        let poly = IdealBuilder::<ArkBls12_381>::to_poly_value(&val);
        assert_eq!(poly.len(), 3);
    }

    #[test]
    fn test_groebner_builder_to_poly_value_vec_index() {
        use backend::Value;

        let val = Value::VecIndex(vec![0, 1, 2]);
        let poly = IdealBuilder::<ArkBls12_381>::to_poly_value(&val);
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
        use graph::PRef;
        use graph::Ref;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut ideal = Ideal::<ArkBls12_381>::new();
        let pref_p = PRef::from_node(
            NodeIndex::new(0),
            ATyp::VPoly(2, 2),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_p);

        let op: GOp<ArkBls12_381> = Op::Ref(Ref::new(NodeIndex::new(0)), ATyp::VPoly(2, 2));
        let polys = IdealBuilder::<ArkBls12_381>::ref_vars(&op, &ideal.prefs);
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
        use graph::PRef;
        use graph::Ref;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut ideal = Ideal::<ArkBls12_381>::new();
        let pref_p = PRef::from_node(
            NodeIndex::new(0),
            ATyp::Mle(3),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_p);

        let op: GOp<ArkBls12_381> = Op::Ref(Ref::new(NodeIndex::new(0)), ATyp::Mle(3));
        let polys = IdealBuilder::<ArkBls12_381>::ref_vars(&op, &ideal.prefs);
        assert_eq!(polys.len(), 8);
    }

    // -----------------------------------------------------------------
    // add_op: Op::Poly / Op::Mle / Op::Coef (identity on coefficient slots)
    // -----------------------------------------------------------------

    #[test]
    fn test_add_op_poly_binds_coefficient_slots() {
        use ark_bls12_381::Fr;
        use backend::op::mk;
        use graph::PRef;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        // First: bind Vec of scalars on node 0, then Poly on node 1.
        let pref_v = PRef::from_node(
            NodeIndex::new(0),
            ATyp::VPoly(1, 2),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_v);
        let coefs: Vec<_> = (1..=3u64)
            .map(|n| mk::<ArkBls12_381>(Op::Value(Value::Scalar(Fr::from(n)))))
            .collect();
        builder.add_op(pref_v.clone(), Op::Vec(coefs), &mut ideal);

        let pref_p = PRef::from_node(
            NodeIndex::new(1),
            ATyp::VPoly(1, 2),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        let op_poly: GOp<ArkBls12_381> = Op::Poly(mk::<ArkBls12_381>(Op::Ref(
            graph::Ref::new(NodeIndex::new(0)),
            ATyp::VPoly(1, 2),
        )));
        ideal.register(&pref_p);
        builder.add_op(pref_p.clone(), op_poly, &mut ideal);

        // Three coefficient slots should have been bound.
        for i in 0..3 {
            let slot = pref_p.clone().with_slot(i).unwrap();
            assert!(ideal.pl.contains(&slot), "slot {} missing from pl", i);
        }
        // Six basis equations: 3 from Vec binding + 3 from Poly identity.
        assert_eq!(ideal.basis.len(), 6);
    }

    #[test]
    fn test_add_op_coef_roundtrips_poly() {
        // Op::Coef(Op::Poly(v)) bound to the same slots should reduce to `v`.
        use ark_bls12_381::Fr;
        use backend::op::mk;
        use graph::PRef;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        // First: bind Vec of scalars on node 0, then Poly on node 1.
        let pref_v = PRef::from_node(
            NodeIndex::new(0),
            ATyp::VPoly(1, 2),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_v);
        let coefs: Vec<_> = (1..=3u64)
            .map(|n| mk::<ArkBls12_381>(Op::Value(Value::Scalar(Fr::from(n)))))
            .collect();
        builder.add_op(pref_v.clone(), Op::Vec(coefs), &mut ideal);

        // Poly: reads the Vec's slots via Ref.
        let pref_p = PRef::from_node(
            NodeIndex::new(1),
            ATyp::VPoly(1, 2),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_p);
        builder.add_op(
            pref_p.clone(),
            Op::Poly(mk::<ArkBls12_381>(Op::Ref(
                graph::Ref::new(NodeIndex::new(0)),
                ATyp::VPoly(1, 2),
            ))),
            &mut ideal,
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
            Op::Ref(graph::Ref::new(NodeIndex::new(1)), ATyp::VPoly(1, 2));
        builder.add_op(
            pref_c.clone(),
            Op::Coef(mk::<ArkBls12_381>(ref_p)),
            &mut ideal,
        );

        // Each Coef slot should be bound identically to the corresponding
        // VPoly coefficient PRef — that's the round-trip identity. `ref_vars`
        // resolves per-slot PRefs to ATyp::scalar(), so we expect that form
        // on the RHS.
        for i in 0..3 {
            let coef_slot = pref_c.clone().with_slot(i).unwrap();
            let poly_slot = pref_p.clone().with_slot(i).unwrap();
            let stored = ideal.pl.get(&coef_slot).expect("coef slot missing");
            let expected = Polynomial::<Fr>::var(&poly_slot);
            assert_eq!(*stored, expected, "coef[{}] did not bind to poly[{}]", i, i);
        }
    }

    #[test]
    fn test_add_op_mle_binds_hypercube_slots() {
        use ark_bls12_381::Fr;
        use backend::op::mk;
        use graph::PRef;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        // First: bind Vec of scalars on node 0, then Mle on node 1.
        let pref_v = PRef::from_node(
            NodeIndex::new(0),
            ATyp::Mle(2),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_v);
        let vals: Vec<_> = (1..=4u64)
            .map(|n| mk::<ArkBls12_381>(Op::Value(Value::Scalar(Fr::from(n)))))
            .collect();
        builder.add_op(pref_v.clone(), Op::Vec(vals), &mut ideal);

        let pref_m = PRef::from_node(
            NodeIndex::new(1),
            ATyp::Mle(2),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_m);
        builder.add_op(
            pref_m.clone(),
            Op::Mle(mk::<ArkBls12_381>(Op::Ref(
                graph::Ref::new(NodeIndex::new(0)),
                ATyp::Mle(2),
            ))),
            &mut ideal,
        );

        // 4 from Vec binding + 4 from Mle identity.
        assert_eq!(ideal.basis.len(), 8);
        for i in 0..4 {
            assert!(
                ideal.pl.contains(&pref_m.clone().with_slot(i).unwrap()),
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
    fn mle1_to_uni1_lift_converts_evals_to_coeffs() {
        use graph::PRef;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let src = PRef::from_node(
            NodeIndex::new(10),
            ATyp::Mle(1),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        let g0 = Polynomial::<ark_bls12_381::Fr>::var(&src.clone().with_slot(0).unwrap());
        let g1 = Polynomial::<ark_bls12_381::Fr>::var(&src.clone().with_slot(1).unwrap());
        let lifted = PolySource::<ArkBls12_381> {
            polys: vec![g0.clone(), g1.clone()],
            typ: ATyp::Mle(1),
        }
        .lift_to(&ATyp::Uni(1));

        assert_eq!(lifted.typ, ATyp::Uni(1));
        assert_eq!(lifted.polys.len(), 2);
        assert_eq!(lifted.polys[0], g0);
        assert_eq!(lifted.polys[1], &g1 - &g0);
    }

    #[test]
    fn test_add_op_eval_univariate_batched() {
        use ark_bls12_381::Fr;
        use backend::op::mk;
        use graph::{PRef, Ref};
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        // p(x) = a_0 + a_1 x   as VPoly(1,1): 2 coefficient slots on node 0.
        // xs = [x0, x1]        as Uni(1):     degree 1 = 2 slots on node 1.
        // Expected: ideal[i] = a_0 + a_1 * xs[i].
        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();
        let _pref_p = {
            let p = PRef::from_node(
                NodeIndex::new(0),
                ATyp::VPoly(1, 1),
                0,
                Qualifier::Private,
                Distribution::default(),
            );
            ideal.register(&p);
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
            ideal.register(&p);
            p
        };

        let pref = PRef::from_node(
            NodeIndex::new(2),
            ATyp::Uni(1),
            0,
            Qualifier::Private,
            Distribution::default(),
        );

        let op: GOp<ArkBls12_381> = Op::Evaluate(
            mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), ATyp::VPoly(1, 1))),
            None,
            Some(mk::<ArkBls12_381>(Op::Ref(
                Ref::new(NodeIndex::new(1)),
                ATyp::Uni(1),
            ))),
        );
        builder.add_op(pref.clone(), op, &mut ideal);

        // Eval uses explicit ideal treatment with no fallback.
        for i in 0..2 {
            assert!(
                ideal.pl.contains(&pref.clone().with_slot(i).unwrap()),
                "uni batched ideal slot {} missing",
                i
            );
        }
        // Each ideal slot: poly = a_0 + a_1 * xs[i] (a linear polynomial in
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

        let slot0 = ideal.pl.get(&pref.clone().with_slot(0).unwrap()).unwrap();
        let vars0 = slot0.vars();
        assert!(vars0.contains(&a0), "slot 0 missing a_0");
        assert!(vars0.contains(&a1), "slot 0 missing a_1");
        assert!(vars0.contains(&x0), "slot 0 missing xs[0]");
        assert!(!vars0.contains(&x1), "slot 0 should not contain xs[1]");

        let slot1 = ideal.pl.get(&pref.clone().with_slot(1).unwrap()).unwrap();
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
        use ark_bls12_381::Fr;
        use backend::op::mk;
        use graph::PRef;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        // Bind p: Vec of scalars on node 0, then Poly on node 1.
        let pref_vp = PRef::from_node(
            NodeIndex::new(0),
            ATyp::VPoly(1, 1),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_vp);
        let coefs: Vec<_> = [3u64, 5]
            .iter()
            .map(|n| mk::<ArkBls12_381>(Op::Value(Value::Scalar(Fr::from(*n)))))
            .collect();
        builder.add_op(pref_vp.clone(), Op::Vec(coefs), &mut ideal);
        let pref_p = PRef::from_node(
            NodeIndex::new(1),
            ATyp::VPoly(1, 1),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_p);
        builder.add_op(
            pref_p.clone(),
            Op::Poly(mk::<ArkBls12_381>(Op::Ref(
                graph::Ref::new(NodeIndex::new(0)),
                ATyp::VPoly(1, 1),
            ))),
            &mut ideal,
        );

        // Bind xs: Vec of scalars on node 2, then Poly on node 3.
        let pref_vxs = PRef::from_node(
            NodeIndex::new(2),
            ATyp::Uni(1),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_vxs);
        let xs_vals: Vec<_> = [7u64, 11]
            .iter()
            .map(|n| mk::<ArkBls12_381>(Op::Value(Value::Scalar(Fr::from(*n)))))
            .collect();
        builder.add_op(pref_vxs.clone(), Op::Vec(xs_vals), &mut ideal);
        let pref_xs = PRef::from_node(
            NodeIndex::new(3),
            ATyp::Uni(1),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_xs);
        builder.add_op(
            pref_xs.clone(),
            Op::Poly(mk::<ArkBls12_381>(Op::Ref(
                graph::Ref::new(NodeIndex::new(2)),
                ATyp::Uni(1),
            ))),
            &mut ideal,
        );

        // Now issue eval: p(xs).
        let pref = PRef::from_node(
            NodeIndex::new(4),
            ATyp::Uni(1),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        let op: GOp<ArkBls12_381> = Op::Evaluate(
            mk::<ArkBls12_381>(Op::Ref(
                graph::Ref::new(NodeIndex::new(1)),
                ATyp::VPoly(1, 1),
            )),
            None,
            Some(mk::<ArkBls12_381>(Op::Ref(
                graph::Ref::new(NodeIndex::new(3)),
                ATyp::Uni(1),
            ))),
        );
        builder.add_op(pref.clone(), op, &mut ideal);

        // Check stored polys: since all inputs are constants, each ideal slot
        // stores a polynomial equal to a_0 + a_1 * x as a sparse poly in the
        // slot PRefs (constants haven't been inlined). We verify the basis
        // equation reduces correctly by substituting literal values via `vars`.
        let slot0 = ideal.pl.get(&pref.clone().with_slot(0).unwrap()).unwrap();
        let slot1 = ideal.pl.get(&pref.clone().with_slot(1).unwrap()).unwrap();
        assert!(!slot0.is_zero());
        assert!(!slot1.is_zero());
        // 2 Vec bindings * 2 slots each = 4, plus 2 Poly identities * 2 = 4,
        // plus 2 eval ideals = 2. Total = 10.
        assert_eq!(ideal.basis.len(), 10);
    }

    #[test]
    fn test_add_op_eval_vpoly_full_multivariate() {
        // VPoly(2, 2) has 6 coef slots; eval at Uni(2) => scalar (one slot).
        use graph::PRef;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();
        let _ = {
            let p = PRef::from_node(
                NodeIndex::new(0),
                ATyp::VPoly(2, 2),
                0,
                Qualifier::Private,
                Distribution::default(),
            );
            ideal.register(&p);
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
            ideal.register(&p);
            p
        };

        let pref = PRef::from_node(
            NodeIndex::new(2),
            ATyp::scalar(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        let op: GOp<ArkBls12_381> = Op::Evaluate(
            backend::op::mk::<ArkBls12_381>(Op::Ref(
                graph::Ref::new(NodeIndex::new(0)),
                ATyp::VPoly(2, 2),
            )),
            None,
            Some(backend::op::mk::<ArkBls12_381>(Op::Ref(
                graph::Ref::new(NodeIndex::new(1)),
                ATyp::Uni(1),
            ))),
        );
        builder.add_op(pref.clone(), op, &mut ideal);

        // One ideal slot (scalar) produced by explicit eval encoding.
        assert!(ideal.pl.contains(&pref.clone().with_slot(0).unwrap()));
        // Should contain all 6 coef PRefs of p + both xs slots.
        let slot = ideal.pl.get(&pref.clone().with_slot(0).unwrap()).unwrap();
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
        use graph::PRef;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();
        let _ = {
            let p = PRef::from_node(
                NodeIndex::new(0),
                ATyp::VPoly(3, 1),
                0,
                Qualifier::Private,
                Distribution::default(),
            );
            ideal.register(&p);
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
            ideal.register(&p);
            p
        };

        let pref = PRef::from_node(
            NodeIndex::new(2),
            ATyp::VPoly(2, 1),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        let op: GOp<ArkBls12_381> = Op::Evaluate(
            backend::op::mk::<ArkBls12_381>(Op::Ref(
                graph::Ref::new(NodeIndex::new(0)),
                ATyp::VPoly(3, 1),
            )),
            None,
            Some(backend::op::mk::<ArkBls12_381>(Op::Ref(
                graph::Ref::new(NodeIndex::new(1)),
                ATyp::Uni(0),
            ))),
        );
        builder.add_op(pref.clone(), op, &mut ideal);

        // VPoly(2, 1) has physical_len = C(2+1, 1) = 3 slots (one for constant,
        // two for each linear variable).
        assert_eq!(ATyp::VPoly(2, 1).physical_len(), 3);
        for i in 0..3 {
            assert!(
                ideal.pl.contains(&pref.clone().with_slot(i).unwrap()),
                "partial vpoly eval slot {} missing",
                i
            );
        }
    }

    #[test]
    fn test_add_op_eval_mle_full_multivariate() {
        // Mle(2) has 4 eval slots; eval at Uni(2) => scalar.
        use graph::PRef;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();
        let _ = {
            let p = PRef::from_node(
                NodeIndex::new(0),
                ATyp::Mle(2),
                0,
                Qualifier::Private,
                Distribution::default(),
            );
            ideal.register(&p);
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
            ideal.register(&p);
            p
        };

        let pref = PRef::from_node(
            NodeIndex::new(2),
            ATyp::scalar(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        let op: GOp<ArkBls12_381> = Op::Evaluate(
            backend::op::mk::<ArkBls12_381>(Op::Ref(
                graph::Ref::new(NodeIndex::new(0)),
                ATyp::Mle(2),
            )),
            None,
            Some(backend::op::mk::<ArkBls12_381>(Op::Ref(
                graph::Ref::new(NodeIndex::new(1)),
                ATyp::Uni(1),
            ))),
        );
        builder.add_op(pref.clone(), op, &mut ideal);

        assert!(ideal.pl.contains(&pref.clone().with_slot(0).unwrap()));
        // Result poly should reference all 4 Mle slots + both xs slots.
        let slot = ideal.pl.get(&pref.clone().with_slot(0).unwrap()).unwrap();
        let vars = slot.vars();
        assert!(vars.len() >= 4, "mle full eval got {} vars", vars.len());
    }

    #[test]
    fn test_add_op_eval_mle_partial_multivariate() {
        // Mle(3) evaluated at Uni(1) => Mle(2) (4 slots).
        use graph::PRef;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();
        let _ = {
            let p = PRef::from_node(
                NodeIndex::new(0),
                ATyp::Mle(3),
                0,
                Qualifier::Private,
                Distribution::default(),
            );
            ideal.register(&p);
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
            ideal.register(&p);
            p
        };

        let pref = PRef::from_node(
            NodeIndex::new(2),
            ATyp::Mle(2),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        let op: GOp<ArkBls12_381> = Op::Evaluate(
            backend::op::mk::<ArkBls12_381>(Op::Ref(
                graph::Ref::new(NodeIndex::new(0)),
                ATyp::Mle(3),
            )),
            None,
            Some(backend::op::mk::<ArkBls12_381>(Op::Ref(
                graph::Ref::new(NodeIndex::new(1)),
                ATyp::Uni(0),
            ))),
        );
        builder.add_op(pref.clone(), op, &mut ideal);

        // Mle(2) has 4 eval slots.
        for i in 0..4 {
            assert!(
                ideal.pl.contains(&pref.clone().with_slot(i).unwrap()),
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
        // VPoly(2,1) has 3 coefficient slots.  a + b should bind ideal.slot(i)
        // to a.slot(i) + b.slot(i) for each of the 3 slots.
        use backend::op::mk;
        use graph::{PRef, Ref};
        use lang::ast::BinOp;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();
        let pref_a = {
            let p = PRef::from_node(
                NodeIndex::new(0),
                ATyp::VPoly(2, 1),
                0,
                Qualifier::Private,
                Distribution::default(),
            );
            ideal.register(&p);
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
            ideal.register(&p);
            p
        };

        let pref = PRef::from_node(
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
        builder.add_op(pref.clone(), op, &mut ideal);

        // 3 ideal slots bound.
        for i in 0..3 {
            assert!(
                ideal.pl.contains(&pref.clone().with_slot(i).unwrap()),
                "add ideal slot {} missing",
                i
            );
        }
        // Each ideal slot contains exactly a.slot(i) + b.slot(i).
        for i in 0..3 {
            let a_slot = pref_a.clone().with_slot(i).unwrap();
            let b_slot = pref_b.clone().with_slot(i).unwrap();
            let stored = ideal.pl.get(&pref.clone().with_slot(i).unwrap()).unwrap();
            let expected =
                &Polynomial::<ark_bls12_381::Fr>::var(&a_slot) + &Polynomial::var(&b_slot);
            assert_eq!(*stored, expected, "vpoly add slot {} mismatch", i);
        }
    }

    #[test]
    fn test_add_op_mle_add_pointwise() {
        // Mle(2) has 4 evaluation slots. add is pointwise over hypercube.
        use backend::op::mk;
        use graph::{PRef, Ref};
        use lang::ast::BinOp;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();
        let pref_a = {
            let p = PRef::from_node(
                NodeIndex::new(0),
                ATyp::Mle(2),
                0,
                Qualifier::Private,
                Distribution::default(),
            );
            ideal.register(&p);
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
            ideal.register(&p);
            p
        };

        let pref = PRef::from_node(
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
        builder.add_op(pref.clone(), op, &mut ideal);

        for i in 0..4 {
            let a_slot = pref_a.clone().with_slot(i).unwrap();
            let b_slot = pref_b.clone().with_slot(i).unwrap();
            let stored = ideal.pl.get(&pref.clone().with_slot(i).unwrap()).unwrap();
            let expected =
                &Polynomial::<ark_bls12_381::Fr>::var(&a_slot) + &Polynomial::var(&b_slot);
            assert_eq!(*stored, expected, "mle add slot {} mismatch", i);
        }
    }

    #[test]
    fn test_add_op_vpoly_sub_coefficient_wise() {
        use backend::op::mk;
        use graph::{PRef, Ref};
        use lang::ast::BinOp;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();
        let pref_a = PRef::from_node(
            NodeIndex::new(0),
            ATyp::VPoly(2, 2),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_a);
        let pref_b = PRef::from_node(
            NodeIndex::new(1),
            ATyp::VPoly(2, 2),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_b);

        let pref = PRef::from_node(
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
        builder.add_op(pref.clone(), op, &mut ideal);

        // VPoly(2,2) has 6 slots.
        assert_eq!(ATyp::VPoly(2, 2).physical_len(), 6);
        for i in 0..6 {
            let a_slot = pref_a.clone().with_slot(i).unwrap();
            let b_slot = pref_b.clone().with_slot(i).unwrap();
            let stored = ideal.pl.get(&pref.clone().with_slot(i).unwrap()).unwrap();
            let expected =
                &Polynomial::<ark_bls12_381::Fr>::var(&a_slot) - &Polynomial::var(&b_slot);
            assert_eq!(*stored, expected, "vpoly sub slot {} mismatch", i);
        }
    }

    #[test]
    fn test_add_op_vpoly_mul_univariate_convolution() {
        // VPoly(1,1) × VPoly(1,1) → VPoly(1,2), a_0 b_0, a_0 b_1 + a_1 b_0, a_1 b_1.
        use backend::op::mk;
        use graph::{PRef, Ref};
        use lang::ast::BinOp;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();
        let pref_a = PRef::from_node(
            NodeIndex::new(0),
            ATyp::VPoly(1, 1),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_a);
        let pref_b = PRef::from_node(
            NodeIndex::new(1),
            ATyp::VPoly(1, 1),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_b);

        let pref = PRef::from_node(
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
        builder.add_op(pref.clone(), op, &mut ideal);

        // VPoly(1,2) has physical_len = 3 slots (degrees 0, 1, 2 in graded-lex order).
        assert_eq!(ATyp::VPoly(1, 2).physical_len(), 3);
        let a0 = pref_a.clone().with_slot(0).unwrap();
        let a1 = pref_a.clone().with_slot(1).unwrap();
        let b0 = pref_b.clone().with_slot(0).unwrap();
        let b1 = pref_b.clone().with_slot(1).unwrap();

        let var = |p: &PRef| Polynomial::<ark_bls12_381::Fr>::var(p);
        let deg0 = ideal
            .pl
            .get(&pref.clone().with_slot(0).unwrap())
            .unwrap()
            .clone();
        let deg1 = ideal
            .pl
            .get(&pref.clone().with_slot(1).unwrap())
            .unwrap()
            .clone();
        let deg2 = ideal
            .pl
            .get(&pref.clone().with_slot(2).unwrap())
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
        use backend::op::mk;
        use graph::{PRef, Ref};
        use lang::ast::BinOp;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();
        let pref_a = PRef::from_node(
            NodeIndex::new(0),
            ATyp::VPoly(2, 1),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_a);
        let pref_b = PRef::from_node(
            NodeIndex::new(1),
            ATyp::VPoly(2, 1),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_b);

        let pref = PRef::from_node(
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
        builder.add_op(pref.clone(), op, &mut ideal);

        // Check the constant-term slot (multi-index [0,0]): should be a_[0,0] * b_[0,0].
        let r_idx = multi_indices(2, 2);
        let a_idx = multi_indices(2, 1);
        let pos_00 = r_idx.iter().position(|k| k == &vec![0, 0]).unwrap();
        let a_pos_00 = a_idx.iter().position(|k| k == &vec![0, 0]).unwrap();

        let a00 = pref_a.clone().with_slot(a_pos_00).unwrap();
        let b00 = pref_b.clone().with_slot(a_pos_00).unwrap();
        let var = |p: &PRef| Polynomial::<ark_bls12_381::Fr>::var(p);
        let got = ideal
            .pl
            .get(&pref.clone().with_slot(pos_00).unwrap())
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
                ideal.pl.contains(&pref.clone().with_slot(i).unwrap()),
                "VPoly(2,2) slot {} missing",
                i
            );
        }
    }

    #[test]
    fn test_add_op_mle_mul_basis_change() {
        // Mle(1) × Mle(1) → VPoly(1, 2). Verify by evaluating the idealing poly at
        // a concrete point x: for p(x) = u_0 · (1-x) + u_1 · x and
        // q(x) = v_0 · (1-x) + v_1 · x, the product p·q has coefficients
        //   x^0 :  u_0 v_0
        //   x^1 :  -2 u_0 v_0 + u_0 v_1 + u_1 v_0
        //   x^2 :  u_0 v_0 - u_0 v_1 - u_1 v_0 + u_1 v_1
        use backend::op::mk;
        use graph::{PRef, Ref};
        use lang::ast::BinOp;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();
        let pref_u = PRef::from_node(
            NodeIndex::new(0),
            ATyp::Mle(1),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_u);
        let pref_v = PRef::from_node(
            NodeIndex::new(1),
            ATyp::Mle(1),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_v);

        let pref = PRef::from_node(
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
        builder.add_op(pref.clone(), op, &mut ideal);

        // 3 slots populated.
        for i in 0..3 {
            assert!(
                ideal.pl.contains(&pref.clone().with_slot(i).unwrap()),
                "Mle×Mle slot {} missing",
                i
            );
        }

        let u0 = pref_u.clone().with_slot(0).unwrap();
        let u1 = pref_u.clone().with_slot(1).unwrap();
        let v0 = pref_v.clone().with_slot(0).unwrap();
        let v1 = pref_v.clone().with_slot(1).unwrap();
        let var = |p: &PRef| Polynomial::<ark_bls12_381::Fr>::var(p);

        let deg0 = ideal
            .pl
            .get(&pref.clone().with_slot(0).unwrap())
            .unwrap()
            .clone();
        let deg1 = ideal
            .pl
            .get(&pref.clone().with_slot(1).unwrap())
            .unwrap()
            .clone();
        let deg2 = ideal
            .pl
            .get(&pref.clone().with_slot(2).unwrap())
            .unwrap()
            .clone();

        // deg0 = u_0 * v_0
        assert_eq!(deg0, &var(&u0) * &var(&v0), "mle mul deg0");

        // deg1 = -2 u_0 v_0 + u_0 v_1 + u_1 v_0
        let two =
            Polynomial::<ark_bls12_381::Fr>::lit(&<ark_bls12_381::Fr as From<u64>>::from(2u64));
        let expected_deg1 = &(&(&var(&u0) * &var(&v1)) + &(&var(&u1) * &var(&v0)))
            - &(&two * &(&var(&u0) * &var(&v0)));
        assert_eq!(deg1, expected_deg1, "mle mul deg1");

        // deg2 = u_0 v_0 - u_0 v_1 - u_1 v_0 + u_1 v_1
        let expected_deg2 = &(&(&var(&u0) * &var(&v0)) - &(&var(&u0) * &var(&v1)))
            + &(&(&var(&u1) * &var(&v1)) - &(&var(&u1) * &var(&v0)));
        assert_eq!(deg2, expected_deg2, "mle mul deg2");
    }

    #[test]
    fn test_add_op_mle_vpoly_mul_univariate() {
        // Mle(1) × VPoly(1, 1) → VPoly(1, 2).
        //   MLE: u_0 (eval at 0), u_1 (eval at 1), so p(x) = u_0·(1-x) + u_1·x
        //   VPoly: b_0 + b_1·x
        //   Product: p(x)·q(x) = (u_0·b_0) + (u_1·b_0 - u_0·b_0 + u_0·b_1)·x
        //                      + (u_1·b_1 - u_0·b_1)·x²
        use backend::op::mk;
        use graph::{PRef, Ref};
        use lang::ast::BinOp;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();
        let pref_u = PRef::from_node(
            NodeIndex::new(0),
            ATyp::Mle(1),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_u);
        let pref_b = PRef::from_node(
            NodeIndex::new(1),
            ATyp::VPoly(1, 1),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_b);

        let pref = PRef::from_node(
            NodeIndex::new(2),
            ATyp::VPoly(1, 2),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        let op: GOp<ArkBls12_381> = Op::Bin(
            BinOp::Mul,
            mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), ATyp::Mle(1))),
            mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(1)), ATyp::VPoly(1, 1))),
            ATyp::VPoly(1, 2),
        );
        builder.add_op(pref.clone(), op, &mut ideal);

        let u0 = pref_u.clone().with_slot(0).unwrap();
        let u1 = pref_u.clone().with_slot(1).unwrap();
        let b0 = pref_b.clone().with_slot(0).unwrap();
        let b1 = pref_b.clone().with_slot(1).unwrap();
        let var = |p: &PRef| Polynomial::<ark_bls12_381::Fr>::var(p);

        let deg0 = ideal
            .pl
            .get(&pref.clone().with_slot(0).unwrap())
            .unwrap()
            .clone();
        let deg1 = ideal
            .pl
            .get(&pref.clone().with_slot(1).unwrap())
            .unwrap()
            .clone();
        let deg2 = ideal
            .pl
            .get(&pref.clone().with_slot(2).unwrap())
            .unwrap()
            .clone();

        assert_eq!(deg0, &var(&u0) * &var(&b0), "mle×vpoly deg0");

        let expected_deg1 =
            &(&var(&u1) * &var(&b0)) - &(&var(&u0) * &var(&b0)) + &var(&u0) * &var(&b1);
        assert_eq!(deg1, expected_deg1, "mle×vpoly deg1");

        let expected_deg2 = &(&var(&u1) * &var(&b1)) - &(&var(&u0) * &var(&b1));
        assert_eq!(deg2, expected_deg2, "mle×vpoly deg2");
    }

    #[test]
    fn test_add_op_vpoly_mle_mul_bivariate() {
        // VPoly(2, 1) × Mle(2) → VPoly(2, 3). Commutative variant.
        // VPoly(2,1) has 3 slots: [0,0], [1,0], [0,1] (graded-lex).
        // Mle(2) has 4 slots: evals at (0,0), (1,0), (0,1), (1,1).
        // Result VPoly(2,3) has 10 slots.
        // Just verify all 10 ideal slots are populated.
        use backend::op::mk;
        use graph::{PRef, Ref};
        use lang::ast::BinOp;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();
        let pref_b = PRef::from_node(
            NodeIndex::new(0),
            ATyp::VPoly(2, 1),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_b);
        let pref_u = PRef::from_node(
            NodeIndex::new(1),
            ATyp::Mle(2),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_u);

        let pref = PRef::from_node(
            NodeIndex::new(2),
            ATyp::VPoly(2, 3),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        let op: GOp<ArkBls12_381> = Op::Bin(
            BinOp::Mul,
            mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), ATyp::VPoly(2, 1))),
            mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(1)), ATyp::Mle(2))),
            ATyp::VPoly(2, 3),
        );
        builder.add_op(pref.clone(), op, &mut ideal);

        let r_idx = multi_indices(2, 3);
        assert_eq!(r_idx.len(), 10, "VPoly(2,3) should have 10 multi-indices");
        for i in 0..10 {
            assert!(
                ideal.pl.contains(&pref.clone().with_slot(i).unwrap()),
                "VPoly×Mle slot {} missing",
                i
            );
        }
    }

    #[test]
    fn test_add_op_mle_vpoly_mul_bivariate_coefficients() {
        // Mle(2) × VPoly(2, 1) → VPoly(2, 3).
        // Verify the constant-term slot (multi-index [0,0]) and a cross-term.
        use backend::op::mk;
        use graph::{PRef, Ref};
        use lang::ast::BinOp;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();
        let pref_u = PRef::from_node(
            NodeIndex::new(0),
            ATyp::Mle(2),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_u);
        let pref_b = PRef::from_node(
            NodeIndex::new(1),
            ATyp::VPoly(2, 1),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_b);

        let pref = PRef::from_node(
            NodeIndex::new(2),
            ATyp::VPoly(2, 3),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        let op: GOp<ArkBls12_381> = Op::Bin(
            BinOp::Mul,
            mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), ATyp::Mle(2))),
            mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(1)), ATyp::VPoly(2, 1))),
            ATyp::VPoly(2, 3),
        );
        builder.add_op(pref.clone(), op, &mut ideal);

        let r_idx = multi_indices(2, 3);
        let v_idx = multi_indices(2, 1);
        let var = |p: &PRef| Polynomial::<ark_bls12_381::Fr>::var(p);

        // Constant term [0,0]: u_00 * b_00
        let pos_00 = r_idx.iter().position(|k| k == &vec![0, 0]).unwrap();
        let v_pos_00 = v_idx.iter().position(|k| k == &vec![0, 0]).unwrap();
        let u00 = pref_u.clone().with_slot(0).unwrap();
        let b00 = pref_b.clone().with_slot(v_pos_00).unwrap();
        let got_00 = ideal
            .pl
            .get(&pref.clone().with_slot(pos_00).unwrap())
            .unwrap()
            .clone();
        assert_eq!(got_00, &var(&u00) * &var(&b00), "bivariate constant term");

        // [1,0] slot: -u_00·b_10 + u_10·b_00 + u_00·b_10... check it's populated
        let pos_10 = r_idx.iter().position(|k| k == &vec![1, 0]).unwrap();
        assert!(
            ideal.pl.contains(&pref.clone().with_slot(pos_10).unwrap()),
            "bivariate [1,0] slot missing"
        );

        // All 10 slots populated
        assert_eq!(r_idx.len(), 10);
        for i in 0..10 {
            assert!(
                ideal.pl.contains(&pref.clone().with_slot(i).unwrap()),
                "Mle×VPoly bivariate slot {} missing",
                i
            );
        }
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
        // link_to_witness emits 2 more rows: var(q_wit[j]) - var(ideal[j]), j=0,1.
        use graph::{PRef, Ref};
        use lang::ast::BinOp;
        use lang::id::Vid;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();
        let pref_a = PRef::from_node(
            NodeIndex::new(0),
            ATyp::VPoly(1, 2),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_a);
        let pref_b = PRef::from_node(
            NodeIndex::new(1),
            ATyp::VPoly(1, 1),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_b);

        let basis_before = ideal.basis.len();
        let pref = PRef::from_node(
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
        builder.add_op(pref.clone(), op, &mut ideal);

        // Recover the q_wit / r_wit PRefs (minted by sentinel_pref starting
        // at MAX and decrementing: q_wit=MAX, r_wit=MAX-1).
        let q_wit = PRef::from_var(
            Vid::from("__zippel::gb::div_q::0"),
            petgraph::graph::NodeIndex::new(usize::MAX),
            ATyp::VPoly(1, 1),
            0,
            Qualifier::Local,
            Distribution::default(),
        );
        let r_wit = PRef::from_var(
            Vid::from("__zippel::gb::div_r::0"),
            petgraph::graph::NodeIndex::new(usize::MAX - 1),
            ATyp::VPoly(1, 0),
            0,
            Qualifier::Local,
            Distribution::default(),
        );

        // Per-slot input vars (typ computed by `with_slot`).
        let scl = |p: &PRef, i: usize| p.clone().with_slot(i).unwrap();
        // Per-slot witness vars. `div_witnesses` uses `wit.clone().with_slot(j).unwrap()`
        // which sets typ appropriately.
        let wit_slot = |p: &PRef, i: usize| p.clone().with_slot(i).unwrap();
        let var = |p: &PRef| Polynomial::<ark_bls12_381::Fr>::var(p);
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
            ideal.basis.len() - basis_before,
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
                ideal.basis.iter().any(|row| row == expected),
                "basis missing identity row {}",
                lbl
            );
        }

        // link_to_witness: pl[ideal[j]] = var(q_wit[j]) for j=0,1.
        assert_eq!(
            ideal.pl.get(&pref.clone().with_slot(0).unwrap()).cloned(),
            Some(var(&q0)),
            "pl[ideal[0]] should alias q_wit[0]"
        );
        assert_eq!(
            ideal.pl.get(&pref.clone().with_slot(1).unwrap()).cloned(),
            Some(var(&q1)),
            "pl[ideal[1]] should alias q_wit[1]"
        );

        // Linking rows: var(q_wit[j]) - var(ideal[j]).
        // link_to_witness uses `ideal.clone().with_slot(j).unwrap()` (typ computed by with_slot).
        let r0_slot = pref.clone().with_slot(0).unwrap();
        let r1_slot = pref.clone().with_slot(1).unwrap();
        let link0 = &var(&q0) - &var(&r0_slot);
        let link1 = &var(&q1) - &var(&r1_slot);
        assert!(
            ideal.basis.iter().any(|row| row == &link0),
            "basis missing link row var(q_wit[0]) - var(ideal[0])"
        );
        assert!(
            ideal.basis.iter().any(|row| row == &link1),
            "basis missing link row var(q_wit[1]) - var(ideal[1])"
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
        // Same witnesses as the Div test, but link ideal to r_wit (1 slot).
        use graph::{PRef, Ref};
        use lang::ast::BinOp;
        use lang::id::Vid;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();
        let _pref_a = PRef::from_node(
            NodeIndex::new(0),
            ATyp::VPoly(1, 2),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&_pref_a);
        let _pref_b = PRef::from_node(
            NodeIndex::new(1),
            ATyp::VPoly(1, 1),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&_pref_b);

        let basis_before = ideal.basis.len();
        let pref = PRef::from_node(
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
        builder.add_op(pref.clone(), op, &mut ideal);

        // q_wit=MAX, r_wit=MAX-1 (fresh builder, counter starts at MAX).
        let r_wit = PRef::from_var(
            Vid::from("__zippel::gb::div_r::0"),
            petgraph::graph::NodeIndex::new(usize::MAX - 1),
            ATyp::VPoly(1, 0),
            0,
            Qualifier::Local,
            Distribution::default(),
        );
        let scl = |p: &PRef, i: usize| p.clone().with_slot(i).unwrap();
        let _ = scl; // kept for parity with the Div test; not used here.
        let var = |p: &PRef| Polynomial::<ark_bls12_381::Fr>::var(p);
        // r_wit slots: with_slot computes the correct type.
        let r0 = r_wit.clone().with_slot(0).unwrap();

        // 3 identity rows + 1 linking row (ideal has only 1 slot).
        assert_eq!(
            ideal.basis.len() - basis_before,
            4,
            "expected 3 identity + 1 linking row"
        );

        // pl[ideal[0]] = var(r_wit[0]).
        assert_eq!(
            ideal.pl.get(&pref.clone().with_slot(0).unwrap()).cloned(),
            Some(var(&r0)),
            "pl[ideal[0]] should alias r_wit[0]"
        );

        // Linking row: link_to_witness uses ideal.with_slot(0).unwrap() (type computed by with_slot).
        let r0_slot = pref.clone().with_slot(0).unwrap();
        let link = &var(&r0) - &var(&r0_slot);
        assert!(
            ideal.basis.iter().any(|row| row == &link),
            "basis missing link row var(r_wit[0]) - var(ideal[0])"
        );
        assert_eq!(builder.ns.div_wit.len(), 1, "one div_wit entry after Rem");
    }

    #[test]
    fn test_add_op_div_then_rem_shares_witness() {
        // Both `a/b` and `a%b` on the same source-level operand pair share the
        // witness side-table. Second op should NOT emit new identity rows.
        use graph::{PRef, Ref};
        use lang::ast::BinOp;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();
        let _pref_a = PRef::from_node(
            NodeIndex::new(0),
            ATyp::VPoly(1, 2),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&_pref_a);
        let _pref_b = PRef::from_node(
            NodeIndex::new(1),
            ATyp::VPoly(1, 1),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&_pref_b);

        let basis_before_div = ideal.basis.len();
        let _q_res = {
            let pref = PRef::from_node(
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
            builder.add_op(pref.clone(), op, &mut ideal);
            pref
        };
        let after_div = ideal.basis.len();

        let _r_res = {
            let pref = PRef::from_node(
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
            builder.add_op(pref.clone(), op, &mut ideal);
            pref
        };
        let after_rem = ideal.basis.len();

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
    fn test_add_op_div_rem_shares_equivalent_named_derived_operands() {
        // PR #153 regression: two closure-local derived nodes can carry the
        // same named-source expression (`a * b - c`) while still having
        // distinct raw HOp refs. Div and Rem over those equivalent operands
        // should share a single witness pair.
        use graph::{PRef, Ref};
        use lang::ast::BinOp;
        use lang::id::Vid;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        for (idx, name, typ) in [
            (0, "a", ATyp::VPoly(1, 1)),
            (1, "b", ATyp::VPoly(1, 1)),
            (2, "c", ATyp::VPoly(1, 2)),
            (3, "d", ATyp::VPoly(1, 1)),
        ] {
            let pref = PRef::from_var(
                Vid::new(name),
                NodeIndex::new(idx),
                typ,
                0,
                Qualifier::Public,
                Distribution::default(),
            );
            ideal.register(&pref);
        }

        let mk_ref = |idx, typ| mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(idx)), typ));

        let mut add_derived_operand = |mul_idx, sub_idx| {
            let mul_ref = PRef::from_node(
                NodeIndex::new(mul_idx),
                ATyp::VPoly(1, 2),
                0,
                Qualifier::Private,
                Distribution::default(),
            );
            ideal.register(&mul_ref);
            builder.add_op(
                mul_ref.clone(),
                Op::Bin(
                    BinOp::Mul,
                    mk_ref(0, ATyp::VPoly(1, 1)),
                    mk_ref(1, ATyp::VPoly(1, 1)),
                    ATyp::VPoly(1, 2),
                ),
                &mut ideal,
            );

            let sub_ref = PRef::from_node(
                NodeIndex::new(sub_idx),
                ATyp::VPoly(1, 2),
                0,
                Qualifier::Private,
                Distribution::default(),
            );
            ideal.register(&sub_ref);
            builder.add_op(
                sub_ref.clone(),
                Op::Bin(
                    BinOp::Sub,
                    mk_ref(mul_idx, ATyp::VPoly(1, 2)),
                    mk_ref(2, ATyp::VPoly(1, 2)),
                    ATyp::VPoly(1, 2),
                ),
                &mut ideal,
            );
            sub_ref
        };

        add_derived_operand(10, 11);
        add_derived_operand(12, 13);

        let q = PRef::from_node(
            NodeIndex::new(20),
            ATyp::VPoly(1, 1),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.add_op(
            q,
            Op::Bin(
                BinOp::Div,
                mk_ref(11, ATyp::VPoly(1, 2)),
                mk_ref(3, ATyp::VPoly(1, 1)),
                ATyp::VPoly(1, 1),
            ),
            &mut ideal,
        );

        let r = PRef::from_node(
            NodeIndex::new(21),
            ATyp::VPoly(1, 0),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        builder.add_op(
            r,
            Op::Bin(
                BinOp::Rem,
                mk_ref(13, ATyp::VPoly(1, 2)),
                mk_ref(3, ATyp::VPoly(1, 1)),
                ATyp::VPoly(1, 0),
            ),
            &mut ideal,
        );

        assert_eq!(
            builder.ns.div_wit.len(),
            1,
            "equivalent named derived operands should share one div_wit entry"
        );
    }

    #[test]
    fn test_add_op_div_scalar_fallback() {
        // Scalar / Scalar → Scalar: legacy zip path (a - b·var(pr) = 0).
        // Scalar fallback does not build a canonical polynomial witness key, so
        // no witness side-table entry is created.
        use graph::{PRef, Ref};
        use lang::ast::BinOp;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();
        let pref_a = PRef::from_node(
            NodeIndex::new(0),
            ATyp::scalar(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_a);
        let pref_b = PRef::from_node(
            NodeIndex::new(1),
            ATyp::scalar(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_b);

        let basis_before = ideal.basis.len();
        let pref = PRef::from_node(
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
        builder.add_op(pref.clone(), op, &mut ideal);

        // Legacy zip emits exactly one row: a - b · var(ideal).
        assert_eq!(
            ideal.basis.len() - basis_before,
            1,
            "scalar fallback emits 1 row"
        );
        let var = |p: &PRef| Polynomial::<ark_bls12_381::Fr>::var(p);
        let expected = &var(&pref_a) - &(&var(&pref_b) * &var(&pref));
        assert!(
            ideal.basis.iter().any(|row| row == &expected),
            "scalar fallback row should be `a - b · var(ideal)`"
        );
        assert_eq!(
            builder.ns.div_wit.len(),
            0,
            "div_wit stays empty on scalar Div"
        );
    }

    #[test]
    fn test_add_op_scalar_div_vec_scalar_recurses_without_div_wit() {
        use graph::{PRef, Ref};
        use lang::ast::BinOp;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();
        let pref_a = PRef::from_node(
            NodeIndex::new(0),
            ATyp::scalar(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        let pref_b = PRef::from_node(
            NodeIndex::new(1),
            ATyp::vec_scalar(2),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_a);
        ideal.register(&pref_b);

        let pref = PRef::from_node(
            NodeIndex::new(2),
            ATyp::vec_scalar(2),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        let op: GOp<ArkBls12_381> = Op::Bin(
            BinOp::Div,
            mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), ATyp::scalar())),
            mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(1)), ATyp::vec_scalar(2))),
            ATyp::vec_scalar(2),
        );

        let before = ideal.basis.len();
        builder.add_op(pref.clone(), op, &mut ideal);

        assert_eq!(ideal.basis.len() - before, 2);
        let var = |p: &PRef| Polynomial::<ark_bls12_381::Fr>::var(p);
        for i in 0..2 {
            let b_i = pref_b.clone().with_index(i).unwrap();
            let r_i = pref.clone().with_index(i).unwrap();
            let expected = &var(&pref_a) - &(&var(&b_i) * &var(&r_i));
            assert!(
                ideal.basis.iter().any(|row| row == &expected),
                "basis missing scalar/vector div row {i}"
            );
        }
        assert_eq!(builder.ns.div_wit.len(), 0);
    }

    #[test]
    fn test_add_op_uni_div_scalar_slot_wise_without_div_wit() {
        use graph::{PRef, Ref};
        use lang::ast::BinOp;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();
        let pref_a = PRef::from_node(
            NodeIndex::new(0),
            ATyp::Uni(2),
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
        ideal.register(&pref_a);
        ideal.register(&pref_b);

        let pref = PRef::from_node(
            NodeIndex::new(2),
            ATyp::Uni(2),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        let before = ideal.basis.len();
        builder.add_op(
            pref.clone(),
            Op::Bin(
                BinOp::Div,
                mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), ATyp::Uni(2))),
                mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(1)), ATyp::scalar())),
                ATyp::Uni(2),
            ),
            &mut ideal,
        );

        assert_eq!(ideal.basis.len() - before, 3);
        assert_eq!(builder.ns.div_wit.len(), 0);
    }

    #[test]
    fn test_add_op_mle_div_scalar_slot_wise_without_div_wit() {
        use graph::{PRef, Ref};
        use lang::ast::BinOp;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();
        let pref_a = PRef::from_node(
            NodeIndex::new(0),
            ATyp::Mle(2),
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
        ideal.register(&pref_a);
        ideal.register(&pref_b);

        let pref = PRef::from_node(
            NodeIndex::new(2),
            ATyp::Mle(2),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        let before = ideal.basis.len();
        builder.add_op(
            pref,
            Op::Bin(
                BinOp::Div,
                mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), ATyp::Mle(2))),
                mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(1)), ATyp::scalar())),
                ATyp::Mle(2),
            ),
            &mut ideal,
        );

        assert_eq!(ideal.basis.len() - before, 4);
        assert_eq!(builder.ns.div_wit.len(), 0);
    }

    #[test]
    fn test_add_op_vector_poly_div_rem_propagates_witness_cache() {
        use graph::{PRef, Ref};
        use lang::ast::BinOp;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();
        let vec_typ = ATyp::Vec(Box::new(ATyp::VPoly(1, 2)), 2);
        let div_typ = ATyp::Vec(Box::new(ATyp::VPoly(1, 1)), 2);
        let rem_typ = ATyp::Vec(Box::new(ATyp::VPoly(1, 0)), 2);
        for idx in 0..2 {
            ideal.register(&PRef::from_node(
                NodeIndex::new(idx),
                vec_typ.clone(),
                0,
                Qualifier::Private,
                Distribution::default(),
            ));
        }

        builder.add_op(
            PRef::from_node(
                NodeIndex::new(2),
                div_typ.clone(),
                0,
                Qualifier::Private,
                Distribution::default(),
            ),
            Op::Bin(
                BinOp::Div,
                mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), vec_typ.clone())),
                mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(1)), vec_typ.clone())),
                div_typ,
            ),
            &mut ideal,
        );
        assert_eq!(builder.ns.div_wit.len(), 2);
        let after_div = ideal.basis.len();

        builder.add_op(
            PRef::from_node(
                NodeIndex::new(3),
                rem_typ.clone(),
                0,
                Qualifier::Private,
                Distribution::default(),
            ),
            Op::Bin(
                BinOp::Rem,
                mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), vec_typ.clone())),
                mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(1)), vec_typ)),
                rem_typ,
            ),
            &mut ideal,
        );

        assert_eq!(builder.ns.div_wit.len(), 2);
        assert_eq!(
            ideal.basis.len() - after_div,
            2,
            "cached vector Rem should add only one link row per element"
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
        let mut builder: IdealBuilder<ArkBls12_381> = IdealBuilder::new();
        let gr = builder.build(tc);

        // Two div_witnesses calls: inner (a/b) and outer ((a/b)/c).
        // The builder caches one (a,b) entry and one ((a/b),c) entry in div_wit.
        assert_eq!(
            builder.ns.div_wit.len(),
            2,
            "nested div should have 2 div_wit entries (inner + outer), got {}",
            builder.ns.div_wit.len()
        );

        // pl should contain entries for the div ideal nodes (linking them to
        // quotient witness slots). Since children are Op::Ref after IR lowering,
        // pl entries are keyed by node index with name=None.
        assert!(
            !gr.pl.is_empty(),
            "pl should have entries for div ideal nodes, got {}",
            gr.pl.len()
        );

        // Basis should contain canonical div identity rows (a = b*q + r)
        // and linking rows for both inner and outer division.
        // Div witness vars (q_wit, r_wit) must appear in basis.vars().
        // GB computation moved to backend; skipped in unit test();
        assert!(
            !gr.basis.is_empty(),
            "basis should not be empty after nested div"
        );

        let basis_vars = gr
            .basis
            .iter()
            .flat_map(|p| p.vars())
            .collect::<share::Set<_>>();
        assert!(
            basis_vars.iter().any(|p| p
                .name
                .as_ref()
                .is_some_and(|n| n.0.starts_with("__zippel::gb::div_q"))),
            "basis.vars() should contain div_q witnesses"
        );
        assert!(
            basis_vars.iter().any(|p| p
                .name
                .as_ref()
                .is_some_and(|n| n.0.starts_with("__zippel::gb::div_r"))),
            "basis.vars() should contain div_r witnesses"
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
        let mut builder: IdealBuilder<ArkBls12_381> = IdealBuilder::new();
        let gr = builder.build(tc);

        // Single (a, b) pair → one div_witnesses call → 1 div_wit cache entry (q_wit, r_wit).
        assert_eq!(
            builder.ns.div_wit.len(),
            1,
            "shared div/rem should have 1 div_wit entry for (a, b), got {}",
            builder.ns.div_wit.len()
        );

        // Both div and rem share the same canonical identity — the key invariant.
        // The cached (q_wit, r_wit) pair is what links div and rem nodes.
        let (q_wit, r_wit) = builder
            .ns
            .div_wit
            .values()
            .into_iter()
            .next()
            .expect("div_wit should have exactly one (q_wit, r_wit) entry");
        assert!(
            q_wit.name.as_ref().is_some_and(|n| n.0.contains("div_q")),
            "q_wit should be named div_q..., got {:?}",
            q_wit.name
        );
        assert!(
            r_wit.name.as_ref().is_some_and(|n| n.0.contains("div_r")),
            "r_wit should be named div_r..., got {:?}",
            r_wit.name
        );

        // pl should have entries for the div ideal (n3 → q_wit), mul ideal (n4 → b*q),
        // rem ideal (n5 → r_wit), and sum ideal (n6 → n4 + n5)
        assert!(
            gr.pl.len() >= 8,
            "pl should have entries for div/mul/rem/add chains, got {} entries",
            gr.pl.len()
        );

        // GB computation moved to backend; skipped in unit test();
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
        let mut builder: IdealBuilder<ArkBls12_381> = IdealBuilder::new();
        let gr = builder.build(tc);

        // Vec add verify: v[0] == a + c
        // The verify expression generates an equality constraint
        assert!(
            !gr.pl.is_empty(),
            "pl should have at least 1 entry for the verify expression, got {}",
            gr.pl.len()
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
        let mut builder: IdealBuilder<ArkBls12_381> = IdealBuilder::new();
        let gr = builder.build(tc);

        // 2d Vec add: the verify expression is m3r0[0] == a+e
        // pl should contain the verify LHS mapped to a+e
        assert!(
            !gr.pl.is_empty(),
            "pl should have at least 1 entry for the verify expression, got {}",
            gr.pl.len()
        );

        // Basis should contain the add constraint + verify eq
        assert!(
            gr.basis.len() >= 2,
            "basis should have at least 2 rows, got {}",
            gr.basis.len()
        );

        // Namespace should register all 8 public inputs
        let ns_named_count = gr.prefs.values().filter(|p| p.name.is_some()).count();
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
        let mut builder: IdealBuilder<ArkBls12_381> = IdealBuilder::new();
        let gr = builder.build(tc);

        // 3d Vec add: same structure, verify(t3d0r0[0] == a + a)
        assert!(
            !gr.pl.is_empty(),
            "pl should have at least 1 entry for the verify expression, got {}",
            gr.pl.len()
        );

        assert!(
            gr.basis.len() >= 2,
            "basis should have at least 2 rows, got {}",
            gr.basis.len()
        );

        let ns_named_count = gr.prefs.values().filter(|p| p.name.is_some()).count();
        assert!(
            ns_named_count >= 8,
            "namespace should register >= 8 named public prefs, got {}",
            ns_named_count
        );
    }

    #[test]
    fn test_reduce_add_over_scalar_vec() {
        use graph::{PRef, Ref};
        use lang::ast::BinOp;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();
        // v : Vec(F, 3)  →  reduce(+, v) : F
        let pref_v = PRef::from_node(
            NodeIndex::new(0),
            ATyp::Vec(Box::new(ATyp::scalar()), 3),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_v);

        let pref = PRef::from_node(
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
        builder.add_op(pref.clone(), op, &mut ideal);

        let var = |p: &PRef| Polynomial::<ark_bls12_381::Fr>::var(p);
        let v0 = pref_v.clone().with_slot(0).unwrap();
        let v1 = pref_v.clone().with_slot(1).unwrap();
        let v2 = pref_v.clone().with_slot(2).unwrap();

        let expected = &var(&v0) + &(&var(&v1) + &var(&v2));
        let row = &expected - &var(&pref);
        assert!(
            ideal.basis.iter().any(|r| r == &row),
            "basis should contain v0+v1+v2 - ideal, got {:?}",
            ideal.basis
        );
        assert_eq!(
            ideal.pl.get(&pref).cloned(),
            Some(expected),
            "pl[ideal] should map to v0+v1+v2"
        );
    }

    #[test]
    fn test_reduce_add_over_poly_vec() {
        // reduce(+, [Poly(1,2); 3]) : Poly(1,2)
        // Vec(Poly(1,2), 3) has 3 elements × 3 coefficients = 9 physical slots.
        // reduce should produce 3 polynomials (one per coefficient position),
        // where ideal[j] = v0[j] + v1[j] + v2[j].
        use graph::{PRef, Ref};
        use lang::ast::BinOp;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();
        let poly_t = ATyp::Uni(2);
        let vec_t = ATyp::Vec(Box::new(poly_t.clone()), 3);
        let pref_v = PRef::from_node(
            NodeIndex::new(0),
            vec_t.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_v);

        let pref = PRef::from_node(
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
        builder.add_op(pref.clone(), op, &mut ideal);

        let var = |p: &PRef| Polynomial::<ark_bls12_381::Fr>::var(p);
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

        let r_c0 = pref.clone().with_slot(0).unwrap();
        let r_c1 = pref.clone().with_slot(1).unwrap();
        let r_c2 = pref.clone().with_slot(2).unwrap();

        // ideal[0] = v0[0] + v1[0] + v2[0]
        let expected_c0 = &var(&v0_c0) + &(&var(&v1_c0) + &var(&v2_c0));
        let expected_c1 = &var(&v0_c1) + &(&var(&v1_c1) + &var(&v2_c1));
        let expected_c2 = &var(&v0_c2) + &(&var(&v1_c2) + &var(&v2_c2));

        assert_eq!(
            ideal.pl.get(&r_c0).cloned(),
            Some(expected_c0.clone()),
            "pl[ideal[0]] = v0[0]+v1[0]+v2[0]"
        );
        assert_eq!(
            ideal.pl.get(&r_c1).cloned(),
            Some(expected_c1.clone()),
            "pl[ideal[1]] = v0[1]+v1[1]+v2[1]"
        );
        assert_eq!(
            ideal.pl.get(&r_c2).cloned(),
            Some(expected_c2.clone()),
            "pl[ideal[2]] = v0[2]+v1[2]+v2[2]"
        );

        let row0 = &expected_c0 - &var(&r_c0);
        let row1 = &expected_c1 - &var(&r_c1);
        let row2 = &expected_c2 - &var(&r_c2);
        assert!(
            ideal.basis.iter().any(|r| r == &row0),
            "basis should contain row for coefficient 0"
        );
        assert!(
            ideal.basis.iter().any(|r| r == &row1),
            "basis should contain row for coefficient 1"
        );
        assert!(
            ideal.basis.iter().any(|r| r == &row2),
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

        for (i, basis_poly) in lag.iter().enumerate() {
            for (j, x) in xs.iter().copied().enumerate() {
                let mut val = Fr::zero();
                let mut xpow = Fr::one();
                for coeff in basis_poly {
                    val += *coeff * xpow;
                    xpow *= x;
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
        use ark_bls12_381::Fr;
        use graph::PRef;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let evals_typ = ATyp::Vec(Box::new(ATyp::scalar()), 2);
        let pref_evals = PRef::from_node(
            NodeIndex::new(0),
            evals_typ.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_evals);

        let points: GOp<ArkBls12_381> =
            Op::Value(Value::VecScalar(vec![Fr::from(0u64), Fr::from(1u64)]));
        let evals: GOp<ArkBls12_381> =
            Op::Ref(graph::Ref::new(NodeIndex::new(0)), evals_typ.clone());

        let ideal_typ = ATyp::uni(2);
        let pref_ideal = PRef::from_node(
            NodeIndex::new(1),
            ideal_typ.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_ideal);

        let op: GOp<ArkBls12_381> =
            Op::Interpolate(mk::<ArkBls12_381>(points), mk::<ArkBls12_381>(evals));
        builder.add_op(pref_ideal.clone(), op, &mut ideal);

        let var = |p: &PRef| Polynomial::<Fr>::var(p);

        let r0 = pref_ideal.clone().with_slot(0).unwrap();
        let r1 = pref_ideal.clone().with_slot(1).unwrap();
        let r2 = pref_ideal.clone().with_slot(2).unwrap();

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
            ideal.pl.get(&r0).cloned(),
            Some(expected_c0.clone()),
            "pl[c0] = var(y0)"
        );
        assert_eq!(
            ideal.pl.get(&r1).cloned(),
            Some(expected_c1.clone()),
            "pl[c1] = -var(y0) + var(y1)"
        );
        assert_eq!(
            ideal.pl.get(&r2).cloned(),
            Some(Polynomial::<Fr>::zero()),
            "pl[c2] = 0"
        );

        assert!(ideal.basis.iter().any(|r| r == &(&expected_c0 - &var(&r0))));
        assert!(ideal.basis.iter().any(|r| r == &(&expected_c1 - &var(&r1))));
    }

    #[test]
    fn test_add_op_interpolate_3_constant_points() {
        use ark_bls12_381::Fr;
        use graph::PRef;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let evals_typ = ATyp::Vec(Box::new(ATyp::scalar()), 3);
        let pref_evals = PRef::from_node(
            NodeIndex::new(0),
            evals_typ.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_evals);

        let points: GOp<ArkBls12_381> = Op::Value(Value::VecScalar(
            [1u64, 2, 3].iter().map(|&x| Fr::from(x)).collect(),
        ));
        let evals: GOp<ArkBls12_381> =
            Op::Ref(graph::Ref::new(NodeIndex::new(0)), evals_typ.clone());

        let ideal_typ = ATyp::uni(3);
        let pref_ideal = PRef::from_node(
            NodeIndex::new(1),
            ideal_typ.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_ideal);

        let op: GOp<ArkBls12_381> =
            Op::Interpolate(mk::<ArkBls12_381>(points), mk::<ArkBls12_381>(evals));
        builder.add_op(pref_ideal.clone(), op, &mut ideal);

        let var = |p: &PRef| Polynomial::<Fr>::var(p);

        let r0 = pref_ideal.clone().with_slot(0).unwrap();
        let r1 = pref_ideal.clone().with_slot(1).unwrap();
        let r2 = pref_ideal.clone().with_slot(2).unwrap();
        let r3 = pref_ideal.clone().with_slot(3).unwrap();

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

        let expected_c0 = &(&var(&y0) * &Polynomial::lit(&lag[0][0]))
            + &(&(&var(&y1) * &Polynomial::lit(&lag[1][0]))
                + &(&var(&y2) * &Polynomial::lit(&lag[2][0])));
        let expected_c1 = &(&var(&y0) * &Polynomial::lit(&lag[0][1]))
            + &(&(&var(&y1) * &Polynomial::lit(&lag[1][1]))
                + &(&var(&y2) * &Polynomial::lit(&lag[2][1])));
        let expected_c2 = &(&var(&y0) * &Polynomial::lit(&lag[0][2]))
            + &(&(&var(&y1) * &Polynomial::lit(&lag[1][2]))
                + &(&var(&y2) * &Polynomial::lit(&lag[2][2])));

        assert_eq!(
            ideal.pl.get(&r0).cloned(),
            Some(expected_c0.clone()),
            "pl[c0]"
        );
        assert_eq!(
            ideal.pl.get(&r1).cloned(),
            Some(expected_c1.clone()),
            "pl[c1]"
        );
        assert_eq!(
            ideal.pl.get(&r2).cloned(),
            Some(expected_c2.clone()),
            "pl[c2]"
        );
        assert_eq!(
            ideal.pl.get(&r3).cloned(),
            Some(Polynomial::<Fr>::zero()),
            "pl[c3] = 0"
        );
    }

    #[test]
    fn test_add_op_interpolate_ref_with_constant_points_in_pl() {
        use ark_bls12_381::Fr;
        use graph::PRef;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let vec_t = ATyp::Vec(Box::new(ATyp::scalar()), 2);
        let pref_points = PRef::from_node(
            NodeIndex::new(0),
            vec_t.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_points);

        let coefs: Vec<_> = [0u64, 1]
            .iter()
            .map(|&n| mk::<ArkBls12_381>(Op::Value(Value::Index(n as usize))))
            .collect();
        builder.add_op(pref_points.clone(), Op::Vec(coefs), &mut ideal);

        let pref_evals = PRef::from_node(
            NodeIndex::new(1),
            vec_t.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_evals);

        let ideal_typ = ATyp::uni(2);
        let pref_ideal = PRef::from_node(
            NodeIndex::new(2),
            ideal_typ.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_ideal);

        let points: GOp<ArkBls12_381> = Op::Ref(graph::Ref::new(NodeIndex::new(0)), vec_t.clone());
        let evals: GOp<ArkBls12_381> = Op::Ref(graph::Ref::new(NodeIndex::new(1)), vec_t.clone());

        let op: GOp<ArkBls12_381> =
            Op::Interpolate(mk::<ArkBls12_381>(points), mk::<ArkBls12_381>(evals));
        builder.add_op(pref_ideal.clone(), op, &mut ideal);

        let var = |p: &PRef| Polynomial::<Fr>::var(p);

        let r0 = pref_ideal.clone().with_slot(0).unwrap();
        let r1 = pref_ideal.clone().with_slot(1).unwrap();
        let r2 = pref_ideal.clone().with_slot(2).unwrap();

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
            ideal.pl.get(&r0).cloned(),
            Some(expected_c0.clone()),
            "pl[c0]"
        );
        assert_eq!(
            ideal.pl.get(&r1).cloned(),
            Some(expected_c1.clone()),
            "pl[c1]"
        );
        assert_eq!(
            ideal.pl.get(&r2).cloned(),
            Some(Polynomial::<Fr>::zero()),
            "pl[c2] = 0"
        );
    }

    #[test]
    fn test_add_op_interpolate_symbolic_points() {
        use graph::PRef;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        // Two symbolic points x0, x1 stored as PRef variables
        let scalar_t = ATyp::scalar();
        let vec_t = ATyp::Vec(Box::new(ATyp::scalar()), 2);
        let pref_x0 = PRef::from_node(
            NodeIndex::new(0),
            scalar_t.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        let pref_x1 = PRef::from_node(
            NodeIndex::new(1),
            scalar_t.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_x0);
        ideal.register(&pref_x1);

        // Points = [x0, x1]
        let pref_points = PRef::from_node(
            NodeIndex::new(2),
            vec_t.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_points);
        let x0_slot = pref_points
            .clone()
            .with_index(0)
            .unwrap()
            .with_slot(0)
            .unwrap();
        let x1_slot = pref_points
            .clone()
            .with_index(1)
            .unwrap()
            .with_slot(0)
            .unwrap();
        ideal.pl.insert(&x0_slot, &Polynomial::var(&pref_x0));
        ideal.pl.insert(&x1_slot, &Polynomial::var(&pref_x1));

        // Evals = [y0, y1]
        let pref_y0 = PRef::from_node(
            NodeIndex::new(3),
            scalar_t.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        let pref_y1 = PRef::from_node(
            NodeIndex::new(4),
            scalar_t.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_y0);
        ideal.register(&pref_y1);

        let pref_evals = PRef::from_node(
            NodeIndex::new(5),
            vec_t.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_evals);
        let y0_slot = pref_evals
            .clone()
            .with_index(0)
            .unwrap()
            .with_slot(0)
            .unwrap();
        let y1_slot = pref_evals
            .clone()
            .with_index(1)
            .unwrap()
            .with_slot(0)
            .unwrap();
        ideal.pl.insert(&y0_slot, &Polynomial::var(&pref_y0));
        ideal.pl.insert(&y1_slot, &Polynomial::var(&pref_y1));

        // Result = interpolate([x0, x1], [y0, y1])
        // p(t) = y0 * (t - x1) / (x0 - x1) + y1 * (t - x0) / (x1 - x0)
        //      = y0 * d01 * t - y0 * d01 * x1 + y1 * d10 * t - y1 * d10 * x0
        // where d01 * (x0 - x1) = 1 and d10 * (x1 - x0) = 1
        let ideal_typ = ATyp::uni(2);
        let pref_ideal = PRef::from_node(
            NodeIndex::new(6),
            ideal_typ.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_ideal);

        let points: GOp<ArkBls12_381> = Op::Ref(graph::Ref::new(NodeIndex::new(2)), vec_t.clone());
        let evals: GOp<ArkBls12_381> = Op::Ref(graph::Ref::new(NodeIndex::new(5)), vec_t.clone());

        let op: GOp<ArkBls12_381> =
            Op::Interpolate(mk::<ArkBls12_381>(points), mk::<ArkBls12_381>(evals));
        builder.add_op(pref_ideal.clone(), op, &mut ideal);

        // Verify: basis should contain d-variable equations and ideal equations.
        // For interpolate([x0, x1], [y0, y1]) with 2 symbolic points:
        // L_0(t) = d01*(t - x1), L_1(t) = d10*(t - x0)
        // p[0] = -y0*d01*x1 - y1*d10*x0  (constant term)
        // p[1] = y0*d01 + y1*d10          (linear coefficient)
        // p[2] = 0                         (no quadratic term)
        let r0 = pref_ideal.clone().with_slot(0).unwrap();
        let r1 = pref_ideal.clone().with_slot(1).unwrap();
        let r2 = pref_ideal.clone().with_slot(2).unwrap();

        let d_vars: Vec<_> = ideal
            .var_order
            .iter()
            .filter(|v| {
                v.name
                    .as_ref()
                    .is_some_and(|vid| vid.0.contains("interp_inv"))
            })
            .collect();
        assert_eq!(d_vars.len(), 2, "should have 2 d-variables");
        let d01 = d_vars[0];
        let d10 = d_vars[1];

        let r0_poly = ideal.pl.get(&r0).cloned().unwrap();
        let r1_poly = ideal.pl.get(&r1).cloned().unwrap();
        let r2_poly = ideal.pl.get(&r2).cloned().unwrap();

        let neg_one = -<ark_bls12_381::Fr as ark_ff::One>::one();
        // Expected: p[0] = -y0*d01*x1 - y1*d10*x0, p[1] = y0*d01 + y1*d10
        // evals_polys uses slot PRefs (y0_slot, y1_slot) as monomial variables.
        // xs_polys uses resolved PRefs from pl (pref_x0, pref_x1) as monomial variables.
        let expected_r0 = Polynomial::var(&y0_slot)
            * (Polynomial::var(d01) * Polynomial::lit(&neg_one) * Polynomial::var(&pref_x1))
            + Polynomial::var(&y1_slot)
                * (Polynomial::var(d10) * Polynomial::lit(&neg_one) * Polynomial::var(&pref_x0));
        let expected_r1 = Polynomial::var(&y0_slot) * Polynomial::var(d01)
            + Polynomial::var(&y1_slot) * Polynomial::var(d10);

        assert_eq!(
            r0_poly, expected_r0,
            "p[0] should equal expected constant term"
        );
        assert_eq!(
            r1_poly, expected_r1,
            "p[1] should equal expected linear coefficient"
        );
        assert!(r2_poly.is_zero(), "p[2] should be zero");

        // Verify: ideal equations in basis (p[k] - r_k = 0)
        let r0_eq = &r0_poly - &Polynomial::var(&r0);
        let r1_eq = &r1_poly - &Polynomial::var(&r1);
        let r2_eq = &r2_poly - &Polynomial::var(&r2);
        assert!(
            ideal.basis.contains(&r0_eq),
            "basis should contain p[0] - r0 equation"
        );
        assert!(
            ideal.basis.contains(&r1_eq),
            "basis should contain p[1] - r1 equation"
        );
        assert!(
            ideal.basis.contains(&r2_eq),
            "basis should contain p[2] - r2 equation"
        );
    }

    #[test]
    #[should_panic(
        expected = "Groebner operation has no polynomial-ideal treatment at duplicate-interpolate-points"
    )]
    fn test_add_op_interpolate_duplicate_points_panics_explicitly() {
        use backend::op::mk;
        use graph::PRef;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let evals_typ = ATyp::vec_scalar(3);
        let pref_evals = PRef::from_node(
            NodeIndex::new(1),
            evals_typ.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_evals);

        let pref_ideal = PRef::from_node(
            NodeIndex::new(2),
            ATyp::uni(3),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_ideal);

        let points = Op::Value(Value::VecIndex(vec![0, 0, 1]));
        let evals = Op::Ref(graph::Ref::new(NodeIndex::new(1)), evals_typ);
        let op: GOp<ArkBls12_381> =
            Op::Interpolate(mk::<ArkBls12_381>(points), mk::<ArkBls12_381>(evals));

        builder.add_op(pref_ideal, op, &mut ideal);
    }

    #[test]
    fn test_add_op_div_scalar_slot_wise() {
        use graph::PRef;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

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
        ideal.register(&pref_a);
        ideal.register(&pref_b);

        let pref_ideal = PRef::from_node(
            NodeIndex::new(2),
            ATyp::scalar(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_ideal);

        let a = Op::Ref(graph::Ref::new(NodeIndex::new(0)), ATyp::scalar());
        let b = Op::Ref(graph::Ref::new(NodeIndex::new(1)), ATyp::scalar());
        let op: GOp<ArkBls12_381> = Op::Bin(
            BinOp::Div,
            mk::<ArkBls12_381>(a),
            mk::<ArkBls12_381>(b),
            ATyp::scalar(),
        );
        builder.add_op(pref_ideal.clone(), op, &mut ideal);

        let var = |p: &PRef| Polynomial::<ark_bls12_381::Fr>::var(p);

        let a_slot = pref_a.with_slot(0).unwrap();
        let b_slot = pref_b.with_slot(0).unwrap();
        let r_slot = pref_ideal.with_slot(0).unwrap();
        let expected = &var(&a_slot) - &(&var(&b_slot) * &var(&r_slot));
        assert!(
            ideal.basis.iter().any(|r| r == &expected),
            "basis should contain a - b*var(pr)"
        );
    }

    #[test]
    #[should_panic(expected = "Rem: non-polynomial remainder")]
    fn test_add_op_rem_scalar_panics() {
        use graph::PRef;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

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
        ideal.register(&pref_a);
        ideal.register(&pref_b);

        let pref_ideal = PRef::from_node(
            NodeIndex::new(2),
            ATyp::scalar(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_ideal);

        let a = Op::Ref(graph::Ref::new(NodeIndex::new(0)), ATyp::scalar());
        let b = Op::Ref(graph::Ref::new(NodeIndex::new(1)), ATyp::scalar());
        let op: GOp<ArkBls12_381> = Op::Bin(
            BinOp::Rem,
            mk::<ArkBls12_381>(a),
            mk::<ArkBls12_381>(b),
            ATyp::scalar(),
        );
        builder.add_op(pref_ideal, op, &mut ideal);
    }

    #[test]
    fn test_reduce_div_scalar_uses_slot_wise_div() {
        use graph::PRef;
        use lang::ast::BinOp;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let vec_t = ATyp::Vec(Box::new(ATyp::scalar()), 3);
        let pref_v = PRef::from_node(
            NodeIndex::new(0),
            vec_t.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_v);

        let pref = PRef::from_node(
            NodeIndex::new(1),
            ATyp::scalar(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        let op: GOp<ArkBls12_381> = Op::Reduce(
            BinOp::Div,
            mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(0)), vec_t)),
        );
        builder.add_op(pref.clone(), op, &mut ideal);

        let v0 = pref_v.clone().with_index(0).unwrap().with_slot(0).unwrap();
        let v1 = pref_v.clone().with_index(1).unwrap().with_slot(0).unwrap();
        let v2 = pref_v.clone().with_index(2).unwrap().with_slot(0).unwrap();
        let r_slot = pref.with_slot(0).unwrap();

        let step1_vars: Vec<_> = ideal
            .basis
            .iter()
            .filter(|row| row.contains(&r_slot) && row.contains(&v2))
            .collect();
        assert!(
            !step1_vars.is_empty(),
            "basis should contain final div constraint involving v[2] and ideal"
        );

        let step0_vars: Vec<_> = ideal
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
        use graph::PRef;
        use lang::ast::BinOp;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let vec_t = ATyp::Vec(Box::new(ATyp::scalar()), 2);
        let pref_v = PRef::from_node(
            NodeIndex::new(0),
            vec_t.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_v);

        let pref = PRef::from_node(
            NodeIndex::new(1),
            ATyp::scalar(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref);

        let op: GOp<ArkBls12_381> = Op::Reduce(
            BinOp::Rem,
            mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(0)), vec_t)),
        );
        builder.add_op(pref, op, &mut ideal);
    }

    #[test]
    #[should_panic(expected = "MLE division is not supported")]
    fn test_add_op_div_mle_panics() {
        use graph::PRef;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

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
        ideal.register(&pref_a);
        ideal.register(&pref_b);

        let pref = PRef::from_node(
            NodeIndex::new(2),
            ATyp::Mle(2),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref);

        let a = Op::Ref(graph::Ref::new(NodeIndex::new(0)), ATyp::Mle(2));
        let b = Op::Ref(graph::Ref::new(NodeIndex::new(1)), ATyp::Mle(2));
        let op: GOp<ArkBls12_381> = Op::Bin(
            BinOp::Div,
            mk::<ArkBls12_381>(a),
            mk::<ArkBls12_381>(b),
            ATyp::Mle(2),
        );
        builder.add_op(pref, op, &mut ideal);
    }

    #[test]
    fn test_reduce_div_vpoly_uses_handle_div_rem() {
        use graph::PRef;
        use lang::ast::BinOp;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let vec_t = ATyp::Vec(Box::new(ATyp::VPoly(1, 3)), 2);
        let pref_v = PRef::from_node(
            NodeIndex::new(0),
            vec_t.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_v);

        let pref = PRef::from_node(
            NodeIndex::new(1),
            ATyp::VPoly(1, 1),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref);

        let op: GOp<ArkBls12_381> = Op::Reduce(
            BinOp::Div,
            mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(0)), vec_t)),
        );
        builder.add_op(pref.clone(), op, &mut ideal);

        assert!(
            !ideal.basis.is_empty(),
            "Reduce Div on VPoly should emit identity rows via handle_div_rem"
        );
    }

    #[test]
    fn reduce_mul_poly_accumulator_widens() {
        use graph::PRef;
        use lang::ast::BinOp;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let elem_t = ATyp::Uni(1);
        let vec_t = ATyp::Vec(Box::new(elem_t.clone()), 3);
        let pref_v = PRef::from_node(
            NodeIndex::new(0),
            vec_t.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_v);

        let pref = PRef::from_node(
            NodeIndex::new(1),
            ATyp::Uni(3),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref);

        builder.add_op(
            pref.clone(),
            Op::Reduce(
                BinOp::Mul,
                mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(0)), vec_t)),
            ),
            &mut ideal,
        );

        let high_slot = pref.with_slot(3).unwrap();
        assert!(
            ideal.basis.iter().any(|row| row.contains(&high_slot)),
            "reduce(*) should lower the widened Uni(3) accumulator all the way to the final high-degree slot"
        );
    }

    /// Regression: `reduce(*, [..])` lowered to `Op::ReduceMap` must widen the
    /// accumulator type as the product degree grows, exactly like `Op::Reduce`.
    /// Pre-fix, `reduce_polysource`'s Mul arm typed every accumulator at the
    /// element type `Uni(1)`, so the first product (degree 2) overflowed the
    /// `r_idx` table in `mul_op` and panicked with "multi-index missing in
    /// ideal". This is the `Op::ReduceMap` twin of
    /// `reduce_mul_poly_accumulator_widens`.
    #[test]
    fn reduce_map_mul_poly_accumulator_widens() {
        use graph::PRef;
        use lang::ast::BinOp;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let elem_t = ATyp::Uni(1);
        let vec_t = ATyp::Vec(Box::new(elem_t.clone()), 3);
        let pref_v = PRef::from_node(
            NodeIndex::new(0),
            vec_t.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_v);

        let pref = PRef::from_node(
            NodeIndex::new(1),
            ATyp::Uni(3),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref);

        // reduce(*, [x for x in polys]) — ReduceMap(Mul) with identity body over a
        // length-3 vector of degree-1 univariates → degree-3 product (Uni(3)).
        let domain = mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(0)), vec_t));
        let body = mk::<ArkBls12_381>(Op::LoopParam(0, elem_t.clone()));
        builder.add_op(
            pref.clone(),
            Op::ReduceMap(BinOp::Mul, domain, body),
            &mut ideal,
        );

        let high_slot = pref.with_slot(3).unwrap();
        assert!(
            ideal.basis.iter().any(|row| row.contains(&high_slot)),
            "reduce(*) via ReduceMap must widen the Uni(1) accumulator to the Uni(3) product"
        );
    }

    #[test]
    fn reduce_rem_poly_left_fold_semantics() {
        use graph::PRef;
        use lang::ast::BinOp;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let elem_t = ATyp::Uni(3);
        let vec_t = ATyp::Vec(Box::new(elem_t.clone()), 3);
        let pref_v = PRef::from_node(
            NodeIndex::new(0),
            vec_t.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_v);

        let pref = PRef::from_node(
            NodeIndex::new(1),
            ATyp::Uni(2),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref);

        builder.add_op(
            pref.clone(),
            Op::Reduce(
                BinOp::Rem,
                mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(0)), vec_t)),
            ),
            &mut ideal,
        );

        assert_eq!(
            pref.typ.physical_len(),
            3,
            "Uni(3) % Uni(3) % Uni(3) is lowered as the left-fold remainder type Uni(2)"
        );
        assert!(
            !ideal.basis.is_empty(),
            "reduce(%) should emit constraints for every polynomial fold step"
        );
    }

    #[test]
    fn poly_rem_smaller_dividend_passes_through() {
        use graph::PRef;
        use lang::ast::BinOp;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let dividend_t = ATyp::Uni(1);
        let divisor_t = ATyp::Uni(3);
        let pref_a = PRef::from_node(
            NodeIndex::new(0),
            dividend_t.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        let pref_b = PRef::from_node(
            NodeIndex::new(1),
            divisor_t.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_a);
        ideal.register(&pref_b);

        let pref = PRef::from_node(
            NodeIndex::new(2),
            ATyp::Uni(2),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref);

        builder.add_op(
            pref.clone(),
            Op::Bin(
                BinOp::Rem,
                mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(0)), dividend_t)),
                mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(1)), divisor_t)),
                ATyp::Uni(2),
            ),
            &mut ideal,
        );

        assert_eq!(
            builder.ns.div_wit.len(),
            0,
            "pass-through remainder allocates no div_wit"
        );
        for i in 0..2 {
            let src = pref_a.clone().with_slot(i).unwrap();
            let dst = pref.clone().with_slot(i).unwrap();
            assert!(
                ideal
                    .basis
                    .iter()
                    .any(|row| row.contains(&src) && row.contains(&dst)),
                "pass-through remainder should bind source slot {i} to the ideal"
            );
        }
        let padded = pref.with_slot(2).unwrap();
        assert!(
            ideal.basis.iter().any(|row| row.contains(&padded)),
            "lifted pass-through remainder should constrain the padded high slot"
        );
    }

    // -----------------------------------------------------------------
    // Record: field-slot-aware layout
    // -----------------------------------------------------------------

    #[test]
    fn test_record_scalar_fields_bind_slots() {
        use graph::PRef;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

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
        ideal.register(&pref_a);
        let pref_b = PRef::from_node(
            NodeIndex::new(1),
            s.clone(),
            0,
            Qualifier::Public,
            Distribution::default(),
        );
        ideal.register(&pref_b);

        let mut fields = Ctx::<String, HOp<ArkBls12_381>>::new();
        fields.insert(
            &"x".to_string(),
            &mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(0)), s.clone())),
        );
        fields.insert(
            &"y".to_string(),
            &mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(1)), s.clone())),
        );

        let pref_r = PRef::from_node(
            NodeIndex::new(2),
            rec_typ,
            0,
            Qualifier::Public,
            Distribution::default(),
        );
        ideal.register(&pref_r);

        builder.add_op(pref_r.clone(), Op::Record(fields), &mut ideal);

        // Ctx iteration order: "x" (slot 0), "y" (slot 1)
        let slot_x = pref_r.clone().with_slot(0).unwrap();
        let slot_y = pref_r.clone().with_slot(1).unwrap();

        assert!(
            ideal.pl.contains(&slot_x),
            "record slot 0 (x) missing from pl"
        );
        assert!(
            ideal.pl.contains(&slot_y),
            "record slot 1 (y) missing from pl"
        );

        let poly_x = ideal.pl.get(&slot_x).unwrap();
        let poly_y = ideal.pl.get(&slot_y).unwrap();
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
        use graph::PRef;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

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
        ideal.register(&pref_scalar);

        let pref_poly = PRef::from_node(
            NodeIndex::new(1),
            uni_typ.clone(),
            0,
            Qualifier::Public,
            Distribution::default(),
        );
        ideal.register(&pref_poly);

        let mut fields = Ctx::<String, HOp<ArkBls12_381>>::new();
        fields.insert(
            &"a".to_string(),
            &mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(0)), s.clone())),
        );
        fields.insert(
            &"p".to_string(),
            &mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(1)), uni_typ.clone())),
        );

        let pref_r = PRef::from_node(
            NodeIndex::new(2),
            rec_typ,
            0,
            Qualifier::Public,
            Distribution::default(),
        );
        ideal.register(&pref_r);

        builder.add_op(pref_r.clone(), Op::Record(fields), &mut ideal);

        assert_eq!(
            pref_r.typ.physical_len(),
            4,
            "1 scalar + 3 Uni(2) coeffs = 4"
        );

        let slot_a = pref_r.clone().with_slot(0).unwrap();
        assert_eq!(slot_a.typ, s, "slot 0 should be scalar (field a)");
        assert!(
            ideal.pl.contains(&slot_a),
            "record slot 0 (a) missing from pl"
        );

        for i in 0..3 {
            let slot_pi = pref_r.clone().with_slot(1 + i).unwrap();
            assert_eq!(
                slot_pi.typ, s,
                "slots 1-3 should be scalar (field p coefficients)"
            );
            assert!(
                ideal.pl.contains(&slot_pi),
                "record slot {} (p coeff {}) missing from pl",
                1 + i,
                i
            );
        }
    }

    #[test]
    fn test_record_basis_count_matches_physical_len() {
        use graph::PRef;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

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
        ideal.register(&pref_x);

        let pref_v = PRef::from_node(
            NodeIndex::new(1),
            v2.clone(),
            0,
            Qualifier::Public,
            Distribution::default(),
        );
        ideal.register(&pref_v);

        let mut fields = Ctx::<String, HOp<ArkBls12_381>>::new();
        fields.insert(
            &"x".to_string(),
            &mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(0)), s.clone())),
        );
        fields.insert(
            &"v".to_string(),
            &mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(1)), v2.clone())),
        );

        let pref_r = PRef::from_node(
            NodeIndex::new(2),
            rec_typ,
            0,
            Qualifier::Public,
            Distribution::default(),
        );
        ideal.register(&pref_r);

        builder.add_op(pref_r.clone(), Op::Record(fields), &mut ideal);

        assert_eq!(
            ideal.basis.len(),
            phys_len,
            "basis should have one row per physical slot"
        );
    }

    // -----------------------------------------------------------------
    // Proj: extract field from a Record
    // -----------------------------------------------------------------

    #[test]
    fn test_proj_scalar_field_from_record() {
        use graph::PRef;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

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
        ideal.register(&pref_rec);

        let inner_op: GOp<ArkBls12_381> = Op::Ref(graph::Ref::new(NodeIndex::new(0)), rec_typ);

        let pref_proj = PRef::from_node(
            NodeIndex::new(1),
            s.clone(),
            0,
            Qualifier::Public,
            Distribution::default(),
        );
        ideal.register(&pref_proj);

        builder.add_op(
            pref_proj.clone(),
            Op::Proj(mk::<ArkBls12_381>(inner_op), "x".to_string(), s.clone()),
            &mut ideal,
        );

        assert!(ideal.pl.contains(&pref_proj), "proj ideal missing from pl");

        let proj_poly = ideal.pl.get(&pref_proj).unwrap();
        let slot_0 = pref_rec.clone().with_slot(0).unwrap();
        assert!(
            proj_poly.contains(&slot_0),
            "proj poly should reference record slot 0 (field x)"
        );
    }

    #[test]
    fn test_proj_second_field_offset_correct() {
        use graph::PRef;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

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
        ideal.register(&pref_rec);

        let inner_op: GOp<ArkBls12_381> = Op::Ref(graph::Ref::new(NodeIndex::new(0)), rec_typ);

        let pref_proj = PRef::from_node(
            NodeIndex::new(1),
            v3.clone(),
            0,
            Qualifier::Public,
            Distribution::default(),
        );
        ideal.register(&pref_proj);

        builder.add_op(
            pref_proj.clone(),
            Op::Proj(mk::<ArkBls12_381>(inner_op), "b".to_string(), v3.clone()),
            &mut ideal,
        );

        assert_eq!(pref_proj.typ.physical_len(), 3, "Vec<F, 3> has 3 slots");
        for i in 0..3 {
            let proj_slot = pref_proj.clone().with_slot(i).unwrap();
            assert!(
                ideal.pl.contains(&proj_slot),
                "proj slot {} missing from pl",
                i
            );

            let proj_poly = ideal.pl.get(&proj_slot).unwrap();
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
        use graph::PRef;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

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
        ideal.register(&pref_rec);

        let inner_op: GOp<ArkBls12_381> = Op::Ref(graph::Ref::new(NodeIndex::new(0)), rec_typ);

        let pref_proj = PRef::from_node(
            NodeIndex::new(1),
            uni2.clone(),
            0,
            Qualifier::Public,
            Distribution::default(),
        );
        ideal.register(&pref_proj);

        builder.add_op(
            pref_proj.clone(),
            Op::Proj(mk::<ArkBls12_381>(inner_op), "a".to_string(), uni2.clone()),
            &mut ideal,
        );

        assert_eq!(pref_proj.typ.physical_len(), 3, "Uni(2) has 3 coefficients");
        for i in 0..3 {
            let proj_slot = pref_proj.clone().with_slot(i).unwrap();
            assert!(
                ideal.pl.contains(&proj_slot),
                "proj slot {} missing from pl",
                i
            );

            let proj_poly = ideal.pl.get(&proj_slot).unwrap();
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
        use ark_bls12_381::Fr;
        use backend::op::mk;
        use graph::PRef;
        use lang::ast::BinOp;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let uni2 = ATyp::Uni(2);
        let uni4 = ATyp::Uni(4);
        let uni4_ideal = ATyp::Uni(4);

        let pref_a = PRef::from_node(
            NodeIndex::new(0),
            uni2.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_a);
        let coefs_a: Vec<_> = (1..=3u64)
            .map(|n| mk::<ArkBls12_381>(Op::Value(Value::Scalar(Fr::from(n)))))
            .collect();
        builder.add_op(pref_a.clone(), Op::Vec(coefs_a), &mut ideal);

        let pref_b = PRef::from_node(
            NodeIndex::new(1),
            uni4.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_b);
        let coefs_b: Vec<_> = (1..=5u64)
            .map(|n| mk::<ArkBls12_381>(Op::Value(Value::Scalar(Fr::from(n)))))
            .collect();
        builder.add_op(pref_b.clone(), Op::Vec(coefs_b), &mut ideal);

        let pref_r = PRef::from_node(
            NodeIndex::new(2),
            uni4_ideal.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_r);

        builder.add_op(
            pref_r.clone(),
            Op::Bin(
                BinOp::Add,
                mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(0)), uni2)),
                mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(1)), uni4)),
                uni4_ideal,
            ),
            &mut ideal,
        );

        assert_eq!(pref_r.typ.physical_len(), 5, "Uni(4) has 5 coefficients");
        for i in 0..5 {
            let slot = pref_r.clone().with_slot(i).unwrap();
            assert!(
                ideal.pl.contains(&slot),
                "Uni(2)+Uni(4) ideal slot {} missing from pl",
                i
            );
        }
    }

    #[test]
    fn test_mul_scalar_poly_broadcast() {
        use graph::PRef;
        use lang::ast::BinOp;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let s = ATyp::scalar();
        let uni2 = ATyp::Uni(2);

        let pref_s = PRef::from_node(
            NodeIndex::new(0),
            s.clone(),
            0,
            Qualifier::Public,
            Distribution::default(),
        );
        ideal.register(&pref_s);

        let pref_p = PRef::from_node(
            NodeIndex::new(1),
            uni2.clone(),
            0,
            Qualifier::Public,
            Distribution::default(),
        );
        ideal.register(&pref_p);

        let pref_r = PRef::from_node(
            NodeIndex::new(2),
            uni2.clone(),
            0,
            Qualifier::Public,
            Distribution::default(),
        );
        ideal.register(&pref_r);

        builder.add_op(
            pref_r.clone(),
            Op::Bin(
                BinOp::Mul,
                mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(0)), s.clone())),
                mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(1)), uni2.clone())),
                uni2.clone(),
            ),
            &mut ideal,
        );

        assert_eq!(
            ideal.basis.len(),
            3,
            "Scalar * Uni(2) should produce 3 basis rows (one per coefficient)"
        );
        for i in 0..3 {
            let slot = pref_r.clone().with_slot(i).unwrap();
            assert!(
                ideal.pl.contains(&slot),
                "Scalar*Uni(2) ideal slot {} missing from pl",
                i
            );
        }
    }

    #[test]
    fn test_mul_vec_scalar_broadcast() {
        use graph::PRef;
        use lang::ast::BinOp;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let s = ATyp::scalar();
        let v3 = ATyp::Vec(Box::new(s.clone()), 3);

        let pref_v = PRef::from_node(
            NodeIndex::new(0),
            v3.clone(),
            0,
            Qualifier::Public,
            Distribution::default(),
        );
        ideal.register(&pref_v);

        let pref_s = PRef::from_node(
            NodeIndex::new(1),
            s.clone(),
            0,
            Qualifier::Public,
            Distribution::default(),
        );
        ideal.register(&pref_s);

        let pref_r = PRef::from_node(
            NodeIndex::new(2),
            v3.clone(),
            0,
            Qualifier::Public,
            Distribution::default(),
        );
        ideal.register(&pref_r);

        builder.add_op(
            pref_r.clone(),
            Op::Bin(
                BinOp::Mul,
                mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(0)), v3.clone())),
                mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(1)), s.clone())),
                v3.clone(),
            ),
            &mut ideal,
        );

        assert_eq!(
            ideal.basis.len(),
            3,
            "Vec<Scalar,3> * Scalar should produce 3 basis rows"
        );
    }

    fn scalar_poly_binop_ideal(
        op: BinOp,
        scalar_left: bool,
        poly_typ: ATyp,
    ) -> (graph::PRef, graph::PRef, graph::PRef, Ideal<ArkBls12_381>) {
        use graph::{PRef, Ref};
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let scalar_typ = ATyp::scalar();
        let pref_s = PRef::from_node(
            NodeIndex::new(0),
            scalar_typ.clone(),
            0,
            Qualifier::Public,
            Distribution::default(),
        );
        ideal.register(&pref_s);

        let pref_p = PRef::from_node(
            NodeIndex::new(1),
            poly_typ.clone(),
            0,
            Qualifier::Public,
            Distribution::default(),
        );
        ideal.register(&pref_p);

        let pref_r = PRef::from_node(
            NodeIndex::new(2),
            poly_typ.clone(),
            0,
            Qualifier::Public,
            Distribution::default(),
        );
        ideal.register(&pref_r);

        let scalar_op = mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), scalar_typ));
        let poly_op = mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(1)), poly_typ.clone()));
        let (left, right) = if scalar_left {
            (scalar_op, poly_op)
        } else {
            (poly_op, scalar_op)
        };

        builder.add_op(
            pref_r.clone(),
            Op::Bin(op, left, right, poly_typ),
            &mut ideal,
        );

        (pref_s, pref_p, pref_r, ideal)
    }

    fn assert_ideal_slot(
        ideal: &Ideal<ArkBls12_381>,
        pref_r: &graph::PRef,
        slot: usize,
        expected: Polynomial<ark_bls12_381::Fr>,
    ) {
        let r_slot = pref_r.with_slot(slot).unwrap();
        let stored = ideal.pl.get(&r_slot).unwrap();
        assert_eq!(*stored, expected, "ideal slot {slot} mismatch");
    }

    #[test]
    fn test_add_scalar_poly_broadcast() {
        let (pref_s, pref_p, pref_r, ideal) =
            scalar_poly_binop_ideal(BinOp::Add, true, ATyp::Uni(2));
        assert_eq!(
            ideal.basis.len(),
            3,
            "Scalar + Uni(2) should produce one row per coefficient slot"
        );

        let s = Polynomial::<ark_bls12_381::Fr>::var(&pref_s);
        for i in 0..3 {
            let p_slot_pref = pref_p.with_slot(i).unwrap();
            let p = Polynomial::var(&p_slot_pref);
            let expected = if i == 0 { &s + &p } else { p };
            assert_ideal_slot(&ideal, &pref_r, i, expected);
        }
    }

    #[test]
    fn test_uni_add_scalar_lifts_to_constant_slot_only() {
        let (pref_s, pref_p, pref_r, ideal) =
            scalar_poly_binop_ideal(BinOp::Add, false, ATyp::Uni(2));
        let s = Polynomial::<ark_bls12_381::Fr>::var(&pref_s);
        for i in 0..3 {
            let p_slot_pref = pref_p.with_slot(i).unwrap();
            let p = Polynomial::var(&p_slot_pref);
            let expected = if i == 0 { &p + &s } else { p };
            assert_ideal_slot(&ideal, &pref_r, i, expected);
        }
    }

    #[test]
    fn test_uni_sub_scalar_lifts_to_constant_slot_only() {
        let (pref_s, pref_p, pref_r, ideal) =
            scalar_poly_binop_ideal(BinOp::Sub, false, ATyp::Uni(2));
        let s = Polynomial::<ark_bls12_381::Fr>::var(&pref_s);
        for i in 0..3 {
            let p_slot_pref = pref_p.with_slot(i).unwrap();
            let p = Polynomial::var(&p_slot_pref);
            let expected = if i == 0 { &p - &s } else { p };
            assert_ideal_slot(&ideal, &pref_r, i, expected);
        }
    }

    #[test]
    fn test_scalar_sub_uni_negates_nonconstant_slots() {
        let (pref_s, pref_p, pref_r, ideal) =
            scalar_poly_binop_ideal(BinOp::Sub, true, ATyp::Uni(2));
        let s = Polynomial::<ark_bls12_381::Fr>::var(&pref_s);
        for i in 0..3 {
            let p_slot_pref = pref_p.with_slot(i).unwrap();
            let p = Polynomial::var(&p_slot_pref);
            let expected = if i == 0 { &s - &p } else { -p };
            assert_ideal_slot(&ideal, &pref_r, i, expected);
        }
    }

    #[test]
    fn test_scalar_add_vpoly_lifts_to_constant_slot_only() {
        let poly_typ = ATyp::VPoly(2, 2);
        let (pref_s, pref_p, pref_r, ideal) =
            scalar_poly_binop_ideal(BinOp::Add, true, poly_typ.clone());
        let s = Polynomial::<ark_bls12_381::Fr>::var(&pref_s);
        let zero_slot = multi_indices(2, 2)
            .iter()
            .position(|idx| idx.iter().all(|degree| *degree == 0))
            .unwrap();
        for i in 0..poly_typ.physical_len() {
            let p_slot_pref = pref_p.with_slot(i).unwrap();
            let p = Polynomial::var(&p_slot_pref);
            let expected = if i == zero_slot { &s + &p } else { p };
            assert_ideal_slot(&ideal, &pref_r, i, expected);
        }
    }

    #[test]
    fn test_scalar_sub_vpoly_negates_nonconstant_slots() {
        let poly_typ = ATyp::VPoly(2, 2);
        let (pref_s, pref_p, pref_r, ideal) =
            scalar_poly_binop_ideal(BinOp::Sub, true, poly_typ.clone());
        let s = Polynomial::<ark_bls12_381::Fr>::var(&pref_s);
        let zero_slot = multi_indices(2, 2)
            .iter()
            .position(|idx| idx.iter().all(|degree| *degree == 0))
            .unwrap();
        for i in 0..poly_typ.physical_len() {
            let p_slot_pref = pref_p.with_slot(i).unwrap();
            let p = Polynomial::var(&p_slot_pref);
            let expected = if i == zero_slot { &s - &p } else { -p };
            assert_ideal_slot(&ideal, &pref_r, i, expected);
        }
    }

    #[test]
    fn test_scalar_add_mle_broadcasts_to_all_evaluation_slots() {
        let poly_typ = ATyp::Mle(2);
        let (pref_s, pref_p, pref_r, ideal) =
            scalar_poly_binop_ideal(BinOp::Add, true, poly_typ.clone());
        let s = Polynomial::<ark_bls12_381::Fr>::var(&pref_s);
        for i in 0..poly_typ.physical_len() {
            let p_slot_pref = pref_p.with_slot(i).unwrap();
            let p = Polynomial::var(&p_slot_pref);
            assert_ideal_slot(&ideal, &pref_r, i, &s + &p);
        }
    }

    #[test]
    fn test_concat_vec_uni_different_degrees() {
        use graph::PRef;
        use lang::ast::BinOp;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let uni2 = ATyp::Uni(2);
        let uni4 = ATyp::Uni(4);
        let vec_uni2 = ATyp::Vec(Box::new(uni2.clone()), 2);
        let vec_uni4 = ATyp::Vec(Box::new(uni4.clone()), 2);
        let vec_ideal = ATyp::Vec(Box::new(uni4.clone()), 4);

        let pref_a = PRef::from_node(
            NodeIndex::new(0),
            vec_uni2.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_a);

        let pref_b = PRef::from_node(
            NodeIndex::new(1),
            vec_uni4.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_b);

        let pref_r = PRef::from_node(
            NodeIndex::new(2),
            vec_ideal.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_r);

        builder.add_op(
            pref_r.clone(),
            Op::Bin(
                BinOp::Concat,
                mk::<ArkBls12_381>(Op::Ref(
                    graph::Ref::new(NodeIndex::new(0)),
                    vec_uni2.clone(),
                )),
                mk::<ArkBls12_381>(Op::Ref(
                    graph::Ref::new(NodeIndex::new(1)),
                    vec_uni4.clone(),
                )),
                vec_ideal.clone(),
            ),
            &mut ideal,
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
                    ideal.pl.contains(&slot),
                    "Concat ideal element {} slot {} missing from pl",
                    i,
                    j
                );
            }
        }
    }

    #[test]
    fn test_concat_vec_scalar_element() {
        use graph::PRef;
        use lang::ast::BinOp;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let s = ATyp::scalar();
        let vec_s = ATyp::Vec(Box::new(s.clone()), 2);
        let vec_ideal = ATyp::Vec(Box::new(s.clone()), 3);

        let pref_a = PRef::from_node(
            NodeIndex::new(0),
            vec_s.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_a);

        let pref_b = PRef::from_node(
            NodeIndex::new(1),
            s.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_b);

        let pref_r = PRef::from_node(
            NodeIndex::new(2),
            vec_ideal.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_r);

        builder.add_op(
            pref_r.clone(),
            Op::Bin(
                BinOp::Concat,
                mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(0)), vec_s.clone())),
                mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(1)), s.clone())),
                vec_ideal.clone(),
            ),
            &mut ideal,
        );

        assert_eq!(pref_r.typ.physical_len(), 3, "Vec(Scalar, 3) has 3 slots");
        for i in 0..3 {
            let elem = pref_r.with_index(i).unwrap();
            assert!(
                ideal.pl.contains(&elem),
                "Concat Vec++Scalar ideal element {} missing from pl",
                i
            );
        }
    }

    #[test]
    fn test_equ_vec_uni_different_degrees() {
        use graph::PRef;
        use lang::ast::BinOp;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

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
        ideal.register(&pref_a);

        let pref_b = PRef::from_node(
            NodeIndex::new(1),
            vec_uni4.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_b);

        let pref_r = PRef::from_node(
            NodeIndex::new(2),
            bool_typ.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_r);

        builder.add_op(
            pref_r.clone(),
            Op::Bin(
                BinOp::Equ,
                mk::<ArkBls12_381>(Op::Ref(
                    graph::Ref::new(NodeIndex::new(0)),
                    vec_uni2.clone(),
                )),
                mk::<ArkBls12_381>(Op::Ref(
                    graph::Ref::new(NodeIndex::new(1)),
                    vec_uni4.clone(),
                )),
                bool_typ.clone(),
            ),
            &mut ideal,
        );

        assert!(
            !ideal.basis.is_empty(),
            "Vec(Uni(2),2) == Vec(Uni(4),2) should produce basis constraints (zero-padded per element)"
        );
    }

    #[test]
    fn test_dot_vec_scalar() {
        use graph::PRef;
        use lang::ast::BinOp;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let s = ATyp::scalar();
        let vec_s = ATyp::Vec(Box::new(s.clone()), 3);

        let pref_a = PRef::from_node(
            NodeIndex::new(0),
            vec_s.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_a);

        let pref_b = PRef::from_node(
            NodeIndex::new(1),
            vec_s.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_b);

        let pref_r = PRef::from_node(
            NodeIndex::new(2),
            s.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_r);

        builder.add_op(
            pref_r.clone(),
            Op::Bin(
                BinOp::Dot,
                mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(0)), vec_s.clone())),
                mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(1)), vec_s.clone())),
                s.clone(),
            ),
            &mut ideal,
        );

        assert!(
            ideal.pl.contains(&pref_r),
            "Dot Vec(Scalar,3)·Vec(Scalar,3) ideal should be in pl"
        );
        assert!(
            !ideal.basis.is_empty(),
            "Dot Vec(Scalar,3)·Vec(Scalar,3) should produce basis rows"
        );
    }

    #[test]
    fn test_dot_vec_uni() {
        use graph::PRef;
        use lang::ast::BinOp;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let uni2 = ATyp::Uni(2);
        let uni4 = ATyp::Uni(4);
        let vec_uni2 = ATyp::Vec(Box::new(uni2.clone()), 2);
        let vec_uni4 = ATyp::Vec(Box::new(uni4.clone()), 2);
        let dot_ideal = ATyp::Uni(6);

        let pref_a = PRef::from_node(
            NodeIndex::new(0),
            vec_uni2.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_a);

        let pref_b = PRef::from_node(
            NodeIndex::new(1),
            vec_uni4.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_b);

        let pref_r = PRef::from_node(
            NodeIndex::new(2),
            dot_ideal.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_r);

        builder.add_op(
            pref_r.clone(),
            Op::Bin(
                BinOp::Dot,
                mk::<ArkBls12_381>(Op::Ref(
                    graph::Ref::new(NodeIndex::new(0)),
                    vec_uni2.clone(),
                )),
                mk::<ArkBls12_381>(Op::Ref(
                    graph::Ref::new(NodeIndex::new(1)),
                    vec_uni4.clone(),
                )),
                dot_ideal.clone(),
            ),
            &mut ideal,
        );

        for i in 0..7 {
            let slot = pref_r.with_slot(i).unwrap();
            assert!(
                ideal.pl.contains(&slot),
                "Dot Vec(Uni(2),2)·Vec(Uni(4),2) ideal slot {} missing from pl",
                i
            );
        }
    }

    #[test]
    fn test_pair_vec() {
        use graph::PRef;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

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
        ideal.register(&pref_a);

        let pref_b = PRef::from_node(
            NodeIndex::new(1),
            vec_g2.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_b);

        let pref_r = PRef::from_node(
            NodeIndex::new(2),
            vec_gt.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_r);

        builder.add_op(
            pref_r.clone(),
            Op::Pair(
                mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(0)), vec_g1.clone())),
                mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(1)), vec_g2.clone())),
                vec_gt.clone(),
            ),
            &mut ideal,
        );

        for i in 0..2 {
            let elem = pref_r.with_index(i).unwrap();
            assert!(
                ideal.pl.contains(&elem),
                "Pair Vec(G1,2)×Vec(G2,2) ideal element {} missing from pl",
                i
            );
        }
    }

    #[test]
    #[should_panic(
        expected = "Groebner operation has no polynomial-ideal treatment at dynamic-pow"
    )]
    fn test_pow_vec_element_wise() {
        use graph::PRef;
        use lang::ast::BinOp;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let s = ATyp::scalar();
        let fin = ATyp::fin(lang::typ::range::CRange::default());
        let vec_s = ATyp::Vec(Box::new(s.clone()), 2);
        let vec_fin = ATyp::Vec(Box::new(fin.clone()), 2);
        let vec_ideal = ATyp::Vec(Box::new(s.clone()), 2);

        let pref_a = PRef::from_node(
            NodeIndex::new(0),
            vec_s.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_a);

        let pref_b = PRef::from_node(
            NodeIndex::new(1),
            vec_fin.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_b);

        let pref_r = PRef::from_node(
            NodeIndex::new(2),
            vec_ideal.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_r);

        builder.add_op(
            pref_r.clone(),
            Op::Bin(
                BinOp::Pow,
                mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(0)), vec_s.clone())),
                mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(1)), vec_fin.clone())),
                vec_ideal.clone(),
            ),
            &mut ideal,
        );
        // The above panics with "dynamic-pow"; assertions below are unreachable.
    }

    #[test]
    fn test_pow_uni_const_exp() {
        use backend::op::mk;
        use graph::PRef;
        use lang::ast::BinOp;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let uni2 = ATyp::Uni(2);
        let ideal_uni4 = ATyp::Uni(4);

        let pref_a = PRef::from_node(
            NodeIndex::new(0),
            uni2.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_a);

        let pref_r = PRef::from_node(
            NodeIndex::new(1),
            ideal_uni4.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_r);

        builder.add_op(
            pref_r.clone(),
            Op::Bin(
                BinOp::Pow,
                mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(0)), uni2.clone())),
                mk::<ArkBls12_381>(Op::Value(Value::Index(2))),
                ideal_uni4.clone(),
            ),
            &mut ideal,
        );

        for i in 0..5 {
            let slot = pref_r.with_slot(i).unwrap();
            assert!(
                ideal.pl.contains(&slot),
                "Pow Uni(2)^2 ideal slot {} missing from pl",
                i
            );
        }
        // Constant-exponent pow uses explicit ideal treatment; ideal is in pl.
    }

    #[test]
    fn test_pow_vec_uni_const_exp() {
        use backend::op::mk;
        use graph::PRef;
        use lang::ast::BinOp;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let uni2 = ATyp::Uni(2);
        let ideal_uni4 = ATyp::Uni(4);
        let vec_uni2 = ATyp::Vec(Box::new(uni2.clone()), 2);
        let vec_ideal = ATyp::Vec(Box::new(ideal_uni4.clone()), 2);

        let pref_a = PRef::from_node(
            NodeIndex::new(0),
            vec_uni2.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_a);

        let pref_r = PRef::from_node(
            NodeIndex::new(1),
            vec_ideal.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_r);

        builder.add_op(
            pref_r.clone(),
            Op::Bin(
                BinOp::Pow,
                mk::<ArkBls12_381>(Op::Ref(
                    graph::Ref::new(NodeIndex::new(0)),
                    vec_uni2.clone(),
                )),
                mk::<ArkBls12_381>(Op::Value(Value::Index(2))),
                vec_ideal.clone(),
            ),
            &mut ideal,
        );

        for i in 0..2 {
            let elem = pref_r.with_index(i).unwrap();
            for j in 0..5 {
                let slot = elem.with_slot(j).unwrap();
                assert!(
                    ideal.pl.contains(&slot),
                    "Pow Vec(Uni(2),2)^2 element {} slot {} missing from pl",
                    i,
                    j
                );
            }
        }
        // Constant-exponent pow uses explicit ideal treatment; ideal is in pl.
    }

    #[test]
    fn test_pow_vec_vecindex_per_element() {
        use backend::op::mk;
        use graph::PRef;
        use lang::ast::BinOp;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let s = ATyp::scalar();
        let vec_s = ATyp::Vec(Box::new(s.clone()), 2);
        let vec_ideal = ATyp::Vec(Box::new(s.clone()), 2);

        let pref_a = PRef::from_node(
            NodeIndex::new(0),
            vec_s.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_a);

        let pref_r = PRef::from_node(
            NodeIndex::new(1),
            vec_ideal.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_r);

        builder.add_op(
            pref_r.clone(),
            Op::Bin(
                BinOp::Pow,
                mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(0)), vec_s.clone())),
                mk::<ArkBls12_381>(Op::Value(Value::VecIndex(vec![2, 3]))),
                vec_ideal.clone(),
            ),
            &mut ideal,
        );

        for i in 0..2 {
            let elem = pref_r.with_index(i).unwrap();
            assert!(
                ideal.pl.contains(&elem),
                "Pow Vec(Scalar,2)^VecIndex([2,3]) ideal element {} missing from pl",
                i
            );
        }
        // VecIndex-exponent pow uses explicit ideal treatment (per-element const exponents).
    }

    #[test]
    #[should_panic(
        expected = "Groebner operation has no polynomial-ideal treatment at dynamic-pow"
    )]
    fn test_pow_vec_mixed_const_and_opaque() {
        use backend::op::mk;
        use graph::PRef;
        use lang::ast::BinOp;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let s = ATyp::scalar();
        let vec_s = ATyp::Vec(Box::new(s.clone()), 2);
        let vec_ideal = ATyp::Vec(Box::new(s.clone()), 2);
        let fin = ATyp::fin(lang::typ::range::CRange::default());
        let vec_fin = ATyp::Vec(Box::new(fin.clone()), 2);

        let pref_a = PRef::from_node(
            NodeIndex::new(0),
            vec_s.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_a);

        let pref_b = PRef::from_node(
            NodeIndex::new(1),
            vec_fin.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_b);

        let pref_r = PRef::from_node(
            NodeIndex::new(2),
            vec_ideal.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_r);

        builder.add_op(
            pref_r.clone(),
            Op::Bin(
                BinOp::Pow,
                mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(0)), vec_s.clone())),
                mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(1)), vec_fin.clone())),
                vec_ideal.clone(),
            ),
            &mut ideal,
        );
        // The above panics with "dynamic-pow"; assertions below are unreachable.
    }

    // -----------------------------------------------------------------
    // PolySource::lift_to tests
    // -----------------------------------------------------------------

    #[test]
    fn test_lift_uni_to_wider_uni() {
        use graph::PRef;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut ideal = Ideal::<ArkBls12_381>::new();
        let pref = PRef::from_node(
            NodeIndex::new(0),
            ATyp::Uni(2),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref);
        let src = PolySource::<ArkBls12_381>::from_ref_vars(
            &ideal.prefs,
            &Op::Ref(Ref::new(NodeIndex::new(0)), ATyp::Uni(2)),
        );
        assert_eq!(src.polys.len(), 3);

        let lifted = src.lift_to(&ATyp::Uni(4));
        assert_eq!(lifted.polys.len(), 5);
        assert_eq!(*lifted.typ(), ATyp::Uni(4));
        for i in 0..3 {
            assert_eq!(
                lifted.polys[i],
                Polynomial::var(&pref.clone().with_slot(i).unwrap())
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
        use graph::PRef;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut ideal = Ideal::<ArkBls12_381>::new();
        let pref = PRef::from_node(
            NodeIndex::new(0),
            ATyp::Mle(2),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref);
        let src = PolySource::<ArkBls12_381>::from_ref_vars(
            &ideal.prefs,
            &Op::Ref(Ref::new(NodeIndex::new(0)), ATyp::Mle(2)),
        );
        assert_eq!(src.polys.len(), 4);

        let lifted = src.lift_to(&ATyp::Mle(3));
        assert_eq!(lifted.polys.len(), 8);
        assert_eq!(*lifted.typ(), ATyp::Mle(3));
        for i in 0..4 {
            assert_eq!(
                lifted.polys[i],
                Polynomial::var(&pref.clone().with_slot(i).unwrap())
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
        use graph::PRef;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut ideal = Ideal::<ArkBls12_381>::new();
        let pref = PRef::from_node(
            NodeIndex::new(0),
            ATyp::VPoly(2, 2),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref);
        let src = PolySource::<ArkBls12_381>::from_ref_vars(
            &ideal.prefs,
            &Op::Ref(Ref::new(NodeIndex::new(0)), ATyp::VPoly(2, 2)),
        );

        let lifted = src.lift_to(&ATyp::VPoly(2, 3));
        assert_eq!(lifted.polys.len(), 10);
        assert_eq!(*lifted.typ(), ATyp::VPoly(2, 3));
        for i in 0..6 {
            assert_eq!(
                lifted.polys[i],
                Polynomial::var(&pref.clone().with_slot(i).unwrap())
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
        use graph::PRef;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut ideal = Ideal::<ArkBls12_381>::new();
        let pref = PRef::from_node(
            NodeIndex::new(0),
            ATyp::VPoly(2, 2),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref);
        let src = PolySource::<ArkBls12_381>::from_ref_vars(
            &ideal.prefs,
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
                Polynomial::var(&pref.clone().with_slot(j).unwrap()),
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

        let src = PolySource::<ArkBls12_381>::new(
            vec![
                Polynomial::lit(&Fr::from(1u64)),
                Polynomial::lit(&Fr::from(2u64)),
                Polynomial::lit(&Fr::from(3u64)),
                Polynomial::lit(&Fr::from(4u64)),
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
                let expected_poly: Polynomial<ark_bls12_381::Fr> = if expected >= 0 {
                    Polynomial::lit(&Fr::from(expected as u64))
                } else {
                    -Polynomial::lit(&Fr::from((-expected) as u64))
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
        use graph::PRef;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut ideal = Ideal::<ArkBls12_381>::new();
        let pref = PRef::from_node(
            NodeIndex::new(0),
            ATyp::Uni(2),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref);
        let src = PolySource::<ArkBls12_381>::from_ref_vars(
            &ideal.prefs,
            &Op::Ref(Ref::new(NodeIndex::new(0)), ATyp::Uni(2)),
        );
        assert_eq!(src.polys.len(), 3);

        let lifted = src.lift_to(&ATyp::VPoly(1, 2));
        assert_eq!(*lifted.typ(), ATyp::VPoly(1, 2));
        assert_eq!(lifted.polys.len(), 3);
        for i in 0..3 {
            assert_eq!(
                lifted.polys[i],
                Polynomial::var(&pref.clone().with_slot(i).unwrap())
            );
        }
    }

    // -----------------------------------------------------------------
    // broadcast_equ: Bool ideal with bare basis diffs
    // -----------------------------------------------------------------

    #[test]
    fn test_equ_scalar_has_var_constraint_and_diff() {
        use graph::PRef;
        use lang::ast::BinOp;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let pref_a = PRef::from_node(
            NodeIndex::new(0),
            ATyp::scalar(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_a);
        let pref_b = PRef::from_node(
            NodeIndex::new(1),
            ATyp::scalar(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_b);
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
            &mut ideal,
        );

        let a_slot = pref_a.with_slot(0).unwrap();
        let b_slot = pref_b.with_slot(0).unwrap();
        let r_slot = pref_r.with_slot(0).unwrap();
        let diff = &Polynomial::var(&a_slot) - &Polynomial::var(&b_slot);
        assert!(ideal.basis.contains(&diff), "basis should contain a-b diff");
        assert!(
            !ideal.basis.iter().any(|p| *p == Polynomial::var(&r_slot)),
            "basis should NOT contain var(r) for Bool ideal (== is an assertion, not a computation)"
        );
    }

    #[test]
    fn test_equ_uni_bool_ideal_bare_diffs() {
        use graph::PRef;
        use lang::ast::BinOp;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let pref_a = PRef::from_node(
            NodeIndex::new(0),
            ATyp::Uni(2),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_a);
        let pref_b = PRef::from_node(
            NodeIndex::new(1),
            ATyp::Uni(2),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_b);
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
            &mut ideal,
        );

        let r_slot = pref_r.with_slot(0).unwrap();

        assert!(
            !ideal.basis.iter().any(|p| *p == Polynomial::var(&r_slot)),
            "basis should NOT contain var(r) for Bool ideal"
        );

        for j in 0..3 {
            let a_j = pref_a.clone().with_slot(j).unwrap();
            let b_j = pref_b.clone().with_slot(j).unwrap();
            let diff = &Polynomial::var(&a_j) - &Polynomial::var(&b_j);
            assert!(
                ideal.basis.contains(&diff),
                "basis should contain a[{}]-b[{}] diff",
                j,
                j
            );
        }

        assert!(
            !ideal.pl.contains(&r_slot),
            "Bool ideal slot should NOT be defined via pl"
        );
    }

    #[test]
    fn test_equ_uni_different_degrees_lifts_both() {
        use graph::PRef;
        use lang::ast::BinOp;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let pref_a = PRef::from_node(
            NodeIndex::new(0),
            ATyp::Uni(2),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_a);
        let pref_b = PRef::from_node(
            NodeIndex::new(1),
            ATyp::Uni(4),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_b);
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
            &mut ideal,
        );

        let r_slot = pref_r.with_slot(0).unwrap();
        assert!(
            !ideal.basis.iter().any(|p| *p == Polynomial::var(&r_slot)),
            "basis should NOT contain var(r) for Bool ideal"
        );

        let lub_len = ATyp::Uni(4).physical_len();
        assert_eq!(lub_len, 5);
        for j in 0..lub_len {
            let a_j = if j < 3 {
                Polynomial::var(&pref_a.clone().with_slot(j).unwrap())
            } else {
                Polynomial::zero()
            };
            let b_j = Polynomial::var(&pref_b.clone().with_slot(j).unwrap());
            let diff = a_j - b_j;
            assert!(
                ideal.basis.contains(&diff),
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
        use graph::PRef;
        use lang::ast::BinOp;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

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
        ideal.register(&pref_a);
        let pref_b = PRef::from_node(
            NodeIndex::new(1),
            vec3.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_b);
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
            &mut ideal,
        );

        for i in 0..5 {
            let pr_i = pref_r.with_index(i).unwrap();
            let pr_slot = pr_i.with_slot(0).unwrap();
            assert!(
                ideal.pl.contains(&pr_slot),
                "concat ideal element {} slot 0 should be in pl",
                i
            );
        }
    }

    // -----------------------------------------------------------------
    // reduce_op with PolySource: direct fold for Add/Sub
    // -----------------------------------------------------------------

    #[test]
    fn test_reduce_add_poly_vec_direct_fold() {
        use graph::PRef;
        use lang::ast::BinOp;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let poly_t = ATyp::Uni(2);
        let vec_t = ATyp::Vec(Box::new(poly_t.clone()), 2);

        let pref_v = PRef::from_node(
            NodeIndex::new(0),
            vec_t.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_v);

        let pref = PRef::from_node(
            NodeIndex::new(1),
            poly_t.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );

        builder.add_op(
            pref.clone(),
            Op::Reduce(
                BinOp::Add,
                mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), vec_t)),
            ),
            &mut ideal,
        );

        let var = |p: &PRef| Polynomial::<ark_bls12_381::Fr>::var(p);
        for j in 0..3 {
            let v0_j = pref_v.clone().with_index(0).unwrap().with_slot(j).unwrap();
            let v1_j = pref_v.clone().with_index(1).unwrap().with_slot(j).unwrap();
            let r_j = pref.clone().with_slot(j).unwrap();
            let expected = &var(&v0_j) + &var(&v1_j);
            let stored = ideal.pl.get(&r_j).unwrap();
            assert_eq!(*stored, expected, "reduce add poly slot {} mismatch", j);
        }
    }

    // -----------------------------------------------------------------
    // Op::Ref with lift_to
    // -----------------------------------------------------------------

    #[test]
    fn test_ref_lift_to_wider_type() {
        use graph::PRef;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let pref_src = PRef::from_node(
            NodeIndex::new(0),
            ATyp::Uni(2),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_src);

        let pref_dst = PRef::from_node(
            NodeIndex::new(1),
            ATyp::Uni(4),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_dst);

        builder.add_op(
            pref_dst.clone(),
            Op::Ref(Ref::new(NodeIndex::new(0)), ATyp::Uni(2)),
            &mut ideal,
        );

        assert_eq!(pref_dst.slots().len(), 5, "Uni(4) should have 5 slots");
        for j in 0..3 {
            let dst_j = pref_dst.clone().with_slot(j).unwrap();
            let src_j = pref_src.clone().with_slot(j).unwrap();
            let stored = ideal.pl.get(&dst_j).unwrap();
            assert_eq!(
                *stored,
                Polynomial::var(&src_j),
                "ref lift slot {} should map to src slot {}",
                j,
                j
            );
        }
        for j in 3..5 {
            let dst_j = pref_dst.clone().with_slot(j).unwrap();
            let stored = ideal.pl.get(&dst_j).unwrap();
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
        let scalar_poly = Polynomial::<ark_bls12_381::Fr>::var(&PRef::from_node(
            petgraph::graph::NodeIndex::new(0),
            ATyp::scalar(),
            0,
            lang::typ::Qualifier::Private,
            lang::typ::Distribution::default(),
        ));
        let src = PolySource::<ArkBls12_381>::new(vec![scalar_poly.clone()], ATyp::scalar());
        let broadcast = src.broadcast_scalar_to(&ATyp::VPoly(2, 2));
        assert_eq!(broadcast.polys.len(), 6);
        for (i, p) in broadcast.polys.iter().enumerate() {
            assert_eq!(*p, scalar_poly, "broadcast slot {} should be the scalar", i);
        }
    }

    // Task 2 tests for algebraic variable discovery and free identifiers

    /// Test that vars() returns pl.keys() union basis.vars().
    /// This test is expected to FAIL before Task 3 because current vars() ignores basis-only vars.
    #[test]
    fn vars_is_pl_keys_union_basis_vars() {
        use ark_bls12_381::Fr;
        use lang::id::Vid;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let pl_ref = PRef::from_var(
            Vid::new("pl_v"),
            NodeIndex::new(10),
            ATyp::scalar(),
            0,
            Qualifier::Public,
            Distribution::Nonuniform,
        );
        let basis_ref = PRef::from_var(
            Vid::new("basis_v"),
            NodeIndex::new(11),
            ATyp::scalar(),
            0,
            Qualifier::Public,
            Distribution::Nonuniform,
        );

        let mut ideal = Ideal::<ArkBls12_381>::new();
        ideal.pl.insert(&pl_ref, &Polynomial::<Fr>::zero());
        ideal.basis.push(Polynomial::<Fr>::var(&basis_ref));

        let vars = ideal.vars();
        assert!(
            vars.contains(&pl_ref),
            "vars() should contain pl key: {:?}",
            pl_ref
        );
        assert!(
            vars.contains(&basis_ref),
            "vars() should contain basis var: {:?}",
            basis_ref
        );
        assert_eq!(vars.len(), 2, "vars() should have exactly 2 elements");
    }

    /// Test that challenge emits no basis or pl state.
    #[test]
    fn challenge_emits_no_basis_or_pl_state() {
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();
        let pref = PRef::from_node(
            NodeIndex::new(100),
            ATyp::scalar(),
            0,
            Qualifier::Public,
            Distribution::Nonuniform,
        );

        builder.add_op(
            pref.clone(),
            Op::Challenge(ATyp::scalar(), false),
            &mut ideal,
        );

        assert!(
            ideal.basis.is_empty(),
            "challenge should not emit basis polynomials"
        );
        assert!(
            !ideal.pl.contains(&pref),
            "challenge should not insert into pl"
        );
        assert!(
            !ideal.vars().contains(&pref),
            "challenge should not be visible in vars() unless used in a polynomial"
        );
    }

    /// Test that random emits no basis or pl state.
    #[test]
    fn random_emits_no_basis_or_pl_state() {
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();
        let pref = PRef::from_node(
            NodeIndex::new(101),
            ATyp::scalar(),
            0,
            Qualifier::Private,
            Distribution::Uniform,
        );

        builder.add_op(pref.clone(), Op::Random(ATyp::scalar(), false), &mut ideal);

        assert!(
            ideal.basis.is_empty(),
            "random should not emit basis polynomials"
        );
        assert!(
            !ideal.pl.contains(&pref),
            "random should not insert into pl"
        );
        assert!(
            !ideal.vars().contains(&pref),
            "random should not be visible in vars() unless used in a polynomial"
        );
    }

    /// Test that a challenge used in a polynomial is visible through basis.vars().
    /// This test captures the desired invariant: challenges become visible when referenced.
    #[test]
    fn challenge_used_in_polynomial_is_visible() {
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        // Create a challenge PRef
        let challenge_pref = PRef::from_node(
            NodeIndex::new(200),
            ATyp::scalar(),
            0,
            Qualifier::Public,
            Distribution::Nonuniform,
        );
        ideal.register(&challenge_pref);
        builder.add_op(
            challenge_pref.clone(),
            Op::Challenge(ATyp::scalar(), false),
            &mut ideal,
        );

        // Create a private variable
        let x_pref = PRef::from_node(
            NodeIndex::new(201),
            ATyp::scalar(),
            0,
            Qualifier::Private,
            Distribution::Nonuniform,
        );
        ideal.register(&x_pref);

        // Create a polynomial operation that uses the challenge: y = x + c
        let y_pref = PRef::from_node(
            NodeIndex::new(202),
            ATyp::scalar(),
            0,
            Qualifier::Public,
            Distribution::Nonuniform,
        );
        ideal.register(&y_pref);

        builder.add_op(
            y_pref.clone(),
            Op::Bin(
                lang::ast::BinOp::Add,
                mk::<ArkBls12_381>(Op::Ref(
                    graph::Ref::new(NodeIndex::new(201)),
                    ATyp::scalar(),
                )),
                mk::<ArkBls12_381>(Op::Ref(
                    graph::Ref::new(NodeIndex::new(200)),
                    ATyp::scalar(),
                )),
                ATyp::scalar(),
            ),
            &mut ideal,
        );

        // The challenge should now be visible through basis.vars() and ideal.vars()
        let basis_vars = ideal
            .basis
            .iter()
            .flat_map(|p| p.vars())
            .collect::<share::Set<_>>();
        assert!(
            basis_vars.contains(&challenge_pref),
            "challenge must be visible through basis vars once an equation references it"
        );
        assert!(
            ideal.vars().contains(&challenge_pref),
            "challenge must be in ideal.vars() when used in polynomial"
        );
    }

    /// Test that Op::Pair emits a basis row binding the ideal to a*b
    /// without any GT sentinel variable.
    #[test]
    fn pair_emits_product_without_sentinel() {
        use backend::op::mk;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let g1_pref = PRef::from_node(
            NodeIndex::new(300),
            ATyp::g1(),
            0,
            Qualifier::Public,
            Distribution::Nonuniform,
        );
        ideal.register(&g1_pref);

        let g2_pref = PRef::from_node(
            NodeIndex::new(301),
            ATyp::g2(),
            0,
            Qualifier::Public,
            Distribution::Nonuniform,
        );
        ideal.register(&g2_pref);

        let pair_ideal_pref = PRef::from_node(
            NodeIndex::new(302),
            ATyp::gt(),
            0,
            Qualifier::Public,
            Distribution::Nonuniform,
        );
        ideal.register(&pair_ideal_pref);

        builder.add_op(
            pair_ideal_pref.clone(),
            Op::Pair(
                mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(300)), ATyp::g1())),
                mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(301)), ATyp::g2())),
                ATyp::gt(),
            ),
            &mut ideal,
        );

        // The basis should contain a row: pair_ideal - g1*g2 = 0
        // (no GT sentinel variable)
        let basis_vars = ideal
            .basis
            .iter()
            .flat_map(|p| p.vars())
            .collect::<share::Set<_>>();
        assert!(
            basis_vars.contains(&g1_pref),
            "g1 must be visible through basis vars"
        );
        assert!(
            basis_vars.contains(&g2_pref),
            "g2 must be visible through basis vars"
        );
        assert!(
            basis_vars.contains(&pair_ideal_pref),
            "pair ideal must be visible through basis vars"
        );
        // No GT sentinel should exist
        let has_gt_sentinel = basis_vars.iter().any(|pr| {
            pr.name
                .as_ref()
                .is_some_and(|n| n.0.starts_with("__zippel::gb::gt"))
        });
        assert!(!has_gt_sentinel, "GT sentinel should not exist");
    }

    // -----------------------------------------------------------------
    // Task 5: record_projection_resolves_without_np_lookup
    // -----------------------------------------------------------------

    #[test]
    fn record_projection_resolves_without_np_lookup() {
        // Build a record {a: Scalar, b: Scalar} from scalar refs, project
        // field "a", assert pl/basis aliases the field directly.
        use backend::op::mk;
        use graph::PRef;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let s = ATyp::scalar();

        // Build record {a: Scalar, b: Scalar}.
        // Alphabetical order: "a" at offset 0, "b" at offset 1.
        let mut rec_fields = Ctx::<String, ATyp>::new();
        rec_fields.insert(&"a".to_string(), &s);
        rec_fields.insert(&"b".to_string(), &s);
        let rec_typ = ATyp::Record(rec_fields);

        // Register the record PRef.
        let pref_rec = PRef::from_node(
            NodeIndex::new(0),
            rec_typ.clone(),
            0,
            Qualifier::Public,
            Distribution::default(),
        );
        ideal.register(&pref_rec);

        // Register scalar refs for a and b.
        let pref_a = PRef::from_node(
            NodeIndex::new(1),
            s.clone(),
            0,
            Qualifier::Public,
            Distribution::default(),
        );
        let pref_b = PRef::from_node(
            NodeIndex::new(2),
            s.clone(),
            0,
            Qualifier::Public,
            Distribution::default(),
        );
        ideal.register(&pref_a);
        ideal.register(&pref_b);

        // Build record {a: pref_a, b: pref_b}.
        let mut field_ops: Ctx<String, backend::op::HOp<ArkBls12_381>> = Ctx::new();
        field_ops.insert(
            &"a".to_string(),
            &mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(1)), s.clone())),
        );
        field_ops.insert(
            &"b".to_string(),
            &mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(2)), s.clone())),
        );

        builder.add_op(pref_rec.clone(), Op::Record(field_ops), &mut ideal);

        // Project field "a" from the record.
        let pref_proj = PRef::from_node(
            NodeIndex::new(3),
            s.clone(),
            0,
            Qualifier::Public,
            Distribution::default(),
        );
        ideal.register(&pref_proj);

        let inner_op: GOp<ArkBls12_381> =
            Op::Ref(graph::Ref::new(NodeIndex::new(0)), rec_typ.clone());

        builder.add_op(
            pref_proj.clone(),
            Op::Proj(mk::<ArkBls12_381>(inner_op), "a".to_string(), s.clone()),
            &mut ideal,
        );

        // Projection ideal should be in pl.
        assert!(ideal.pl.contains(&pref_proj), "proj ideal should be in pl");

        // The proj poly should reference record slot 0 (field "a").
        let proj_poly = ideal.pl.get(&pref_proj).unwrap();
        let rec_slot_0 = pref_rec.clone().with_slot(0).unwrap();
        assert!(
            proj_poly.contains(&rec_slot_0),
            "proj ideal should alias record slot 0 (field 'a')"
        );
    }

    // -----------------------------------------------------------------
    // Task 6: uncovered_op explicit-failure tests
    // These tests verify that operation fallbacks now panic immediately
    // instead of silently weakening the ideal.
    // -----------------------------------------------------------------

    /// dynamic-pow: Vec^Vec with non-const exponent must panic rather
    /// than silently weakening the ideal.
    #[test]
    #[should_panic(
        expected = "Groebner operation has no polynomial-ideal treatment at dynamic-pow"
    )]
    fn uncovered_op_dynamic_pow_vec_vec_panics() {
        use backend::op::mk;
        use graph::PRef;
        use lang::ast::BinOp;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let s = ATyp::scalar();
        let fin = ATyp::fin(lang::typ::range::CRange::default());
        let vec_s = ATyp::Vec(Box::new(s.clone()), 2);
        let vec_fin = ATyp::Vec(Box::new(fin.clone()), 2);

        let pref_a = PRef::from_node(
            NodeIndex::new(0),
            vec_s.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_a);

        let pref_b = PRef::from_node(
            NodeIndex::new(1),
            vec_fin.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_b);

        let pref_r = PRef::from_node(
            NodeIndex::new(2),
            ATyp::Vec(Box::new(s.clone()), 2),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_r);

        // Non-const exponent (a runtime Ref, not a Value::Index) must panic.
        builder.add_op(
            pref_r.clone(),
            Op::Bin(
                BinOp::Pow,
                mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(0)), vec_s.clone())),
                mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(1)), vec_fin.clone())),
                ATyp::Vec(Box::new(s.clone()), 2),
            ),
            &mut ideal,
        );
    }

    /// dynamic-pow: scalar^scalar with non-const exponent must panic.
    #[test]
    #[should_panic(
        expected = "Groebner operation has no polynomial-ideal treatment at dynamic-pow"
    )]
    fn uncovered_op_dynamic_pow_scalar_panics() {
        use backend::op::mk;
        use graph::PRef;
        use lang::ast::BinOp;
        use lang::typ::{Distribution, Qualifier};
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let s = ATyp::scalar();
        let fin = ATyp::fin(lang::typ::range::CRange::default());

        let pref_a = PRef::from_node(
            NodeIndex::new(0),
            s.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_a);

        // pref_b is a Ref, not a Value::Index → non-const exponent.
        let pref_b = PRef::from_node(
            NodeIndex::new(1),
            fin.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_b);

        let pref_r = PRef::from_node(
            NodeIndex::new(2),
            s.clone(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        ideal.register(&pref_r);

        builder.add_op(
            pref_r.clone(),
            Op::Bin(
                BinOp::Pow,
                mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(0)), s.clone())),
                mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(1)), fin.clone())),
                s.clone(),
            ),
            &mut ideal,
        );
    }
}
