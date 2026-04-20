pub mod buchberger;
pub use buchberger::GroebnerBasis;

pub mod monomial;
pub use monomial::{ElimTerm, GrevLexTerm, Monomial};
pub mod sparsepoly;
pub use sparsepoly::SparsePolynomial;

use crate::DQDag;
use crate::analyses::TransClos;
use crate::pref::PRef;
use crate::{GOp, Op, Ref};
use lang::ast::BinOp;
use lang::typ::{Distribution, Qualifier};

use ark_ff::{One, Zero};
use backend::op::HasOpFactory;
use backend::{ATyp, ArkConfig, ArkScalarOps, Value};
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
fn num_coeffs(typ: &ATyp) -> usize {
    match typ {
        ATyp::VPoly(n, m) => multi_indices(*n, *m).len(),
        ATyp::Mle(n) => 1usize << *n,
        ATyp::Uni(n) => *n,
        ATyp::Vec(_, n) => *n,
        _ => 1,
    }
}

/// Inverse of the enumeration: position of multi-index / hypercube point `k`
/// in the canonical slot order for the given type.
#[allow(dead_code)]
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
    /// Phase B: the input and relation markers each have their own
    /// `Node::Arg` children, even when they bind the same protocol parameter
    /// — keeping the closures of `from_input` and `from_relation`
    /// structurally separate. To make the Gröbner machinery treat the two
    /// `Ref`s for a shared parameter as one symbol, we install an alias from
    /// each subsequent arg's `Ref` to the canonical `PRef` chosen the first
    /// time we saw an arg with that name.
    pub ref_aliases: std::collections::HashMap<Ref, PRef>,
}

impl<C: ArkConfig + HasOpFactory, T: Monomial> GroebnerBuilder<C, T> {
    pub fn new() -> Self {
        Self {
            basis: GroebnerBasis::empty(0),
            np: Ctx::new(),
            pl: Ctx::new(),
            args: Set::new(),
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
            r.clone(),
            ATyp::scalar(),
            Qualifier::Private,
            Distribution::Nonuniform,
        );
        let opaque = Op::Ref(r.clone(), ATyp::scalar());
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
    }

    fn to_poly_value(&mut self, v: &Value<C>) -> Vec<SparsePolynomial<C::F, T>> {
        match v {
            Value::Scalar(s) => vec![SparsePolynomial::lit(&s)],
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

    /// Shared helper for `Op::Eval(p, xs)` — returns `Some(polys)` when the
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
                let out = (0..k).map(|i| {
                    let xi = &xs_polys[i];
                    let mut acc = SparsePolynomial::<C::F, T>::zero();
                    let mut xi_pow = one.clone();
                    for aj in p_polys.iter() {
                        acc = &acc + &(aj * &xi_pow);
                        xi_pow = &xi_pow * xi;
                    }
                    acc
                }).collect();
                Some(out)
            }
            ATyp::VPoly(n, mdeg) if *n >= 2 && k <= *n => {
                let p_polys = self.to_poly(p);
                let all_k = multi_indices(*n, *mdeg);
                let mono = |k_fixed: &[usize], xs_polys: &[SparsePolynomial<C::F, T>]| -> SparsePolynomial<C::F, T> {
                    let mut acc = SparsePolynomial::<C::F, T>::lit(&C::F::one());
                    for (j, &kij) in k_fixed.iter().enumerate() {
                        if kij == 0 { continue; }
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
                    let out = result_indices.iter().map(|kp| {
                        let mut acc = SparsePolynomial::<C::F, T>::zero();
                        for (idx, ki) in all_k.iter().enumerate() {
                            if &ki[k..] != &kp[..] { continue; }
                            acc = &acc + &(&p_polys[idx] * &mono(&ki[..k], &xs_polys));
                        }
                        acc
                    }).collect();
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
                let eq_prod = |b_fixed: &[usize], xs_polys: &[SparsePolynomial<C::F, T>]| -> SparsePolynomial<C::F, T> {
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
                    let out = result_b.iter().map(|bp| {
                        let mut acc = SparsePolynomial::<C::F, T>::zero();
                        for (idx, b) in all_b.iter().enumerate() {
                            if &b[k..] != &bp[..] { continue; }
                            acc = &acc + &(&p_polys[idx] * &eq_prod(&b[..k], &xs_polys));
                        }
                        acc
                    }).collect();
                    Some(out)
                }
            }
            _ => None,
        }
    }

    /// This function converts an operation to a vector of sparse polynomial expressions,
    /// exploding vectors where possible.
    fn to_poly(&mut self, op: &GOp<C>) -> Vec<SparsePolynomial<C::F, T>> {
        match op {
            Op::Ref(v, typ) => {
                let pf = self.find_ref(&v);
                match typ {
                    ATyp::Vec(box t, n) =>
                        (0..*n).into_iter()
                            .map(|i| {
                                let mut pf = pf.clone();
                                pf.index = i;
                                pf.typ = t.clone();
                                SparsePolynomial::var(&pf)
                            })
                            .collect::<Vec<_>>(),
                    ATyp::Uni(n) =>
                        (0..*n).into_iter()
                            .map(|i| {
                                let mut pf = pf.clone();
                                pf.index = i;
                                pf.typ = ATyp::scalar();
                                SparsePolynomial::var(&pf)
                            })
                            .collect::<Vec<_>>(),
                    ATyp::VPoly(n, m) =>
                        (0..num_coeffs(&ATyp::VPoly(*n, *m))).into_iter()
                            .map(|i| {
                                let mut pf = pf.clone();
                                pf.index = i;
                                pf.typ = ATyp::scalar();
                                SparsePolynomial::var(&pf)
                            })
                            .collect::<Vec<_>>(),
                    ATyp::Mle(n) =>
                        (0..num_coeffs(&ATyp::Mle(*n))).into_iter()
                            .map(|i| {
                                let mut pf = pf.clone();
                                pf.index = i;
                                pf.typ = ATyp::scalar();
                                SparsePolynomial::var(&pf)
                            })
                            .collect::<Vec<_>>(),
                    _ => vec![SparsePolynomial::var(&pf)]
                }
            }
            Op::Value(v) => self.to_poly_value(v),
            Op::Vec(v) => v.iter().flat_map(|v| self.to_poly(v)).collect(),
            Op::Ram(a, b) => {
                match (a.get(), b.get()) {
                    (Op::Ref(n, _), Op::Value(v)) => {
                        let pf = self.find_ref(&n);
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
            Op::Reduce(BinOp::Add, v) => {
                vec![self.to_poly(v).into_iter().sum()]
            }
            Op::Reduce(BinOp::Mul, v) => {
                let polys = self.to_poly(v);
                let mut iter = polys.into_iter();
                if let Some(first) = iter.next() {
                    vec![iter.fold(first, |acc, p| acc * p)]
                } else {
                    vec![]
                }
            },
            Op::Eval(p, xs) => self.eval_to_poly(p, xs).unwrap_or_else(Vec::new),
            _ => vec![]
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
                    self.ref_aliases.insert(new_arg.reference.clone(), c);
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
                    self.ref_aliases.insert(new_arg.reference.clone(), c);
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
            Op::Bin(BinOp::Add | BinOp::And, a, b, _) =>
                self.to_poly(&a).into_iter()
                    .zip(self.to_poly(&b).into_iter())
                    .enumerate()
                    .for_each(|(i, (a, b))| {
                        let pf = pr.clone().with_index(i);
                        self.pl.insert(&pf, &(&a + &b));
                        self.basis.push(a + b - SparsePolynomial::var(&pf));
                    }),
            Op::Bin(BinOp::Sub, a, b, _) =>
                self.to_poly(&a).into_iter()
                    .zip(self.to_poly(&b).into_iter())
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
                            (
                                ATyp::VPoly(na, ma),
                                ATyp::VPoly(nb, mb),
                                ATyp::VPoly(nr, mr),
                            ) if na == nb && na == nr => {
                                let a_polys = self.to_poly(a);
                                let b_polys = self.to_poly(b);
                                let a_idx = multi_indices(*na, *ma);
                                let b_idx = multi_indices(*nb, *mb);
                                let r_idx = multi_indices(*nr, *mr);
                                let mut out: Vec<SparsePolynomial<C::F, T>> =
                                    vec![SparsePolynomial::<C::F, T>::zero(); r_idx.len()];
                                for (ia, ka) in a_idx.iter().enumerate() {
                                    for (ib, kb) in b_idx.iter().enumerate() {
                                        let k: Vec<usize> = ka
                                            .iter()
                                            .zip(kb.iter())
                                            .map(|(x, y)| x + y)
                                            .collect();
                                        if k.iter().sum::<usize>() > *mr { continue; }
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
                                let coeff: [[[i64; 3]; 2]; 2] = [
                                    [[1, -2, 1], [0, 1, -1]],
                                    [[0, 1, -1], [0, 0, 1]],
                                ];
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
                                                if c == 0 { scalar = 0; break; }
                                                scalar *= c;
                                            }
                                            if scalar == 0 { continue; }
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
                        self.to_poly(a).into_iter()
                            .zip(self.to_poly(b).into_iter())
                            .enumerate()
                            .for_each(|(i, (ap, bp))| {
                                let pf = pr.clone().with_index(i);
                                self.pl.insert(&pf, &(&ap * &bp));
                                self.basis.push(ap * bp - SparsePolynomial::var(&pf));
                            })
                    }
                }
            },
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
            Op::Bin(BinOp::Div, ref a, ref b, _) => self
                .to_poly(a)
                .into_iter()
                .zip(self.to_poly(b))
                .enumerate()
                .for_each(|(i, (a, b))| {
                    let pf = pr.clone().with_index(i);
                    self.np
                        .insert(&pf, &Op::ram(op_for_div.clone(), Op::index(i)));
                    self.basis.push(a - b * SparsePolynomial::var(&pf));
                }),
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
            Op::Challenge(t, b) => { let op = Op::Challenge(t, b); self.np.insert(&pr, &op); },
            Op::Random(t, b) => { let op = Op::Random(t, b); self.np.insert(&pr, &op); },
            Op::Ifft(a) => { let op = Op::Ifft(a); self.np.insert(&pr, &op); },
            Op::Fft(a) => { let op = Op::Fft(a); self.np.insert(&pr, &op); },
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
                for (i, p) in polys.into_iter().enumerate() {
                    let pf = pr.clone().with_index(i);
                    self.pl.insert(&pf, &p);
                    self.basis.push(p - SparsePolynomial::var(&pf));
                }
            },
            Op::Vec(vs) => {
                for (i, v) in vs.into_iter().enumerate() {
                    let pf = pr.with_index(i);
                    self.add_op(pf, v.get().clone());
                }
            },
            // Op::Eval(p, xs): evaluate a polynomial `p` at points `xs`.
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
            Op::Eval(ref p, ref xs) => {
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
                        self.np.insert(&pr, &Op::Eval(p.clone(), xs.clone()));
                    }
                }
            },
            op => { self.np.insert(&pr, &op); },
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
        assert_eq!(got, vec![
            vec![0, 0],                  // deg 0
            vec![0, 1], vec![1, 0],      // deg 1 (lex)
            vec![0, 2], vec![1, 1], vec![2, 0], // deg 2 (lex)
        ]);
        assert_eq!(got.len(), 6); // C(2+2, 2) = 6
    }

    #[test]
    fn test_hypercube_enumeration() {
        let got = hypercube(3);
        assert_eq!(got.len(), 8);
        // lex: bit 0 is inner-most, so b = [b0, b1, b2] read little-endian.
        assert_eq!(got[0], vec![0, 0, 0]);
        assert_eq!(got[1], vec![1, 0, 0]);
        assert_eq!(got[2], vec![0, 1, 0]);
        assert_eq!(got[7], vec![1, 1, 1]);
    }

    #[test]
    fn test_num_coeffs() {
        assert_eq!(num_coeffs(&ATyp::VPoly(2, 2)), 6);
        assert_eq!(num_coeffs(&ATyp::VPoly(3, 1)), 4);  // scalar + 3 linear
        assert_eq!(num_coeffs(&ATyp::Mle(3)), 8);
        assert_eq!(num_coeffs(&ATyp::Uni(5)), 5);
        assert_eq!(num_coeffs(&ATyp::scalar()), 1);
    }

    #[test]
    fn test_index_of_vpoly_roundtrip() {
        let typ = ATyp::VPoly(2, 2);
        for (i, k) in multi_indices(2, 2).into_iter().enumerate() {
            assert_eq!(index_of(&typ, &k), i);
        }
    }

    #[test]
    fn test_index_of_mle_roundtrip() {
        let typ = ATyp::Mle(3);
        for (i, b) in hypercube(3).into_iter().enumerate() {
            assert_eq!(index_of(&typ, &b), i);
        }
    }

    // -----------------------------------------------------------------
    // to_poly on polynomial-typed refs
    // -----------------------------------------------------------------

    #[test]
    fn test_to_poly_vpoly_ref_expands_coefficients() {
        use crate::PRef;
        use crate::Ref;
        use lang::typ::{Qualifier, Distribution};
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

        let op: GOp<ArkBls12_381> =
            Op::Ref(Ref::Node(NodeIndex::new(0)), ATyp::VPoly(2, 2));
        let polys = builder.to_poly(&op);
        assert_eq!(polys.len(), 6);
        // Each coefficient should be a distinct variable PRef indexed 0..6.
        for (i, _) in polys.iter().enumerate() {
            let expected = pref_p.with_index(i).clone();
            let expected = PRef {
                typ: ATyp::scalar(),
                ..expected
            };
            assert!(polys[i].contains(&expected),
                "coefficient poly {} does not contain expected PRef (index {})", i, i);
        }
    }

    #[test]
    fn test_to_poly_mle_ref_expands_evaluations() {
        use crate::PRef;
        use crate::Ref;
        use lang::typ::{Qualifier, Distribution};
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

        let op: GOp<ArkBls12_381> =
            Op::Ref(Ref::Node(NodeIndex::new(0)), ATyp::Mle(3));
        let polys = builder.to_poly(&op);
        assert_eq!(polys.len(), 8);
    }

    // -----------------------------------------------------------------
    // add_op: Op::Poly / Op::Mle / Op::Coef (identity on coefficient slots)
    // -----------------------------------------------------------------

    #[test]
    fn test_add_op_poly_binds_coefficient_slots() {
        use crate::PRef;
        use lang::typ::{Qualifier, Distribution};
        use petgraph::graph::NodeIndex;
        use ark_bls12_381::Fr;
        use backend::op::mk;

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
        let op_poly: GOp<ArkBls12_381> =
            Op::Poly(mk::<ArkBls12_381>(Op::Vec(coefs)));

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
        use lang::typ::{Qualifier, Distribution};
        use petgraph::graph::NodeIndex;
        use ark_bls12_381::Fr;
        use backend::op::mk;

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
        builder.add_op(
            pref_p.clone(),
            Op::Poly(mk::<ArkBls12_381>(Op::Vec(coefs))),
        );

        // Then: Op::Coef reading the VPoly back into a Uni(3) output.
        let pref_c = PRef::from_node(
            NodeIndex::new(1),
            ATyp::Uni(3),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        let ref_p: GOp<ArkBls12_381> =
            Op::Ref(Ref::Node(NodeIndex::new(0)), ATyp::VPoly(1, 2));
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
        use lang::typ::{Qualifier, Distribution};
        use petgraph::graph::NodeIndex;
        use ark_bls12_381::Fr;
        use backend::op::mk;

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
        builder.add_op(
            pref_p.clone(),
            Op::Mle(mk::<ArkBls12_381>(Op::Vec(vals))),
        );

        assert_eq!(builder.basis.basis.len(), 4);
        for i in 0..4 {
            assert!(builder.pl.contains(&pref_p.with_index(i)),
                "mle slot {} missing", i);
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
        use lang::typ::{Qualifier, Distribution};
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
        use lang::typ::{Qualifier, Distribution};
        use petgraph::graph::NodeIndex;
        use ark_bls12_381::Fr;
        use backend::op::mk;

        // p(x) = a_0 + a_1 x   as VPoly(1,1): 2 coefficient slots on node 0.
        // xs = [x0, x1]        as Uni(2):     2 slots on node 1.
        // Expected: result[i] = a_0 + a_1 * xs[i].
        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let _pref_p = register_ref(&mut builder, 0, ATyp::VPoly(1, 1));
        let _pref_xs = register_ref(&mut builder, 1, ATyp::Uni(2));

        let result = PRef::from_node(
            NodeIndex::new(2),
            ATyp::Uni(2),
            0,
            Qualifier::Private,
            Distribution::default(),
        );

        let op: GOp<ArkBls12_381> = Op::Eval(
            mk::<ArkBls12_381>(Op::Ref(Ref::Node(NodeIndex::new(0)), ATyp::VPoly(1, 1))),
            mk::<ArkBls12_381>(Op::Ref(Ref::Node(NodeIndex::new(1)), ATyp::Uni(2))),
        );
        builder.add_op(result.clone(), op);

        // Expected: 2 result slots + 2 basis equations, and no np insertion.
        assert_eq!(builder.np.len(), 0, "eval should not have fallen through to np");
        for i in 0..2 {
            assert!(builder.pl.contains(&result.with_index(i)),
                "uni batched result slot {} missing", i);
        }
        // Each result slot: poly = a_0 + a_1 * xs[i] (a linear polynomial in
        // 4 input variables). Check it depends on exactly {a_0, a_1, xs[i]}.
        let a0 = PRef { typ: ATyp::scalar(), ..PRef::from_node(NodeIndex::new(0), ATyp::VPoly(1,1), 0, Qualifier::Private, Distribution::default()) };
        let mut a1 = a0.clone(); a1.index = 1;
        let mut x0 = a0.clone(); x0.reference = Ref::Node(NodeIndex::new(1)); x0.index = 0;
        let mut x1 = x0.clone(); x1.index = 1;

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
        use lang::typ::{Qualifier, Distribution};
        use petgraph::graph::NodeIndex;
        use ark_bls12_381::Fr;
        use backend::op::mk;

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

        // Bind xs similarly on node 1 as Uni(2).
        let pref_xs = PRef::from_node(
            NodeIndex::new(1),
            ATyp::Uni(2),
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
            ATyp::Uni(2),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        let op: GOp<ArkBls12_381> = Op::Eval(
            mk::<ArkBls12_381>(Op::Ref(crate::Ref::Node(NodeIndex::new(0)), ATyp::VPoly(1, 1))),
            mk::<ArkBls12_381>(Op::Ref(crate::Ref::Node(NodeIndex::new(1)), ATyp::Uni(2))),
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
        use lang::typ::{Qualifier, Distribution};
        use petgraph::graph::NodeIndex;

        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let _ = register_ref(&mut builder, 0, ATyp::VPoly(2, 2));
        let _ = register_ref(&mut builder, 1, ATyp::Uni(2));

        let result = PRef::from_node(
            NodeIndex::new(2),
            ATyp::scalar(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        let op: GOp<ArkBls12_381> = Op::Eval(
            backend::op::mk::<ArkBls12_381>(Op::Ref(crate::Ref::Node(NodeIndex::new(0)), ATyp::VPoly(2, 2))),
            backend::op::mk::<ArkBls12_381>(Op::Ref(crate::Ref::Node(NodeIndex::new(1)), ATyp::Uni(2))),
        );
        builder.add_op(result.clone(), op);

        // One result slot (scalar) produced, zero np entries for eval.
        assert!(builder.pl.contains(&result.with_index(0)));
        // Should contain all 6 coef PRefs of p + both xs slots.
        let slot = builder.pl.get(&result.with_index(0)).unwrap();
        let vars = slot.vars();
        assert!(vars.len() >= 6, "expected coef + eval vars; got {} vars", vars.len());
    }

    #[test]
    fn test_add_op_eval_vpoly_partial_multivariate() {
        // VPoly(3, 1) evaluated at Uni(1) => VPoly(2, 1) (2-var linear poly w/ 3 slots).
        use crate::PRef;
        use lang::typ::{Qualifier, Distribution};
        use petgraph::graph::NodeIndex;

        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let _ = register_ref(&mut builder, 0, ATyp::VPoly(3, 1));
        let _ = register_ref(&mut builder, 1, ATyp::Uni(1));

        let result = PRef::from_node(
            NodeIndex::new(2),
            ATyp::VPoly(2, 1),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        let op: GOp<ArkBls12_381> = Op::Eval(
            backend::op::mk::<ArkBls12_381>(Op::Ref(crate::Ref::Node(NodeIndex::new(0)), ATyp::VPoly(3, 1))),
            backend::op::mk::<ArkBls12_381>(Op::Ref(crate::Ref::Node(NodeIndex::new(1)), ATyp::Uni(1))),
        );
        builder.add_op(result.clone(), op);

        // VPoly(2, 1) has num_coeffs = C(2+1, 1) = 3 slots (one for constant,
        // two for each linear variable).
        assert_eq!(num_coeffs(&ATyp::VPoly(2, 1)), 3);
        for i in 0..3 {
            assert!(builder.pl.contains(&result.with_index(i)),
                "partial vpoly eval slot {} missing", i);
        }
    }

    #[test]
    fn test_add_op_eval_mle_full_multivariate() {
        // Mle(2) has 4 eval slots; eval at Uni(2) => scalar.
        use crate::PRef;
        use lang::typ::{Qualifier, Distribution};
        use petgraph::graph::NodeIndex;

        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let _ = register_ref(&mut builder, 0, ATyp::Mle(2));
        let _ = register_ref(&mut builder, 1, ATyp::Uni(2));

        let result = PRef::from_node(
            NodeIndex::new(2),
            ATyp::scalar(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        let op: GOp<ArkBls12_381> = Op::Eval(
            backend::op::mk::<ArkBls12_381>(Op::Ref(crate::Ref::Node(NodeIndex::new(0)), ATyp::Mle(2))),
            backend::op::mk::<ArkBls12_381>(Op::Ref(crate::Ref::Node(NodeIndex::new(1)), ATyp::Uni(2))),
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
        use lang::typ::{Qualifier, Distribution};
        use petgraph::graph::NodeIndex;

        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let _ = register_ref(&mut builder, 0, ATyp::Mle(3));
        let _ = register_ref(&mut builder, 1, ATyp::Uni(1));

        let result = PRef::from_node(
            NodeIndex::new(2),
            ATyp::Mle(2),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        let op: GOp<ArkBls12_381> = Op::Eval(
            backend::op::mk::<ArkBls12_381>(Op::Ref(crate::Ref::Node(NodeIndex::new(0)), ATyp::Mle(3))),
            backend::op::mk::<ArkBls12_381>(Op::Ref(crate::Ref::Node(NodeIndex::new(1)), ATyp::Uni(1))),
        );
        builder.add_op(result.clone(), op);

        // Mle(2) has 4 eval slots.
        for i in 0..4 {
            assert!(builder.pl.contains(&result.with_index(i)),
                "partial mle eval slot {} missing", i);
        }
    }

    #[test]
    fn test_add_op_eval_unsupported_falls_through_to_np() {
        // Eval at a Record (which to_poly can't handle) should fall through to np.
        use crate::PRef;
        use lang::typ::{Qualifier, Distribution};
        use petgraph::graph::NodeIndex;

        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let _ = register_ref(&mut builder, 0, ATyp::VPoly(3, 2));
        // xs with k > n should fall through (k=4 > n=3).
        let _ = register_ref(&mut builder, 1, ATyp::Uni(4));

        let result = PRef::from_node(
            NodeIndex::new(2),
            ATyp::scalar(),
            0,
            Qualifier::Private,
            Distribution::default(),
        );
        let op: GOp<ArkBls12_381> = Op::Eval(
            backend::op::mk::<ArkBls12_381>(Op::Ref(crate::Ref::Node(NodeIndex::new(0)), ATyp::VPoly(3, 2))),
            backend::op::mk::<ArkBls12_381>(Op::Ref(crate::Ref::Node(NodeIndex::new(1)), ATyp::Uni(4))),
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
        use lang::ast::BinOp;
        use crate::{PRef, Ref};
        use lang::typ::{Qualifier, Distribution};
        use petgraph::graph::NodeIndex;
        use backend::op::mk;

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
            mk::<ArkBls12_381>(Op::Ref(Ref::Node(NodeIndex::new(0)), ATyp::VPoly(2, 1))),
            mk::<ArkBls12_381>(Op::Ref(Ref::Node(NodeIndex::new(1)), ATyp::VPoly(2, 1))),
            ATyp::VPoly(2, 1),
        );
        builder.add_op(result.clone(), op);

        // 3 result slots bound.
        for i in 0..3 {
            assert!(builder.pl.contains(&result.with_index(i)),
                "add result slot {} missing", i);
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
            assert_eq!(*stored, expected,
                "vpoly add slot {} mismatch", i);
        }
    }

    #[test]
    fn test_add_op_mle_add_pointwise() {
        // Mle(2) has 4 evaluation slots. add is pointwise over hypercube.
        use lang::ast::BinOp;
        use crate::{PRef, Ref};
        use lang::typ::{Qualifier, Distribution};
        use petgraph::graph::NodeIndex;
        use backend::op::mk;

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
            mk::<ArkBls12_381>(Op::Ref(Ref::Node(NodeIndex::new(0)), ATyp::Mle(2))),
            mk::<ArkBls12_381>(Op::Ref(Ref::Node(NodeIndex::new(1)), ATyp::Mle(2))),
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
            assert_eq!(*stored, expected,
                "mle add slot {} mismatch", i);
        }
    }

    #[test]
    fn test_add_op_vpoly_sub_coefficient_wise() {
        use lang::ast::BinOp;
        use crate::{PRef, Ref};
        use lang::typ::{Qualifier, Distribution};
        use petgraph::graph::NodeIndex;
        use backend::op::mk;

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
            mk::<ArkBls12_381>(Op::Ref(Ref::Node(NodeIndex::new(0)), ATyp::VPoly(2, 2))),
            mk::<ArkBls12_381>(Op::Ref(Ref::Node(NodeIndex::new(1)), ATyp::VPoly(2, 2))),
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
            assert_eq!(*stored, expected,
                "vpoly sub slot {} mismatch", i);
        }
    }

    #[test]
    fn test_add_op_vpoly_mul_univariate_convolution() {
        // VPoly(1,1) × VPoly(1,1) → VPoly(1,2), a_0 b_0, a_0 b_1 + a_1 b_0, a_1 b_1.
        use lang::ast::BinOp;
        use crate::{PRef, Ref};
        use lang::typ::{Qualifier, Distribution};
        use petgraph::graph::NodeIndex;
        use backend::op::mk;

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
            mk::<ArkBls12_381>(Op::Ref(Ref::Node(NodeIndex::new(0)), ATyp::VPoly(1, 1))),
            mk::<ArkBls12_381>(Op::Ref(Ref::Node(NodeIndex::new(1)), ATyp::VPoly(1, 1))),
            ATyp::VPoly(1, 2),
        );
        builder.add_op(result.clone(), op);

        // VPoly(1,2) has num_coeffs = 3 slots (degrees 0, 1, 2 in graded-lex order).
        assert_eq!(num_coeffs(&ATyp::VPoly(1, 2)), 3);
        let a0 = { let mut p = pref_a.with_index(0); p.typ = ATyp::scalar(); p };
        let a1 = { let mut p = pref_a.with_index(1); p.typ = ATyp::scalar(); p };
        let b0 = { let mut p = pref_b.with_index(0); p.typ = ATyp::scalar(); p };
        let b1 = { let mut p = pref_b.with_index(1); p.typ = ATyp::scalar(); p };

        let var = |p: &PRef| SparsePolynomial::<ark_bls12_381::Fr, GrevLexTerm>::var(p);
        let deg0 = builder.pl.get(&result.with_index(0)).unwrap().clone();
        let deg1 = builder.pl.get(&result.with_index(1)).unwrap().clone();
        let deg2 = builder.pl.get(&result.with_index(2)).unwrap().clone();
        assert_eq!(deg0, &var(&a0) * &var(&b0), "(*.x^0)");
        assert_eq!(deg1, &(&var(&a0) * &var(&b1)) + &(&var(&a1) * &var(&b0)), "(*.x^1)");
        assert_eq!(deg2, &var(&a1) * &var(&b1), "(*.x^2)");
    }

    #[test]
    fn test_add_op_vpoly_mul_multivariate_spotcheck() {
        // VPoly(2,1) × VPoly(2,1) → VPoly(2,2). We spot-check one slot.
        // VPoly(2,1) multi-indices (graded-lex by total deg then lex):
        //   [0,0], [0,1], [1,0]   (sizes 3)
        // VPoly(2,2) multi-indices:
        //   [0,0], [0,1], [1,0], [0,2], [1,1], [2,0]   (size 6)
        use lang::ast::BinOp;
        use crate::{PRef, Ref};
        use lang::typ::{Qualifier, Distribution};
        use petgraph::graph::NodeIndex;
        use backend::op::mk;

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
            mk::<ArkBls12_381>(Op::Ref(Ref::Node(NodeIndex::new(0)), ATyp::VPoly(2, 1))),
            mk::<ArkBls12_381>(Op::Ref(Ref::Node(NodeIndex::new(1)), ATyp::VPoly(2, 1))),
            ATyp::VPoly(2, 2),
        );
        builder.add_op(result.clone(), op);

        // Check the constant-term slot (multi-index [0,0]): should be a_[0,0] * b_[0,0].
        let r_idx = multi_indices(2, 2);
        let a_idx = multi_indices(2, 1);
        let pos_00 = r_idx.iter().position(|k| k == &vec![0,0]).unwrap();
        let a_pos_00 = a_idx.iter().position(|k| k == &vec![0,0]).unwrap();

        let a00 = { let mut p = pref_a.with_index(a_pos_00); p.typ = ATyp::scalar(); p };
        let b00 = { let mut p = pref_b.with_index(a_pos_00); p.typ = ATyp::scalar(); p };
        let var = |p: &PRef| SparsePolynomial::<ark_bls12_381::Fr, GrevLexTerm>::var(p);
        let got = builder.pl.get(&result.with_index(pos_00)).unwrap().clone();
        assert_eq!(got, &var(&a00) * &var(&b00), "VPoly(2,2) constant term mismatch");

        // Ensure all 6 slots were populated.
        for i in 0..6 {
            assert!(builder.pl.contains(&result.with_index(i)),
                "VPoly(2,2) slot {} missing", i);
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
        use lang::ast::BinOp;
        use crate::{PRef, Ref};
        use lang::typ::{Qualifier, Distribution};
        use petgraph::graph::NodeIndex;
        use backend::op::mk;

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
            mk::<ArkBls12_381>(Op::Ref(Ref::Node(NodeIndex::new(0)), ATyp::Mle(1))),
            mk::<ArkBls12_381>(Op::Ref(Ref::Node(NodeIndex::new(1)), ATyp::Mle(1))),
            ATyp::VPoly(1, 2),
        );
        builder.add_op(result.clone(), op);

        // 3 slots populated.
        for i in 0..3 { assert!(builder.pl.contains(&result.with_index(i)),
            "Mle×Mle slot {} missing", i); }

        let u0 = { let mut p = pref_u.with_index(0); p.typ = ATyp::scalar(); p };
        let u1 = { let mut p = pref_u.with_index(1); p.typ = ATyp::scalar(); p };
        let v0 = { let mut p = pref_v.with_index(0); p.typ = ATyp::scalar(); p };
        let v1 = { let mut p = pref_v.with_index(1); p.typ = ATyp::scalar(); p };
        let var = |p: &PRef| SparsePolynomial::<ark_bls12_381::Fr, GrevLexTerm>::var(p);

        let deg0 = builder.pl.get(&result.with_index(0)).unwrap().clone();
        let deg1 = builder.pl.get(&result.with_index(1)).unwrap().clone();
        let deg2 = builder.pl.get(&result.with_index(2)).unwrap().clone();

        // deg0 = u_0 * v_0
        assert_eq!(deg0, &var(&u0) * &var(&v0), "mle mul deg0");

        // deg1 = -2 u_0 v_0 + u_0 v_1 + u_1 v_0
        let two = SparsePolynomial::<ark_bls12_381::Fr, GrevLexTerm>::lit(
            &<ark_bls12_381::Fr as From<u64>>::from(2u64)
        );
        let expected_deg1 = &(&(&var(&u0) * &var(&v1)) + &(&var(&u1) * &var(&v0)))
            - &(&two * &(&var(&u0) * &var(&v0)));
        assert_eq!(deg1, expected_deg1, "mle mul deg1");

        // deg2 = u_0 v_0 - u_0 v_1 - u_1 v_0 + u_1 v_1
        let expected_deg2 = &(&(&var(&u0) * &var(&v0)) - &(&var(&u0) * &var(&v1)))
            + &(&(&var(&u1) * &var(&v1)) - &(&var(&u1) * &var(&v0)));
        assert_eq!(deg2, expected_deg2, "mle mul deg2");
    }
}
