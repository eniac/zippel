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
            Op::Bin(BinOp::Mul, a, b, _) => self
                .to_poly(&a)
                .into_iter()
                .zip(self.to_poly(&b))
                .enumerate()
                .for_each(|(i, (a, b))| {
                    let pf = pr.clone().with_index(i);
                    self.pl.insert(&pf, &(&a * &b));
                    self.basis.push(a * b - SparsePolynomial::var(&pf));
                }),
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
}
