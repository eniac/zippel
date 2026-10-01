//! Symbolic group mode ("formal AGM") for the special soundness analysis.
//!
//! Arguments bind their witnesses computationally, so extraction needs the
//! per-generator coefficient separation that binding provides — a step that
//! is an assumption, not a polynomial fact. This module implements it as a
//! transform over the assembled polynomial sets: detect a generator basis,
//! re-express every other group variable as scalar coefficients over it,
//! and split each group equation into one scalar equation per basis element.
//!
//! The model is three-tiered, mirroring what the algebraic group model
//! grants an adversary — representations over everything it *received*:
//!
//! - **Basis `B`**: group-typed protocol arguments the relation does not
//!   pin (see [`SymbolicGroup::detect`]). Free symbols; the coordinates of
//!   the split.
//! - **Statement `S`**: the other group-typed arguments. Each `U ∈ S` gets
//!   coefficient variables `c_{U,b}` over `B` that are *not*
//!   verifier-visible: they exist so equations mentioning `U` can split,
//!   and the extractor learns them only when the verifier's equations pin
//!   them to visible values.
//! - **Transcript `T`**: prover-sent group elements. Each `t ∈ T` gets
//!   *visible* coefficients over `B` and over `S`; its basis representation
//!   is `c_{t,b} + Σ_U c_{t,U}·c_{U,b}`. Representations over `S` matter:
//!   restricting `T` to basis-only coefficients would assume the adversary
//!   cannot echo a statement element, and a verifier checking `t == U`
//!   would wrongly prove knowledge of `U`'s representation (the copy
//!   attack). Conversely, making statement coefficients visible would prove
//!   every protocol vacuously. Neither direction survives this model: see
//!   the regression tests in `soundness.rs`.
//!
//! Any other group variable that survives inlining (a leftover computed
//! node) is treated like a statement element: invisible coefficients over
//! `B`, pinned only by its own defining equations. Conservative.
//!
//! A result that used this transform holds under the binding/AGM
//! assumption for the detected basis; [`SymbolicGroup::label`] names it.

use std::collections::HashMap;

use ark_ff::PrimeField;
use backend::ArkConfig;
use share::{Ctx, Set};

use crate::Var;
use crate::completeness::defined_var;
use crate::frontend::{Monomial, Polynomial};

/// The classification and coefficient table of one transform; see the
/// module docs.
pub struct SymbolicGroup<F: PrimeField> {
    /// The basis `B`, in `Var` order.
    pub basis: Vec<Var>,
    /// The statement elements `S`, in `Var` order.
    pub statement: Vec<Var>,
    /// The transcript elements `T` encountered, in first-seen order.
    pub transcript: Vec<Var>,
    /// The basis representation of every non-basis group variable:
    /// `v -> [(b, coefficient polynomial)]`.
    rep: HashMap<Var, Vec<(Var, Polynomial<F>)>>,
    /// Coefficient variables the extractor may use (those of `T`).
    pub visible_coeffs: Vec<Var>,
    /// Whether any group polynomial was actually split.
    fired: bool,
}

/// Why the transform cannot handle a protocol yet.
#[derive(Debug, Clone)]
pub enum Unsupported {
    /// GT variables need the product basis (plan milestone M3).
    Pairing(Var),
    /// Group-typed witnesses need coefficient witness slots (M3).
    GroupWitness(Var),
}

impl std::fmt::Display for Unsupported {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Unsupported::Pairing(v) => write!(f, "GT variable {v} needs the pairing basis (M3)"),
            Unsupported::GroupWitness(v) => {
                write!(f, "group-typed witness {v} needs coefficient slots (M3)")
            }
        }
    }
}

/// `m` with `v` removed.
fn mono_without(m: &Monomial, v: &Var) -> Monomial {
    let mut ctx: Ctx<Var, usize> = Ctx::new();
    for (var, pow) in m.vars().into_iter().zip(m.powers()) {
        if &var != v {
            ctx.insert(&var, &pow);
        }
    }
    Monomial::new(ctx)
}

/// The polynomial with the single term `c·m`.
fn term_poly<F: PrimeField>(m: Monomial, c: F) -> Polynomial<F> {
    let mut terms = HashMap::new();
    terms.insert(m, c);
    Polynomial { terms }
}

/// The zero polynomial.
fn zero_poly<F: PrimeField>() -> Polynomial<F> {
    Polynomial {
        terms: HashMap::new(),
    }
}

/// Substitute away every variable a generator of `polys` pins to a
/// *constant* (`b − c`, `c` a field element), within `polys` itself.
///
/// Sound per set: such a generator means `b = c` holds in that set's ideal,
/// so substituting preserves the ideal. Used before the split to collapse
/// the bool encoding's asserted sentinels (`b − 1`) — which turns the mixed
/// group/scalar aggregates `Σ dⱼ·invⱼ + b − 1` into homogeneous group
/// equations the per-basis split can handle. Scalar-only; never touches a
/// group variable.
pub fn pin_self_constants<F: PrimeField>(polys: &mut Vec<Polynomial<F>>) {
    loop {
        let mut def: Option<(Var, Polynomial<F>)> = None;
        for p in polys.iter() {
            if let Some((x, value)) = defined_var(p, &|x: &Var, value: &Polynomial<F>| {
                !x.typ.is_group() && value.vars().is_empty()
            }) {
                def = Some((x, value));
                break;
            }
        }
        let Some((x, value)) = def else { break };
        let ctx = Ctx::singleton(x, value);
        *polys = std::mem::take(polys)
            .into_iter()
            .map(|p| p.inline_vars(&ctx).0)
            .filter(|p| !p.is_zero())
            .collect();
    }
}

impl<F: PrimeField> SymbolicGroup<F> {
    /// Classify the group-typed argument slots: an argument any relation
    /// goal pins with a constant coefficient (`big_y − h1·x1 − …`) is
    /// statement; group witnesses are unsupported; the rest — `instance`
    /// and `extra` alike, both go through the same demotion scan — form the
    /// basis.
    pub fn detect(
        arg_slots: &[Var],
        rel_goals: &[Polynomial<F>],
    ) -> Result<SymbolicGroup<F>, Unsupported> {
        let group_args: Vec<Var> = arg_slots
            .iter()
            .filter(|a| a.typ.is_group())
            .cloned()
            .collect();
        if let Some(w) = group_args.iter().find(|a| a.is_witness()) {
            return Err(Unsupported::GroupWitness(w.clone()));
        }
        if let Some(v) = group_args.iter().find(|a| a.typ.is_gt()) {
            return Err(Unsupported::Pairing(v.clone()));
        }

        let candidates: Set<Var> = group_args.iter().cloned().collect();
        let mut demoted: Set<Var> = Set::new();
        for goal in rel_goals {
            if let Some((x, _)) = defined_var(goal, &|x: &Var, _value: &Polynomial<F>| {
                x.typ.is_group() && candidates.contains(x)
            }) {
                demoted.insert(x);
            }
        }

        let mut basis: Vec<Var> = group_args
            .iter()
            .filter(|a| !demoted.contains(a))
            .cloned()
            .collect();
        basis.sort();
        let mut statement: Vec<Var> = demoted.iter().cloned().collect();
        statement.sort();

        Ok(SymbolicGroup {
            basis,
            statement,
            transcript: Vec::new(),
            rep: HashMap::new(),
            visible_coeffs: Vec::new(),
            fired: false,
        })
    }

    /// Build the coefficient table for every non-basis group variable in
    /// `polys`. `mint` allocates a fresh scalar variable for a coefficient
    /// (the caller's sentinel namespace); `transcript_vars` are the
    /// prover-sent elements (tier `T`); everything else non-basis is tier
    /// `S`-like (invisible coefficients over `B`).
    pub fn build_reps(
        &mut self,
        mint: &mut impl FnMut(&str) -> Var,
        polys: &[&Polynomial<F>],
        transcript_vars: &impl Fn(&Var) -> bool,
    ) -> Result<(), Unsupported> {
        let basis_set: Set<Var> = self.basis.iter().cloned().collect();
        let mut seen: Set<Var> = Set::new();
        let mut order: Vec<Var> = Vec::new();
        for p in polys {
            for v in p.vars() {
                if v.typ.is_gt() {
                    return Err(Unsupported::Pairing(v));
                }
                if v.typ.is_group() && !basis_set.contains(&v) && !seen.contains(&v) {
                    if v.is_witness() {
                        return Err(Unsupported::GroupWitness(v));
                    }
                    seen.insert(v.clone());
                    order.push(v);
                }
            }
        }
        // Statement first, so transcript representations can reference
        // their coefficients.
        order.sort_by_key(|v| (transcript_vars(v), v.clone()));

        let mut statement_coeffs: Vec<(Var, Vec<(Var, Var)>)> = Vec::new();
        for v in order {
            // Coefficients range over the basis elements of v's own group.
            let bases: Vec<Var> = self
                .basis
                .iter()
                .filter(|b| b.typ == v.typ)
                .cloned()
                .collect();
            let coeff_var =
                |mint: &mut dyn FnMut(&str) -> Var, of: &Var| mint(&format!("{v}~{of}"));
            if transcript_vars(&v) {
                // T: c_{t,b} + Σ_U c_{t,U}·c_{U,b}, all c_{t,·} visible.
                let direct: Vec<(Var, Var)> = bases
                    .iter()
                    .map(|b| (b.clone(), coeff_var(mint, b)))
                    .collect();
                let through: Vec<(Var, Var)> = statement_coeffs
                    .iter()
                    .filter(|(u, _)| u.typ == v.typ)
                    .map(|(u, _)| (u.clone(), coeff_var(mint, u)))
                    .collect();
                self.visible_coeffs
                    .extend(direct.iter().map(|(_, c)| c.clone()));
                self.visible_coeffs
                    .extend(through.iter().map(|(_, c)| c.clone()));
                let rep = bases
                    .iter()
                    .map(|b| {
                        let mut poly = direct
                            .iter()
                            .find(|(bb, _)| bb == b)
                            .map(|(_, c)| Polynomial::var(c))
                            .expect("direct coefficient exists per basis element");
                        for (u, c_tu) in &through {
                            let c_ub = statement_coeffs
                                .iter()
                                .find(|(uu, _)| uu == u)
                                .and_then(|(_, cs)| cs.iter().find(|(bb, _)| bb == b))
                                .map(|(_, c)| c.clone())
                                .expect("statement coefficient exists per basis element");
                            poly = &poly + &(&Polynomial::var(c_tu) * &Polynomial::var(&c_ub));
                        }
                        (b.clone(), poly)
                    })
                    .collect();
                self.transcript.push(v.clone());
                self.rep.insert(v, rep);
            } else {
                // S (and leftovers): invisible coefficients over B.
                let coeffs: Vec<(Var, Var)> = bases
                    .iter()
                    .map(|b| (b.clone(), coeff_var(mint, b)))
                    .collect();
                let rep = coeffs
                    .iter()
                    .map(|(b, c)| (b.clone(), Polynomial::var(c)))
                    .collect();
                if !self.statement.contains(&v) {
                    self.statement.push(v.clone());
                }
                statement_coeffs.push((v.clone(), coeffs));
                self.rep.insert(v, rep);
            }
        }
        Ok(())
    }

    /// Transform one polynomial: substitute non-basis group variables by
    /// their representations and split per basis element. A scalar
    /// polynomial passes through unchanged.
    ///
    /// # Panics
    /// If a term carries more than one group variable or a group power
    /// above 1 — the encoders' group-linearity invariant rules this out
    /// for pairing-free protocols, and a panic beats a silent mis-split.
    pub fn transform_poly(&mut self, p: &Polynomial<F>) -> Vec<Polynomial<F>> {
        let mut per_basis: HashMap<Var, Polynomial<F>> = HashMap::new();
        let mut scalar = zero_poly::<F>();
        let mut saw_group = false;
        for (mono, coeff) in p.terms.iter() {
            let group_vars: Vec<Var> = mono
                .vars()
                .into_iter()
                .filter(|v| v.typ.is_group())
                .collect();
            match group_vars.as_slice() {
                [] => {
                    scalar = &scalar + &term_poly(mono.clone(), *coeff);
                }
                [v] => {
                    assert!(
                        mono.powers_for(v) == 1,
                        "symbolic group: term has group power > 1: {p}"
                    );
                    saw_group = true;
                    let rest = term_poly(mono_without(mono, v), *coeff);
                    if let Some(rep) = self.rep.get(v) {
                        for (b, c_poly) in rep {
                            let addend = &rest * c_poly;
                            let entry = per_basis.entry(b.clone()).or_insert_with(zero_poly);
                            *entry = &*entry + &addend;
                        }
                    } else {
                        // A basis element itself.
                        let entry = per_basis.entry(v.clone()).or_insert_with(zero_poly);
                        *entry = &*entry + &rest;
                    }
                }
                _ => panic!("symbolic group: term has several group variables: {p}"),
            }
        }
        if !saw_group {
            return vec![p.clone()];
        }
        assert!(
            scalar.is_zero(),
            "symbolic group: polynomial mixes group and scalar terms: {p}"
        );
        self.fired = true;
        let mut out: Vec<Polynomial<F>> = per_basis
            .into_values()
            .filter(|poly| !poly.is_zero())
            .collect();
        // Deterministic output order.
        out.sort_by_key(|poly| format!("{poly}"));
        out
    }

    /// Transform a whole set in place.
    pub fn transform_set(&mut self, polys: &mut Vec<Polynomial<F>>) {
        *polys = std::mem::take(polys)
            .iter()
            .flat_map(|p| self.transform_poly(p))
            .collect();
    }

    /// The assumption this run's result holds under, or `None` when no
    /// group equation was split (the result is then unconditional).
    pub fn label(&self) -> Option<String> {
        if !self.fired {
            return None;
        }
        let names: Vec<String> = self.basis.iter().map(|b| b.to_string()).collect();
        Some(format!("binding w.r.t. {{{}}}", names.join(", ")))
    }
}

impl<C: ArkConfig> From<Unsupported> for crate::error::AnalysisError<C> {
    fn from(u: Unsupported) -> Self {
        crate::error::AnalysisError::UnsupportedSymbolicGroup(u.to_string())
    }
}
