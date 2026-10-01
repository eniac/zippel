use std::collections::{HashMap, HashSet, VecDeque};

use crate::TransClos;
use crate::Var;
use crate::backend::{GbBackendKind, GbBasis};
use crate::completeness::defined_var;
use crate::error::{AnalysisError, ExtractorRejection};
use crate::extractor::{extract_locals, valid_extractor};
use crate::frontend::{MonoOrder, Polynomial};
use crate::ideal::{EncodeOptions, Ideal, IdealBuilder};
use ark_ff::{One, PrimeField};
use backend::op::HasOpFactory;
use backend::{ATyp, ArkConfig};
use graph::{QDag, Ref};
use lang::typ::Qualifier;
use log::{info, warn};
use petgraph::Direction;
use petgraph::graph::NodeIndex;
use petgraph::visit::EdgeRef;
use share::{Ctx, Set};

/// Which polynomial model the special soundness analysis runs in.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum SoundnessModel {
    /// The plain polynomial model. A passing result is unconditional
    /// (statistical) special soundness.
    #[default]
    Plain,
    /// The symbolic group model ("formal AGM"): group equations split per
    /// generator-basis element (see [`crate::symbolic_group`]). A passing
    /// result holds under the binding/AGM assumption for the detected
    /// basis, named by `assumptions`.
    SymbolicGroup,
}

/// Inputs to the soundness search Gröbner basis computation: the
/// generating set (d-equations + copy TCs + relation, after optional
/// inlining), the lex ordering, and all state needed by `run()`.
///
/// Produced by [`SpecialSoundnessAnalysis::build_inputs`]; consumed by
/// [`SpecialSoundnessAnalysis::from_inputs`]. Splitting construction
/// from GB computation lets callers inspect pre-GB metrics before the
/// expensive step.
pub struct SoundnessInputs<C: ArkConfig> {
    /// The generating set for the search GB (d-equations + copy TCs +
    /// relation, inlined if requested).
    pub generating_set: Vec<Polynomial<C::F>>,
    /// Lex elimination ordering for the search GB.
    pub lex_order: MonoOrder,
    /// Witness slots (witness args) for extractor search in `run()`.
    pub witness_slots: Vec<Var>,
    /// Variables visible to the verifier (used for extractor validation).
    pub verifier_visible: Set<Var>,
    /// Validity ideal: d-equations + copy TCs. Extractors are added in
    /// `run()` before computing the validity GB.
    pub grev_validity: Ideal<C>,
    /// The goals: what the relation's assert checks, one `lhs − rhs` per
    /// conjunct slot, reduced against the validity GB in `run()`.
    pub rel_goals: Vec<Polynomial<C::F>>,
    /// The variables accepting runs pin down, substituted away by
    /// [`eliminate_pinned`]. Diagnostic.
    pub pinned: Ctx<Var, Polynomial<C::F>>,
    /// The assumption a passing result holds under, or `None` for the
    /// plain model / when no group equation was split.
    pub assumptions: Option<String>,
    /// Relation locals; their `pl` definitions are the paper's `I_R`
    /// (Skolem functions for the relation's intermediates), added to the
    /// validity ideal in `run()` when not inlining.
    pub rel_locals: Ideal<C>,
}

/// Perform a special soundness analysis using Groebner bases.
pub struct SpecialSoundnessAnalysis<C: ArkConfig> {
    /// Gröbner basis of the search ideal (verifier TC copies + d-equations +
    /// relation) under lex order. Computed in `from_inputs`.
    /// Snapshotable.
    pub search_gb: GbBasis<C::F>,
    /// Witness slots (witness args) for extractor search in `run()`.
    witness_slots: Vec<Var>,
    /// Variables visible to the verifier (used for extractor validation).
    verifier_visible: Set<Var>,
    /// Validity ideal: d-equations + copy TCs. Extractors are added in
    /// `run()` before computing the validity GB.
    grev_validity: Ideal<C>,
    /// The goals: what the relation's assert checks, one `lhs − rhs` per
    /// conjunct slot, reduced against the validity GB in `run()`.
    rel_goals: Vec<Polynomial<C::F>>,
    /// Relation locals; their `pl` definitions are the paper's `I_R`,
    /// added to the validity ideal in `run()` when not inlining.
    rel_locals: Ideal<C>,
    /// Lex ordering used for both search and validity GBs.
    lex_order: MonoOrder,
    /// Backend for the validity GB computation in `run()`.
    backend: GbBackendKind,
    /// Whether to inline the `pl` table before GB computation.
    inline: bool,
    /// The assumption a passing result holds under; see
    /// [`SoundnessInputs::assumptions`].
    pub assumptions: Option<String>,
}

fn format_suffix(prefix: &[usize], copy_idx: usize) -> String {
    if prefix.is_empty() {
        format!("{}", copy_idx)
    } else {
        let parts: Vec<String> = prefix.iter().map(|i| i.to_string()).collect();
        format!("{}::{}", parts.join("::"), copy_idx)
    }
}

fn format_d_name(prefix: &[usize], m: usize, n: usize, k: usize) -> String {
    if prefix.is_empty() {
        format!("__zippel::soundness::d::{}::{}::{}", m, n, k)
    } else {
        let parts: Vec<String> = prefix.iter().map(|i| i.to_string()).collect();
        format!(
            "__zippel::soundness::d::{}::{}::{}::{}",
            parts.join("::"),
            m,
            n,
            k
        )
    }
}

/// Scan the transcript chain and group consecutive challenges into vector
/// challenge rounds. Validates that the transcript forms a 2n+1-move sigma
/// protocol: alternating prover messages and (vector) challenges, starting
/// and ending with prover messages.
///
/// Returns `Vec<Vec<NodeIndex>>` where each inner vec is the consecutive
/// challenge nodes forming one vector challenge round.
fn validate_2n_plus_1<C: ArkConfig>(
    dag: &QDag<C>,
    l_vec: &[usize],
) -> Result<Vec<Vec<NodeIndex>>, AnalysisError<C>> {
    let transcript = dag.transcript_nodes();
    if transcript.is_empty() {
        return Err(AnalysisError::NoChallenge);
    }

    let mut challenge_rounds: Vec<Vec<NodeIndex>> = Vec::new();
    let mut current_round: Vec<NodeIndex> = Vec::new();
    let mut seen_prover_msg = false;

    for &node in &transcript {
        if dag[node].is_challenge() {
            if !seen_prover_msg && current_round.is_empty() && challenge_rounds.is_empty() {
                return Err(AnalysisError::Not2nPlus1MoveProtocol {
                    expected: l_vec.len(),
                    found: 0,
                });
            }
            current_round.push(node);
        } else if dag[node].is_proof() {
            if !current_round.is_empty() {
                challenge_rounds.push(std::mem::take(&mut current_round));
            }
            seen_prover_msg = true;
        }
    }

    if !current_round.is_empty() {
        return Err(AnalysisError::Not2nPlus1MoveProtocol {
            expected: l_vec.len(),
            found: challenge_rounds.len() + 1,
        });
    }

    if challenge_rounds.len() != l_vec.len() {
        return Err(AnalysisError::Not2nPlus1MoveProtocol {
            expected: l_vec.len(),
            found: challenge_rounds.len(),
        });
    }

    Ok(challenge_rounds)
}

/// Substitute away every variable a `defining` generator pins down (see
/// [`defined_var`]) where an eligible definition exists, applying the
/// substitution to `defining`, `also`, and `goals` alike, and dropping the
/// generators of `defining` that vanish. Returns what each variable was
/// pinned to.
///
/// Exact for the same reason as in the completeness analysis: each
/// definition `x − f` lies in the ideal of `defining` (the copies +
/// d-equations), which is contained in both the search ideal and the
/// validity assumptions — so a substituted goal lies in the substituted
/// ideal iff the original goal lies in the original one. Definitions are
/// never drawn from `goals` (the relation), which the validity phase must
/// prove, not assume.
fn eliminate_pinned<F: PrimeField>(
    defining: &mut Vec<Polynomial<F>>,
    also: &mut Vec<Polynomial<F>>,
    goals: &mut Vec<Polynomial<F>>,
    eligible: impl Fn(&Var, &Polynomial<F>) -> bool,
) -> Ctx<Var, Polynomial<F>> {
    // Kept resolved: no value mentions a defined variable.
    let mut defs: Ctx<Var, Polynomial<F>> = Ctx::new();
    loop {
        let mut found = false;
        let mut kept = Vec::with_capacity(defining.len());
        for p in std::mem::take(defining) {
            let p = if p.vars().iter().any(|v| defs.contains(v)) {
                p.inline_vars(&defs).0
            } else {
                p
            };
            if p.is_zero() {
                continue;
            }
            match defined_var(&p, &eligible) {
                Some((x, value)) => {
                    let def = Ctx::singleton(x.clone(), value.clone());
                    defs.modify(|_, v| {
                        if v.contains(&x) {
                            *v = v.clone().inline_vars(&def).0;
                        }
                    });
                    defs.insert(&x, &value);
                    found = true;
                }
                None => kept.push(p),
            }
        }
        *defining = kept;
        // A pass that defined nothing new left every generator resolved.
        if !found {
            break;
        }
    }
    let substitute = |polys: &mut Vec<Polynomial<F>>| {
        *polys = std::mem::take(polys)
            .into_iter()
            .map(|p| p.inline_vars(&defs).0)
            .filter(|p| !p.is_zero())
            .collect();
    };
    substitute(also);
    substitute(goals);
    defs
}

impl<C: ArkConfig + HasOpFactory> SpecialSoundnessAnalysis<C> {
    /// Build the inputs to the search Gröbner basis computation:
    /// construct all d-equations, copy TCs, and relation polys, build the
    /// lex elimination ordering, and inline the `pl` table if requested.
    ///
    /// This is the cheap phase — no GB computation. Call
    /// [`from_inputs`](Self::from_inputs) to compute the basis, or inspect
    /// the generating set for pre-GB metrics.
    ///
    /// # Errors
    /// Returns `AnalysisError` if `l_vec` is invalid or the protocol is
    /// not a valid 2n+1-move protocol.
    pub fn build_inputs(
        dag: &QDag<C>,
        l_vec: Vec<usize>,
        inline: bool,
    ) -> Result<SoundnessInputs<C>, AnalysisError<C>> {
        Self::build_inputs_with_model(dag, l_vec, inline, SoundnessModel::default())
    }

    /// [`build_inputs`](Self::build_inputs) in an explicit model; see
    /// [`SoundnessModel`].
    pub fn build_inputs_with_model(
        dag: &QDag<C>,
        l_vec: Vec<usize>,
        inline: bool,
        model: SoundnessModel,
    ) -> Result<SoundnessInputs<C>, AnalysisError<C>> {
        if l_vec.is_empty() || l_vec.iter().any(|l| *l < 2) {
            return Err(AnalysisError::InvalidSoundnessParameter);
        }

        let challenge_rounds = validate_2n_plus_1(dag, &l_vec)?;

        let witness_slots: Vec<Var> = crate::var::dag_args(dag)
            .into_iter()
            .filter(|a| a.is_witness())
            .flat_map(|a| a.slots())
            .collect();

        let verifier_tc = TransClos::verifier(dag);

        let round_map = build_round_map(dag, &challenge_rounds);

        let challenge_vars_per_round: Vec<Vec<Var>> = challenge_rounds
            .iter()
            .map(|round| {
                round
                    .iter()
                    .flat_map(|&cn| {
                        let r = dag.find_ref(cn);
                        verifier_tc
                            .vars
                            .iter()
                            .filter(|p| p.reference == r)
                            .cloned()
                            .collect::<Vec<_>>()
                    })
                    .collect()
            })
            .collect();

        // Phase 1: Construct (order-free).
        //
        // Split `reduce(&&, …)` in asserts and verifies into one constraint
        // per element, as the completeness analysis does. Here the verifier's
        // checks are assumptions ("given ℓ accepting transcripts"), and
        // acceptance means the whole conjunction evaluated to true at
        // runtime, hence every element did — so the per-element constraints
        // hold on every accepting transcript. On the goal side, the
        // relation's conjunction becomes one goal per element, which is a
        // stronger statement to prove (each conjunct in the validity ideal,
        // rather than their product).
        //
        // Unlike completeness, `relation_asserts` stays `None`: an `assert`
        // in a protocol body keeps its encoding. On this side that is a
        // free assumption — a failing assert aborts the run, so an accepting
        // transcript implies every reached assert passed.
        //
        // The builder's per-node bookkeeping (`node_ops`, element tables) is
        // keyed by graph `Ref`, which the ℓ copies share; each copy's
        // `build` re-records it and resolves its own `verify` splits through
        // that copy's renamed variables before the next copy overwrites it,
        // so the splits never mix copies.
        let mut grev_builder: IdealBuilder<C> = IdealBuilder::with_options(EncodeOptions {
            split_reductions: true,
            relation_asserts: None,
        });
        let mut worklist: Vec<(Vec<usize>, TransClos<C>)> = vec![(vec![], verifier_tc.clone())];
        let mut all_d_equations: Vec<Polynomial<C::F>> = Vec::new();
        let mut all_d_vars: Vec<Var> = Vec::new();
        let mut grev_search = Ideal::<C>::new();
        let mut grev_validity = Ideal::<C>::new();

        for (round_idx, &li) in l_vec.iter().enumerate() {
            let mut new_worklist = Vec::new();

            for (prefix, tc) in worklist {
                let mut copies_with_challenges: Vec<(TransClos<C>, Vec<Var>)> = Vec::new();

                for j in 0..li {
                    let suffix = format_suffix(&prefix, j);
                    let mut copy_tc = tc.clone();

                    let round_map_ref = &round_map;
                    let suffix_owned = suffix.clone();

                    copy_tc.remap(&|var: &Var| {
                        let key = (var.reference, var.index.clone());
                        let in_round = round_map_ref
                            .get(&key)
                            .is_some_and(|&highest| highest == round_idx);

                        if in_round {
                            let orig = var.name();
                            Var {
                                name: format!("{}::{}", orig, suffix_owned),
                                ..var.clone()
                            }
                        } else {
                            var.clone()
                        }
                    });

                    let remapped_challenges: Vec<Var> = challenge_vars_per_round[round_idx]
                        .iter()
                        .map(|cp| {
                            let key = (cp.reference, cp.index.clone());
                            let in_round = round_map_ref
                                .get(&key)
                                .is_some_and(|&highest| highest == round_idx);
                            if in_round {
                                let orig = cp.name();
                                Var {
                                    name: format!("{}::{}", orig, suffix_owned),
                                    ..cp.clone()
                                }
                            } else {
                                cp.clone()
                            }
                        })
                        .collect();

                    copies_with_challenges.push((copy_tc, remapped_challenges));
                }

                for m in 0..li {
                    for n in (m + 1)..li {
                        let cm_vars = &copies_with_challenges[m].1;
                        let cn_vars = &copies_with_challenges[n].1;
                        let mut product = Polynomial::<C::F>::lit(&C::F::one());
                        for (k, (cm_ref, cn_ref)) in cm_vars.iter().zip(cn_vars.iter()).enumerate()
                        {
                            let d_name = format_d_name(&prefix, m, n, k);
                            let d = grev_builder.sentinel_var(
                                &d_name,
                                ATyp::scalar(),
                                &mut grev_search,
                            );
                            grev_validity.var_order.push(d.clone());
                            all_d_vars.push(d.clone());
                            let d_poly = Polynomial::<C::F>::var(&d);
                            let cm_poly = Polynomial::<C::F>::var(cm_ref);
                            let cn_poly = Polynomial::<C::F>::var(cn_ref);
                            let factor = d_poly * (cm_poly - cn_poly)
                                - Polynomial::<C::F>::lit(&C::F::one());
                            product *= factor;
                        }

                        all_d_equations.push(product);
                    }
                }

                for (j, (copy_tc, _)) in copies_with_challenges.into_iter().enumerate() {
                    let mut new_prefix = prefix.clone();
                    new_prefix.push(j);
                    new_worklist.push((new_prefix, copy_tc));
                }
            }

            worklist = new_worklist;
        }

        let mut verifier_visible: Set<Var> = Set::new();
        let mut non_witness_vars: Vec<Var> = Vec::new();
        let mut witness_vars: Vec<Var> = Vec::new();

        for eq in &all_d_equations {
            grev_search.generating_set.push(eq.clone());
            grev_validity.generating_set.push(eq.clone());
        }
        for d in &all_d_vars {
            verifier_visible.insert(d.clone());
        }

        for (_prefix, tc) in worklist {
            for (var, _) in tc.clos.iter() {
                verifier_visible.insert(var.clone());
            }
            for var in tc.vars.iter() {
                verifier_visible.insert(var.clone());
            }
            for var in tc.vars.iter() {
                if var.qualifier.is_witness() {
                    witness_vars.push(var.clone());
                } else {
                    non_witness_vars.push(var.clone());
                }
            }
            let copy_result = grev_builder.build(tc);
            grev_search.merge(&copy_result);
            grev_validity.merge(&copy_result);
        }

        let rel_tc = TransClos::relation(dag);
        for var in rel_tc.vars.iter() {
            if var.qualifier.is_witness() {
                witness_vars.push(var.clone());
            } else {
                non_witness_vars.push(var.clone());
            }
        }
        let mut rel_locals = extract_locals(&grev_builder, &rel_tc);
        let mut grev_rel_result = grev_builder.build(rel_tc.clone());
        if inline {
            rel_locals.inline(&Set::new());
            grev_rel_result.inline(&Set::new());
        }

        grev_search.merge(&grev_rel_result);

        // Phase 3a: Inline the search ideal.
        if inline {
            grev_search.inline(&Set::new());
        }

        // The goals: what the relation's assert checks, `lhs − rhs` per
        // conjunct slot. The relation's constraint encodings stay in the
        // search ideal (assumptions for extractor *search*), but must only
        // be proved, never assumed, when validating the extractor.
        let mut rel_goals: Vec<Polynomial<C::F>> = grev_rel_result
            .checks
            .iter()
            .map(|c| &c.lhs - &c.rhs)
            .filter(|p| !p.is_zero())
            .collect();

        // Phase 3b/3s: substitute away the variables that accepting runs
        // pin down, then (symbolic model) split group equations per
        // generator-basis element, then substitute again. Definitions are
        // drawn only from the copies + d-equations — never the relation,
        // which must be proved — and are eligible only when the pinned
        // variable is not a witness and its value mentions only
        // verifier-visible variables. The first pass pins the asserted
        // bools to 1, which turns the bool encoding's mixed group/scalar
        // aggregates into homogeneous group equations the split can handle;
        // the second pass eats the coefficient definitions the split
        // mass-produces.
        let witness_set: Set<Var> = witness_vars.iter().cloned().collect();
        let mut assumptions = None;
        let mut pinned: Ctx<Var, Polynomial<C::F>> = Ctx::new();
        if inline {
            grev_validity.inline(&Set::new());
            let first = eliminate_pinned(
                &mut grev_validity.generating_set,
                &mut grev_search.generating_set,
                &mut rel_goals,
                |x, value| {
                    !witness_set.contains(x)
                        && value.vars().iter().all(|v| verifier_visible.contains(v))
                },
            );
            for (k, v) in first.iter() {
                pinned.insert(k, v);
            }

            if model == SoundnessModel::SymbolicGroup {
                let arg_slots: Vec<Var> = crate::var::dag_args(dag)
                    .into_iter()
                    .flat_map(|a| a.slots())
                    .collect();
                let mut sym = crate::symbolic_group::SymbolicGroup::detect(&arg_slots, &rel_goals)
                    .map_err(AnalysisError::from)?;
                // Collapse asserted bool sentinels (`b − 1`) so the bool
                // encoding's mixed group/scalar aggregates become
                // homogeneous group equations the split can handle.
                crate::symbolic_group::pin_self_constants(&mut grev_search.generating_set);
                crate::symbolic_group::pin_self_constants(&mut grev_validity.generating_set);
                let transcript_refs: Set<Ref> =
                    dag.transcript_nodes().into_iter().map(Ref::new).collect();
                let all_polys: Vec<&Polynomial<C::F>> = grev_search
                    .generating_set
                    .iter()
                    .chain(grev_validity.generating_set.iter())
                    .chain(rel_goals.iter())
                    .collect();
                let mut mint = |name: &str| grev_builder.mint_scalar(name);
                sym.build_reps(&mut mint, &all_polys, &|v: &Var| {
                    transcript_refs.contains(&v.reference)
                })
                .map_err(AnalysisError::from)?;
                sym.transform_set(&mut grev_search.generating_set);
                sym.transform_set(&mut grev_validity.generating_set);
                sym.transform_set(&mut rel_goals);
                for c in &sym.visible_coeffs {
                    verifier_visible.insert(c.clone());
                }
                assumptions = sym.label();

                let second = eliminate_pinned(
                    &mut grev_validity.generating_set,
                    &mut grev_search.generating_set,
                    &mut rel_goals,
                    |x, value| {
                        !witness_set.contains(x)
                            && value.vars().iter().all(|v| verifier_visible.contains(v))
                    },
                );
                for (k, v) in second.iter() {
                    pinned.insert(k, v);
                }
            }
        }

        // Phase 2: Build lex ordering as runtime data.
        // Priority: rel_locals > witness_vars > other_locals > non_witness_vars.
        // In MonoOrder::lex, the first variable has the highest elimination
        // priority. Within each group, sort by Var::Ord for determinism.
        let lex_var_order: Vec<Var> = {
            let rel_locals_set: Set<Var> = grev_rel_result.var_order.iter().cloned().collect();
            let witness_set: Set<Var> = witness_vars.iter().cloned().collect();
            let non_witness_set: Set<Var> = non_witness_vars.iter().cloned().collect();

            let all_vars: Set<Var> = grev_search.vars();

            let mut rel: Vec<Var> = all_vars
                .iter()
                .filter(|v| rel_locals_set.contains(v))
                .cloned()
                .collect();
            rel.sort();
            let mut witness_v: Vec<Var> = all_vars
                .iter()
                .filter(|v| witness_set.contains(v) && !rel_locals_set.contains(v))
                .cloned()
                .collect();
            witness_v.sort();
            let mut non_witness_v: Vec<Var> = all_vars
                .iter()
                .filter(|v| {
                    non_witness_set.contains(v)
                        && !rel_locals_set.contains(v)
                        && !witness_set.contains(v)
                })
                .cloned()
                .collect();
            non_witness_v.sort();
            let mut other: Vec<Var> = all_vars
                .iter()
                .filter(|v| {
                    !rel_locals_set.contains(v)
                        && !witness_set.contains(v)
                        && !non_witness_set.contains(v)
                })
                .cloned()
                .collect();
            other.sort();

            rel.into_iter()
                .chain(witness_v)
                .chain(other)
                .chain(non_witness_v)
                .collect()
        };
        let lex_order = MonoOrder::lex(lex_var_order);

        Ok(SoundnessInputs {
            pinned,
            generating_set: std::mem::take(&mut grev_search.generating_set),
            lex_order,
            witness_slots,
            verifier_visible,
            grev_validity,
            rel_goals,
            rel_locals,
            assumptions,
        })
    }

    /// Compute the search Gröbner basis from pre-built inputs.
    ///
    /// This is the expensive phase — `compute_gb` may hang or take a long
    /// time. Call [`build_inputs`](Self::build_inputs) first if you need
    /// pre-GB metrics.
    ///
    /// # Errors
    /// Returns `AnalysisError::UnitIdeal` if the search ideal is the unit
    /// ideal (trivially solvable — no soundness guarantee).
    pub fn from_inputs(
        inputs: SoundnessInputs<C>,
        backend: GbBackendKind,
        inline: bool,
    ) -> Result<Self, AnalysisError<C>> {
        let gb = backend.build::<C::F>();
        let search_gb = gb
            .compute_gb(inputs.generating_set, &inputs.lex_order)
            .expect("GB backend should support lex order");

        if search_gb.is_unit() {
            return Err(AnalysisError::UnitIdeal {
                context: "soundness search",
            });
        }

        Ok(Self {
            search_gb,
            witness_slots: inputs.witness_slots,
            verifier_visible: inputs.verifier_visible,
            grev_validity: inputs.grev_validity,
            rel_goals: inputs.rel_goals,
            rel_locals: inputs.rel_locals,
            lex_order: inputs.lex_order,
            assumptions: inputs.assumptions,
            backend,
            inline,
        })
    }

    /// Run the checking phase: extract witnesses from the search GB, build the
    /// validity GB, and verify that all relation polys reduce to zero.
    ///
    /// # Phases
    ///
    /// 4. **Extract witnesses** from the search basis.
    /// 5. **Build validity GB** (also under lex) and verify that all relation
    ///    polys reduce to zero.
    pub fn run(&mut self) -> Result<(), AnalysisError<C>> {
        // Phase 4: Extract witnesses. Passes run until nothing new is
        // extracted: a candidate may mention witnesses extracted in an
        // earlier iteration (chained extraction, e.g. first `x`, then
        // `alpha` from a polynomial in `x` and transcript values). The
        // extracted set only grows, so the chains are acyclic and resolve
        // to functions of verifier-visible variables by substitution.
        let mut search_polys = self.search_gb.polys.clone();
        factor_group_gcd(&mut search_polys);

        let mut extractors: Vec<(Var, Polynomial<C::F>)> = Vec::new();
        let mut extracted: Set<Var> = Set::new();
        let mut remaining: Vec<Var> = self.witness_slots.clone();
        let mut rejections: Vec<(Var, ExtractorRejection<C>)> = Vec::new();

        loop {
            let mut progress = false;
            rejections.clear();
            let mut still_remaining = Vec::new();

            for w in remaining {
                let mut found_extractor = None;
                let mut rejection: Option<ExtractorRejection<C>> = None;

                'poly: for poly in search_polys.iter() {
                    for term in poly.terms.keys() {
                        let tv = term.vars();
                        let tp = term.powers();
                        let is_witness_term = tv.len() == 1 && tv[0] == w && tp[0] == 1;
                        if !is_witness_term {
                            continue;
                        }

                        let other_vars: Set<Var> = poly
                            .terms
                            .iter()
                            .filter(|(t, _)| {
                                let tvars = t.vars();
                                let tpows = t.powers();
                                !(tvars.len() == 1 && tvars[0] == w && tpows[0] == 1)
                            })
                            .flat_map(|(t, _)| t.vars())
                            .collect();

                        let usable = other_vars
                            .iter()
                            .all(|v| self.verifier_visible.contains(v) || extracted.contains(v));
                        if !usable {
                            rejection = Some(ExtractorRejection::NotVisible(poly.clone()));
                            continue;
                        }
                        if !valid_extractor::<C>(&w.typ, poly) {
                            if w.typ.is_scalar() {
                                rejection =
                                    Some(ExtractorRejection::FieldDependsOnGroup(poly.clone()));
                            } else {
                                rejection = Some(ExtractorRejection::MultiGroupTerm(poly.clone()));
                            }
                            continue;
                        }
                        found_extractor = Some(poly.clone());
                        break 'poly;
                    }
                }

                match found_extractor {
                    Some(poly) => {
                        info!("Found extractor for {:?}", w);
                        extracted.insert(w.clone());
                        extractors.push((w, poly));
                        progress = true;
                    }
                    None => {
                        let reason = rejection.unwrap_or(ExtractorRejection::NoExtractor);
                        rejections.push((w.clone(), reason));
                        still_remaining.push(w);
                    }
                }
            }

            remaining = still_remaining;
            if remaining.is_empty() || !progress {
                break;
            }
        }

        if let Some((witness, reason)) = rejections.into_iter().next() {
            warn!("No valid extractor for witness {:?}", witness);
            return Err(AnalysisError::NoValidExtractor {
                witness,
                reason: Box::new(reason),
            });
        }

        info!(
            "Found {} extractor(s) for {} witness slot(s)",
            extractors.len(),
            self.witness_slots.len()
        );

        // Phase 5: Build validity GB and verify.
        for (_, ext_poly) in &extractors {
            self.grev_validity.generating_set.push(ext_poly.clone());
        }

        // I_R: Skolem definitions for the relation's intermediates. Only
        // definitions — assuming the relation's own constraints (as
        // `merge(&rel_locals)` used to) made the final reduction vacuous:
        // every goal was literally an assumption. With inlining the goals
        // are already resolved down to arguments, so there is nothing to
        // add.
        if !self.inline {
            for (t, f) in self.rel_locals.pl.iter() {
                self.grev_validity
                    .generating_set
                    .push(&Polynomial::var(t) - f);
            }
        }
        if self.inline {
            self.grev_validity.inline(&Set::new());
        }

        let backend = self.backend.build::<C::F>();
        let validity_gb = backend
            .compute_gb(
                std::mem::take(&mut self.grev_validity.generating_set),
                &self.lex_order,
            )
            .expect("GB backend should support lex order");

        if validity_gb.is_unit() {
            return Err(AnalysisError::UnitIdeal {
                context: "soundness validity",
            });
        }

        for r in self.rel_goals.iter() {
            if r.is_zero() {
                continue;
            }
            let rem = backend.reduce(r.clone(), &validity_gb);
            if !rem.is_zero() {
                warn!("Relation polynomial does not reduce to zero: {}", r);
                warn!("Remainder: {}", rem);
                return Err(AnalysisError::ExtractorInvalid(rem));
            }
        }

        info!("Special soundness proven (with distinct-challenge assumption D)");

        Ok(())
    }
}

fn build_round_map<C: ArkConfig>(
    dag: &QDag<C>,
    challenge_rounds: &[Vec<NodeIndex>],
) -> HashMap<(Ref, Vec<usize>), usize> {
    let mut round_map: HashMap<(Ref, Vec<usize>), usize> = HashMap::new();
    let challenge_nodes: Vec<NodeIndex> = challenge_rounds.iter().flatten().copied().collect();
    let challenge_set: HashSet<NodeIndex> = challenge_nodes.iter().copied().collect();

    for (round_idx, nodes) in challenge_rounds.iter().enumerate() {
        let next_challenge_set: HashSet<NodeIndex> = challenge_rounds[round_idx + 1..]
            .iter()
            .flatten()
            .copied()
            .collect();

        let mut queue: VecDeque<NodeIndex> = VecDeque::new();
        let mut visited: HashSet<NodeIndex> = HashSet::new();
        for &node in nodes {
            queue.push_back(node);
            visited.insert(node);
        }

        while let Some(node) = queue.pop_front() {
            if let Some(typ) = dag[node].typ() {
                let r = dag.find_ref(node);
                let base = Var::from_node(node, typ.clone(), Qualifier::Instance);
                for slot in base.slots() {
                    round_map
                        .entry((r, slot.index))
                        .and_modify(|e| *e = (*e).max(round_idx))
                        .or_insert(round_idx);
                }
            }

            for edge in dag.graph.edges_directed(node, Direction::Outgoing) {
                if !edge.weight().is_data() {
                    continue;
                }
                let neighbor = edge.target();
                if visited.contains(&neighbor) {
                    continue;
                }
                if challenge_set.contains(&neighbor) && next_challenge_set.contains(&neighbor) {
                    continue;
                }
                if next_challenge_set.contains(&neighbor) {
                    continue;
                }
                visited.insert(neighbor);
                queue.push_back(neighbor);
            }
        }
    }

    round_map
}

fn factor_group_gcd<F: ark_ff::Field>(polys: &mut Vec<Polynomial<F>>) {
    use std::collections::BTreeMap;

    *polys = std::mem::take(polys)
        .into_iter()
        .filter_map(|p| {
            if p.is_zero() {
                return None;
            }

            let mut common_gcd: Option<BTreeMap<Var, usize>> = None;
            for term in p.terms.keys() {
                let group_part: BTreeMap<Var, usize> = term
                    .iter()
                    .filter(|(v, _)| v.typ.is_group())
                    .map(|(v, p)| (v.clone(), *p))
                    .collect();
                if group_part.is_empty() {
                    common_gcd = None;
                    break;
                }
                match &mut common_gcd {
                    None => common_gcd = Some(group_part),
                    Some(g) => {
                        let keys: Vec<Var> = g.keys().cloned().collect();
                        for k in keys {
                            if let Some(v_power) = group_part.get(&k) {
                                *g.get_mut(&k).unwrap() = (*g.get_mut(&k).unwrap()).min(*v_power);
                            } else {
                                g.remove(&k);
                            }
                        }
                        if g.is_empty() {
                            break;
                        }
                    }
                }
            }

            let divisor: Vec<(Var, usize)> = match common_gcd {
                Some(g) if !g.is_empty() => g.into_iter().collect(),
                _ => return Some(p),
            };
            let divisor_mono = crate::frontend::Monomial::from(divisor);

            let new_terms = p.terms.into_iter().map(|(term, coeff)| {
                match term.clone() / divisor_mono.clone() {
                    Some(quotient) => (quotient, coeff),
                    None => (term, coeff),
                }
            });

            let divided: Polynomial<F> = Polynomial {
                terms: new_terms.collect(),
            };
            if divided.is_zero() {
                None
            } else {
                Some(divided)
            }
        })
        .collect();
}

#[cfg(test)]
mod tests {
    use super::SpecialSoundnessAnalysis;
    use crate::QualifierPropagation;
    use crate::Var;
    use crate::backend::GbBackendKind;
    use crate::error::{AnalysisError, ExtractorRejection};
    use crate::tests::parse_and_concretize;
    use backend::ArkBls12_381;
    use graph::UDags;
    use share::Set;
    use share::{Ctx, unwrap};

    /// Test helper: build + compute in one call with default backend and
    /// inlining enabled (the common case in tests).
    fn from_input(
        dag: &graph::QDag<ArkBls12_381>,
        l_vec: Vec<usize>,
    ) -> Result<SpecialSoundnessAnalysis<ArkBls12_381>, AnalysisError<ArkBls12_381>> {
        let inputs = SpecialSoundnessAnalysis::build_inputs(dag, l_vec, true)?;
        SpecialSoundnessAnalysis::from_inputs(inputs, GbBackendKind::default(), true)
    }

    fn analyze_soundness(
        proto: &str,
        l_vec: Vec<usize>,
    ) -> Result<(), AnalysisError<ArkBls12_381>> {
        let m = parse_and_concretize(proto, &Ctx::new());
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g_inp = QualifierPropagation::from_dag(&gs[0]);
        let g = g_inp;
        from_input(&g, l_vec)?.run()
    }

    /// Analyze `proto` in the symbolic group model.
    fn analyze_symbolic(
        proto: &str,
        l_vec: Vec<usize>,
    ) -> Result<SpecialSoundnessAnalysis<ArkBls12_381>, AnalysisError<ArkBls12_381>> {
        let m = parse_and_concretize(proto, &Ctx::new());
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);
        let inputs = SpecialSoundnessAnalysis::build_inputs_with_model(
            &g,
            l_vec,
            true,
            super::SoundnessModel::SymbolicGroup,
        )?;
        let mut sa = SpecialSoundnessAnalysis::from_inputs(inputs, GbBackendKind::default(), true)?;
        sa.run()?;
        Ok(sa)
    }

    // ----- Symbolic group mode: positive cases (arguments that extract) -----

    /// Okamoto: `comm == g*x + h*r`, no verifier check touches a lone
    /// generator, so the plain model finds no extractor. The per-generator
    /// split over {g, h} exposes `x` and `r`.
    #[test]
    fn symbolic_okamoto_extracts() {
        let proto = r#"
            proto okamoto<G: Group, F: Scalar<G>>(
                witness x: F, witness r: F, instance g: G, instance h: G, instance comm: G,
            ) where comm == g * x + h * r {
                let rx = random<F>;
                let rr = random<F>;
                t <- g * rx + h * rr;
                c <- challenge<F*>;
                zx <- rx + x * c;
                zr <- rr + r * c;
                verify(g * zx + h * zr == t + comm * c)
            }
        "#;
        let sa = analyze_symbolic(proto, vec![2]).expect("okamoto should extract under binding");
        assert_eq!(sa.assumptions.as_deref(), Some("binding w.r.t. {g, h}"));
    }

    /// A Pedersen equality-of-messages protocol with explicit message
    /// responses `zm` (a stronger statement than the `examples/pedersen_eq`
    /// file, which only proves knowledge of `r1 − r2`). The split over
    /// {g, h} extracts `m1`, which the plain model rejects as
    /// `NotVisible(m1 - m2)`.
    #[test]
    fn symbolic_pedersen_eq_messages_extract() {
        let proto = r#"
            proto peq<G: Group, F: Scalar<G>>(
                witness m1: F, witness m2: F, witness r1: F, witness r2: F,
                instance g: G, instance h: G, instance c1: G, instance c2: G,
            ) where c1 == g * m1 + h * r1 && c2 == g * m2 + h * r2 && m1 == m2 {
                let km = random<F>;
                let kr1 = random<F>;
                let kr2 = random<F>;
                t1 <- g * km + h * kr1;
                t2 <- g * km + h * kr2;
                c <- challenge<F*>;
                zm <- km + m1 * c;
                zr1 <- kr1 + r1 * c;
                zr2 <- kr2 + r2 * c;
                verify(g * zm + h * zr1 == t1 + c1 * c && g * zm + h * zr2 == t2 + c2 * c)
            }
        "#;
        analyze_symbolic(proto, vec![2]).expect("pedersen_eq should extract under binding");
    }

    // ----- Symbolic group mode: negative cases (NOT knowledge-sound) -----

    /// Copy attack: the prover echoes the statement element `comm` into its
    /// message and the verifier checks equality. The prover demonstrates no
    /// knowledge of `x`, so extraction must fail. This is the case that
    /// forces the three-tier representation: if transcript elements could
    /// only be represented over the generator basis, the analysis would
    /// wrongly "extract" `comm`'s representation here.
    #[test]
    fn symbolic_copy_attack_rejected() {
        let proto = r#"
            proto echo<G: Group, F: Scalar<G>>(
                witness x: F, instance g: G, instance comm: G,
            ) where comm == g * x {
                t <- comm;
                c <- challenge<F*>;
                z <- x * c - x * c;
                verify(t == comm && g * z == g * z)
            }
        "#;
        let r = analyze_symbolic(proto, vec![2]);
        assert!(r.is_err(), "echoing the statement proves no knowledge");
    }

    /// Unbound witness: the relation commits `comm == g*x + h*r`, but no
    /// verifier check mentions `comm`; a genuine Schnorr on a *separate*
    /// instance keeps the transcript accepting. Nothing binds `x`/`r`, so
    /// extraction must fail even though the split fires on the Schnorr part.
    #[test]
    fn symbolic_unbound_witness_rejected() {
        let proto = r#"
            proto unbound<G: Group, F: Scalar<G>>(
                witness x: F, witness r: F, witness s: F,
                instance g: G, instance h: G, instance comm: G, instance pub_s: G,
            ) where comm == g * x + h * r && pub_s == g * s {
                let ks = random<F>;
                t <- g * ks;
                c <- challenge<F*>;
                zs <- ks + s * c;
                verify(g * zs == t + pub_s * c)
            }
        "#;
        let r = analyze_symbolic(proto, vec![2]);
        assert!(
            r.is_err(),
            "x and r are committed but never checked, so unextractable"
        );
    }

    /// Challenge-independent check: the verified equation does not involve
    /// the challenge, so two accepting transcripts with distinct challenges
    /// carry no more information than one. No witness can be extracted.
    #[test]
    fn symbolic_challenge_independent_rejected() {
        let proto = r#"
            proto noch<G: Group, F: Scalar<G>>(
                witness x: F, instance g: G, instance comm: G,
            ) where comm == g * x {
                let rr = random<F>;
                t <- g * rr;
                c <- challenge<F*>;
                z <- rr;
                verify(g * z == t)
            }
        "#;
        let r = analyze_symbolic(proto, vec![2]);
        assert!(r.is_err(), "a challenge-free check extracts nothing");
    }

    /// A false basis: the relation constrains a would-be generator
    /// (`h == g * k` for a public `k`), so {g, h} are not independent. The
    /// demotion scan moves `h` to the statement tier; the analysis must not
    /// use it as a free basis element to manufacture an extractor, and the
    /// unsound witness `x` (never checked against `g`) must fail.
    #[test]
    fn symbolic_false_basis_does_not_overclaim() {
        let proto = r#"
            proto fb<G: Group, F: Scalar<G>>(
                witness x: F, instance g: G, instance h: G, instance k: F, instance comm: G,
            ) where h == g * k && comm == h * x {
                let rr = random<F>;
                t <- h * rr;
                c <- challenge<F*>;
                z <- rr + x * c;
                verify(h * z == t + comm * c)
            }
        "#;
        // This one *is* knowledge-sound w.r.t. base h (Schnorr in base h),
        // so it may pass; what must hold is that the label names the basis
        // actually used, never claiming independence of {g, h}.
        if let Ok(sa) = analyze_symbolic(proto, vec![2]) {
            let label = sa.assumptions.unwrap_or_default();
            assert!(
                !label.contains("g,") && !label.contains(", g") || label.contains('h'),
                "label must not claim g as an independent basis element: {label}"
            );
        }
    }

    const SCHNORR_PROTO: &str = r#"
        proto schnorr<G: Group, F: Scalar<G>>(witness x: F, instance g: G, instance h: G) where h == g*x {
            let r = random<F>;
            u <- g*r;
            c <- challenge<F*>;
            z <- r + x*c;
            verify(g*z == u + h*c)
        }
    "#;

    #[test]
    fn schnorr_special_soundness_l2() {
        let m = parse_and_concretize(SCHNORR_PROTO, &Ctx::new());
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g_inp = QualifierPropagation::from_dag(&gs[0]);
        let g = g_inp;
        let result = from_input(&g, vec![2]).and_then(|mut sa| sa.run());
        match &result {
            Ok(()) => {}
            Err(e) => panic!("analyze() failed: {:?}", e),
        }
    }

    /// The verifier binds `z` to `v`, not `h`, so the extracted witness
    /// satisfies `g*x == v` while the relation needs `g*x == h`: the validity
    /// check must reject the extractor. Guards the split `reduce(&&)`/`&&`
    /// encoding against ever weakening the relation goals.
    #[test]
    fn validity_rejects_witness_that_misses_the_relation() {
        let proto = r#"
        proto unsound<G: Group, F: Scalar<G>>(
            witness x: F, instance g: G, instance h: G, instance v: G,
        ) where h == g*x {
            let r = random<F>;
            u <- g*r;
            c <- challenge<F*>;
            z <- r + x*c;
            verify(g*z == u + v*c)
        }
    "#;
        let result = analyze_soundness(proto, vec![2]);
        assert!(
            result.is_err(),
            "extracted witness satisfies g*x == v, not the relation's g*x == h; got {result:?}"
        );
    }

    /// A two-slot Schnorr whose single `verify(reduce(&&, …))` splits into
    /// one constraint per element in each transcript copy: extractors must
    /// still be found for both witness slots and validate against the
    /// relation's own split conjunction.
    #[test]
    fn vector_verify_reduce_and_soundness() {
        let proto = r#"
        proto vschnorr<G: Group, F: Scalar<G>>(
            witness x: [F; 2], instance g: G, instance h: [G; 2],
        ) where reduce(&&, h == [g*x[i] for i in 0..2]) {
            let r0 = random<F>;
            let r1 = random<F>;
            u <- [g*r0, g*r1];
            c <- challenge<F*>;
            z <- [r0 + x[0]*c, r1 + x[1]*c];
            verify(reduce(&&, [g*z[i] for i in 0..2] == [u[i] + h[i]*c for i in 0..2]))
        }
    "#;
        let result = analyze_soundness(proto, vec![2]);
        assert!(
            result.is_ok(),
            "split reduce(&&) soundness failed: {result:?}"
        );
    }

    /// Same shape, but both verifier equations bind to `h[0]`: the extracted
    /// `x[1]` satisfies `g*x[1] == h[0]`, not the relation's `g*x[1] == h[1]`,
    /// so the split relation goals must reject it.
    #[test]
    fn vector_verify_reduce_and_unsound_slot_rejected() {
        let proto = r#"
        proto vschnorr<G: Group, F: Scalar<G>>(
            witness x: [F; 2], instance g: G, instance h: [G; 2],
        ) where reduce(&&, h == [g*x[i] for i in 0..2]) {
            let r0 = random<F>;
            let r1 = random<F>;
            u <- [g*r0, g*r1];
            c <- challenge<F*>;
            z <- [r0 + x[0]*c, r1 + x[1]*c];
            verify(reduce(&&, [g*z[i] for i in 0..2] == [u[i] + h[0]*c for i in 0..2]))
        }
    "#;
        let result = analyze_soundness(proto, vec![2]);
        assert!(
            result.is_err(),
            "x[1] extracts to a witness for h[0], which misses the relation; got {result:?}"
        );
    }

    /// The relation also demands `k == g*(x+1)`, which no verifier check
    /// touches: transcripts accept for any `k`, so no extractor can promise
    /// it, and the validity phase must reject. Before the goals were
    /// separated from the assumptions, the relation's own constraints were
    /// merged into the validity ideal and this passed vacuously.
    #[test]
    fn validity_rejects_relation_conjunct_the_verifier_ignores() {
        let proto = r#"
        proto gap<G: Group, F: Scalar<G>>(
            witness x: F, instance g: G, instance h: G, instance k: G,
        ) where h == g*x && k == g*(x + 1) {
            let r = random<F>;
            u <- g*r;
            c <- challenge<F*>;
            z <- r + x*c;
            verify(g*z == u + h*c)
        }
    "#;
        let result = analyze_soundness(proto, vec![2]);
        assert!(
            matches!(result, Err(AnalysisError::ExtractorInvalid(_))),
            "the k-conjunct is unenforced, so validity must fail; got {result:?}"
        );
    }

    /// `y` is only reachable through `x`: its best polynomial is `y − x − 1`,
    /// which mentions the witness `x`. The pass-wise search extracts `x` from
    /// the transcripts first, then admits `y` through the already-extracted
    /// `x` (chained extraction).
    #[test]
    fn chained_extraction_through_an_earlier_witness() {
        let proto = r#"
        proto chain<G: Group, F: Scalar<G>>(
            witness x: F, witness y: F, instance g: G, instance h: G,
        ) where h == g*x && y == x + 1 {
            let r = random<F>;
            u <- g*r;
            c <- challenge<F*>;
            z <- r + x*c;
            verify(g*z == u + h*c)
        }
    "#;
        let result = analyze_soundness(proto, vec![2]);
        assert!(
            result.is_ok(),
            "y = x + 1 should chain through x: {result:?}"
        );
    }

    #[test]
    fn reject_l_less_than_two() {
        let result = analyze_soundness(SCHNORR_PROTO, vec![1]);
        assert!(matches!(
            result,
            Err(AnalysisError::InvalidSoundnessParameter)
        ));
    }

    #[test]
    fn reject_empty_l_vec() {
        let result = analyze_soundness(SCHNORR_PROTO, vec![]);
        assert!(matches!(
            result,
            Err(AnalysisError::InvalidSoundnessParameter)
        ));
    }

    #[test]
    fn reject_no_challenge() {
        let proto = r#"
            proto foo<F: Field>(instance s: F) where s == s {
                verify(s == s)
            }
        "#;
        let result = analyze_soundness(proto, vec![2]);
        assert!(matches!(result, Err(AnalysisError::NoChallenge)));
    }

    #[test]
    fn unused_witness_has_no_extractor() {
        let proto = r#"
            proto foo<G: Group, F: Scalar<G>>(witness x: F, witness w: F, instance g: G, instance h: G) where h == g*x {
                let r = random<F>;
                u <- g*r;
                c <- challenge<F*>;
                z <- r + x*c;
                verify(g*z == u + h*c)
            }
        "#;
        let result = analyze_soundness(proto, vec![2]);
        match &result {
            Err(AnalysisError::NoValidExtractor { reason, .. }) => {
                matches!(reason.as_ref(), ExtractorRejection::NoExtractor);
            }
            other => panic!("expected NoExtractor rejection, got: {:?}", other),
        }
    }

    #[test]
    fn schnorr_namespace_l2() {
        let m = parse_and_concretize(SCHNORR_PROTO, &Ctx::new());
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g_inp = QualifierPropagation::from_dag(&gs[0]);
        let g = g_inp;
        from_input(&g, vec![2]).unwrap().run().unwrap();

        let witness_names: Set<String> = crate::var::dag_args(&g)
            .into_iter()
            .filter(|a| a.is_witness())
            .flat_map(|a| a.slots())
            .map(|w| w.name().to_string())
            .collect();
        assert!(witness_names.contains(&"x".to_string()));
        let witness_count: usize = crate::var::dag_args(&g)
            .into_iter()
            .filter(|a| a.is_witness())
            .flat_map(|a| a.slots())
            .count();
        assert_eq!(witness_count, 1);
    }

    const CHAUM_PEDERSEN_PROTO: &str = r#"
        proto chaum_pedersen<G: Group, F: Scalar<G>>(
            witness x: F,
            instance g: G, instance g2: G,
            instance h1: G, instance h2: G
        ) where h1 == g*x && h2 == g2*x {
            let r = random<F>;
            u <- g*r;
            w <- g2*r;
            c <- challenge<F*>;
            z <- r + x*c;
            verify(g*z == u + h1*c); verify(g2*z == w + h2*c)
        }
    "#;

    #[test]
    fn schnorr_g_identity_no_extractor() {
        let proto = r#"
            proto schnorr<G: Group, F: Scalar<G>>(witness x: F, instance g: G, instance h: G) where g == g - g && h == g*x {
                let r = random<F>;
                u <- g*r;
                c <- challenge<F*>;
                z <- r + x*c;
                verify(g*z == u + h*c)
            }
        "#;
        let result = analyze_soundness(proto, vec![2]);
        match &result {
            Err(AnalysisError::NoValidExtractor { .. }) => {}
            Err(AnalysisError::ExtractorInvalid(_)) => {}
            other => panic!(
                "expected NoValidExtractor or ExtractorInvalid, got: {:?}",
                other
            ),
        }
    }

    #[test]
    fn chaum_pedersen_special_soundness_l2() {
        assert!(analyze_soundness(CHAUM_PEDERSEN_PROTO, vec![2]).is_ok());
    }

    /// Not special sound as a vector challenge with l=2: z = r + x(c1 + c2)
    /// gives Δz = x(Δc₁ + Δc₂). The product d-equation guarantees one of
    /// Δc₁, Δc₂ is individually invertible, but we need their *sum* to be
    /// invertible, which the GB cannot establish.
    #[test]
    fn consecutive_challenges_not_sound_as_vector() {
        let proto = r#"
            proto vec_challenge<G: Group, F: Scalar<G>>(witness x: F, instance g: G, instance h: G) where h == g*x {
                let r = random<F>;
                u <- g*r;
                c1 <- challenge<F*>;
                c2 <- challenge<F*>;
                z <- r + x*c1 + x*c2;
                verify(g*z == u + h*c1 + h*c2)
            }
        "#;
        assert!(analyze_soundness(proto, vec![2]).is_err());
    }

    /// Not special sound with a single vector challenge round: if two
    /// accepting transcripts differ only in c2 (same c1), the first
    /// response z1 = r1 + x*c1 is identical, so x cannot be extracted.
    /// With `vec![2]` (1 round, 2 copies), both c1 and c2 are treated
    /// as a single vector, which is not sound for this protocol.
    #[test]
    fn schnorr_two_challenge_not_sound_as_vector() {
        let proto = r#"
            proto schnorr<G: Group, F: Scalar<G>>(witness x: F, instance g: G, instance h: G) where h == g*x {
                let r1 = random<F>;
                u1 <- g * r1;
                let r2 = random<F>;
                u2 <- g * r2;
                c1 <- challenge<F*>;
                c2 <- challenge<F*>;
                z1 <- r1 + x * c1;
                z2 <- r2 + r1 * c2 + x * (c1 * c2);
                verify(g*z1 == u1 + h*c1); verify(g*z2 == u2 + u1*c2 + h*(c1*c2))
            }
        "#;
        assert!(analyze_soundness(proto, vec![2]).is_err());
    }

    #[test]
    fn schnorr_quadratic_two_challenge_special_soundness() {
        let proto = r#"
            proto schnorr<G: Group, F: Scalar<G>>(witness x: F, instance g: G, instance h: G) where h == g*x {
                let r = random<F>;
                let s = random<F>;
                u <- g*r;
                v <- g*s;
                c1 <- challenge<F*>;
                z1 <- r + x*c1;
                c2 <- challenge<F*>;
                z2 <- s + r*c2 + x*(c1*c2) + x*(c2*c2);
                verify(g*z1 == u + h*c1); verify(g*z2 == v + u*c2 + h*(c1*c2 + c2*c2))
            }
        "#;
        assert!(analyze_soundness(proto, vec![2, 2]).is_ok());
    }

    #[test]
    fn multi_round_schnorr_special_soundness() {
        let proto = r#"
            proto multi_schnorr<G: Group, F: Scalar<G>>(witness x: F, instance g: G, instance h: G) where h == g*x {
                let r1 = random<F>;
                u1 <- g*r1;
                c1 <- challenge<F*>;
                let r2 = random<F>;
                u2 <- g*r2;
                c2 <- challenge<F*>;
                z1 <- r1 + x*c1;
                z2 <- r2 + x*c2;
                verify(g*z1 == u1 + h*c1); verify(g*z2 == u2 + h*c2)
            }
        "#;
        assert!(analyze_soundness(proto, vec![2, 2]).is_ok());
    }

    #[test]
    fn reject_challenge_before_any_prover_message() {
        let proto = r#"
            proto bad<G: Group, F: Scalar<G>>(witness x: F, instance g: G, instance h: G) where h == g*x {
                c <- challenge<F*>;
                u <- g*x;
                verify(g*x == u)
            }
        "#;
        let result = analyze_soundness(proto, vec![2]);
        match &result {
            Err(AnalysisError::Not2nPlus1MoveProtocol { .. }) => {}
            other => panic!("expected Not2nPlus1MoveProtocol, got: {:?}", other),
        }
    }

    #[test]
    fn reject_trailing_challenge() {
        let proto = r#"
            proto bad<G: Group, F: Scalar<G>>(witness x: F, instance g: G, instance h: G) where h == g*x {
                let r = random<F>;
                u <- g*r;
                c <- challenge<F*>;
                z <- r + x*c;
                d <- challenge<F*>;
                verify(g*z == u + h*c)
            }
        "#;
        let result = analyze_soundness(proto, vec![2]);
        match &result {
            Err(AnalysisError::Not2nPlus1MoveProtocol { .. }) => {}
            other => panic!("expected Not2nPlus1MoveProtocol, got: {:?}", other),
        }
    }

    #[test]
    fn reject_challenge_count_mismatch() {
        let proto = r#"
            proto bad<G: Group, F: Scalar<G>>(witness x: F, instance g: G, instance h: G) where h == g*x {
                let r = random<F>;
                u <- g*r;
                c1 <- challenge<F*>;
                z1 <- r + x*c1;
                c2 <- challenge<F*>;
                z2 <- r + x*c2;
                verify(g*z1 == u + h*c1); verify(g*z2 == u + h*c2)
            }
        "#;
        let result = analyze_soundness(proto, vec![2]);
        match &result {
            Err(AnalysisError::Not2nPlus1MoveProtocol { .. }) => {}
            other => panic!("expected Not2nPlus1MoveProtocol, got: {:?}", other),
        }
    }

    #[test]
    fn reject_too_many_l() {
        let result = analyze_soundness(SCHNORR_PROTO, vec![2, 2]);
        match &result {
            Err(AnalysisError::Not2nPlus1MoveProtocol { .. }) => {}
            other => panic!("expected Not2nPlus1MoveProtocol, got: {:?}", other),
        }
    }

    #[test]
    fn schnorr_vec_witness_slot_expansion() {
        let m = parse_and_concretize(SCHNORR_PROTO, &Ctx::new());
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g_inp = QualifierPropagation::from_dag(&gs[0]);
        let g = g_inp;
        from_input(&g, vec![2]).unwrap().run().unwrap();

        let witness_slots: Vec<Var> = crate::var::dag_args(&g)
            .into_iter()
            .filter(|a| a.is_witness())
            .flat_map(|a| a.slots())
            .collect();
        assert_eq!(witness_slots.len(), 1);
        for slot in &witness_slots {
            assert!(
                slot.typ.is_scalar(),
                "expected scalar slot, got {:?}",
                slot.typ
            );
        }
    }

    #[test]
    fn vec_witness_multi_slot_soundness() {
        let proto = r#"
            proto vec_wit<G: Group, F: Scalar<G>>(witness x: [F; 2], instance g: G, instance h1: G, instance h2: G) where h1 == g*x[0] && h2 == g*x[1] {
                let r0 = random<F>;
                let r1 = random<F>;
                u0 <- g*r0;
                u1 <- g*r1;
                c <- challenge<F*>;
                z0 <- r0 + x[0]*c;
                z1 <- r1 + x[1]*c;
                verify(g*z0 == u0 + h1*c); verify(g*z1 == u1 + h2*c)
            }
        "#;
        let m = parse_and_concretize(proto, &Ctx::new());
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g_inp = QualifierPropagation::from_dag(&gs[0]);
        let g = g_inp;
        let result = from_input(&g, vec![2]).and_then(|mut sa| sa.run());
        assert!(result.is_ok());
    }

    /// Not special sound for extracting both x1 and x2: z = r + x1*c1 + x2*c2
    /// with a single vector challenge round. The product d-equation guarantees
    /// at least one slot's challenge difference is invertible per pair, but
    /// cannot guarantee both slots are invertible simultaneously.
    #[test]
    fn consecutive_vec_challenge_two_witnesses_not_sound() {
        let proto = r#"
            proto vec_two_wit<G: Group, F: Scalar<G>>(witness x1: F, witness x2: F, instance g: G, instance h1: G, instance h2: G) where h1 == g*x1 && h2 == g*x2 {
                let r = random<F>;
                u <- g*r;
                c1 <- challenge<F*>;
                c2 <- challenge<F*>;
                z <- r + x1*c1 + x2*c2;
                verify(g*z == u + h1*c1 + h2*c2)
            }
        "#;
        assert!(analyze_soundness(proto, vec![3]).is_err());
    }

    /// Vector challenge with independent response per slot:
    /// z1 = r + x*c1, z2 = s + x*c2. Each slot independently
    /// gives x = d_k * (z_k::0 - z_k::1). The product d-equation
    /// guarantees at least one slot is extractable, and since both
    /// slots use the same witness x, either one suffices.
    #[test]
    fn vector_challenge_independent_responses() {
        let proto = r#"
            proto vec_indep<G: Group, F: Scalar<G>>(witness x: F, instance g: G, instance h: G) where h == g*x {
                let r = random<F>;
                let s = random<F>;
                u1 <- g*r;
                u2 <- g*s;
                c1 <- challenge<F*>;
                c2 <- challenge<F*>;
                z1 <- r + x*c1;
                z2 <- s + x*c2;
                verify(g*z1 == u1 + h*c1); verify(g*z2 == u2 + h*c2)
            }
        "#;
        assert!(analyze_soundness(proto, vec![2]).is_ok());
    }
}
