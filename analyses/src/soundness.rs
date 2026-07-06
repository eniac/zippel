use std::collections::{HashMap, HashSet, VecDeque};

use crate::TransClos;
use crate::Var;
use crate::backend::{GbBackendKind, GbBasis};
use crate::error::{AnalysisError, ExtractorRejection};
use crate::extractor::{extract_locals, valid_extractor};
use crate::frontend::{MonoOrder, Polynomial};
use crate::ideal::{Ideal, IdealBuilder};
use ark_ff::One;
use backend::op::HasOpFactory;
use backend::{ATyp, ArkConfig};
use graph::{DQDag, Ref};
use lang::typ::Qualifier;
use log::{info, warn};
use petgraph::Direction;
use petgraph::graph::NodeIndex;
use petgraph::visit::EdgeRef;
use share::Set;

pub struct SpecialSoundnessAnalysis<C: ArkConfig> {
    /// Gröbner basis of the search ideal (verifier TC copies + d-equations +
    /// relation) under lex order. Computed in `from_input_with_backend`.
    /// Snapshotable.
    pub search_gb: GbBasis<C::F>,
    /// Witness slots (private args) for extractor search in `run()`.
    witness_slots: Vec<Var>,
    /// Variables visible to the verifier (used for extractor validation).
    verifier_visible: Set<Var>,
    /// Validity ideal: d-equations + copy TCs. Extractors are added in
    /// `run()` before computing the validity GB.
    grev_validity: Ideal<C>,
    /// Relation ideal (inlined). Relation polys are reduced against the
    /// validity GB in `run()`.
    grev_rel_result: Ideal<C>,
    /// Relation locals (merged into validity ideal in `run()`).
    rel_locals: Ideal<C>,
    /// Lex ordering used for both search and validity GBs.
    lex_order: MonoOrder,
    /// Backend for the validity GB computation in `run()`.
    backend: GbBackendKind,
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
    dag: &DQDag<C>,
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

impl<C: ArkConfig + HasOpFactory> SpecialSoundnessAnalysis<C> {
    /// Analyze special soundness of a sigma protocol.
    ///
    /// Convenience wrapper: `from_input_with_backend` + `run`.
    pub fn analyze(dag: &DQDag<C>, l_vec: Vec<usize>) -> Result<(), AnalysisError<C>> {
        Self::analyze_with_backend(dag, l_vec, GbBackendKind::default())
    }

    /// Like [`analyze`](Self::analyze) but with a user-selected GB backend.
    pub fn analyze_with_backend(
        dag: &DQDag<C>,
        l_vec: Vec<usize>,
        backend: GbBackendKind,
    ) -> Result<(), AnalysisError<C>> {
        let mut sa = Self::from_input_with_backend(dag, l_vec, backend)?;
        sa.run()
    }

    /// Build the analysis from the DAG, computing the search Gröbner basis.
    ///
    /// # Phases
    ///
    /// 1. **Construct**: build all GB inputs — d-equations, copy TCs,
    ///    relation polys (order-free).
    /// 2. **Build lex ordering**: compute the lex-elimination var_order from
    ///    `var_order` as `MonoOrder::lex(var_order)` — runtime data, no TLS.
    /// 3. **Inline & compute** the search GB via the backend under lex.
    pub fn from_input_with_backend(
        dag: &DQDag<C>,
        l_vec: Vec<usize>,
        backend: GbBackendKind,
    ) -> Result<Self, AnalysisError<C>> {
        if l_vec.is_empty() || l_vec.iter().any(|l| *l < 2) {
            return Err(AnalysisError::InvalidSoundnessParameter);
        }

        let challenge_rounds = validate_2n_plus_1(dag, &l_vec)?;

        let witness_slots: Vec<Var> = crate::var::dag_args(dag)
            .into_iter()
            .filter(|a| a.is_private())
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
        let mut grev_builder: IdealBuilder<C> = IdealBuilder::new();
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
        let mut pub_vars: Vec<Var> = Vec::new();
        let mut priv_vars: Vec<Var> = Vec::new();

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
                if var.qualifier.is_private() {
                    priv_vars.push(var.clone());
                } else {
                    pub_vars.push(var.clone());
                }
            }
            let copy_result = grev_builder.build(tc);
            grev_search.merge(&copy_result);
            grev_validity.merge(&copy_result);
        }

        let rel_tc = TransClos::relation(dag);
        for var in rel_tc.vars.iter() {
            if var.qualifier.is_private() {
                priv_vars.push(var.clone());
            } else {
                pub_vars.push(var.clone());
            }
        }
        let mut rel_locals = extract_locals(&grev_builder, &rel_tc);
        let mut grev_rel_result = grev_builder.build(rel_tc.clone());
        rel_locals.inline(&Set::new());
        grev_rel_result.inline(&Set::new());

        grev_search.merge(&grev_rel_result);

        // Phase 2: Build lex ordering as runtime data.
        // Priority: rel_locals > priv_vars > other_locals > pub_vars.
        // In MonoOrder::lex, the first variable has the highest elimination
        // priority. Within each group, sort by Var::Ord for determinism.
        let lex_var_order: Vec<Var> = {
            let rel_locals_set: Set<Var> = grev_rel_result.var_order.iter().cloned().collect();
            let priv_set: Set<Var> = priv_vars.iter().cloned().collect();
            let pub_set: Set<Var> = pub_vars.iter().cloned().collect();

            let all_vars: Set<Var> = grev_search.vars();

            let mut rel: Vec<Var> = all_vars
                .iter()
                .filter(|v| rel_locals_set.contains(v))
                .cloned()
                .collect();
            rel.sort();
            let mut priv_v: Vec<Var> = all_vars
                .iter()
                .filter(|v| priv_set.contains(v) && !rel_locals_set.contains(v))
                .cloned()
                .collect();
            priv_v.sort();
            let mut pub_v: Vec<Var> = all_vars
                .iter()
                .filter(|v| {
                    pub_set.contains(v) && !rel_locals_set.contains(v) && !priv_set.contains(v)
                })
                .cloned()
                .collect();
            pub_v.sort();
            let mut other: Vec<Var> = all_vars
                .iter()
                .filter(|v| {
                    !rel_locals_set.contains(v) && !priv_set.contains(v) && !pub_set.contains(v)
                })
                .cloned()
                .collect();
            other.sort();

            rel.into_iter()
                .chain(priv_v)
                .chain(other)
                .chain(pub_v)
                .collect()
        };
        let lex_order = MonoOrder::lex(lex_var_order);

        // Phase 3: Inline & compute the search GB via the backend.
        grev_search.inline(&Set::new());

        let gb = backend.build::<C::F>();
        let search_gb = gb
            .compute_gb(std::mem::take(&mut grev_search.generating_set), &lex_order)
            .expect("GB backend should support lex order");

        if search_gb.is_unit() {
            return Err(AnalysisError::UnitIdeal {
                context: "soundness search",
            });
        }

        Ok(Self {
            search_gb,
            witness_slots,
            verifier_visible,
            grev_validity,
            grev_rel_result,
            rel_locals,
            lex_order,
            backend,
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
        // Phase 4: Extract witnesses.
        let mut search_polys = self.search_gb.polys.clone();
        factor_group_gcd(&mut search_polys);

        let mut extractors: Vec<(Var, Polynomial<C::F>)> = Vec::new();

        for w in &self.witness_slots {
            let mut found_extractor = None;
            let mut rejection: Option<ExtractorRejection<C>> = None;

            'poly: for poly in search_polys.iter() {
                for term in poly.terms.keys() {
                    let tv = term.vars();
                    let tp = term.powers();
                    let is_witness_term = tv.len() == 1 && tv[0] == *w && tp[0] == 1;
                    if !is_witness_term {
                        continue;
                    }

                    let other_vars: Set<Var> = poly
                        .terms
                        .iter()
                        .filter(|(t, _)| {
                            let tvars = t.vars();
                            let tpows = t.powers();
                            !(tvars.len() == 1 && tvars[0] == *w && tpows[0] == 1)
                        })
                        .flat_map(|(t, _)| t.vars())
                        .collect();

                    let all_visible = other_vars.iter().all(|v| self.verifier_visible.contains(v));
                    if !all_visible {
                        rejection = Some(ExtractorRejection::NotVisible(poly.clone()));
                        continue;
                    }
                    if !valid_extractor::<C>(&w.typ, poly) {
                        if w.typ.is_scalar() {
                            rejection = Some(ExtractorRejection::FieldDependsOnGroup(poly.clone()));
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
                    extractors.push((w.clone(), poly));
                }
                None => {
                    let reason = rejection.unwrap_or(ExtractorRejection::NoExtractor);
                    warn!("No valid extractor for witness {:?}", w);
                    return Err(AnalysisError::NoValidExtractor {
                        witness: w.clone(),
                        reason: Box::new(reason),
                    });
                }
            }
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

        self.grev_validity.merge(&self.rel_locals);
        self.grev_validity.inline(&Set::new());

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

        for r in self.grev_rel_result.generating_set.iter() {
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
    dag: &DQDag<C>,
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
                let base = Var::from_node(node, typ.clone(), Qualifier::Public);
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
    use crate::Var;
    use crate::error::{AnalysisError, ExtractorRejection};
    use crate::{QualifierPropagation, UniformityPropagation};
    use backend::ArkBls12_381;
    use graph::UDags;
    use lang::ast::UModule;
    use share::Set;
    use share::{Ctx, unwrap};

    fn analyze_soundness(
        proto: &str,
        l_vec: Vec<usize>,
    ) -> Result<(), AnalysisError<ArkBls12_381>> {
        let m = UModule::from_str(proto)
            .unwrap()
            .concretize(&Ctx::new())
            .unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g_inp = QualifierPropagation::from_dag(&gs[0]);
        let g = UniformityPropagation::from_dag(&g_inp).annotate_dag(&g_inp);
        SpecialSoundnessAnalysis::analyze(&g, l_vec)
    }

    const SCHNORR_PROTO: &str = r#"
        proto schnorr<G: Group, F: Scalar<G>>(private x: F, public g: G, public h: G) where h == g*x {
            let r = random<F>;
            u <- g*r;
            c <- challenge<F*>;
            z <- r + x*c;
            verify(g*z == u + h*c)
        }
    "#;

    #[test]
    fn schnorr_special_soundness_l2() {
        let m = UModule::from_str(SCHNORR_PROTO)
            .unwrap()
            .concretize(&Ctx::new())
            .unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g_inp = QualifierPropagation::from_dag(&gs[0]);
        let g = UniformityPropagation::from_dag(&g_inp).annotate_dag(&g_inp);
        let result = SpecialSoundnessAnalysis::analyze(&g, vec![2]);
        match &result {
            Ok(()) => {}
            Err(e) => panic!("analyze() failed: {:?}", e),
        }
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
            proto foo<F: Field>(public s: F) where s == s {
                verify(s == s)
            }
        "#;
        let result = analyze_soundness(proto, vec![2]);
        assert!(matches!(result, Err(AnalysisError::NoChallenge)));
    }

    #[test]
    fn unused_witness_has_no_extractor() {
        let proto = r#"
            proto foo<G: Group, F: Scalar<G>>(private x: F, private w: F, public g: G, public h: G) where h == g*x {
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
        let m = UModule::from_str(SCHNORR_PROTO)
            .unwrap()
            .concretize(&Ctx::new())
            .unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g_inp = QualifierPropagation::from_dag(&gs[0]);
        let g = UniformityPropagation::from_dag(&g_inp).annotate_dag(&g_inp);
        SpecialSoundnessAnalysis::analyze(&g, vec![2]).unwrap();

        let witness_names: Set<String> = crate::var::dag_args(&g)
            .into_iter()
            .filter(|a| a.is_private())
            .flat_map(|a| a.slots())
            .map(|w| w.name().to_string())
            .collect();
        assert!(witness_names.contains(&"x".to_string()));
        let witness_count: usize = crate::var::dag_args(&g)
            .into_iter()
            .filter(|a| a.is_private())
            .flat_map(|a| a.slots())
            .count();
        assert_eq!(witness_count, 1);
    }

    const CHAUM_PEDERSEN_PROTO: &str = r#"
        proto chaum_pedersen<G: Group, F: Scalar<G>>(
            private x: F,
            public g: G, public g2: G,
            public h1: G, public h2: G
        ) where h1 == g*x && h2 == g2*x {
            let r = random<F>;
            u <- g*r;
            w <- g2*r;
            c <- challenge<F*>;
            z <- r + x*c;
            verify(g*z == u + h1*c && g2*z == w + h2*c)
        }
    "#;

    #[test]
    fn schnorr_g_identity_no_extractor() {
        let proto = r#"
            proto schnorr<G: Group, F: Scalar<G>>(private x: F, public g: G, public h: G) where g == g - g && h == g*x {
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
            proto vec_challenge<G: Group, F: Scalar<G>>(private x: F, public g: G, public h: G) where h == g*x {
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
            proto schnorr<G: Group, F: Scalar<G>>(private x: F, public g: G, public h: G) where h == g*x {
                let r1 = random<F>;
                u1 <- g * r1;
                let r2 = random<F>;
                u2 <- g * r2;
                c1 <- challenge<F*>;
                c2 <- challenge<F*>;
                z1 <- r1 + x * c1;
                z2 <- r2 + r1 * c2 + x * (c1 * c2);
                verify(g*z1 == u1 + h*c1 && g*z2 == u2 + u1*c2 + h*(c1*c2))
            }
        "#;
        assert!(analyze_soundness(proto, vec![2]).is_err());
    }

    #[test]
    fn schnorr_quadratic_two_challenge_special_soundness() {
        let proto = r#"
            proto schnorr<G: Group, F: Scalar<G>>(private x: F, public g: G, public h: G) where h == g*x {
                let r = random<F>;
                let s = random<F>;
                u <- g*r;
                v <- g*s;
                c1 <- challenge<F*>;
                z1 <- r + x*c1;
                c2 <- challenge<F*>;
                z2 <- s + r*c2 + x*(c1*c2) + x*(c2*c2);
                verify(g*z1 == u + h*c1 && g*z2 == v + u*c2 + h*(c1*c2 + c2*c2))
            }
        "#;
        assert!(analyze_soundness(proto, vec![2, 2]).is_ok());
    }

    #[test]
    fn multi_round_schnorr_special_soundness() {
        let proto = r#"
            proto multi_schnorr<G: Group, F: Scalar<G>>(private x: F, public g: G, public h: G) where h == g*x {
                let r1 = random<F>;
                u1 <- g*r1;
                c1 <- challenge<F*>;
                let r2 = random<F>;
                u2 <- g*r2;
                c2 <- challenge<F*>;
                z1 <- r1 + x*c1;
                z2 <- r2 + x*c2;
                verify(g*z1 == u1 + h*c1 && g*z2 == u2 + h*c2)
            }
        "#;
        assert!(analyze_soundness(proto, vec![2, 2]).is_ok());
    }

    #[test]
    fn reject_challenge_before_any_prover_message() {
        let proto = r#"
            proto bad<G: Group, F: Scalar<G>>(private x: F, public g: G, public h: G) where h == g*x {
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
            proto bad<G: Group, F: Scalar<G>>(private x: F, public g: G, public h: G) where h == g*x {
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
            proto bad<G: Group, F: Scalar<G>>(private x: F, public g: G, public h: G) where h == g*x {
                let r = random<F>;
                u <- g*r;
                c1 <- challenge<F*>;
                z1 <- r + x*c1;
                c2 <- challenge<F*>;
                z2 <- r + x*c2;
                verify(g*z1 == u + h*c1 && g*z2 == u + h*c2)
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
        let m = UModule::from_str(SCHNORR_PROTO)
            .unwrap()
            .concretize(&Ctx::new())
            .unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g_inp = QualifierPropagation::from_dag(&gs[0]);
        let g = UniformityPropagation::from_dag(&g_inp).annotate_dag(&g_inp);
        SpecialSoundnessAnalysis::analyze(&g, vec![2]).unwrap();

        let witness_slots: Vec<Var> = crate::var::dag_args(&g)
            .into_iter()
            .filter(|a| a.is_private())
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
            proto vec_wit<G: Group, F: Scalar<G>>(private x: [F; 2], public g: G, public h1: G, public h2: G) where h1 == g*x[0] && h2 == g*x[1] {
                let r0 = random<F>;
                let r1 = random<F>;
                u0 <- g*r0;
                u1 <- g*r1;
                c <- challenge<F*>;
                z0 <- r0 + x[0]*c;
                z1 <- r1 + x[1]*c;
                verify(g*z0 == u0 + h1*c && g*z1 == u1 + h2*c)
            }
        "#;
        let m = UModule::from_str(proto)
            .unwrap()
            .concretize(&Ctx::new())
            .unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g_inp = QualifierPropagation::from_dag(&gs[0]);
        let g = UniformityPropagation::from_dag(&g_inp).annotate_dag(&g_inp);
        let result = SpecialSoundnessAnalysis::analyze(&g, vec![2]);
        assert!(result.is_ok());
    }

    /// Not special sound for extracting both x1 and x2: z = r + x1*c1 + x2*c2
    /// with a single vector challenge round. The product d-equation guarantees
    /// at least one slot's challenge difference is invertible per pair, but
    /// cannot guarantee both slots are invertible simultaneously.
    #[test]
    fn consecutive_vec_challenge_two_witnesses_not_sound() {
        let proto = r#"
            proto vec_two_wit<G: Group, F: Scalar<G>>(private x1: F, private x2: F, public g: G, public h1: G, public h2: G) where h1 == g*x1 && h2 == g*x2 {
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
            proto vec_indep<G: Group, F: Scalar<G>>(private x: F, public g: G, public h: G) where h == g*x {
                let r = random<F>;
                let s = random<F>;
                u1 <- g*r;
                u2 <- g*s;
                c1 <- challenge<F*>;
                c2 <- challenge<F*>;
                z1 <- r + x*c1;
                z2 <- s + x*c2;
                verify(g*z1 == u1 + h*c1 && g*z2 == u2 + h*c2)
            }
        "#;
        assert!(analyze_soundness(proto, vec![2]).is_ok());
    }
}
