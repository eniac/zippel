use std::collections::{HashMap, HashSet, VecDeque};

use crate::analyses::TransClos;
use crate::analyses::error::AnalysisError;
use crate::analyses::extractor::{ExtractLocalTerm, extract_locals};
use crate::analyses::groebner::monomial::{ElimMono, ElimStrategy, Monomial};
use crate::analyses::groebner::{GroebnerBuilder, GroebnerResult, SparsePolynomial};
use crate::{DQDag, PRef, Ref};
use ark_ff::{One, Zero};
use backend::op::HasOpFactory;
use backend::{ATyp, ArkConfig};
use lang::id::Vid;
use log::{info, warn};
use petgraph::Direction;
use petgraph::graph::NodeIndex;
use petgraph::visit::EdgeRef;
use share::{Ctx, Set};

/// Special-soundness elimination strategy: all private variables (witnesses)
/// are eliminated first. Local and public variables are kept.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Soundness;

impl ElimStrategy for Soundness {
    fn eliminate_var(v: &PRef) -> bool {
        v.qualifier.is_private() || v.is_local()
    }
}

/// Special-soundness elimination term. Type alias for the soundness case.
pub type SoundnessElimTerm = ElimMono<Soundness>;

type Poly<C> = SparsePolynomial<<C as ArkConfig>::F, SoundnessElimTerm>;

pub struct SpecialSoundnessAnalysis<C: ArkConfig> {
    search_result: GroebnerResult<C, SoundnessElimTerm>,
    validity_result: GroebnerResult<C, SoundnessElimTerm>,
    #[allow(dead_code, unnameable_types)]
    relation_polys: Vec<Poly<C>>,
    witness_slots: Vec<PRef>,
    rel_tc: TransClos<C>,
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
    pub fn from_input(dag: &DQDag<C>, l_vec: Vec<usize>) -> Result<Self, AnalysisError<C>> {
        if l_vec.is_empty() || l_vec.iter().any(|l| *l < 2) {
            return Err(AnalysisError::InvalidSoundnessParameter);
        }

        let challenge_rounds = validate_2n_plus_1(dag, &l_vec)?;
        let challenge_nodes: Vec<NodeIndex> = challenge_rounds.iter().flatten().copied().collect();

        let witness_slots: Vec<PRef> = dag
            .args()
            .into_iter()
            .filter(|a| a.is_private())
            .flat_map(|a| a.slots())
            .collect();

        let verifier_tc = TransClos::verifier(dag);

        let round_map = build_round_map(dag, &challenge_nodes);

        let challenge_prefs_per_round: Vec<Vec<PRef>> = challenge_rounds
            .iter()
            .map(|round| {
                round
                    .iter()
                    .flat_map(|&cn| {
                        let r = dag.find_ref(cn);
                        verifier_tc
                            .clos
                            .iter()
                            .filter(|(p, _)| p.reference == r)
                            .map(|(p, _)| p.clone())
                            .collect::<Vec<_>>()
                    })
                    .collect()
            })
            .collect();

        let mut search_builder: GroebnerBuilder<C, SoundnessElimTerm> = GroebnerBuilder::new();
        let mut validity_builder: GroebnerBuilder<C, SoundnessElimTerm> = GroebnerBuilder::new();

        let mut worklist: Vec<(Vec<usize>, TransClos<C>)> = vec![(vec![], verifier_tc.clone())];
        let mut all_d_equations: Vec<Poly<C>> = Vec::new();

        for (round_idx, &li) in l_vec.iter().enumerate() {
            let mut new_worklist = Vec::new();

            for (prefix, tc) in worklist {
                let mut copies_with_challenges: Vec<(TransClos<C>, Vec<PRef>)> = Vec::new();

                for j in 0..li {
                    let suffix = format_suffix(&prefix, j);
                    let mut copy_tc = tc.clone();

                    let round_map_ref = &round_map;
                    let suffix_owned = suffix.clone();

                    copy_tc.remap(&|pref: &PRef| {
                        let key = (pref.reference, pref.index);
                        let in_round = round_map_ref
                            .get(&key)
                            .is_some_and(|&highest| highest == round_idx);

                        if in_round {
                            let orig = pref.name().map(|v| v.0.clone()).unwrap_or_default();
                            PRef {
                                name: Some(Vid::new(&format!("{}::{}", orig, suffix_owned))),
                                ..pref.clone()
                            }
                        } else {
                            pref.clone()
                        }
                    });

                    let remapped_challenges: Vec<PRef> = challenge_prefs_per_round[round_idx]
                        .iter()
                        .map(|cp| {
                            let key = (cp.reference, cp.index);
                            let in_round = round_map_ref
                                .get(&key)
                                .is_some_and(|&highest| highest == round_idx);
                            if in_round {
                                let orig = cp.name().map(|v| v.0.clone()).unwrap_or_default();
                                PRef {
                                    name: Some(Vid::new(&format!("{}::{}", orig, suffix_owned))),
                                    ..cp.clone()
                                }
                            } else {
                                cp.clone()
                            }
                        })
                        .collect();

                    copies_with_challenges.push((copy_tc, remapped_challenges));
                }

                // D-equations: for each pair of copies (m, n) in this round,
                // assert that the vector challenges differ in at least one
                // component. If the round has challenges (c1, c2, ...), this
                // is encoded as:
                //   d_0*(c1_m - c1_n) + d_1*(c2_m - c2_n) + ... - 1 = 0
                // where each d_k is a fresh invertible variable. If any
                // component differs, the corresponding d_k makes that term
                // invertible, so the sum is invertible (≠ 0). If no
                // component differs, every term is 0 and the equation
                // reduces to -1 = 0, a contradiction.
                for m in 0..li {
                    for n in (m + 1)..li {
                        let cm_prefs = &copies_with_challenges[m].1;
                        let cn_prefs = &copies_with_challenges[n].1;
                        let one = Poly::<C>::lit(&C::F::one());

                        let diff: Poly<C> = cm_prefs.iter().zip(cn_prefs.iter()).enumerate().fold(
                            Poly::<C>::zero(),
                            |acc, (k, (cm_ref, cn_ref))| {
                                let d_name = format_d_name(&prefix, m, n, k);
                                let d = search_builder.ns.sentinel_pref(&d_name, ATyp::scalar());
                                let d_poly = Poly::<C>::var(&d);
                                let cm_poly = Poly::<C>::var(cm_ref);
                                let cn_poly = Poly::<C>::var(cn_ref);
                                acc + d_poly * (cm_poly - cn_poly)
                            },
                        );

                        all_d_equations.push(diff - one);
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

        let mut search_result = GroebnerResult::<C, SoundnessElimTerm>::new();
        let mut validity_result = GroebnerResult::<C, SoundnessElimTerm>::new();

        for eq in &all_d_equations {
            search_result.basis.push(eq.clone());
            validity_result.basis.push(eq.clone());
        }

        for (_prefix, tc) in worklist {
            let copy_result = search_builder.build(tc);
            search_result.merge(&copy_result);
            validity_result.merge(&copy_result);
        }

        let rel_tc = TransClos::relation(dag);
        let rel_result = search_builder.build(rel_tc.clone());
        let relation_polys: Vec<Poly<C>> = rel_result
            .basis
            .iter()
            .filter_map(|p| {
                if p.is_zero() {
                    return None;
                }
                Some(p.clone())
            })
            .collect();
        for p in &relation_polys {
            search_result.basis.push(p.clone());
        }

        validity_builder.build(verifier_tc);

        search_result.inline();

        Ok(Self {
            search_result,
            validity_result,
            relation_polys,
            witness_slots,
            rel_tc,
        })
    }

    pub fn run(&mut self) -> Result<(), AnalysisError<C>> {
        info!("Running extractor-search Gröbner basis...");

        self.search_result.run::<128>();
        factor_group_gcd(&mut self.search_result);

        let mut extractors: Vec<(PRef, Poly<C>)> = Vec::new();

        for w in &self.witness_slots {
            let is_field_witness = w.typ.is_scalar();
            let mut found_extractor = None;

            for poly in self.search_result.basis.iter() {
                if let Some((_lc, lt)) = poly.leading_term() {
                    let lt_vars = lt.vars();
                    let lt_powers = lt.powers();
                    let is_witness_term =
                        lt_vars.len() == 1 && lt_vars[0] == *w && lt_powers[0] == 1;
                    if !is_witness_term {
                        continue;
                    }

                    let remainder_vars: Set<PRef> = poly
                        .terms
                        .iter()
                        .filter(|(t, _)| {
                            let tv = t.vars();
                            let tp = t.powers();
                            !(tv.len() == 1 && tv[0] == *w && tp[0] == 1)
                        })
                        .flat_map(|(t, _)| t.vars())
                        .collect();
                    let all_visible = remainder_vars.iter().all(|v| !v.qualifier.is_private());
                    if !all_visible {
                        warn!(
                            "Found extractor for {:?} but it depends on non-visible variables",
                            w
                        );
                        return Err(AnalysisError::ExtractorNotVisible {
                            witness: w.clone(),
                            poly: poly.clone(),
                        });
                    }
                    if is_field_witness {
                        let has_group_var = remainder_vars.iter().any(|v| v.typ.is_group());
                        if has_group_var {
                            warn!(
                                "Found extractor for field witness {:?} but it depends on group variables",
                                w
                            );
                            return Err(AnalysisError::ExtractorNotVisible {
                                witness: w.clone(),
                                poly: poly.clone(),
                            });
                        }
                    } else {
                        for (term, _coeff) in poly.terms.iter() {
                            let group_count: usize = term
                                .iter()
                                .filter_map(|(v, i)| if v.typ.is_group() { Some(*i) } else { None })
                                .sum();
                            if group_count > 1 {
                                warn!(
                                    "Found extractor for group witness {:?} but a monomial has >1 group variable",
                                    w
                                );
                                return Err(AnalysisError::ExtractorNotVisible {
                                    witness: w.clone(),
                                    poly: poly.clone(),
                                });
                            }
                        }
                    }
                    found_extractor = Some(poly.clone());
                    break;
                }
            }

            match found_extractor {
                Some(poly) => {
                    info!("Found extractor for {:?}", w);
                    extractors.push((w.clone(), poly));
                }
                None => {
                    warn!("No extractor found for witness {:?}", w);
                    return Err(AnalysisError::NoExtractor(w.clone()));
                }
            }
        }

        info!(
            "Found {} extractor(s) for {} witness slot(s)",
            extractors.len(),
            self.witness_slots.len()
        );

        for (_, ext_poly) in &extractors {
            self.validity_result.basis.push(ext_poly.clone());
        }

        let local_extractors = extract_locals(&self.rel_tc);
        for (_, lex_poly) in &local_extractors {
            let converted = convert_extract_local_poly::<C>(lex_poly);
            self.validity_result.basis.push(converted);
        }

        self.validity_result.inline();
        self.validity_result.run::<128>();
        factor_group_gcd(&mut self.validity_result);

        for r in self.relation_polys.iter() {
            if r.is_zero() {
                continue;
            }
            let rem = self.validity_result.basis.reduce(r.clone());
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
    challenge_nodes: &[NodeIndex],
) -> HashMap<(Ref, usize), usize> {
    let mut round_map: HashMap<(Ref, usize), usize> = HashMap::new();
    let challenge_set: HashSet<NodeIndex> = challenge_nodes.iter().copied().collect();

    for (round_idx, &challenge_node) in challenge_nodes.iter().enumerate() {
        let next_challenge_set: HashSet<NodeIndex> =
            challenge_nodes[round_idx + 1..].iter().copied().collect();

        let mut queue = VecDeque::new();
        let mut visited = HashSet::new();
        queue.push_back(challenge_node);
        visited.insert(challenge_node);

        while let Some(node) = queue.pop_front() {
            if let Some(typ) = dag[node].typ() {
                let r = dag.find_ref(node);
                for idx in 0..typ.physical_len() {
                    round_map
                        .entry((r, idx))
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

fn convert_extract_local_poly<C: ArkConfig>(
    p: &SparsePolynomial<C::F, ExtractLocalTerm>,
) -> Poly<C> {
    let mut terms: Ctx<SoundnessElimTerm, C::F> = Ctx::new();
    for (term, coeff) in p.terms.iter() {
        let pairs: Vec<(PRef, usize)> = term.vars().into_iter().zip(term.powers()).collect();
        let new_term: SoundnessElimTerm = pairs.into();
        *terms.entry(new_term).or_insert(C::F::zero()) += *coeff;
    }
    SparsePolynomial { terms }
}

fn factor_group_gcd<C: ArkConfig>(result: &mut GroebnerResult<C, SoundnessElimTerm>) {
    use std::collections::BTreeMap;

    result.basis.basis = result
        .basis
        .basis
        .drain(..)
        .filter_map(|p| {
            if p.is_zero() {
                return None;
            }

            let mut common_gcd: Option<BTreeMap<PRef, usize>> = None;
            for (term, _coeff) in p.terms.iter() {
                let group_part: BTreeMap<PRef, usize> = term
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
                        let keys: Vec<PRef> = g.keys().cloned().collect();
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

            let divisor: Vec<(PRef, usize)> = match common_gcd {
                Some(g) if !g.is_empty() => g.into_iter().collect(),
                _ => return Some(p),
            };
            let divisor_mono: SoundnessElimTerm = divisor.clone().into();

            let new_terms = p.terms.into_iter().map(|(term, coeff)| {
                match term.clone() / divisor_mono.clone() {
                    Some(quotient) => (quotient, coeff),
                    None => (term, coeff),
                }
            });

            let divided = Poly::<C> {
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
    use super::*;
    use crate::UDags;
    use crate::analyses::{QualifierPropagation, UniformityPropagation};
    use backend::ArkBls12_381;
    use lang::ast::UModule;
    use share::Ctx;
    use share::unwrap;

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
        let mut analysis = SpecialSoundnessAnalysis::from_input(&g, l_vec)?;
        analysis.run()
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
        let mut analysis = SpecialSoundnessAnalysis::from_input(&g, vec![2]).unwrap();
        let result = analysis.run();
        match &result {
            Ok(()) => {}
            Err(e) => panic!("run() failed: {:?}", e),
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
            Err(AnalysisError::NoExtractor(_)) => {}
            other => panic!("expected NoExtractor, got: {:?}", other),
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
        let analysis = SpecialSoundnessAnalysis::from_input(&g, vec![2]).unwrap();

        let witness_names: Set<String> = analysis
            .witness_slots
            .iter()
            .filter_map(|w| w.name().map(|v| v.0.clone()))
            .collect();
        assert!(witness_names.contains(&"x".to_string()));
        assert_eq!(analysis.witness_slots.len(), 1);
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
            Err(AnalysisError::NoExtractor(_)) => {}
            Err(AnalysisError::ExtractorNotVisible { .. }) => {}
            Err(AnalysisError::ExtractorInvalid(_)) => {}
            other => panic!(
                "expected NoExtractor, ExtractorNotVisible, or ExtractorInvalid, got: {:?}",
                other
            ),
        }
    }

    #[test]
    fn chaum_pedersen_special_soundness_l2() {
        assert!(analyze_soundness(CHAUM_PEDERSEN_PROTO, vec![2]).is_ok());
    }

    #[test]
    fn consecutive_challenges_grouped_as_vector() {
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
        let result = analyze_soundness(proto, vec![2]);
        match &result {
            Ok(()) => {}
            Err(e) => panic!("expected Ok, got: {:?}", e),
        }
    }

    #[test]
    fn schnorr_two_challenge_special_soundness() {
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
        assert!(analyze_soundness(proto, vec![2]).is_ok());
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
        let mut analysis = SpecialSoundnessAnalysis::from_input(&g, vec![2]).unwrap();

        assert_eq!(analysis.witness_slots.len(), 1);
        for slot in &analysis.witness_slots {
            assert!(
                slot.typ.is_scalar(),
                "expected scalar slot, got {:?}",
                slot.typ
            );
        }

        assert!(
            analysis.run().is_ok(),
            "Schnorr should be special sound with l=2"
        );
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
        let mut analysis = SpecialSoundnessAnalysis::from_input(&g, vec![2]).unwrap();

        assert_eq!(analysis.witness_slots.len(), 2);
        for slot in &analysis.witness_slots {
            assert!(
                slot.typ.is_scalar(),
                "expected scalar slot, got {:?}",
                slot.typ
            );
        }

        assert!(analysis.run().is_ok());
    }
}
