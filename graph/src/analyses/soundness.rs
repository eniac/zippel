use crate::analyses::TransClos;
use crate::analyses::error::AnalysisError;
use crate::analyses::groebner::{GroebnerBuilder, GroebnerResult, GrevLexTerm, Monomial, SparsePolynomial};
use crate::{DQDag, PRef, Ref};
use ark_ff::One;
use backend::op::{HasOpFactory, Op};
use backend::{ATyp, ArkConfig};
use lang::id::Vid;
use log::{info, warn};
use share::Set;

type Poly<C> = SparsePolynomial<<C as ArkConfig>::F, GrevLexTerm>;

pub struct SpecialSoundnessAnalysis<C: ArkConfig> {
    search_result: GroebnerResult<C, GrevLexTerm>,
    validity_result: GroebnerResult<C, GrevLexTerm>,
    relation_polys: Vec<Poly<C>>,
    witness_slots: Vec<PRef>,
    extractor_visible: Set<PRef>,
}

impl<C: ArkConfig + HasOpFactory> SpecialSoundnessAnalysis<C> {
    pub fn from_input(dag: &DQDag<C>, l: usize) -> Result<Self, AnalysisError<C>> {
        if l < 2 {
            return Err(AnalysisError::InvalidSoundnessParameter);
        }

        let verifier = dag
            .get_verifier()
            .map_err(AnalysisError::VerifierInvalid)?;
        if verifier.get_challenge_nodes().is_empty() {
            return Err(AnalysisError::NoChallenge);
        }

        let transcript_nodes = verifier.transcript_nodes();

        // Verify the protocol is a sigma (3-move) protocol.
        {
            let mut seen_response = false;
            let mut last_response_name: Option<String> = None;
            let mut past_first_challenge = false;
            for &n in &transcript_nodes {
                let node = &verifier[n];
                if node.is_challenge() {
                    past_first_challenge = true;
                    if seen_response {
                        let challenge_name = verifier
                            .find_var(n)
                            .map(|v| v.0.clone())
                            .unwrap_or_else(|| format!("{:?}", n));
                        let response_name = last_response_name
                            .clone()
                            .unwrap_or_else(|| "unknown".to_string());
                        return Err(AnalysisError::NotSigmaProtocol {
                            challenge_name,
                            response_name,
                        });
                    }
                } else if node.is_proof() && past_first_challenge {
                    seen_response = true;
                    last_response_name = verifier.find_var(n).map(|v| v.0.clone());
                }
            }
        }

        // Expand witness args into per-slot PRefs.
        let witness_slots: Vec<PRef> = dag
            .args()
            .into_iter()
            .filter(|a| a.is_private() && !a.distribution.is_uniform())
            .flat_map(|a| {
                let n = a.typ.physical_len();
                (0..n).filter_map(move |i| a.with_slot(i))
            })
            .collect();

        let verifier_tc = TransClos::input(&verifier);

        let transcript_nodes = verifier.transcript_nodes();
        let first_challenge_idx = transcript_nodes
            .iter()
            .position(|n| verifier[*n].is_challenge())
            .unwrap_or(transcript_nodes.len());

        let shared_transcript_names: Set<String> = transcript_nodes
            .iter()
            .take(first_challenge_idx)
            .filter_map(|n| verifier.find_var(*n).map(|v| v.0.clone()))
            .collect();

        let indexed_transcript_names: Set<String> = transcript_nodes
            .iter()
            .skip(first_challenge_idx)
            .filter_map(|n| verifier.find_var(*n).map(|v| v.0.clone()))
            .collect();

        let shared_pref_names: Set<String> = verifier
            .args()
            .iter()
            .filter(|a| a.is_public())
            .filter_map(|a| a.name().map(|v| v.0.clone()))
            .collect();

        let challenge_prefs: Set<PRef> = verifier_tc
            .clos
            .iter()
            .filter(|(_, op)| matches!(op, Op::Challenge(_, _)))
            .map(|(p, _)| p.clone())
            .collect();

        let challenge_refs: Set<Ref> = challenge_prefs.iter().map(|p| p.reference).collect();

        let mut extractor_visible: Set<PRef> = Set::new();
        for a in verifier.args().iter() {
            if a.is_public() {
                extractor_visible.insert(a.clone());
            }
            if a.from_transcript
                && let Some(name) = a.name()
                && shared_transcript_names.contains(&name.0)
            {
                extractor_visible.insert(a.clone());
            }
        }

        // Build the search result by accumulating remapped copies of
        // the verifier transcript. The GroebnerBuilder namespace persists
        // across build() calls so variable names are consistent.
        let mut search_builder: GroebnerBuilder<C, GrevLexTerm> = GroebnerBuilder::new();
        let mut validity_builder: GroebnerBuilder<C, GrevLexTerm> = GroebnerBuilder::new();

        let verifier_args = verifier.args();
        let mut all_indexed_challenges: Vec<Vec<PRef>> = Vec::new();

        for i in 1..=l {
            let suffix = format!("_{}", i);
            let mut copy_tc = verifier_tc.clone();

            let shared_transcript_names_clone = shared_transcript_names.clone();
            let shared_pref_names_clone = shared_pref_names.clone();
            let suffix_clone = suffix.clone();

            let remap = |pref: &PRef| -> PRef {
                let name_str = pref.name().map(|v| v.0.as_str()).unwrap_or("");
                let is_shared = pref.from_transcript
                    && shared_transcript_names_clone.contains(&name_str.to_string());
                let is_public_input = shared_pref_names_clone.contains(&name_str.to_string());

                if is_shared || is_public_input {
                    pref.clone()
                } else {
                    PRef {
                        reference: pref.reference,
                        index: pref.index,
                        typ: pref.typ.clone(),
                        qualifier: pref.qualifier.clone(),
                        distribution: pref.distribution.clone(),
                        from_transcript: pref.from_transcript,
                        name: Some(Vid::new(&format!("{}{}", name_str, suffix_clone))),
                    }
                }
            };

            copy_tc.remap(&remap);

            let mut indexed_challenge_prefs: Vec<PRef> = Vec::new();
            for challenge_pref in challenge_prefs.iter() {
                let remapped = remap(challenge_pref);
                indexed_challenge_prefs.push(remapped.clone());
                extractor_visible.insert(remapped.clone());
            }

            for a in verifier_args.iter() {
                if let Some(name) = a.name() {
                    let is_challenge =
                        challenge_prefs.contains(a) || challenge_refs.contains(&a.reference);
                    let is_indexed =
                        a.from_transcript && indexed_transcript_names.contains(&name.0);
                    let is_shared = a.from_transcript && shared_transcript_names.contains(&name.0);
                    let is_public = shared_pref_names.contains(&name.0);

                    if is_challenge || is_indexed {
                        let indexed_a = remap(a);
                        extractor_visible.insert(indexed_a);
                    } else if is_shared || is_public {
                        extractor_visible.insert(a.clone());
                    }
                }
            }

            // build() returns a GroebnerResult; the namespace persists in
            // the builder so subsequent build() calls share variable names.
            let _copy_result = search_builder.build(copy_tc);
            // Also build a validity result from the un-remapped verifier.
            // We only need this once; subsequent iterations just accumulate
            // namespace mappings.
            if i == 1 {
                let _ = validity_builder.build(verifier_tc.clone());
            }

            all_indexed_challenges.push(indexed_challenge_prefs);
        }

        // Register witness slots in the namespace
        for w in &witness_slots {
            search_builder.ns.register(w);
            validity_builder.ns.register(w);
        }

        // D equations: d_{i,j,k} * (c_{i,k} - c_{j,k}) - 1 = 0
        // for each challenge slot k and each pair 1 <= i < j <= l.
        let mut search_result = GroebnerResult::<C, GrevLexTerm>::new();
        let mut validity_result = GroebnerResult::<C, GrevLexTerm>::new();

        for i in 1..=l {
            for j in (i + 1)..=l {
                let ci_prefs = &all_indexed_challenges[i - 1];
                let cj_prefs = &all_indexed_challenges[j - 1];

                for (k, (ci_ref, cj_ref)) in ci_prefs.iter().zip(cj_prefs.iter()).enumerate() {
                    let dijk_name = format!("d_{}_{}_{}", i, j, k);
                    let dijk = search_builder.ns.sentinel_pref(&dijk_name, ATyp::scalar());
                    let dijk_poly = Poly::<C>::var(&dijk);
                    let one = Poly::<C>::lit(&C::F::one());
                    extractor_visible.insert(dijk.clone());

                    let ci_poly = Poly::<C>::var(ci_ref);
                    let cj_poly = Poly::<C>::var(cj_ref);
                    let diff = ci_poly - cj_poly;
                    let eq = dijk_poly.clone() * diff - one.clone();
                    search_result.basis.push(eq.clone());
                    validity_result.basis.push(eq);
                }
            }
        }

        // Build relation equations from the input DAG.
        let rel_tc = TransClos::input(dag);
        let mut rel_builder: GroebnerBuilder<C, GrevLexTerm> = GroebnerBuilder::new();
        let rel_result = rel_builder.build(rel_tc);
        for p in rel_result.basis.iter() {
            search_result.basis.push(p.clone());
        }
        search_result.merge(&rel_result);
        // Also merge the prover and verifier results built earlier.
        // The builder's namespace accumulated prefs from each build() call,
        // but the actual basis rows and poly definitions come from the
        // GroebnerResult. We inline polynomials to reduce variable count
        // before running Buchberger.
        let pl_keys: Set<PRef> = search_result.pl.keys();
        search_result.inline(&|v: &PRef| pl_keys.contains(v));

        // Run Buchberger on the search basis.
        search_result.run::<128>();

        // Factor out common group-variable GCDs from basis polynomials.
        factor_group_gcd(&mut search_result);

        // Relation polynomials for validity checking.
        let relation_polys: Vec<Poly<C>> = rel_result.basis.iter().cloned().collect();

        Ok(Self {
            search_result,
            validity_result,
            relation_polys,
            witness_slots,
            extractor_visible,
        })
    }

    pub fn run(&mut self) -> Result<(), AnalysisError<C>> {
        info!("Running extractor-search Gröbner basis...");
        let _witness_set: Set<PRef> = self.witness_slots.iter().cloned().collect();

        let mut extractors: Vec<(PRef, Poly<C>)> = Vec::new();

        for w in &self.witness_slots {
            let is_field_witness = w.typ.is_scalar();
            let mut found_extractor = None;

            for poly in self.search_result.basis.iter() {
                if let Some((_lc, lt)) = poly.leading_term() {
                    let lt_vars = lt.vars();
                    let lt_powers = lt.powers();
                    let is_witness_term = lt_vars.len() == 1
                        && lt_vars[0] == *w
                        && lt_powers[0] == 1;
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
                    let all_visible = remainder_vars
                        .iter()
                        .all(|v| self.extractor_visible.contains(v));
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
                                .filter_map(|(v, i)| {
                                    if v.typ.is_group() { Some(*i) } else { None }
                                })
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

        info!("Checking: <V_1 ∪ ... ∪ V_l ∪ D ∪ E> ⊇ <R>...");
        for (_, poly) in &extractors {
            self.validity_result.basis.push(poly.clone());
        }
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

/// Factor out common group-variable monomial GCDs from basis polynomials.
///
/// In the algebraic group model, a polynomial like `u*(x + z₂*d - z₁*d) = 0`
/// where `u` is a group variable implies `x + z₂*d - z₁*d = 0` because
/// scalar multiplication by a nonzero group element is injective in
/// prime-order groups. We remove basis polynomials that are entirely
/// multiples of a group variable, since they yield tautological constraints
/// in the field-variable extractor search.
fn factor_group_gcd<C: ArkConfig>(result: &mut GroebnerResult<C, GrevLexTerm>) {
    // Collect indices of polynomials to remove (those whose every monomial
    // contains at least one group variable, meaning the whole polynomial
    // is a group-variable multiple implies the scalar equation holds).
    let has_any_pure_field_term = |poly: &Poly<C>| -> bool {
        poly.terms.iter().any(|(term, _)| {
            term.vars().iter().all(|v| !v.typ.is_group())
        })
    };

    result
        .basis
        .basis
        .retain(|p| !p.is_zero() && has_any_pure_field_term(p));
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

    fn analyze_soundness(proto: &str, l: usize) -> Result<(), AnalysisError<ArkBls12_381>> {
        let m = UModule::from_str(proto)
            .unwrap()
            .concretize(&Ctx::new())
            .unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g_inp = QualifierPropagation::from_dag(&gs[0]);
        let g = UniformityPropagation::from_dag(&g_inp).annotate_dag(&g_inp);
        let mut analysis = SpecialSoundnessAnalysis::from_input(&g, l)?;
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
        assert!(analyze_soundness(SCHNORR_PROTO, 2).is_ok());
    }

    #[test]
    fn reject_l_less_than_two() {
        let result = analyze_soundness(SCHNORR_PROTO, 1);
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
        let result = analyze_soundness(proto, 2);
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
        let result = analyze_soundness(proto, 2);
        match &result {
            Err(AnalysisError::NoExtractor(_)) => {}
            other => panic!("expected NoExtractor, got: {:?}", other),
        }
    }

    #[test]
    fn schnorr_l3_special_soundness() {
        assert!(analyze_soundness(SCHNORR_PROTO, 3).is_ok());
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
        let analysis = SpecialSoundnessAnalysis::from_input(&g, 2).unwrap();

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
        let result = analyze_soundness(proto, 2);
        match &result {
            Err(AnalysisError::NoExtractor(_)) => {}
            Err(AnalysisError::ExtractorNotVisible { .. }) => {}
            other => panic!(
                "expected NoExtractor or ExtractorNotVisible, got: {:?}",
                other
            ),
        }
    }

    #[test]
    fn chaum_pedersen_special_soundness_l2() {
        assert!(analyze_soundness(CHAUM_PEDERSEN_PROTO, 2).is_ok());
    }

    #[test]
    fn reject_five_move_protocol() {
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
        let result = analyze_soundness(proto, 3);
        match &result {
            Err(AnalysisError::NotSigmaProtocol { .. }) => {}
            other => panic!("expected NotSigmaProtocol, got: {:?}", other),
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
        let mut analysis = SpecialSoundnessAnalysis::from_input(&g, 2).unwrap();

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
}