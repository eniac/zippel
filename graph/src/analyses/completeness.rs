use std::collections::HashMap;
use backend::ArkConfig;
use backend::op::{HasOpFactory, Ref};

use log::debug;
use petgraph::graph::NodeIndex;
use crate::{DQDag, PRef};
use crate::analyses::groebner::{GrevLexTerm, GroebnerBuilder};
use crate::analyses::error::AnalysisError;


/// Perform a completeness analysis using Groebner bases.
/// This analysis checks if the relation is included in the implementation.
pub struct CompletenessAnalysis<C: ArkConfig> {
    pub prover: GroebnerBuilder<C, GrevLexTerm>,
    pub verifier: GroebnerBuilder<C, GrevLexTerm>
}

/// Invert a node_map (old_dag_idx → new_subgraph_Ref) to build a PRef remapping closure.
fn make_remap_fn(
    node_map: &HashMap<NodeIndex, Ref>,
) -> impl Fn(&PRef) -> PRef + '_ {
    let inverse: HashMap<NodeIndex, (NodeIndex, Ref)> = node_map.iter()
        .map(|(old_idx, new_ref)| (new_ref.node(), (*old_idx, new_ref.clone())))
        .collect();

    move |pref: &PRef| {
        if let Some((old_idx, original_ref)) = inverse.get(&pref.node()) {
            let new_ref = match (original_ref, &pref.reference) {
                (Ref::Var(v, _), _) => Ref::Var(v.clone(), *old_idx),
                (Ref::Node(_), Ref::Var(v, _)) => Ref::Var(v.clone(), *old_idx),
                (Ref::Node(_), Ref::Node(_)) => Ref::Node(*old_idx),
            };
            PRef { reference: new_ref, ..pref.clone() }
        } else {
            pref.clone()
        }
    }
}

/// Build a remap closure from a NodeIndex→NodeIndex map with an override.
#[allow(dead_code)]
fn make_remap_fn_idx_with_override(
    node_map: &HashMap<NodeIndex, NodeIndex>,
    override_from: NodeIndex,
    override_to: NodeIndex,
) -> impl Fn(&PRef) -> PRef + '_ {
    let mut inverse: HashMap<NodeIndex, NodeIndex> = node_map.iter()
        .map(|(old_idx, new_idx)| (*new_idx, *old_idx))
        .collect();

    if let Some(&subgraph_node) = node_map.get(&override_from) {
        inverse.insert(subgraph_node, override_to);
    }

    move |pref: &PRef| {
        if let Some(&old_idx) = inverse.get(&pref.node()) {
            let new_ref = match &pref.reference {
                Ref::Node(_) => Ref::Node(old_idx),
                Ref::Var(v, _) => Ref::Var(v.clone(), old_idx),
            };
            PRef { reference: new_ref, ..pref.clone() }
        } else {
            pref.clone()
        }
    }
}

impl<C: HasOpFactory> CompletenessAnalysis<C> {
    pub fn from_input(dag: &DQDag<C>) -> Self {
        let spec = dag.get_relation().unwrap();
        let (prover, prover_node_map) = dag.get_prover();

        // Build prover basis from prover subgraph, then remap to full-DAG namespace
        let mut g_prover = GroebnerBuilder::new();
        g_prover.add_input(&prover);
        let prover_remap = make_remap_fn(&prover_node_map);
        g_prover.remap_vars(&prover_remap);

        // Build relation basis from relation subgraph, then remap to full-DAG namespace
        let mut g_rel = GroebnerBuilder::new();
        g_rel.add_relation(&spec);

        // Combine: prover + relation
        let mut g_ps = g_prover;
        g_ps.merge(&g_rel);

        let mut g_impl = GroebnerBuilder::new();
        g_impl.add_input(&dag);

        Self { prover: g_ps, verifier: g_impl }
    }

    pub fn run(&mut self) -> Result<(), AnalysisError<C>> {
        self.prover.run();
        self.verifier.run();
        debug!("Prover:\n{}", self.prover);
        debug!("Impl:\n{}", self.verifier);

        // Only check verifier polynomials whose variables are all in the prover's
        // vocabulary. Internal verifier nodes are irrelevant for completeness.
        let prover_vars = self.prover.vars();
        for p in self.verifier.basis.iter() {
            let poly_vars = p.vars();
            if poly_vars.iter().all(|v| prover_vars.contains(v)) {
                let remainder = self.prover.basis.reduce(p.clone());
                if !remainder.is_zero() {
                    return Err(AnalysisError::Incomplete(remainder));
                }
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use lang::ast::UModule;
    use lang::id::Vid;
    use crate::{analyses::{QualifierPropagation, UniformityPropagation}, UDags};
    use crate::analyses::groebner::{SparsePolynomial, GroebnerBasis};
    use share::unwrap;
    use share::Ctx;
    use backend::ArkBls12_381;

    #[test]
    #[ignore]
    fn completeness_test() {
        let ex = r#"
            proto ex_complete<F: Field>(private s: F, private s': F) where s == s' {
                let r = random<F*>;
                a <- s * r;
                b <- s' * r;
                verify(a == b);
            }"#;

        debug!("Parsing example: {}", ex);
        let m = UModule::from_str(ex).unwrap().concretize(&Ctx::new()).unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));

        let g = QualifierPropagation::from_dag(&gs[0]);
        let mut up = UniformityPropagation::new();
        let g = up.from_dag(&g);

        let mut ca = CompletenessAnalysis::from_input(&g);
        assert!(ca.run().is_ok());
    }

    #[test]
    fn schnorr_completeness() {
        let ex = r#"
            proto schnorr<G: Group, F: Scalar<G>>(private x: F, public g: G, public h: G) where h == g*x {
                let r = random<F>;
                u <- g*r;
                c <- challenge<F>;
                z <- r + x*c;
                verify(g*z == u + h*c);
            }"#;

        let m = UModule::from_str(ex).unwrap().concretize(&Ctx::new()).unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);
        let mut up = UniformityPropagation::new();
        let g = up.from_dag(&g);

        let mut ca = CompletenessAnalysis::from_input(&g);
        assert!(ca.run().is_ok(), "Schnorr protocol should be complete");
    }

    #[test]
    fn test_buchberger_spoly_produces_ux_hr() {
        use lang::typ::{Qualifier, Distribution};
        use backend::ATyp;

        let mk_var = |name: &str, idx: usize| -> PRef {
            PRef::from_var(Vid(name.to_string()), NodeIndex::new(idx), ATyp::scalar(), 0, Qualifier::Public, Distribution::default())
        };
        let g_var = mk_var("g", 0);
        let x_var = mk_var("x", 1);
        let h_var = mk_var("h", 2);
        let r_var = mk_var("r", 3);
        let u_var = mk_var("u", 4);

        type Poly = SparsePolynomial<<ArkBls12_381 as backend::ArkConfig>::F, GrevLexTerm>;
        let var = |p: &PRef| -> Poly { SparsePolynomial::var(p) };

        let p1 = var(&g_var) * var(&x_var) - var(&h_var);
        let p2 = var(&g_var) * var(&r_var) - var(&u_var);

        let spoly = p1.s_poly(&p2);
        let expected_positive = var(&u_var) * var(&x_var) - var(&h_var) * var(&r_var);
        let expected_negative = var(&h_var) * var(&r_var) - var(&u_var) * var(&x_var);
        assert!(spoly == expected_positive || spoly == expected_negative);

        let basis = GroebnerBasis::new(5, vec![p1, p2]);
        let gb = basis.buchberger_and_reduce();

        let target = var(&h_var) * var(&r_var) - var(&u_var) * var(&x_var);
        let rem = gb.reduce(target);
        assert!(rem.is_zero(), "h*r - u*x should reduce to 0 given g*x = h and g*r = u");
    }
}
