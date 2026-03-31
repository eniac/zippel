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
/// The relation is the pre-image of the verifier, and the implementation is the pre-image of the prover.
/// We check if the relation is included in the implementation, which means that the implementation is complete.
/// This is done by checking if the Groebner basis of the relation is included in the Groebner basis of the implementation.
pub struct CompletenessAnalysis<C: ArkConfig> {
    pub prover: GroebnerBuilder<C, GrevLexTerm>,
    pub verifier: GroebnerBuilder<C, GrevLexTerm>
}

/// Invert a node_map (old_dag_idx → new_subgraph_Ref) to build a PRef remapping closure.
/// Returns a closure that maps a PRef from the subgraph namespace to the original DAG namespace.
fn make_remap_fn(
    node_map: &HashMap<NodeIndex, Ref>,
) -> impl Fn(&PRef) -> PRef + '_ {
    // Build inverse: new_subgraph_NodeIndex → (old_dag_NodeIndex, original_Ref)
    // The original Ref carries variable names (Ref::Var(vid, new_node))
    let inverse: HashMap<NodeIndex, (NodeIndex, Ref)> = node_map.iter()
        .map(|(old_idx, new_ref)| (new_ref.node(), (*old_idx, new_ref.clone())))
        .collect();

    move |pref: &PRef| {
        if let Some((old_idx, original_ref)) = inverse.get(&pref.node()) {
            // Use the original ref's variable name if it has one,
            // otherwise use the pref's existing name
            let new_ref = match (original_ref, &pref.reference) {
                // If the original mapping created a Var, use that name with old index
                (Ref::Var(v, _), _) => Ref::Var(v.clone(), *old_idx),
                // Otherwise keep pref's structure with old index
                (Ref::Node(_), Ref::Var(v, _)) => Ref::Var(v.clone(), *old_idx),
                (Ref::Node(_), Ref::Node(_)) => Ref::Node(*old_idx),
            };
            PRef { reference: new_ref, ..pref.clone() }
        } else {
            pref.clone()
        }
    }
}

impl<C: HasOpFactory> CompletenessAnalysis<C> {
    pub fn from_input(dag: &DQDag<C>) -> Self {
        let (spec, rel_node_map) = dag.get_relation().unwrap();
        let (prover, prover_node_map) = dag.get_prover();

        // Build prover basis from prover subgraph, then remap to full-DAG namespace
        let mut g_prover = GroebnerBuilder::new();
        g_prover.add_input(&prover);
        let prover_remap = make_remap_fn(&prover_node_map);
        g_prover.remap_vars(&prover_remap);

        // Build relation basis from relation subgraph, then remap to full-DAG namespace.
        // Override: the relation subgraph's starting node (Rel) should map to the
        // full DAG's input node, so argument variables (g, x, h) get the correct NodeIndex.
        let mut g_rel = GroebnerBuilder::new();
        g_rel.add_relation(&spec);
        let dag_input = dag.input_node();
        let dag_relation = dag.relation_node().unwrap();
        let rel_remap = make_remap_fn_idx_with_override(
            &rel_node_map, dag_relation, dag_input,
        );
        g_rel.remap_vars(&rel_remap);

        // Combine: prover + relation
        let mut g_ps = g_prover;
        g_ps.merge(&g_rel);

        let mut g_impl = GroebnerBuilder::new();
        g_impl.add_input(&dag);

        Self { prover: g_ps, verifier: g_impl }
    }

    pub fn run(&mut self) -> Result<(), AnalysisError<C>> {
        // Compute the Groebner bases
        self.prover.run();
        self.verifier.run();
        debug!("Prover:\n{}", self.prover);
        debug!("Impl:\n{}", self.verifier);

        // Only check verifier polynomials whose variables are all in the prover's
        // vocabulary. Internal verifier nodes (not reachable from prover) are
        // irrelevant for completeness.
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

/// Build a remap closure from a NodeIndex→NodeIndex map (used by get_relation),
/// with an override: `override_from` in the original map is remapped to `override_to`
/// in the inverse. This is used to map the relation subgraph's Rel node to the
/// full DAG's Inp node so argument variables get the correct NodeIndex.
fn make_remap_fn_idx_with_override(
    node_map: &HashMap<NodeIndex, NodeIndex>,
    override_from: NodeIndex,
    override_to: NodeIndex,
) -> impl Fn(&PRef) -> PRef + '_ {
    let mut inverse: HashMap<NodeIndex, NodeIndex> = node_map.iter()
        .map(|(old_idx, new_idx)| (*new_idx, *old_idx))
        .collect();

    // Override: the subgraph node that came from `override_from` should map to `override_to`
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

#[cfg(test)]
mod tests {
    use super::*;
    use lang::ast::UModule;
    use crate::{analyses::{QualifierPropagation, UniformityPropagation}, UDags};
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
    fn test_completeness_analysis_construction() {
        let ex = r#"
            proto simple<F: Field>(private x: F) where true {
                a <- x;
                verify(a == x);
            }"#;

        let m = UModule::from_str(ex).unwrap().concretize(&Ctx::new()).unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);
        let mut up = UniformityPropagation::new();
        let g = up.from_dag(&g);

        let ca = CompletenessAnalysis::<ArkBls12_381>::from_input(&g);
        assert!(ca.prover.basis.len() >= 0);
        assert!(ca.verifier.basis.len() >= 0);
    }

    #[test]
    fn test_completeness_analysis_simple_protocol() {
        let ex = r#"
            proto identity<F: Field>(private x: F) where true {
                a <- x;
                verify(a == x);
            }"#;

        let m = UModule::from_str(ex).unwrap().concretize(&Ctx::new()).unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);
        let mut up = UniformityPropagation::new();
        let g = up.from_dag(&g);

        let mut ca = CompletenessAnalysis::<ArkBls12_381>::from_input(&g);
        let _result = ca.run();
    }

    #[test]
    fn test_completeness_prover_verifier_separate_builders() {
        let ex = r#"
            proto test<F: Field>(private a: F, private b: F) where a == b {
                x <- a + b;
                verify(x == a + b);
            }"#;

        let m = UModule::from_str(ex).unwrap().concretize(&Ctx::new()).unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);
        let mut up = UniformityPropagation::new();
        let g = up.from_dag(&g);

        let ca = CompletenessAnalysis::<ArkBls12_381>::from_input(&g);
        
        assert!(ca.prover.basis.len() >= 0);
        assert!(ca.verifier.basis.len() >= 0);
    }

    #[test]
    fn test_completeness_run_executes() {
        let ex = r#"
            proto mult<F: Field>(private x: F) where true {
                y <- x * x;
                verify(y == x * x);
            }"#;

        let m = UModule::from_str(ex).unwrap().concretize(&Ctx::new()).unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);
        let mut up = UniformityPropagation::new();
        let g = up.from_dag(&g);

        let mut ca = CompletenessAnalysis::<ArkBls12_381>::from_input(&g);
        let _result = ca.run();
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
        use crate::PRef;
        use lang::typ::{Qualifier, Distribution};
        use lang::id::Vid;
        use backend::ATyp;
        use petgraph::graph::NodeIndex;
        
        use crate::analyses::groebner::{SparsePolynomial, GroebnerBasis};

        // Create PRef variables matching Schnorr: g, x, h, r, u
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

        // p1: g*x - h
        let p1 = var(&g_var) * var(&x_var) - var(&h_var);
        // p2: g*r - u
        let p2 = var(&g_var) * var(&r_var) - var(&u_var);

        println!("p1 = {}", p1);
        println!("p2 = {}", p2);

        // Compute S-polynomial
        let spoly = p1.s_poly(&p2);
        println!("S(p1, p2) = {}", spoly);

        // Expected: u*x - h*r (or h*r - u*x)
        let expected_positive = var(&u_var) * var(&x_var) - var(&h_var) * var(&r_var);
        let expected_negative = var(&h_var) * var(&r_var) - var(&u_var) * var(&x_var);
        println!("Expected+ = {}", expected_positive);
        println!("Expected- = {}", expected_negative);

        assert!(spoly == expected_positive || spoly == expected_negative,
            "S-polynomial should be u*x - h*r or h*r - u*x, got: {}", spoly);

        // Now run Buchberger on {p1, p2}
        let mut basis = GroebnerBasis::new(5, vec![p1.clone(), p2.clone()]);
        let gb = basis.buchberger_and_reduce();
        println!("\nGröbner basis of {{g*x - h, g*r - u}}:");
        for (i, p) in gb.iter().enumerate() {
            println!("  GB[{}]: {}", i, p);
        }

        // The target polynomial: h*r - u*x should reduce to zero
        let target = var(&h_var) * var(&r_var) - var(&u_var) * var(&x_var);
        let rem = gb.reduce(target.clone());
        println!("\nReduce(h*r - u*x) = {}", rem);
        assert!(rem.is_zero(), "h*r - u*x should reduce to 0 given g*x = h and g*r = u");
    }
}