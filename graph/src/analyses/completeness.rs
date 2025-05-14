use backend::ArkConfig;
use crate::{DQDag, Ref, PRef, LexTerm, WritePdf};
use crate::analyses::groebner::{GroebnerBuilder, GroebnerBasis};
use share::Ctx;
use petgraph::graph::NodeIndex;
use lang::id::Vid;


/// Perform a completeness analysis using Groebner bases.
/// This analysis checks if the relation is included in the implementation.
/// The relation is the pre-image of the verifier, and the implementation is the pre-image of the prover.
/// We check if the relation is included in the implementation, which means that the implementation is complete.
/// This is done by checking if the Groebner basis of the relation is included in the Groebner basis of the implementation.
pub struct CompletenessAnalysis<C: ArkConfig> {
    lhs: GroebnerBasis<C::F, PRef, LexTerm>,
    rhs: GroebnerBasis<C::F, PRef, LexTerm>,
}

impl<C: ArkConfig> CompletenessAnalysis<C> {
    pub fn new(dag: &DQDag<C>) -> Self {
        let relation = dag.get_relation().unwrap();
        let (prover, node_map) = dag.get_prover();

        // Prover transcript nodes lost their names, so we need to map them back to the original variables
        let transcript_map: Ctx<NodeIndex, Vid> = 
            dag.transcript_nodes()
            .into_iter()
            .map(|n| (node_map[&n], dag.find_var(n).unwrap())).collect();

        // To show completeness, we need to show
        // R_pre \cup R_prover \subseteq R_impl
        let mut g_prover = GroebnerBuilder::from_input(&prover);
        g_prover.add_relation(&relation);

        let mut g_impl = GroebnerBuilder::from_input(&dag);

        // Compute the Grobner bases
        g_prover.run();
        g_impl.run();

        // Transcript variables are not in the prover graph, so we need to map them back to the original variables
        let prover_basis = g_prover.basis().map_vars(&|pr| 
            if let Some(v) = transcript_map.get(&pr.node()) {
                pr.with_var(v.clone())
            } else {
                pr
            }
        );

        let impl_basis = g_impl.basis();
        println!("Prover:\n{}", prover_basis);
        println!("Impl:\n{}", impl_basis);

        CompletenessAnalysis {
            lhs: prover_basis,
            rhs: impl_basis,
        }
    }

    pub fn run(&self) -> bool {
        if self.lhs.contains(&self.rhs) {
            println!("Complete: R_prover >= R_impl");
            true
        } else {
            println!("Incomplete: The relation is not included in the implementation");
            false
        }
    }
}

#[cfg(test)] use lang::ast::UModule;
#[cfg(test)] use crate::{analyses::{QualifierPropagation, UniformityPropagation}, UDags};
#[cfg(test)] use share::unwrap;
#[cfg(test)] use backend::ArkBls12_381;
#[test]
fn completeness_test() {

    let ex = r#"
        proto ex_complete<F: Field>(private s: F, private s': F) where s == s' {
            let r = random<F*>;
            a <- s * r;
            b <- s' * r;
            verify(a == b);
        }"#;

    println!("Parsing example: {}", ex);
    let m = UModule::from_str(ex).unwrap().concretize().unwrap();
    let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));

    // Propagate qualifiers
    let g = QualifierPropagation::from_dag(&gs[0]);

    // Uniformity propagation
    let mut up = UniformityPropagation::new();
    let g = up.from_dag(&g);
    g.write_pdf("completeness_test").unwrap();

    // Completeness analysis
    let completeness = CompletenessAnalysis::new(&g);
    assert!(completeness.run());

}

