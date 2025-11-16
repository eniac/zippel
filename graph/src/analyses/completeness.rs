use backend::ArkConfig;
use log::debug;
use crate::{DQDag, Ref, PRef, WritePdf};
use crate::analyses::groebner::{GrevLexTerm, GroebnerBasis, GroebnerBuilder};
use share::Ctx;
use petgraph::graph::NodeIndex;
use lang::id::Vid;


/// Perform a completeness analysis using Groebner bases.
/// This analysis checks if the relation is included in the implementation.
/// The relation is the pre-image of the verifier, and the implementation is the pre-image of the prover.
/// We check if the relation is included in the implementation, which means that the implementation is complete.
/// This is done by checking if the Groebner basis of the relation is included in the Groebner basis of the implementation.
pub struct CompletenessAnalysis<C: ArkConfig> {
    pub prover: GroebnerBuilder<C, GrevLexTerm>,
    pub verifier: GroebnerBuilder<C, GrevLexTerm>
}

impl<C: ArkConfig> CompletenessAnalysis<C> {
    pub fn from_input(dag: &DQDag<C>) -> Self {
        let spec = dag.get_relation().unwrap();
        let (prover, _node_map) = dag.get_prover();

        // To show completeness, we need to show
        // R_pre \cup R_prover \subseteq R_impl
        let mut g_ps= GroebnerBuilder::new();
        g_ps.add_input(&prover);
        g_ps.add_relation(&spec);

        let mut g_impl = GroebnerBuilder::new();
        g_impl.add_input(&dag);

        Self { prover: g_ps, verifier: g_impl }
    }

    pub fn run(&mut self) -> bool {
        // Compute the Groebner bases
        self.prover.run();
        self.verifier.run();
        debug!("Prover:\n{}", self.prover);
        debug!("Impl:\n{}", self.verifier);

        self.prover.basis.contains(&self.verifier.basis)
    }
}

#[cfg(test)] use lang::ast::UModule;
#[cfg(test)] use crate::{analyses::{QualifierPropagation, UniformityPropagation}, UDags};
#[cfg(test)] use share::unwrap;
#[cfg(test)] use backend::ArkBls12_381;
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
    let mut ca = CompletenessAnalysis::from_input(&g);
    let complete = ca.run();
    assert!(complete);

}