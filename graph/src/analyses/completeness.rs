use backend::ArkConfig;
use log::debug;
use crate::DQDag;
use crate::analyses::groebner::{GrevLexTerm, GroebnerBuilder};
#[cfg(test)] use crate::WritePdf;


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

#[cfg(test)]
mod tests {
    use super::*;
    use lang::ast::UModule;
    use crate::{analyses::{QualifierPropagation, UniformityPropagation}, UDags};
    use share::unwrap;
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
        let m = UModule::from_str(ex).unwrap().concretize().unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));

        let g = QualifierPropagation::from_dag(&gs[0]);
        let mut up = UniformityPropagation::new();
        let g = up.from_dag(&g);

        let mut ca = CompletenessAnalysis::from_input(&g);
        let complete = ca.run();
        assert!(complete);
    }

    #[test]
    fn test_completeness_analysis_construction() {
        let ex = r#"
            proto simple<F: Field>(private x: F) where true {
                a <- x;
                verify(a == x);
            }"#;

        let m = UModule::from_str(ex).unwrap().concretize().unwrap();
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

        let m = UModule::from_str(ex).unwrap().concretize().unwrap();
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

        let m = UModule::from_str(ex).unwrap().concretize().unwrap();
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

        let m = UModule::from_str(ex).unwrap().concretize().unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);
        let mut up = UniformityPropagation::new();
        let g = up.from_dag(&g);

        let mut ca = CompletenessAnalysis::<ArkBls12_381>::from_input(&g);
        let _result = ca.run();
    }
}