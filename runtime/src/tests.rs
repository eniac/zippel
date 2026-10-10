#[cfg(test)]
mod runtime_tests {
    use crate::graph::{MutexGraph, ResultKind, RunResult};
    use backend::Value;
    use backend::config::ArkBls12_381;
    use graph::UDags;
    use lang::ast::{CModule, UModule};
    use lang::id::Tid;
    use lang::id::Vid;
    use share::Ctx;
    use std::collections::HashMap;
    use std::sync::Arc;

    type TestConfig = ArkBls12_381;

    #[track_caller]
    fn parse_and_concretize(src: &str, sizes: &Ctx<Tid, usize>) -> CModule {
        let (module, diags) = UModule::parse(src);
        let errors: Vec<_> = diags
            .iter()
            // E0001 (NoProtoDeclaration) is a file-structure rule, not relevant
            // to unit tests using fn-only sources. Suppress by error code.
            .filter(|d| {
                d.severity == lang::diagnostic::Severity::Error
                    && d.code.as_deref() != Some("E0001")
            })
            .collect();
        assert!(
            errors.is_empty(),
            "unexpected errors: {:?}",
            errors.iter().map(|d| &d.summary).collect::<Vec<_>>()
        );
        module.unwrap().concretize(sizes).unwrap()
    }

    #[test]
    fn test_runtime_concurrency_and_evaluation() {
        let src = r#"
            proto test_eval_strong<F: Field>(instance a: F, instance b: F) where 1 == 1 {
                x <- a * a;
                y <- b * b;
                c <- challenge<F>;
                t <- c * (x + y);
                verify(t == c * (x + y))
            }
        "#;
        let m = parse_and_concretize(src, &Ctx::new());
        let gs = UDags::<TestConfig>::from_module(m).unwrap();
        let dag = gs.protocols()[0].clone();

        // Prover graph
        let (prover, _) = dag.get_prover();

        // Verifier graph
        let verifier = dag.get_verifier().unwrap();

        // Prover execution
        let mut inputs = HashMap::new();
        inputs.insert(
            Vid::from("a"),
            Arc::new(Value::Scalar(<TestConfig as backend::ArkConfig>::F::from(
                3u64,
            ))),
        );
        inputs.insert(
            Vid::from("b"),
            Arc::new(Value::Scalar(<TestConfig as backend::ArkConfig>::F::from(
                4u64,
            ))),
        );

        let separator = graph::domain_seperator::ZippelDomainSeparator::new_zippel_domain_seperator(
            "test",
            &dag.clone().erase_ann(),
        );
        let mut prover_state = separator.std_prover();

        let mg_prover = Arc::new(MutexGraph::new(prover));
        let proof =
            match MutexGraph::run_graph(mg_prover, inputs, &mut prover_state, ResultKind::Prover)
                .unwrap()
            {
                RunResult::Prover(v) => v,
                RunResult::Verifier { .. } => unreachable!(),
            };

        // Proof must contain x (9), y (16) and t (c * 25)
        assert_eq!(proof.len(), 3);
        assert_eq!(
            proof[0],
            Value::Scalar(<TestConfig as backend::ArkConfig>::F::from(9u64))
        );
        assert_eq!(
            proof[1],
            Value::Scalar(<TestConfig as backend::ArkConfig>::F::from(16u64))
        );

        // Verifier execution
        let mut verifier_inputs = HashMap::new();
        verifier_inputs.insert(
            Vid::from("a"),
            Arc::new(Value::Scalar(<TestConfig as backend::ArkConfig>::F::from(
                3u64,
            ))),
        );
        verifier_inputs.insert(
            Vid::from("b"),
            Arc::new(Value::Scalar(<TestConfig as backend::ArkConfig>::F::from(
                4u64,
            ))),
        );

        let transcript_args: Vec<lang::id::Vid> = verifier
            .input_args()
            .into_iter()
            .filter_map(|n| match &verifier[n] {
                graph::Node::Arg(name, _, _, _, graph::ArgKind::TranscriptInput) => {
                    Some(name.clone())
                }
                _ => None,
            })
            .collect();

        assert_eq!(transcript_args.len(), proof.len());
        for (name, val) in transcript_args.iter().zip(proof.iter()) {
            verifier_inputs.insert(name.clone(), Arc::new(val.clone()));
        }

        let mut verifier_state = separator.std_prover();
        let mg_verifier = Arc::new(MutexGraph::new(verifier.clone()));
        let verify_results = match MutexGraph::run_graph(
            mg_verifier,
            verifier_inputs,
            &mut verifier_state,
            ResultKind::Verifier,
        )
        .unwrap()
        {
            RunResult::Verifier { verify_results: v } => v,
            RunResult::Prover { .. } => unreachable!(),
        };

        assert_eq!(verify_results.len(), 1);
        assert!(verify_results[0]);
    }

    // A comprehension with an impure body is unrolled, so the vector it
    // builds is one node reading every element. A smoke test of such a wide
    // node end to end; at this size it does not tell a linear operand check
    // in `MutexGraph::new` from a quadratic one.
    #[test]
    fn a_node_reading_thousands_of_operands_runs() {
        let src = r#"
            proto wide<F: Field, N: Size>(instance a: [F; N]) where 1 == 1 {
                let r = [random<F> + a[i] for i in 0..N];
                s <- dot(r, a);
                verify(s == s)
            }
        "#;
        let n = 2048;
        let mut sizes = Ctx::new();
        sizes.insert(&Tid::from("N"), &n);
        let m = parse_and_concretize(src, &sizes);
        let gs = UDags::<TestConfig>::from_module(m).unwrap();
        let dag = gs.protocols()[0].clone();
        let (prover, _) = dag.get_prover();
        let widest = prover
            .node_indices()
            .map(|i| prover[i].references().len())
            .max()
            .unwrap();
        assert!(widest >= n, "expected a node reading all {n} elements");

        let mut inputs = HashMap::new();
        inputs.insert(
            Vid::from("a"),
            Arc::new(Value::vec_scalar(vec![
                <TestConfig as backend::ArkConfig>::F::from(3u64);
                n
            ])),
        );
        let separator = graph::domain_seperator::ZippelDomainSeparator::new_zippel_domain_seperator(
            "test_wide",
            &dag.clone().erase_ann(),
        );
        let mut prover_state = separator.std_prover();
        let mg = Arc::new(MutexGraph::new(prover));
        let proof = match MutexGraph::run_graph(mg, inputs, &mut prover_state, ResultKind::Prover)
            .unwrap()
        {
            RunResult::Prover(v) => v,
            RunResult::Verifier { .. } => unreachable!(),
        };
        assert_eq!(proof.len(), 1);
    }

    #[test]
    fn test_runtime_error_propagation() {
        let src = r#"
            proto test_err<F: Field>(instance a: F, instance b: F) where 1 == 1 {
                verify(b == 999);
                x1 <- a * a;
                x2 <- x1 * x1;
                x3 <- x2 * x2;
                x4 <- x3 * x3;
                verify(x4 == x4)
            }
        "#;
        let m = parse_and_concretize(src, &Ctx::new());
        let gs = UDags::<TestConfig>::from_module(m).unwrap();
        let dag = gs.protocols()[0].clone();
        let (prover, _) = dag.get_prover();

        // Omit 'b' in inputs to cause a MissingArg runtime error on verify(b == 999)
        let mut inputs = HashMap::new();
        inputs.insert(
            Vid::from("a"),
            Arc::new(Value::Scalar(<TestConfig as backend::ArkConfig>::F::from(
                3u64,
            ))),
        );

        let separator = graph::domain_seperator::ZippelDomainSeparator::new_zippel_domain_seperator(
            "test_error",
            &dag.clone().erase_ann(),
        );
        let mut prover_state = separator.std_prover();

        let mg = Arc::new(MutexGraph::new(prover));
        let result = MutexGraph::run_graph(
            mg,
            inputs,
            &mut prover_state,
            crate::graph::ResultKind::Prover,
        );

        assert!(result.is_err());
        assert!(matches!(
            result.unwrap_err(),
            crate::RuntimeError::MissingArg { .. }
        ));
    }
}
