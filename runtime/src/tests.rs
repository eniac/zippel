#[cfg(test)]
mod runtime_tests {
    use crate::graph::{MutexGraph, RuntimeInformation};
    use crate::queue::sync_channel;
    use backend::Value;
    use backend::config::ArkBls12_381;
    use graph::UDags;
    use graph::scheduler::local_scheduler::LocalScheduler;
    use graph::scheduler::{AsymptoticCost, Scheduler};
    use lang::ast::UModule;
    use share::Ctx;
    use std::sync::Arc;
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::thread;

    type TestConfig = ArkBls12_381;

    #[test]
    fn test_runtime_information_creation() {
        // Just test that we can create RuntimeInformation
        let _rt_info = RuntimeInformation::<TestConfig>::new();
    }

    #[test]
    fn test_runtime_concurrency_and_evaluation() {
        let src = r#"
            proto test_eval_strong<F: Field>(public a: F, public b: F) where true {
                x <- a * a;
                y <- b * b;
                c <- challenge<F>;
                t <- c * (x + y);
                verify(t == c * (x + y))
            }
        "#;
        let m = UModule::from_str(src)
            .unwrap()
            .concretize(&Ctx::new())
            .unwrap();
        let gs = UDags::<TestConfig>::from_module(m).unwrap();
        let dag = gs.protocols()[0].clone().rename_inner_nodes();

        // Prover graph
        let (prover, _) = dag.get_prover();
        let scheduler_p = LocalScheduler::new_with_system(&prover, &AsymptoticCost::new(), 30.0);
        let prover_scheduled = scheduler_p.schedule(prover);

        // Verifier graph
        let verifier = dag.get_verifier().unwrap();
        let scheduler_v = LocalScheduler::new_with_system(&verifier, &AsymptoticCost::new(), 30.0);
        let verifier_scheduled = scheduler_v.schedule(verifier.clone());

        // Prover execution
        let mut inputs = Ctx::new();
        inputs.insert(
            &lang::id::Vid::from("a"),
            &Value::Scalar(<TestConfig as backend::ArkConfig>::F::from(3u64)),
        );
        inputs.insert(
            &lang::id::Vid::from("b"),
            &Value::Scalar(<TestConfig as backend::ArkConfig>::F::from(4u64)),
        );

        let separator = graph::domain_seperator::ZippelDomainSeparator::new_zippel_domain_seperator(
            "test",
            &dag.clone().erase_ann(),
        );
        let mut prover_state = separator.std_prover();

        let mg_prover = Arc::new(MutexGraph::new(prover_scheduled));
        let proof = MutexGraph::run_graph(
            mg_prover,
            Arc::new(inputs),
            &mut prover_state,
            crate::graph::ResultKind::Prover,
        )
        .unwrap();

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
        let mut verifier_inputs = Ctx::new();
        verifier_inputs.insert(
            &lang::id::Vid::from("a"),
            &Value::Scalar(<TestConfig as backend::ArkConfig>::F::from(3u64)),
        );
        verifier_inputs.insert(
            &lang::id::Vid::from("b"),
            &Value::Scalar(<TestConfig as backend::ArkConfig>::F::from(4u64)),
        );

        let verifier_args = verifier.args();
        let transcript_args: Vec<graph::PRef> = verifier_args
            .into_iter()
            .filter(|arg| arg.from_transcript)
            .collect();

        assert_eq!(transcript_args.len(), proof.len());
        for (arg, val) in transcript_args.iter().zip(proof.iter()) {
            let name = arg.name().unwrap();
            verifier_inputs.insert(name, val);
        }

        let mut verifier_state = separator.std_prover();
        let mg_verifier = Arc::new(MutexGraph::new(verifier_scheduled));
        let verify_results = MutexGraph::run_graph(
            mg_verifier,
            Arc::new(verifier_inputs),
            &mut verifier_state,
            crate::graph::ResultKind::Verifier,
        )
        .unwrap();

        assert_eq!(verify_results.len(), 1);
        assert_eq!(verify_results[0], Value::Bool(true));
    }

    #[test]
    fn test_runtime_error_propagation() {
        let src = r#"
            proto test_err<F: Field>(public a: F, public b: F) where true {
                verify(b == 999);
                x1 <- a * a;
                x2 <- x1 * x1;
                x3 <- x2 * x2;
                x4 <- x3 * x3;
                verify(x4 == x4)
            }
        "#;
        let m = UModule::from_str(src)
            .unwrap()
            .concretize(&Ctx::new())
            .unwrap();
        let gs = UDags::<TestConfig>::from_module(m).unwrap();
        let dag = gs.protocols()[0].clone().rename_inner_nodes();
        let (prover, _) = dag.get_prover();

        let scheduler = LocalScheduler::new_with_system(&prover, &AsymptoticCost::new(), 30.0);
        let scheduled = scheduler.schedule(prover);

        // Omit 'b' in inputs to cause a MissingArg runtime error on verify(b == 999)
        let mut inputs = Ctx::new();
        inputs.insert(
            &lang::id::Vid::from("a"),
            &Value::Scalar(<TestConfig as backend::ArkConfig>::F::from(3u64)),
        );

        let separator = graph::domain_seperator::ZippelDomainSeparator::new_zippel_domain_seperator(
            "test_error",
            &dag.clone().erase_ann(),
        );
        let mut prover_state = separator.std_prover();

        let mg = Arc::new(MutexGraph::new(scheduled));
        let result = MutexGraph::run_graph(
            mg,
            Arc::new(inputs),
            &mut prover_state,
            crate::graph::ResultKind::Prover,
        );

        assert!(result.is_err());
        assert!(matches!(
            result.unwrap_err(),
            crate::RuntimeError::MissingArg { .. }
        ));
    }

    #[test]
    fn test_sync_queue_concurrency() {
        use std::sync::Barrier;

        let num_workers: usize = 30;
        let (tx, rx) = sync_channel(1);
        let processed_count = Arc::new(AtomicUsize::new(0));
        let mut handles = vec![];

        let barrier = Arc::new(Barrier::new(num_workers + 1));

        for i in 0..num_workers {
            let tx_clone = tx.clone();
            let barrier_clone = Arc::clone(&barrier);
            let handle = thread::spawn(move || {
                barrier_clone.wait();
                tx_clone.push(petgraph::graph::node_index(i));
            });
            handles.push(handle);
        }

        drop(tx);

        let processed_clone = Arc::clone(&processed_count);
        let main_handle = thread::spawn(move || {
            let mut count = 0;
            while let Some(msg) = rx.pop() {
                count += 1;
                thread::sleep(std::time::Duration::from_millis(1));
                drop(msg);
            }
            processed_clone.store(count, Ordering::SeqCst);
        });

        barrier.wait();

        for h in handles {
            h.join().unwrap();
        }
        main_handle.join().unwrap();

        assert_eq!(processed_count.load(Ordering::SeqCst), num_workers);
    }
}
