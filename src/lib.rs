use analyses::{
    CompletenessAnalysis, DEFAULT_GB_W, KnowledgeAnalysis, QualifierPropagation,
    UniformityPropagation,
};
use backend::op::HasOpFactory;
use backend::{ArkConfig, Value, value_to_bytes};
use graph::Dag;
use graph::WritePdf;
use graph::domain_seperator::ZippelDomainSeparator;
use graph::{UDag, UDags};
use lang::ast::{CModule, UModule};
use lang::id::{Tid, Vid};
use lang::typ::range::Range;
use lang::typ::{Distribution, Kind, Qualifier, Size};
use log::{debug, error, info};
use runtime::RuntimeError;
use runtime::graph::ResultKind;
use share::{Ctx, unwrap};
use std::fs;
use std::path::PathBuf;
use std::process;

use graph::PRef;
use runtime::MutexGraph;
use share::traversal::ToTraversal1;
use std::sync::Arc;

/// Arguments for the Zippel handler
#[derive(Debug, Clone)]
pub struct ZippelArgs {
    /// The path to the zippel file to read
    pub file_path: PathBuf,

    /// Stable Fiat-Shamir transcript session identity.
    ///
    /// When unset, existing callers keep the historical behavior: the source
    /// file path display string is used as the domain session.
    pub domain_separator_session: Option<String>,

    /// Optional path for the pdf file
    /// If not provided, defaults to <INPUT_FILE>.pdf
    pub pdf_path_opt: Option<PathBuf>,

    /// An optional subgraph name to analyze
    pub subgraph: Option<String>,
}

impl ZippelArgs {
    pub fn new(file_path: PathBuf) -> Self {
        ZippelArgs {
            file_path,
            domain_separator_session: None,
            pdf_path_opt: None,
            subgraph: None,
        }
    }

    pub fn new_with_domain_session(
        file_path: PathBuf,
        domain_separator_session: impl Into<String>,
    ) -> Self {
        Self::new(file_path).with_domain_session(domain_separator_session)
    }

    pub fn with_domain_session(mut self, domain_separator_session: impl Into<String>) -> Self {
        self.domain_separator_session = Some(domain_separator_session.into());
        self
    }

    pub fn domain_separator_session(&self) -> String {
        self.domain_separator_session
            .clone()
            .unwrap_or_else(|| self.file_path.display().to_string())
    }

    pub fn with_pdf(mut self, pdf_path: PathBuf) -> Self {
        self.pdf_path_opt = Some(pdf_path);
        self
    }

    pub fn with_subgraph(mut self, subgraph: String) -> Self {
        self.subgraph = Some(subgraph);
        self
    }
}

pub struct ZippelHandler<C: ArkConfig> {
    args: ZippelArgs,
    sized_module: Option<UModule>,
    concrete_module: Option<CModule>,
    pub prover_graph: Option<UDag<C>>,
    pub verifier_graph: Option<UDag<C>>,
    public_inputs: Option<Ctx<Vid, Value<C>>>,
    prover_args: Option<Vec<PRef>>,
    analyze_graph: Option<Dag<C, (Qualifier, Distribution)>>,
}

impl<C: ArkConfig + HasOpFactory> ZippelHandler<C> {
    pub fn new(args: ZippelArgs) -> Self {
        // Enable detailed error messages from pest parser
        // This provides more comprehensive error messages for debugging parser errors
        lang::init_parser();

        ZippelHandler {
            args,
            sized_module: None,
            concrete_module: None,
            prover_graph: None,
            verifier_graph: None,
            public_inputs: None,
            prover_args: None,
            analyze_graph: None,
        }
    }

    pub fn args(&self) -> &ZippelArgs {
        &self.args
    }

    pub fn prover_graph(&self) -> &UDag<C> {
        self.prover_graph
            .as_ref()
            .expect("prover_graph not set; call compile() first")
    }

    pub fn verifier_graph(&self) -> &UDag<C> {
        self.verifier_graph
            .as_ref()
            .expect("verifier_graph not set; call compile() first")
    }

    /// Lazily build and return the `DQDag` used by the `analyze_*` methods.
    ///
    /// Rebuilds the `UDags` from the cached `concrete_module` (no extra
    /// parse / concretize cost the first time the analysis graph is
    /// requested after `compile`), runs `QualifierPropagation` +
    /// `UniformityPropagation`, and caches the result. Subsequent calls
    /// return a `&mut` into the cache.
    ///
    /// The `DQDag` returned here is a fresh construction each time the
    /// cache is empty; once populated, it lives for the rest of the
    /// handler's lifetime. Tests that need to mutate it between `compile`
    /// and `analyze_*` (e.g. `tests/completeness_examples.rs::strip_relation`)
    /// use this method's `&mut` return to operate directly on the cached DAG.
    pub fn analyze_graph(&mut self) -> &mut Dag<C, (Qualifier, Distribution)> {
        if self.analyze_graph.is_none() {
            self.analyze_graph = Some(self.build_analyze_graph());
        }
        self.analyze_graph
            .as_mut()
            .expect("analyze_graph cache populated above")
    }

    fn build_analyze_graph(&self) -> Dag<C, (Qualifier, Distribution)> {
        let gs = unwrap!(UDags::<C>::from_module(
            self.concrete_module
                .as_ref()
                .expect("compile() must be called before analyze_*()")
                .clone()
        ));
        let g_analyze = QualifierPropagation::from_dag(self.get_protocol_subgraph(&gs));
        UniformityPropagation::from_dag(&g_analyze).annotate_dag(&g_analyze)
    }

    fn get_protocol_subgraph<'a>(&self, gs: &'a UDags<C>) -> &'a UDag<C> {
        if let Some(main_proto) = &self.args.subgraph {
            debug!("Getting protocol: {}", main_proto);
            gs.get_proto(main_proto).unwrap_or_else(|| {
                panic!(
                    "Protocol {} not found in {}",
                    main_proto,
                    self.args.file_path.display()
                )
            })
        } else {
            gs.protocols().first().unwrap_or_else(|| {
                panic!("No protocols found in {}", self.args.file_path.display())
            })
        }
    }

    pub fn parse(&mut self) {
        debug!("Parsing file: {}", self.args.file_path.display());
        let zfile = fs::read_to_string(&self.args.file_path).unwrap_or_else(|err| {
            error!(
                "Error reading file {}: \n\t{}",
                self.args.file_path.display(),
                err
            );
            process::exit(1);
        });
        self.sized_module = Some(UModule::from_str(&zfile).unwrap());
    }

    /// Will output a PDF if a path is provided, noop otherwise
    pub fn output_pdf<D: WritePdf>(&self, g: &D, msg: &str) {
        if let Some(pdf_path) = &self.args.pdf_path_opt {
            let os_str = pdf_path.clone().into_os_string();
            let mut str_path = os_str.into_string().unwrap();
            if str_path.ends_with(".pdf") {
                str_path = str_path.strip_suffix(".pdf").unwrap().to_string();
            }
            str_path = str_path + "_" + msg + ".pdf";
            debug!("Writing {} PDF to {}", msg, str_path);
            g.write_pdf(str_path.as_str()).unwrap_or_else(|e| {
                error!(
                    "Error writing to PDF, maybe [dot] is not installed? \n\n {}",
                    e
                );
                process::exit(2);
            })
        }
    }
    /// Parse, concretize, build the protocol DAG, and project prover/verifier
    /// graphs. Does not run static-analysis passes; call `analyze_*` methods
    /// to invoke completeness/knowledge/soundness analyses on demand.
    pub fn compile(&mut self, sizes: &Ctx<Tid, usize>) {
        let stack_size = std::env::var("ZIPPEL_COMPILE_STACK_SIZE")
            .ok()
            .and_then(|value| value.parse::<usize>().ok())
            .unwrap_or(64 * 1024 * 1024);

        std::thread::scope(|scope| {
            let handle = std::thread::Builder::new()
                .name("zippel-compile".to_string())
                .stack_size(stack_size)
                .spawn_scoped(scope, || self.compile_inner(sizes))
                .expect("failed to spawn zippel compiler thread");
            if let Err(payload) = handle.join() {
                std::panic::resume_unwind(payload);
            }
        });
    }

    fn compile_inner(&mut self, sizes: &Ctx<Tid, usize>) {
        self.parse();

        debug!("Concretizing module type variables");
        self.concrete_module = Some(
            self.sized_module
                .as_ref()
                .unwrap()
                .concretize(sizes)
                .unwrap(),
        );

        debug!("Creating graphs from module");
        let gs = unwrap!(UDags::<C>::from_module(
            self.concrete_module.as_ref().unwrap().clone()
        ));
        self.output_pdf(&gs, "symbolic_protocol_graph");

        // Extract protocol subgraph and rename inner nodes
        let g = self.get_protocol_subgraph(&gs).clone().rename_inner_nodes();
        self.output_pdf(&g, "concrete_protocol_graph");

        debug!("Projecting prover");
        let (prover, _) = g.clone().get_prover();
        self.prover_graph = Some(prover.clone());
        self.output_pdf(&prover, "prover_graph");

        debug!("Projecting verifier");
        let verifier = g.clone().get_verifier().unwrap();
        self.verifier_graph = Some(verifier.clone());
        self.output_pdf(&verifier, "verifier_graph");
    }

    /// Compose the prover and verifier graphs into a single combined DAG and
    /// emit it as a PDF (if `pdf_path_opt` was set on `ZippelArgs`). No-op
    /// when no PDF path is configured.
    pub fn output_combined_graph(&self) {
        let (Some(prover), Some(verifier)) = (&self.prover_graph, &self.verifier_graph) else {
            return;
        };
        let combined = verifier.combine_dag(prover);
        self.output_pdf(&combined, "combined_graph");
    }

    pub fn set_public_inputs(&mut self, public_inputs: Ctx<Vid, Value<C>>) {
        self.public_inputs = Some(public_inputs);
        let prover = self.prover_graph.as_ref().unwrap();

        // save public inputs as public_inputs
        let prover_args = prover.args();
        self.prover_args = Some(prover_args);
    }

    //Run prover, takes inputs and returns proof
    pub fn run_prover(
        &mut self,
        inputs: Ctx<Vid, Value<C>>,
    ) -> Result<Vec<Value<C>>, RuntimeError> {
        let prover = self.prover_graph.as_ref().unwrap();

        // save public inputs as public_inputs
        let prover_args = prover.args();

        // Validate that every prover argument expected from the caller is
        // present in `inputs`. Transcript-sourced args are produced internally
        // and are not expected to be supplied. Without this check, a typo or
        // mismatch between the protocol declaration and the call-site
        // `inputs` map surfaces deep inside the runtime as an opaque
        // `Option::unwrap() on a None value` panic.
        let expected_args: Vec<Vid> = prover_args
            .iter()
            .filter(|arg| !arg.from_transcript)
            .filter_map(|arg| arg.name().cloned())
            .collect();
        let missing: Vec<&Vid> = expected_args
            .iter()
            .filter(|v| inputs.get(v).is_none())
            .collect();
        if !missing.is_empty() {
            return Err(RuntimeError::missing_inputs(
                missing.iter().copied(),
                expected_args.iter(),
                inputs.iter().map(|(k, _)| k),
            ));
        }

        let public_args: Vec<Vid> = prover_args
            .clone()
            .iter()
            .filter(|arg| arg.is_public())
            .map(|arg| arg.name().cloned().unwrap())
            .collect();
        let public_inputs = inputs
            .clone()
            .into_iter()
            .filter(|(vid, _)| public_args.contains(vid))
            .collect::<Ctx<Vid, Value<C>>>();

        let domain_separator_session = self.args.domain_separator_session();
        let prover_seperator = ZippelDomainSeparator::new_zippel_domain_seperator(
            &domain_separator_session,
            &prover.clone(),
        );

        self.prover_args = Some(prover_args);
        self.public_inputs = Some(public_inputs);
        let mut prover_state = prover_seperator.std_prover();
        MutexGraph::run_graph(
            Arc::new(MutexGraph::new(prover.clone())),
            Arc::new(inputs.clone()),
            &mut prover_state,
            ResultKind::Prover,
        )
    }

    //Run verifier, takes proof and returns result
    pub fn run_verifier(&mut self, proof: Vec<Value<C>>) -> Result<Vec<Value<C>>, RuntimeError> {
        let verifier = self.verifier_graph.as_ref().unwrap();
        let prover_args = self.prover_args.as_ref().unwrap();

        let verifier_args = verifier.args();
        debug!("Verifier args: {:?}", verifier_args);
        let prover_arg_names: std::collections::HashSet<&Vid> =
            prover_args.iter().filter_map(|p| p.name()).collect();
        let pg_additional_args = verifier_args
            .iter()
            .filter(|arg| match arg.name() {
                Some(v) => !prover_arg_names.contains(v),
                None => true,
            })
            .zip(proof.iter())
            .map(|(arg, val)| {
                let v = arg
                    .name()
                    .cloned()
                    .expect("Verifier transcript arg must have a name");
                (v, val.clone())
            })
            .collect::<Ctx<Vid, Value<C>>>();
        let inputs = self.public_inputs.as_ref().unwrap().clone();
        let mut inputs = inputs.clone();
        inputs.append(&pg_additional_args);

        // Verifier uses the same public inputs (instance) as the prover
        // The instance should only contain the public statement, not the proof
        let domain_separator_session = self.args.domain_separator_session();
        let verifier_seperator = ZippelDomainSeparator::new_zippel_domain_seperator(
            &domain_separator_session,
            &verifier.clone(),
        );
        // For now, use prover state since we don't have narg_string yet
        // TODO: Fix this to use proper verifier state when narg_string is available
        let mut verifier_state = verifier_seperator.std_prover();
        MutexGraph::run_graph(
            Arc::new(MutexGraph::new(verifier.clone())),
            Arc::new(inputs),
            &mut verifier_state,
            ResultKind::Verifier,
        )
    }

    pub fn analyze_completeness(&mut self) -> Result<(), analyses::AnalysisError<C>> {
        let g = self.analyze_graph();
        let name = g.name();
        let mut completeness = CompletenessAnalysis::from_input(&*g);
        let result = completeness.run();
        match &result {
            Ok(()) => info!("Complete protocol: {}", name),
            Err(e) => info!("Incomplete protocol {}: {}", name, e),
        }
        result
    }

    pub fn analyze_knowledge(&mut self) -> Result<(), analyses::AnalysisError<C>> {
        let g = self.analyze_graph();
        let name = g.name();
        let mut knowledge = KnowledgeAnalysis::from_input_with_w::<DEFAULT_GB_W>(&*g);
        let result = knowledge.run::<DEFAULT_GB_W>();
        match &result {
            Ok(()) => info!("ZK protocol: {}", name),
            Err(e) => info!("Knowledge leak in {}: {}", name, e),
        }
        result
    }

    pub fn analyze_special_soundness(
        &mut self,
        l_vec: Vec<usize>,
    ) -> Result<(), analyses::AnalysisError<C>> {
        use analyses::SpecialSoundnessAnalysis;
        let g = self.analyze_graph();
        SpecialSoundnessAnalysis::analyze(&*g, l_vec)
    }
}

/// Find the smallest concrete value for each `Kind::SizeVar` parameter in the module
/// such that all dependent `Kind::Range` expressions have at least one element.
pub fn find_minimal_sizes(module: &UModule) -> Ctx<Tid, usize> {
    // Pass 1: Collect all SizeVar params
    let mut size_vars: Vec<Tid> = Vec::new();
    for (sig, _body) in module.iter() {
        for tv in sig.typevars.0.iter() {
            if let Kind::SizeVar = &tv.kind
                && !size_vars.contains(&tv.id)
            {
                size_vars.push(tv.id.clone());
            }
        }
    }

    // Pass 2: Collect all Range params that depend on SizeVars
    let mut ranges: Vec<Range<Size>> = Vec::new();
    for (sig, _body) in module.iter() {
        for tv in sig.typevars.0.iter() {
            if let Kind::Range(r) = &tv.kind {
                let fvs = r.start.free_vars().union(r.end.free_vars());
                if fvs.iter().any(|v| size_vars.contains(v)) {
                    ranges.push(r.clone());
                }
            }
        }
    }

    // For each SizeVar, brute-force S=1..=10 to find the smallest value
    // where all dependent ranges have at least one element (start < end)
    let mut sizes = Ctx::new();
    for sv in &size_vars {
        let mut found = false;
        for candidate in 1..=10usize {
            let mut ctx = sizes.clone();
            ctx.insert(sv, &candidate);

            let all_ok = ranges.iter().all(|r| {
                let fvs = r.start.free_vars().union(r.end.free_vars());
                if !fvs.contains(sv) {
                    return true; // Not dependent on this SizeVar
                }
                match r.clone().traverse1(&mut |s| s.eval(&ctx)) {
                    Ok(cr) => cr.start < cr.end, // Non-empty range
                    Err(_) => false,             // Evaluation failed (e.g., underflow)
                }
            });

            if all_ok {
                sizes.insert(sv, &candidate);
                found = true;
                break;
            }
        }
        if !found {
            // Fallback: use 3 if brute-force fails
            sizes.insert(sv, &3);
        }
    }
    sizes
}

/// Result of verifying a proof
pub struct VerificationResult<C: ArkConfig> {
    pub passed: bool,
    pub outputs: Vec<Value<C>>,
}

/// Interpret verifier output as pass/fail.
/// Passes if every `Value::Bool` in the output is `true`.
pub fn check_verification<C: ArkConfig>(outputs: Vec<Value<C>>) -> VerificationResult<C> {
    let passed = outputs.iter().all(|v| match v {
        Value::Bool(b) => *b,
        _ => true,
    });
    VerificationResult { passed, outputs }
}

/// Compute the total serialized size (in bytes) of a proof certificate.
pub fn proof_size_bytes<C: ArkConfig>(proof: &[Value<C>]) -> usize {
    proof
        .iter()
        .filter_map(|v| value_to_bytes(v).ok())
        .map(|b| b.len())
        .sum()
}

#[cfg(test)]
mod tests {
    use super::*;
    use backend::ArkBls12_381;

    #[test]
    fn zippel_args_domain_session_defaults_to_path_and_can_be_overridden() {
        let file_path = PathBuf::from("examples/sumcheck/sumcheck.zippel");
        let args = ZippelArgs::new(file_path.clone());
        assert_eq!(
            args.domain_separator_session(),
            file_path.display().to_string()
        );

        let args = ZippelArgs::new_with_domain_session(file_path, "logical/sumcheck.zippel");
        assert_eq!(
            args.domain_separator_session(),
            "logical/sumcheck.zippel".to_string()
        );

        let args = args.with_domain_session("other/logical.zippel");
        assert_eq!(
            args.domain_separator_session(),
            "other/logical.zippel".to_string()
        );
    }

    /// Regression: find_minimal_sizes must collect all SizeVars before
    /// collecting ranges, so ranges that appear before their SizeVar
    /// in typevars are still found.
    #[test]
    fn test_find_minimal_sizes_ordering() {
        // Protocol where N: 1..S appears before S: Size in a different declaration
        let src = r#"
            fn foo<F: Field, N: 1..S, S: Size>(a: [F; N]) -> F { a[0] }
            proto bar<F: Field, S: Size, M: 2..S+1>(public x: F) where x == x {
                verify(x == x)
            }
        "#;
        let module = UModule::from_str(src).unwrap();
        let sizes = find_minimal_sizes(&module);
        // S should be found and have a value ≥ 2 (so N: 1..S and M: 2..S+1 are non-empty)
        assert!(
            sizes.get(&Tid::new("S")).is_some(),
            "SizeVar S should be found even when Range appears first"
        );
        let s_val = *sizes.get(&Tid::new("S")).unwrap();
        assert!(s_val >= 2, "S should be ≥ 2, got {}", s_val);
    }
    /// Runtime test: protocol with two verify statements, both passing.
    /// Compile, run prover, run verifier, check that verification passes.
    #[test]
    fn test_runtime_multiple_verify_positive() {
        let src = r#"
proto eq_proof<F: Field>(private a: F, private b: F) where a == b {
    let r = random<F>;
    x <- a * r;
    y <- b * r;
    verify(r == r);
    verify(x == y)
}
"#;
        let temp_dir = tempfile::tempdir().unwrap();
        let file_path = temp_dir.path().join("eq_proof_positive.zippel");
        std::fs::write(&file_path, src).unwrap();
        let args = ZippelArgs::new(file_path);
        let mut handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
        handler.compile(&Ctx::new());

        let mut inputs = Ctx::<Vid, Value<ArkBls12_381>>::new();
        inputs.insert(
            &Vid::new("a"),
            &Value::Scalar(<ArkBls12_381 as ArkConfig>::F::from(5u64)),
        );
        inputs.insert(
            &Vid::new("b"),
            &Value::Scalar(<ArkBls12_381 as ArkConfig>::F::from(5u64)),
        );

        let proof = handler.run_prover(inputs).expect("run_prover failed");
        let verifier_result = handler.run_verifier(proof).expect("run_verifier failed");
        let result = check_verification(verifier_result);
        assert!(
            result.passed,
            "eq_proof with a == b should pass verification"
        );
    }

    /// Regression for issue #157: re-logging earlier transcript values after a
    /// challenge must preserve every proof element and verifier alignment.
    #[test]
    fn test_runtime_issue_157_transcript_relogs_after_challenge() {
        let src = r#"
proto repro<F: Field>(private s: F) where s == s {
    c <- challenge<F>;
    a <- c;
    b <- a;
    d <- c;
    e <- c;
    f <- c;
    g <- c;
    verify(a == g)
}
"#;
        const EXPECTED_PROOF_VALUES: usize = 6;

        let temp_dir = tempfile::tempdir().unwrap();
        let file_path = temp_dir.path().join("issue_157_relogs.zippel");
        std::fs::write(&file_path, src).unwrap();
        let args = ZippelArgs::new(file_path);
        let mut handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
        handler.compile(&Ctx::new());

        let mut inputs = Ctx::<Vid, Value<ArkBls12_381>>::new();
        inputs.insert(
            &Vid::new("s"),
            &Value::Scalar(<ArkBls12_381 as ArkConfig>::F::from(5u64)),
        );

        let proof = handler.run_prover(inputs).expect("run_prover failed");
        assert_eq!(
            proof.len(),
            EXPECTED_PROOF_VALUES,
            "issue #157 repro should emit all six non-challenge transcript proof values"
        );

        let verifier_result = handler.run_verifier(proof).expect("run_verifier failed");
        let result = check_verification(verifier_result);
        assert!(
            result.passed,
            "issue #157 repro should pass verification after transcript relogs"
        );
    }

    /// Runtime test: protocol where a verify condition is deliberately false.
    /// The verification should FAIL when c ≠ 0.
    #[test]
    fn test_runtime_multiple_verify_negative_wrong_condition() {
        let src = r#"
proto bad_check<F: Field>(private a: F, private b: F, public c: F) where a == b {
    let r = random<F>;
    x <- a * r;
    y <- b * r;
    verify(x == y);
    verify(c == 0)
}
"#;
        let temp_dir = tempfile::tempdir().unwrap();
        let file_path = temp_dir.path().join("bad_check_negative.zippel");
        std::fs::write(&file_path, src).unwrap();
        let args = ZippelArgs::new(file_path);
        let mut handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
        handler.compile(&Ctx::new());

        let mut inputs = Ctx::<Vid, Value<ArkBls12_381>>::new();
        inputs.insert(
            &Vid::new("a"),
            &Value::Scalar(<ArkBls12_381 as ArkConfig>::F::from(5u64)),
        );
        inputs.insert(
            &Vid::new("b"),
            &Value::Scalar(<ArkBls12_381 as ArkConfig>::F::from(5u64)),
        );
        inputs.insert(
            &Vid::new("c"),
            &Value::Scalar(<ArkBls12_381 as ArkConfig>::F::from(42u64)),
        );

        let proof = handler.run_prover(inputs).expect("run_prover failed");
        let verifier_result = handler.run_verifier(proof).expect("run_verifier failed");
        let result = check_verification(verifier_result);
        assert!(
            !result.passed,
            "bad_check with c = 42 should fail verification since c != 0"
        );
    }
}
