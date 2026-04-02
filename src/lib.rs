use std::path::PathBuf;
use std::process;
use std::fs;
use lang::typ::{Qualifier, Distribution, Kind, Size};
use lang::typ::range::Range;
use graph::Dag;
use graph::{analyses::KnowledgeAnalysis, WritePdf};
use lang::id::{Tid, Vid};
use backend::{ArkConfig, Value, value_to_bytes};
use backend::op::HasOpFactory;
use lang::ast::{UModule, CModule};
use share::{Ctx, unwrap};
use graph::{
    UDags,
    UDag,
    analyses::{UniformityPropagation, QualifierPropagation, CompletenessAnalysis, AnalysisError}
};
use log::{error, debug, info};
use graph::domain_seperator::ZippelDomainSeparator;

use graph::scheduler::{TDag, Scheduler, AsymptoticCost};
use graph::scheduler::local_scheduler::LocalScheduler;
use runtime::MutexGraph;
use std::sync::Arc;
use graph::Ref;
use graph::PRef;
use share::traversal::ToTraversal1;

/// Arguments for the Zippel handler
#[derive(Debug, Clone)]
pub struct ZippelArgs {
    /// The path to the zippel file to read
    pub file_path: PathBuf,

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
            pdf_path_opt: None,
            subgraph: None,
        }
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

pub struct ZippelHandler<C:ArkConfig> {
    pub args: ZippelArgs,
    pub sized_module: Option<UModule>,
    pub concrete_module: Option<CModule>,
    pub proto_graph: Option<UDag<C>>,
    pub prover_graph: Option<UDag<C>>,
    pub verifier_graph: Option<UDag<C>>,
    pub entry_point: Option<String>,
    pub public_inputs: Option<Ctx<Vid, Value<C>>>,
    pub prover_args: Option<Vec<PRef>>,
    pub analyze_graph: Option<Dag<C, (Qualifier, Distribution)>>,
}

impl<C:ArkConfig + HasOpFactory> ZippelHandler<C> {
    pub fn new(args: ZippelArgs) -> Self {
        // Enable detailed error messages from pest parser
        // This provides more comprehensive error messages for debugging parser errors
        lang::init_parser();
        
        ZippelHandler { 
            args,
            sized_module: None, 
            concrete_module: None, 
            proto_graph: None, 
            prover_graph: None, 
            verifier_graph: None, 
            entry_point: None, 
            public_inputs: None, 
            prover_args: None,
            analyze_graph: None
        }
    }

    fn get_protocol_subgraph<'a>(&self, gs: &'a UDags<C>) -> &'a UDag<C> {
        if let Some(main_proto) = &self.args.subgraph {
            debug!("Getting protocol: {}", main_proto);
            gs.get_proto(main_proto)
              .expect(&format!("Protocol {} not found in {}", main_proto, self.args.file_path.display()))
        } else {
            gs.protocols().first()
              .expect(&format!("No protocols found in {}", self.args.file_path.display()))
        }
    }

    pub fn parse(&mut self) {
        debug!("Parsing file: {}", self.args.file_path.display());
        let zfile = fs::read_to_string(&self.args.file_path).unwrap_or_else(|err| {
            error!("Error reading file {}: \n\t{}", self.args.file_path.display(), err);
            process::exit(1);
        });
        self.sized_module = Some(UModule::from_str(&zfile).unwrap());
    }

    /// Will output a PDF if a path is provided, noop otherwise
    pub fn output_pdf<'a, D: WritePdf>(&self, g: &D, msg: &'a str) {
        if let Some(pdf_path) = &self.args.pdf_path_opt {
            let os_str = pdf_path.clone().into_os_string();
            let mut str_path = os_str.into_string().unwrap();
            if str_path.ends_with(".pdf") {
                str_path = str_path.strip_suffix(".pdf").unwrap().to_string();
            }
            str_path = str_path + "_" + msg + ".pdf";
            debug!("Writing {} PDF to {}", msg, str_path);
            g.write_pdf(str_path.as_str()).unwrap_or_else(|e| {
                error!("Error writing to PDF, maybe [dot] is not installed? \n\n {}", e);
                process::exit(2);
            })
        }
    }
    // at this point only have access to args, should set combined_graph, verifier_graph, prover_graph
    pub fn compile(&mut self, sizes: &Ctx<Tid, usize>) {
        self.parse();

        debug!("Concretizing module type variables");
        self.concrete_module = Some(self.sized_module.as_ref().unwrap().concretize(sizes).unwrap());

        debug!("Creating graphs from module");
        let gs = unwrap!(UDags::<C>::from_module(self.concrete_module.as_ref().unwrap().clone()));
        self.output_pdf(&gs, "symbolic_protocol_graph");

        let g_analyze = QualifierPropagation::from_dag(self.get_protocol_subgraph(&gs)); 

        let mut up = UniformityPropagation::new();        
        let g_analyze = up.from_dag(&g_analyze);
        self.analyze_graph = Some(g_analyze);

        // Extract protocol subgraph and rename inner nodes
        let g = self.get_protocol_subgraph(&gs)
            .clone()
            .rename_inner_nodes();
        self.output_pdf(&g, "concrete_protocol_graph");

        debug!("Projecting prover");
        // Extract protocol subgraph and rename inner nodes
        let g = self.get_protocol_subgraph(&gs)
            .clone()
            .rename_inner_nodes();
        self.output_pdf(&g, "concrete_protocol_graph");

        debug!("Projecting prover");
        let (prover, _) = g.clone().get_prover();
        self.prover_graph = Some(prover.clone());
        self.output_pdf(&prover, "prover_graph");

        debug!("Projecting verifier");
        let verifier = g.clone().get_verifier().unwrap();
        self.verifier_graph = Some(verifier.clone());
        self.output_pdf(&verifier, "verifier_graph");

        debug!("Combining prover and verifier");
        let combined = verifier.combine_dag(&prover);
        self.output_pdf(&combined, "combined_graph");
    }

    //Schedule prover with default scheduler
    pub fn default_schedule_prover(&self) -> TDag<C> {
        let scheduler = LocalScheduler::new_with_system(self.prover_graph.as_ref().unwrap(), &AsymptoticCost::new(), 30.0);
        scheduler.schedule(self.prover_graph.as_ref().unwrap().clone())
    }

    //Run prover, takes inputs and returns proof
    pub fn run_prover(&mut self, prover_scheduled: TDag<C>, inputs: Ctx<Vid, Value<C>>) -> Vec<Value<C>> {
        let prover = self.prover_graph.as_ref().unwrap();
        
        // save public inputs as public_inputs
        let prover_args = prover.args();
        let public_args: Vec<Vid> = prover_args.clone().iter().filter(|arg| arg.is_public()).map(|arg| arg.var().unwrap()).collect();
        let public_inputs = inputs.clone().into_iter().filter(|(vid, _)| public_args.contains(&vid)).collect::<Ctx<Vid, Value<C>>>();
        
        let prover_seperator = ZippelDomainSeparator::new_zippel_domain_seperator(
            &self.args.file_path.display().to_string(), 
            &prover.clone(),
        );
      
        self.prover_args = Some(prover_args);
        self.public_inputs = Some(public_inputs);
        let mut prover_state = prover_seperator.std_prover();
        let result = MutexGraph::run_graph(Arc::new(MutexGraph::new(prover_scheduled)), Arc::new(inputs.clone()), &mut prover_state);
        result
    }

    //Schedule verifier with default scheduler
    pub fn default_schedule_verifier(&self) -> TDag<C> {
        let scheduler = LocalScheduler::new_with_system(&self.verifier_graph.as_ref().unwrap(), &AsymptoticCost::new(), 30.0);
        scheduler.schedule(self.verifier_graph.as_ref().unwrap().clone())
    }

    //Run verifier, takes proof and returns result
    pub fn run_verifier(&mut self, verifier_scheduled: TDag<C>, proof: Vec<Value<C>>) -> Vec<Value<C>> {
        let verifier = self.verifier_graph.as_ref().unwrap();
        let prover_args = self.prover_args.as_ref().unwrap();

       let verifier_args = verifier.args();
       debug!("Verifier args: {:?}", verifier_args);
       let pg_additional_args = verifier_args.iter()
            .filter(|arg| !prover_args.contains(arg))
            .zip(proof.iter())
            .map(|(arg, val)| match &arg.reference {
                Ref::Node(_node) => panic!("Node reference not supported"),
                Ref::Var(v, _) => (v.clone(), val.clone()),
            })
            .collect::<Ctx<Vid, Value<C>>>();
        let inputs = self.public_inputs.as_ref().unwrap().clone();
        let mut inputs = inputs.clone();
        inputs.append(&pg_additional_args);
        
        // Verifier uses the same public inputs (instance) as the prover
        // The instance should only contain the public statement, not the proof
        let verifier_seperator = ZippelDomainSeparator::new_zippel_domain_seperator(
            &self.args.file_path.display().to_string(), 
            &verifier.clone(),
        );
        // For now, use prover state since we don't have narg_string yet
        // TODO: Fix this to use proper verifier state when narg_string is available
        let mut verifier_state = verifier_seperator.std_prover();
        let result = MutexGraph::run_graph(Arc::new(MutexGraph::new(verifier_scheduled)),  Arc::new(inputs), &mut verifier_state);
        result
    }
    
   pub fn analyze_completeness(&self) -> Result<(), graph::analyses::AnalysisError<C>> {
        let g_analyze = self.analyze_graph.as_ref().unwrap();
        let mut completeness = CompletenessAnalysis::from_input(g_analyze);
        let result = completeness.run();
        match &result {
            Ok(()) => info!("Complete protocol: {}", g_analyze.name()),
            Err(e) => info!("Incomplete protocol {}: {}", g_analyze.name(), e),
        }
        result
    }

    pub fn analyze_knowledge(&self) -> Result<(), graph::analyses::AnalysisError<C>> {
        let g_analyze = self.analyze_graph.as_ref().unwrap();
        let mut knowledge = KnowledgeAnalysis::from_input(g_analyze);
        let result = knowledge.run();
        match &result {
            Ok(()) => info!("ZK protocol: {}", g_analyze.name()),
            Err(e) => info!("Knowledge leak in {}: {}", g_analyze.name(), e),
        }
        result
    }

    /// Run completeness and knowledge analysis with automatically computed minimal sizes.
    ///
    /// For each `S: Size` parameter, brute-forces `S = 1..10` to find the smallest
    /// value where all dependent ranges are non-empty, keeping the analysis graph small.
    pub fn minimal_analysis(&mut self) -> AnalysisResult<C> {
        self.parse();
        let module = self.sized_module.as_ref().unwrap();
        let sizes = find_minimal_sizes(module);
        info!("Minimal analysis sizes: {:?}", sizes);
        self.compile(&sizes);
        AnalysisResult {
            completeness: self.analyze_completeness(),
            zk: self.analyze_knowledge(),
        }
    }
}

/// Result of running completeness and knowledge (ZK) analyses.
pub struct AnalysisResult<C: ArkConfig> {
    pub completeness: Result<(), AnalysisError<C>>,
    pub zk: Result<(), AnalysisError<C>>,
}

/// Find the smallest concrete value for each `Kind::SizeVar` parameter in the module
/// such that all dependent `Kind::Range` expressions have at least one element.
pub fn find_minimal_sizes(module: &UModule) -> Ctx<Tid, usize> {
    // Pass 1: Collect all SizeVar params
    let mut size_vars: Vec<Tid> = Vec::new();
    for (sig, _body) in module.iter() {
        for tv in sig.typevars.0.iter() {
            if let Kind::SizeVar = &tv.kind {
                if !size_vars.contains(&tv.id) {
                    size_vars.push(tv.id.clone());
                }
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
                    Err(_) => false, // Evaluation failed (e.g., underflow)
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
    proof.iter()
        .filter_map(|v| value_to_bytes(v).ok())
        .map(|b| b.len())
        .sum()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Regression: find_minimal_sizes must collect all SizeVars before
    /// collecting ranges, so ranges that appear before their SizeVar
    /// in typevars are still found.
    #[test]
    fn test_find_minimal_sizes_ordering() {
        // Protocol where N: 1..S appears before S: Size in a different declaration
        let src = r#"
            fn foo<F: Field, N: 1..S, S: Size>(a: [F; N]) -> F { a[0] }
            proto bar<F: Field, S: Size, M: 2..S+1>(public x: F) where x == x {
                verify(x == x);
            }
        "#;
        let module = UModule::from_str(src).unwrap();
        let sizes = find_minimal_sizes(&module);
        // S should be found and have a value ≥ 2 (so N: 1..S and M: 2..S+1 are non-empty)
        assert!(sizes.get(&Tid::new("S")).is_some(),
            "SizeVar S should be found even when Range appears first");
        let s_val = *sizes.get(&Tid::new("S")).unwrap();
        assert!(s_val >= 2, "S should be ≥ 2, got {}", s_val);
    }
}