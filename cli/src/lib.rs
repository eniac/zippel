use clap::{Subcommand, Parser};
use std::path::{Path, PathBuf};
use std::process; // For process::exit
use criterion::Criterion;
use std::{fs::{self, File}, io::Write};
use lang::typ::{Qualifier, Distribution};
use graph::Dag;
use graph::{analyses::{completeness, KnowledgeAnalysis}, WritePdf};
use lang::id::Vid;
use backend::{ArkConfig,  ArkBls12_381, Value, ATyp, ABase};
use lang::ast::{UModule, CModule};
use costs::Benchmarker;
// use backend::ArkBls12_381
// use backend::ArkBls12_381;
use share::{Ctx, unwrap};
use graph::{
    UDags,
    UDag,
    analyses::{TransClos, GroebnerBuilder},
    analyses::{UniformityPropagation, QualifierPropagation, CompletenessAnalysis}
};
use log::{error, warn, debug};
use spongefish::{ProverState, DefaultHash, DomainSeparator, DuplexSpongeInterface};
use graph::domain_seperator::ZippelDomainSeparator;

use graph::scheduler::{ThreadAlloc, TDag, Scheduler, AsymptoticCost};
use graph::scheduler::ilp::GurobiScheduler;
use graph::scheduler::local_scheduler::LocalScheduler;
use runtime::MutexGraph;
use std::sync::Arc;
use graph::Ref;
use ark_std::test_rng;
use rand::Rng;
use graph::PRef;
use std::time::Instant;
use ark_std::UniformRand;
use lang::ast::Args;

/// Command line arguments
/// Command line arguments
#[derive(Parser, Debug)]
pub struct CliArgs {
    /// The path to the text file to read
    #[arg(value_name = "FILE")]
    pub file_path: PathBuf,

    /// Optional path for the pdf file
    /// If not provided, defaults to <INPUT_FILE>.pdf
    #[arg(short = 'p', long = "pdf", value_name = "PDF_FILE")]
    pub pdf_path_opt: Option<PathBuf>,

    /// An optional subgraph index to print to PDF
    #[arg(long = "subgraph", short = 's', value_name = "SUBGRAPH_NAME")]
    /// An optional subgraph index to print to PDF
    #[arg(long = "subgraph", short = 's', value_name = "SUBGRAPH_NAME")]
    pub subgraph: Option<String>,
}

/// PDF graph pretty-printing options
#[derive(Debug, Eq, PartialEq, Hash, Clone)]
pub struct PdfOpts {
    pub path: PathBuf,
    pub index: usize,
}

// Arguments for the 'benchmark' subcommand
#[derive(Parser, Debug)]
struct BenchmarkArgs {
    /// The path to the JSON output
    #[arg(value_name = "OUT_FILE")]
    out_path: PathBuf,

    /// Number of iterations for the benchmark
    #[arg(short, long, default_value_t = 1000)]
    iterations: u32,
}

pub struct ZippelHandler<C:ArkConfig> {
    pub cli_args: CliArgs,
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

  

impl<C:ArkConfig> ZippelHandler<C> {
    pub fn new(cli_args: CliArgs) -> Self {
        env_logger::init();
        ZippelHandler { 
            cli_args,
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
        if let Some(main_proto) = &self.cli_args.subgraph {
            debug!("Getting protocol: {}", main_proto);
            gs.get_proto(main_proto)
              .expect(&format!("Protocol {} not found in {}", main_proto, self.cli_args.file_path.display()))
        } else {
            gs.protocols().first()
              .expect(&format!("No protocols found in {}", self.cli_args.file_path.display()))
        }
    }

    pub fn parse(&mut self) {
        debug!("Parsing file: {}", self.cli_args.file_path.display());
        let zfile = fs::read_to_string(&self.cli_args.file_path).unwrap_or_else(|err| {
            error!("Error reading file {}: \n\t{}", self.cli_args.file_path.display(), err);
            process::exit(1);
        });
        // At this point we cannot recover from parse errors, so throw
        self.sized_module = Some(UModule::from_str(&zfile).unwrap());
    }

    /// Will output a PDF if a path is provided, noop otherwise
    pub fn output_pdf<'a, D: WritePdf>(&self, g: &D, msg: &'a str) {
        if let Some(pdf_path) = &self.cli_args.pdf_path_opt {
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
    pub fn compile(&mut self) {
        self.parse();

        debug!("Concretizing module type variables");
        self.concrete_module = Some(self.sized_module.as_ref().unwrap().concretize().unwrap());

        debug!("Creating graphs from module");
        let gs = unwrap!(UDags::<C>::from_module(self.concrete_module.as_ref().unwrap().clone()));
        self.output_pdf(&gs, "symbolic_protocol_graph");

        let g_analyze = QualifierPropagation::from_dag(&gs[0].clone()); 

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
        
        self.prover_args = Some(prover_args);
        self.public_inputs = Some(public_inputs);

        let prover_seperator = ZippelDomainSeparator::<DefaultHash>::new_zippel_domain_seperator(&self.cli_args.file_path.display().to_string(), &prover.clone());
        let prover_seperator = ZippelDomainSeparator::<DefaultHash>::new_zippel_domain_seperator(&self.cli_args.file_path.display().to_string(), &prover.clone());
        let mut prover_state = ProverState::new(&prover_seperator.0, rand::rngs::OsRng);
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
        // convert proof to inputs
        let verifier = self.verifier_graph.as_ref().unwrap();
        let prover_args = self.prover_args.as_ref().unwrap();

       // convert proof to inputs 
       let verifier_args = verifier.args();
       debug!("Verifier args: {:?}", verifier_args);
       debug!("Verifier args: {:?}", verifier_args);
       let pg_additional_args = verifier_args.iter()
            .filter(|arg| !prover_args.contains(arg))
            .zip(proof.iter())
            .map(|(arg, val)| match &arg.reference {
                Ref::Node(node) => panic!("Node reference not supported"),
                Ref::Var(v, _) => (v.clone(), val.clone()),
            })
            .collect::<Ctx<Vid, Value<C>>>();
        let inputs = self.public_inputs.as_ref().unwrap().clone();
        let mut inputs = inputs.clone();
        inputs.append(&pg_additional_args);
       
        
        let verifier_seperator = ZippelDomainSeparator::<DefaultHash>::new_zippel_domain_seperator(&self.cli_args.file_path.display().to_string(), &verifier.clone());
        let verifier_seperator = ZippelDomainSeparator::<DefaultHash>::new_zippel_domain_seperator(&self.cli_args.file_path.display().to_string(), &verifier.clone());
        let mut verifier_state = ProverState::new(&verifier_seperator.0, rand::rngs::OsRng);
        let result = MutexGraph::run_graph(Arc::new(MutexGraph::new(verifier_scheduled)),  Arc::new(inputs), &mut verifier_state);
        result
    }
    
   pub fn analyze_completeness(&self) {
        let g_analyze = self.analyze_graph.as_ref().unwrap();
        let mut completeness = CompletenessAnalysis::from_input(g_analyze);
        if completeness.run() {
            println!("Complete protocol: {}", g_analyze.name());
        } else {
            println!("Incomplete protocol: {}", g_analyze.name());
        }
    }

    pub fn analyze_knowledge(&self) {
        let g_analyze = self.analyze_graph.as_ref().unwrap();
        let mut knowledge = KnowledgeAnalysis::from_input(g_analyze);
        let leaks = knowledge.run();
        println!("Leaks: {:?}", leaks);
    }
}

fn benchmark(args: BenchmarkArgs) {
    // // You can call your benchmark function directly from anywhere 
    let criterion = Criterion::default().with_output_color(true);
    let benchmarker = Benchmarker::with_criterion(criterion);
    // benchmarker.run_benches();
    let cost_map = benchmarker.load_from_criterion();
    let json = serde_json::to_string_pretty(&cost_map).unwrap();
    let mut file = File::create(args.out_path).unwrap();
    file.write_all(json.as_bytes()).unwrap();
}