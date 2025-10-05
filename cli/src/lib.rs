use clap::{Subcommand, Parser};
use std::path::{Path, PathBuf};
use std::process; // For process::exit
use criterion::Criterion;
use std::{fs::{self, File}, io::Write};
use graph::{analyses::{completeness, KnowledgeAnalysis}, WritePdf};
use lang::id::Vid;
use backend::{ArkConfig,  ArkBls12_381, Value, ATyp, ABase};
use lang::ast::UModule;
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


#[derive(Parser, Debug)]
pub struct CliArgs {
    /// The path to the text file to read
    #[arg(value_name = "FILE")]
    pub file_path: PathBuf,

    /// Optional path for the pdf file
    /// If not provided, defaults to <INPUT_FILE>.pdf
    #[arg(short = 'p', long = "pdf", value_name = "PDF_FILE")]
    pub pdf_path_opt: Option<PathBuf>,

    /// An optional subgraph name
    #[arg(long = "subgraph", short = 's')]
    pub subgraph: Option<String>,
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

pub struct ZippelHandler<C:ArkConfig>{
    args: CliArgs,
    combined_graph: Option<UDag<C>>,
    prover_graph: Option<UDag<C>>,
    verifier_graph: Option<UDag<C>>,
    public_inputs: Option<Ctx<Vid, Value<C>>>,
    prover_args: Option<Vec<PRef>>,
}

impl<C:ArkConfig> ZippelHandler<C> {
    pub fn new(args: CliArgs) -> Self {
        ZippelHandler { args, combined_graph: None, prover_graph: None, verifier_graph: None, public_inputs: None, prover_args: None }
    }

    fn get_protocol_subgraph<'a>(&self, gs: &'a UDags<C>) -> &'a UDag<C> {
        if let Some(proto_name) = &self.args.subgraph {
            println!("Getting protocol subgraph: {}", proto_name);
            gs.get_proto(&proto_name.clone().into())
            .expect(&format!("Protocol {} not found in {}", proto_name, self.args.file_path.display()))
        } else {
            println!("Getting first protocol subgraph");
            gs.protocols().first()
            .expect(&format!("No protocols found in {}", self.args.file_path.display()))
        }
    }

    // at this point only have access to args, should set combined_graph, verifier_graph, prover_graph
    pub fn compile(&mut self) {
        println!("Compiling file: {}", self.args.file_path.display());
        let zfile = fs::read_to_string(&self.args.file_path).unwrap_or_else(|err| {
            error!("Error reading file {}: \n\t{}", self.args.file_path.display(), err);
            process::exit(1);
        });

        println!("Parsing Zippel program:\n{}", zfile);
        let m = UModule::from_str(&zfile).unwrap().concretize().unwrap();
        println!("Concretized module:\n{:?}", m);
        let gs = unwrap!(UDags::<C>::from_module(m));

        gs.write_pdf("testing_compile").unwrap_or_else(|e| {
            println!("Error writing to PDF, maybe [dot] is not installed? \n\n {}", e);
        });

        let g_temp = self.get_protocol_subgraph(&gs);
        let g = g_temp.clone().map_transcript_nodes();


        println!("Writing PDF");
        g.write_pdf("api_testing_prover_verifier").unwrap_or_else(|e| {
            println!("Error writing to PDF, maybe [dot] is not installed? \n\n {}", e);
        });
        println!("PDF written");
        

        let (prover, _) = g.clone().get_prover();
        self.prover_graph = Some(prover.clone());
        let verifier = g.clone().get_verifier().unwrap();
        self.verifier_graph = Some(verifier.clone());


        self.combined_graph = Some(verifier.combine_dag(&prover));

        self.combined_graph.as_ref().unwrap().write_pdf("prover_verifier_compile").unwrap_or_else(|e| {
            warn!("Error writing to PDF, maybe [dot] is not installed? \n\n {}", e);
        });
    }

    pub fn combined_graph_pdf(&self, filename: &str) {
        self.combined_graph.as_ref().unwrap().write_pdf(filename).unwrap_or_else(|e| {
            println!("Error writing to PDF, maybe [dot] is not installed? \n\n {}", e);
        });
    }

    //Schedule prover with default scheduler
    pub fn default_schedule_prover(&self) -> TDag<C> {
        let scheduler = LocalScheduler::new_with_system(&self.prover_graph.as_ref().unwrap(), &AsymptoticCost::new(), 30.0);
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

        let prover_seperator = ZippelDomainSeparator::<DefaultHash>::new_zippel_domain_seperator(&self.args.file_path.display().to_string(), &prover.clone());
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
       println!("Verifier args: {:?}", verifier_args);
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
       
        
        let verifier_seperator = ZippelDomainSeparator::<DefaultHash>::new_zippel_domain_seperator(&self.args.file_path.display().to_string(), &verifier.clone());
        let mut verifier_state = ProverState::new(&verifier_seperator.0, rand::rngs::OsRng);
        let result = MutexGraph::run_graph(Arc::new(MutexGraph::new(verifier_scheduled)),  Arc::new(inputs), &mut verifier_state);
        result
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
