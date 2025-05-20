use clap::{Subcommand, Parser};
use std::path::PathBuf;
use std::process; // For process::exit
use criterion::Criterion;
use std::{fs::{self, File}, io::Write};
use graph::WritePdf;
use std::collections::HashMap;
use lang::id::Vid;
use backend::{ArkConfig, Value, ATyp, ABase};
use lang::ast::UModule;
use backend::ArkBls12_381;
use costs::Benchmarker;
use share::unwrap;
use graph::{
    UDags,
    UDag,
    analyses::{TransClos, GroebnerBuilder},
    analyses::{UniformityPropagation, QualifierPropagation, CompletenessAnalysis}
};
use graph::scheduler::{ThreadAlloc, TDag, Scheduler, AsymptoticCost};
use graph::scheduler::ilp::GurobiScheduler;
use runtime::MutexGraph;
use std::sync::Arc;
use graph::Ref;
use ark_std::test_rng;
use rand::Rng;
#[derive(Parser, Debug)]
#[command(author, version,
    about = "The Zippel language for cryptographic protocols.",
    long_about = "The Zippel language for cryptographic protocols, compiles into optimized and safe prover and verifier code.")]

#[command(propagate_version = true)]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

// Enum defining the available subcommands
#[derive(Subcommand, Debug)]
enum Commands {
    /// Execute the zippel compiler
    Eval(CliArgs),

    /// Execute the zippel analysis
    Analyze(CliArgs),

    /// Execute the benchmark suite
    Benchmark(BenchmarkArgs),
}

#[derive(Parser, Debug)]
struct CliArgs {
    /// The path to the text file to read
    #[arg(value_name = "FILE")]
    file_path: PathBuf,

    /// Optional path for the pdf file
    /// If not provided, defaults to <INPUT_FILE>.pdf
    #[arg(short = 'p', long = "pdf", value_name = "PDF_FILE")]
    pdf_path_opt: Option<PathBuf>,

    /// An optional subgraph name
    #[arg(long = "subgraph", short = 's')]
    subgraph: Option<String>,
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

fn main() {
    // Parse the command-line arguments using the Args struct
    let cli = Cli::parse();

    match cli.command {
        Commands::Eval(eval_args) => {
            eval(eval_args);
        }
        Commands::Analyze(analyze_args) => {
            analyze(analyze_args);
        }
        Commands::Benchmark(benchmark_args) => {
            benchmark(benchmark_args);
        }
    }
}

fn get_protocol_subgraph<'a>(gs: &'a UDags<ArkBls12_381>, args: &'a CliArgs) -> &'a UDag<ArkBls12_381> {
    if let Some(proto_name) = &args.subgraph {
        gs.get_proto(&proto_name.clone().into())
        .expect(&format!("Protocol {} not found in {}", proto_name, args.file_path.display()))
    } else {
        gs.protocols().first()
        .expect(&format!("No protocols found in {}", args.file_path.display()))
    }
}

fn analyze(args: CliArgs) {
    // Read zippel file
    let zfile = fs::read_to_string(&args.file_path).unwrap_or_else(|err| {
        eprintln!("Error reading file {}: \n\t{}", args.file_path.display(), err);
        process::exit(1);
    });
    let m = UModule::from_str(&zfile).unwrap().concretize().unwrap();
    let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));

    // Save to pdf if provided
    if let Some(mut pdf_path) = args.pdf_path_opt.clone() {
        pdf_path.set_extension("");
        gs.write_pdf(&pdf_path.into_os_string().to_str().unwrap()).unwrap_or_else(|e| {
            println!("Error writing to PDF, maybe [dot] is not installed? \n\n {}", e);
        });
    }

    // Get protocol by name, or the first one if not provided
    let g = get_protocol_subgraph(&gs, &args);

    // Propagate qualifiers in the DAG to all children
    let g= QualifierPropagation::from_dag(&g);

    // Then propagate distribution tags (uniformity)
    let mut up = UniformityPropagation::new();
    let g = up.from_dag(&g);

    // Create an object computing the Groebner basis
    let mut groebner = GroebnerBuilder::from_input(&g);

    // Symbolically eliminate uniform random variables to find leaks
    let leaks = groebner.run();

    if leaks.is_empty() {
        println!("No leaks found");
    } else {
        println!("Leaks found:\n");
        for leak in leaks.iter() {
            println!("{}", leak);
        }
    }

    // Next, check for completeness
    let completeness = CompletenessAnalysis::new(&g);
    completeness.run();
}

fn eval(args: CliArgs) {
    let zfile = fs::read_to_string(&args.file_path).unwrap_or_else(|err| {
        eprintln!("Error reading file {}: \n\t{}", args.file_path.display(), err);
        process::exit(1);
    });

    println!("Parsing Zippel program:\n{}", zfile);
    let m = UModule::from_str(&zfile).unwrap().concretize().unwrap();
    let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));

    // Save to pdf if provided
    if let Some(mut pdf_path) = args.pdf_path_opt.clone() {
        pdf_path.set_extension("");
        gs.write_pdf(&pdf_path.into_os_string().to_str().unwrap()).unwrap_or_else(|e| {
            println!("Error writing to PDF, maybe [dot] is not installed? \n\n {}", e);
        });
    }

    let g = get_protocol_subgraph(&gs, &args);
    let verifier = g.get_verifier().unwrap();
    let (prover, _) = g.get_prover();

    let combined = verifier.combine_dag(&prover);

    combined.write_pdf("prover_verifier").unwrap_or_else(|e| {
        println!("Error writing to PDF, maybe [dot] is not installed? \n\n {}", e);
    });

    let prover_args = prover.args();
    let verifier_args = verifier.args();

    let cost_model = AsymptoticCost::new();
    let miip_gap = 0.50;

    let prover_scheduler = GurobiScheduler::new_with_system(&prover, &cost_model);
    // let prover_tdag = prover_scheduler.schedule(prover, miip_gap);
    let prover_tdag = prover.map_annotations(&|_, _| {
        let mut rng = rand::thread_rng();
        let mut threads = Vec::new();
        for _ in 0..3 {
            threads.push(rng.gen_range(0..prover_scheduler.num_threads()));
        }
        ThreadAlloc::new(threads)
    });
    let prover_mutex_graph = MutexGraph::new(prover_tdag);
    let prover_arc_graph = Arc::new(prover_mutex_graph);
    let verifier_scheduler = GurobiScheduler::new_with_system(&verifier, &cost_model);
    // let verifier_tdag = verifier_scheduler.schedule(verifier, miip_gap);
    let verifier_tdag = verifier.map_annotations(&|_, _| {
        let mut rng = rand::thread_rng();
        let mut threads = Vec::new();
        for _ in 0..6 {
            threads.push(rng.gen_range(0..prover_scheduler.num_threads()));
        }
        ThreadAlloc::new(threads)
    });
    let verifier_mutex_graph = MutexGraph::new(verifier_tdag);
    verifier_mutex_graph.print_edges();
    let verifier_arc_graph = Arc::new(verifier_mutex_graph);

    // TODO: extract inputs from command line
    let mut inputs: HashMap<Vid, Value<ArkBls12_381>> = HashMap::new();

    // TODO: extract inputs from command line
    let n_val_const = 2;
    let mut rng = test_rng();


    let g_vec: Value<ArkBls12_381> = Value::zero(&ATyp::vec(&ATyp::g1(), n_val_const));
    let h_vec: Value<ArkBls12_381> = Value::zero(&ATyp::vec(&ATyp::g1(), n_val_const));
    
    let p_initial_commitment: Value<ArkBls12_381> = Value::zero(&ATyp::g1());
    let ip_val_claimed: Value<ArkBls12_381> = Value::<ArkBls12_381>::random(&mut rng, &ATyp::scalar());
    let u_aux_base: Value<ArkBls12_381> = Value::zero(&ATyp::g1());
    
    let a_vec_witness = Value::<ArkBls12_381>::random(&mut rng, &ATyp::vec_scalar(n_val_const));
    let b_vec_witness = Value::<ArkBls12_381>::random(&mut rng, &ATyp::vec_scalar(n_val_const));

    inputs.insert(Vid("g_vec".to_string()), g_vec);
    inputs.insert(Vid("h_vec".to_string()), h_vec);
    inputs.insert(Vid("P_initial_commitment".to_string()), p_initial_commitment);
    inputs.insert(Vid("ip_val_claimed".to_string()), ip_val_claimed);
    inputs.insert(Vid("u_aux_base".to_string()), u_aux_base);
    inputs.insert(Vid("a_vec_witness".to_string()), a_vec_witness);
    inputs.insert(Vid("b_vec_witness".to_string()), b_vec_witness);

    println!("Prover inputs:");
    for (vid, value) in inputs.iter() {
        println!("{}: {}", vid, value);
    }
    
    let prover_result = MutexGraph::run_graph(prover_arc_graph, Arc::new(inputs.clone()));
    println!("Prover result: {:?}", prover_result);
    let pg_additional_args = verifier_args.iter()
    .filter(|arg| !prover_args.contains(arg))
    .zip(prover_result.iter())
    .map(|(arg, val)| match &arg.reference { 
        Ref::Node(node) => panic!("Node reference not supported"),
        Ref::Var(v, _) => (v.clone(), val.clone()),
    })
    .collect::<HashMap<Vid, Value<ArkBls12_381>>>();
    inputs.extend(pg_additional_args);
    println!("Verifier inputs:");
    for (vid, value) in inputs.iter() {
        println!("{}: {}", vid, value);
    }

    let verifier_result = MutexGraph::run_graph(verifier_arc_graph, Arc::new(inputs));
    println!("Verifier result: {:?}", verifier_result);
    // Runtime on scheduled prover will return vector of values (transcript)
    // Runtime on verifier will take transcript and return value boolean (valid/invalid)
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
