use clap::{Subcommand, Parser};
use std::path::PathBuf;
use std::process; // For process::exit
use criterion::Criterion;
use std::{fs::{self, File}, io::Write};
use graph::{analyses::{completeness, KnowledgeAnalysis}, WritePdf};

use lang::id::Vid;
use backend::{ArkConfig,  ArkBls12_381, Value, ATyp, ABase};
use lang::ast::UModule;
// use backend::ArkBls12_381;
use costs::Benchmarker;
use backend::ArkBls12_381;
use share::unwrap;
use graph::{
    UDags,
    UDag,
    analyses::{TransClos, GroebnerBuilder},
    analyses::{UniformityPropagation, QualifierPropagation, CompletenessAnalysis}
};
use log::{error, warn, debug};

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

    // Initialize logging
    env_logger::init();

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

/// Analysis entry point, analyze a Zippel protocol for completeness and knowledge leaks
fn analyze(args: CliArgs) {
    // Read zippel file
    let zfile = fs::read_to_string(&args.file_path).unwrap_or_else(|err| {
        error!("Error reading file {}: \n\t{}", args.file_path.display(), err);
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

    // Write to pdf
    let pdf_path = args.pdf_path_opt.clone().unwrap_or_else(|| {
        let mut pdf_path = args.file_path.clone();
        pdf_path.set_extension("");
        pdf_path
    });
    g.write_pdf(&pdf_path.into_os_string().to_str().unwrap()).unwrap_or_else(|e| {
        warn!("Error writing to PDF, maybe [dot] is not installed? \n\n {}", e);
    });

    // Completeness analysis first
    let mut completeness = CompletenessAnalysis::from_input(&g);
    if completeness.run() {
        println!("Complete protocol: {}", g.name());
    } else {
        println!("Incomplete protocol: {}", g.name());
    }

    // Create an object computing the Groebner basis
    let mut kz = KnowledgeAnalysis::from_input(&g);

    // Symbolically eliminate uniform random variables to find leaks
    let leaks= kz.run();
}

macro_rules! start_timer {
    ($msg:expr) => {{
        println!("{}", $msg);
        Instant::now()
    }};
}

/// Runtime entry point, evaluate a Zippel program or protocol
fn eval(args: CliArgs) {
    let zfile = fs::read_to_string(&args.file_path).unwrap_or_else(|err| {
        error!("Error reading file {}: \n\t{}", args.file_path.display(), err);
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

    let g_temp = get_protocol_subgraph(&gs, &args);
    let g = g_temp.clone().map_transcript_nodes();
    g.write_pdf("test_prover_verifier").unwrap_or_else(|e| {
        println!("Error writing to PDF, maybe [dot] is not installed? \n\n {}", e);
    });
    // g.print_edges();
    let verifier = g.get_verifier().unwrap();
    let (prover, _) = g.get_prover();
    // verifier.print_edges();

    let combined = verifier.combine_dag(&prover);

    combined.write_pdf("prover_verifier").unwrap_or_else(|e| {
        warn!("Error writing to PDF, maybe [dot] is not installed? \n\n {}", e);
    });

    println!("Graph produced");

    let prover_args = prover.args();
    let verifier_args = verifier.args();

    let cost_model = AsymptoticCost::new();
    let limit: f64 = 30.0;

    let prover_scheduler = LocalScheduler::new_with_system(&prover, &cost_model, limit);
    let prover_tdag = prover_scheduler.schedule(prover);
    let prover_mutex_graph = MutexGraph::new(prover_tdag);
    let prover_arc_graph = Arc::new(prover_mutex_graph);
    let verifier_scheduler = LocalScheduler::new_with_system(&verifier, &cost_model, limit);
    let verifier_tdag = verifier_scheduler.schedule(verifier);
    let verifier_mutex_graph = MutexGraph::new(verifier_tdag);
    let verifier_arc_graph = Arc::new(verifier_mutex_graph);

    println!("Graphs created");
    // TODO: extract inputs from command line
    let mut inputs: HashMap<Vid, Value<ArkBls12_381>> = HashMap::new();

    // TODO: extract inputs from command line
    let n_val_const = 1024;
    let mut rng = test_rng();

    // proto ipa_wrapper<G: Group, F: Scalar<G>, N_val_const: 4>(
    //     // --- Public Inputs ---
    //     public g_vec: [G; N_val_const],    // Corresponds to 'g' in the paper (vector of group elements)
    //     public h_vec: [G; N_val_const],    // Corresponds to 'h' in the paper (vector of group elements)
    //     public P_initial_commitment: G,   // Corresponds to 'P' in the paper
    //     public ip_val_claimed: F,         // Corresponds to 'c' (the inner product value) in the paper
    //     public u_aux_base: G,             // Corresponds to 'u' in the paper

    //     // --- Private Inputs ---
    //     private a_vec_witness: [F; N_val_const],   // Corresponds to 'a' in the paper (vector of field elements)
    //     private b_vec_witness: [F; N_val_const]    // Corresponds to 'b' in the paper (vector of field elements)
    // ) where
    //         (P_initial_commitment == ((g_vec . a_vec_witness)
    //         + (h_vec . b_vec_witness)
    //         + u_aux_base * ip_val_claimed)) && (ip_val_claimed == (a_vec_witness . b_vec_witness)) {



    let u_aux_base: Value<ArkBls12_381> = Value::<ArkBls12_381>::random(&mut rng, &ATyp::g1());

    let g_vec: Value<ArkBls12_381> = Value::<ArkBls12_381>::random(&mut rng, &ATyp::vec(&ATyp::g1(), n_val_const));
    let h_vec: Value<ArkBls12_381> = Value::<ArkBls12_381>::random(&mut rng, &ATyp::vec(&ATyp::g1(), n_val_const));

    // let u_aux_base: Value<ArkBls12_381> = Value::<ArkBls12_381>::random(&mut rng, &ATyp::scalar());
    let a_vec_witness: Value<ArkBls12_381> = Value::<ArkBls12_381>::random(&mut rng, &ATyp::vec_scalar(n_val_const));
    let b_vec_witness: Value<ArkBls12_381> = Value::<ArkBls12_381>::random(&mut rng, &ATyp::vec_scalar(n_val_const));
    // let g_vec: Value<ArkBls12_381> = Value::<ArkBls12_381>::random(&mut rng, &ATyp::vec(&ATyp::scalar(), n_val_const));
    // let h_vec: Value<ArkBls12_381> = Value::<ArkBls12_381>::random(&mut rng, &ATyp::vec(&ATyp::scalar(), n_val_const));
    let ip_val_claimed: Value<ArkBls12_381> = a_vec_witness.clone().dot(b_vec_witness.clone());
    let p_initial_commitment: Value<ArkBls12_381> = g_vec.clone().dot(a_vec_witness.clone()) +
    h_vec.clone().dot(b_vec_witness.clone());
    // + u_aux_base.clone() * ip_val_claimed.clone();
    // let p_initial_commitment = Value::<ArkBls12_381>::random(&mut rng, &ATyp::g1());

    let sum_vec: Value<ArkBls12_381> = Value::<ArkBls12_381>::random(&mut rng, &ATyp::vec_scalar(n_val_const));
    inputs.insert(Vid("g_vec".to_string()), g_vec);
    inputs.insert(Vid("h_vec".to_string()), h_vec);
    inputs.insert(Vid("P_initial_commitment".to_string()), p_initial_commitment);
    inputs.insert(Vid("ip_val_claimed".to_string()), ip_val_claimed);
    inputs.insert(Vid("u_aux_base".to_string()), u_aux_base);
    inputs.insert(Vid("a_vec_witness".to_string()), a_vec_witness);
    inputs.insert(Vid("b_vec_witness".to_string()), b_vec_witness);
    inputs.insert(Vid("sum_vec".to_string()), sum_vec);
    inputs.insert(Vid("val".to_string()), Value::<ArkBls12_381>::random(&mut rng, &ATyp::vec(&ATyp::g1(), n_val_const)));



    let prover_start = start_timer!("Running the prover");
    let prover_result = MutexGraph::run_graph(prover_arc_graph, Arc::new(inputs.clone()));
    let duration_prover = prover_start.elapsed();
    println!("Time taken for prover: {:?} for size {} with limit {}", duration_prover, n_val_const, limit);
    println!("");
    println!("");
    println!("");
    println!("");

    let pg_additional_args = verifier_args.iter()
        .filter(|arg| !prover_args.contains(arg))
        .zip(prover_result.iter())
        .map(|(arg, val)| match &arg.reference {
            Ref::Node(node) => panic!("Node reference not supported"),
            Ref::Var(v, _) => (v.clone(), val.clone()),
        })
        .collect::<HashMap<Vid, Value<ArkBls12_381>>>();
    inputs.extend(pg_additional_args);

    let start = start_timer!("Running the verifier");
    let verifier_result = MutexGraph::run_graph(verifier_arc_graph, Arc::new(inputs));
    println!("Verifier result: {:?}", verifier_result);
    let duration = start.elapsed();
    println!("Time taken: {:?} for size {} with limit {}", duration, n_val_const, limit);
}


// KZG starting point
    // // (private p: Uni<F, 10>, private z: F, public y: F, private s: F, private ss: [F; N],
    // //     public g: G1, public h: G2)
    // //     where p(z) == y && [(ss[i] == s^i) for i in 0..N] {
    //     let g: Value<ArkBls12_381> = Value::G1(<ArkBls12_381 as ArkConfig>::G1::rand(&mut rng));
    //     let h: Value<ArkBls12_381> = Value::G2(<ArkBls12_381 as ArkConfig>::G2::rand(&mut rng));
    //     let z: Value<ArkBls12_381> = Value::<ArkBls12_381>::random(&mut rng, &ATyp::scalar());
    //     let y: Value<ArkBls12_381> = Value::<ArkBls12_381>::random(&mut rng, &ATyp::scalar());
    //     let s: Value<ArkBls12_381> = Value::<ArkBls12_381>::random(&mut rng, &ATyp::scalar());

    //     let p: Value<ArkBls12_381> = Value::<ArkBls12_381>::random(&mut rng, &ATyp::Uni(10));

    //     let ss: Value<ArkBls12_381> = Value::Vec((0..11).map(|i| {
    //         s.clone() ^ Value::Index(i)
    //     }).collect());

    //     inputs.insert(Vid("p".to_string()), p);
    //     inputs.insert(Vid("g".to_string()), g);
    //     inputs.insert(Vid("h".to_string()), h);
    //     inputs.insert(Vid("z".to_string()), z);
    //     inputs.insert(Vid("y".to_string()), y);
    //     inputs.insert(Vid("s".to_string()), s);
    //     inputs.insert(Vid("ss".to_string()), ss);


//     let n_val_const = 4;
//     let mut rng = test_rng();


//     let g_vec: Value<ArkBls12_381> = Value::zero(&ATyp::vec(&ATyp::g1(), n_val_const));
//     let h_vec: Value<ArkBls12_381> = Value::zero(&ATyp::vec(&ATyp::g1(), n_val_const));

//     let p_initial_commitment: Value<ArkBls12_381> = Value::zero(&ATyp::g1());
//     let ip_val_claimed: Value<ArkBls12_381> = Value::<ArkBls12_381>::random(&mut rng, &ATyp::scalar());
//     let u_aux_base: Value<ArkBls12_381> = Value::zero(&ATyp::g1());

//     let a_vec_witness = Value::<ArkBls12_381>::random(&mut rng, &ATyp::vec_scalar(n_val_const));
//     let b_vec_witness = Value::<ArkBls12_381>::random(&mut rng, &ATyp::vec_scalar(n_val_const));

//     inputs.insert(Vid("g_vec".to_string()), g_vec);
//     inputs.insert(Vid("h_vec".to_string()), h_vec);
//     inputs.insert(Vid("P_initial_commitment".to_string()), p_initial_commitment);
//     inputs.insert(Vid("ip_val_claimed".to_string()), ip_val_claimed);
//     inputs.insert(Vid("u_aux_base".to_string()), u_aux_base);
//     inputs.insert(Vid("a_vec_witness".to_string()), a_vec_witness);
//     inputs.insert(Vid("b_vec_witness".to_string()), b_vec_witness);

// Schnorr working
// Accept
//     let g: Value<ArkBls12_381> = Value::G1(<ArkBls12_381 as ArkConfig>::G1::rand(&mut rng));
//  // let h: Value<ArkBls12_381> = Value::G1(<ArkBls12_381 as ArkConfig>::G1::rand(&mut rng)); un comment to break
//     let x: Value<ArkBls12_381> = Value::<ArkBls12_381>::random(&mut rng, &ATyp::scalar());
//     let h = g.clone() * x.clone(); // comment to break

//     inputs.insert(Vid("x".to_string()), x);
//     inputs.insert(Vid("g".to_string()), g);
//     inputs.insert(Vid("h".to_string()), h);

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
