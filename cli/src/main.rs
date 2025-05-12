use clap::{Subcommand, Parser};
use std::path::PathBuf;
use std::process; // For process::exit
use criterion::Criterion;
use std::{fs::{self, File}, io::Write};

use lang::ast::UModule;
use backend::ArkBls12_381;
use costs::Benchmarker;
use share::unwrap;
use graph::{
    UDags,
    analyses::{TransClos, GroebnerBuilder},
    analyses::QualifierPropagation
};

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
    Run(RunArgs),

    /// Execute the zippel analysis
    Analyze(AnalyzeArgs),

    /// Execute the benchmark suite
    Benchmark(BenchmarkArgs),
}

#[derive(Parser, Debug)]
struct RunArgs {
    /// The path to the text file to read
    #[arg(value_name = "FILE")]
    file_path: PathBuf,
}

#[derive(Parser, Debug)]
struct AnalyzeArgs {
    /// The path to the text file to read
    #[arg(value_name = "FILE")]
    file_path: PathBuf,

    /// Optional path for the pdf file
    /// If not provided, defaults to <INPUT_FILE>.pdf
    #[arg(short = 'p', long = "pdf", value_name = "PDF_FILE")]
    pdf_path_opt: Option<PathBuf>,

    /// An optional subgraphy value
    #[arg(long = "subgraph", short = 's', default_value_t = 0)] // Key part!
    subgraph: usize,
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
        Commands::Run(run_args) => {
            run(run_args);
        }
        Commands::Analyze(analyze_args) => {
            analyze(analyze_args);
        }
        Commands::Benchmark(benchmark_args) => {
            benchmark(benchmark_args);
        }
    }
}

fn analyze(args: AnalyzeArgs) {
    let zfile = fs::read_to_string(&args.file_path).unwrap_or_else(|err| {
        eprintln!("Error reading file {}: \n\t{}", args.file_path.display(), err);
        process::exit(1);
    });

    let mut pdf_path = args.pdf_path_opt.unwrap_or_else(|| {
        let mut path = args.file_path.clone();
        path.set_extension("pdf");
        path
    });
    pdf_path.set_extension("");

    println!("Parsing Zippel program: {}", zfile);
    let m = UModule::from_str(&zfile).unwrap().concretize().unwrap();
    let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));

    gs.write_pdf(&pdf_path.into_os_string().to_str().unwrap()).unwrap_or_else(|e| {
        println!("Error writing to PDF, maybe [dot] is not installed? \n\n {}", e);
    });

    assert!(args.subgraph < gs.len(), "Subgraph index out of bounds");

    // Propagate qualifiers in the DAG to all children
    let qg= QualifierPropagation::from_dag(&gs[args.subgraph]);

    println!("\n\nQualifier propagation done");

    // Create an object computing the Groebner basis
    let mut groebner = GroebnerBuilder::from_input(&qg);

    // Compute the Groebner basis
    let leaks = groebner.run();

    println!("{}", groebner);
    if leaks.is_empty() {
        println!("No leaks found");
    } else {
        println!("Leaks found:\n");
        for leak in leaks.iter() {
            println!("{}", leak);
        }
    }
}

fn run(args: RunArgs) {
    let zfile = fs::read_to_string(&args.file_path).unwrap_or_else(|err| {
        eprintln!("Error reading file {}: \n\t{}", args.file_path.display(), err);
        process::exit(1);
    });

    println!("Parsing Zippel program:\n{}", zfile);
    let m = UModule::from_str(&zfile).unwrap().concretize().unwrap();
    let mut gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
    let g = gs.pop();

    let verifier = g.get_verifier().unwrap();
    let prover = g.get_prover();

    let combined = verifier.combine_dag(&prover);

    combined.write_pdf("prover_verifier.pdf").unwrap_or_else(|e| {
        println!("Error writing to PDF, maybe [dot] is not installed? \n\n {}", e);
    });
    // TODO: Runtime
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
