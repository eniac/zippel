//! Single-protocol analysis benchmark: completeness or special soundness.
//! Run with `--help` for the options.
//!
//! Prints JSON lines to stdout with timings, the shape of the generators,
//! goals and basis, and peak memory (see `output.rs`); the last line has the
//! final status (`output::Status`). `--memory-limit-mb` bounds only the
//! analysis, not parsing or lowering (see `memory.rs`).
//!
//! For batch runs across all protocols with timeout handling, use
//! `analysis_all` instead.

#![feature(alloc_error_hook)]

mod memory;
mod output;
mod protocols;

use std::any::Any;
use std::fmt::Write as _;
use std::fs::OpenOptions;
use std::io::Write as _;
use std::path::{Path, PathBuf};
use std::time::Instant;

use analyses::{
    CompletenessAnalysis, GbBackendKind, QualifierPropagation, SpecialSoundnessAnalysis,
};
use backend::ArkBls12_381;
use clap::{Parser, ValueEnum};
use graph::{QDag, UDags};
use lang::ast::UModule;
use lang::diagnostic::Severity;
use lang::id::Tid;
use share::unwrap;

use memory::MemoryWindow;
use output::{BenchOutput, Poly, Status};
use protocols::{Analysis, PROTOCOLS};

/// Analyses one protocol and prints JSON lines with what it measured.
#[derive(Parser)]
#[command(name = "analysis", bin_name = "analysis")]
struct Cli {
    /// The protocol: a registered name, or any name with `--path`.
    #[arg(required_unless_present = "list")]
    protocol: Option<String>,
    #[arg(long, value_enum, default_value_t = Analysis::Completeness)]
    analysis: Analysis,
    #[arg(long, value_enum, default_value_t = Backend::Default)]
    backend: Backend,
    /// Caps virtual address space while the analysis runs (unix only).
    #[arg(long, value_name = "MB")]
    memory_limit_mb: Option<u64>,
    /// Analyses FILE instead of the protocol's registered source.
    #[arg(long, value_name = "FILE")]
    path: Option<PathBuf>,
    /// Sets one size, replacing the registered value. A name the protocol
    /// has no size parameter for is ignored, with a warning.
    #[arg(long = "size", value_name = "NAME=VALUE", value_parser = parse_size)]
    sizes: Vec<(String, usize)>,
    /// The special-soundness round parameters, one per challenge round,
    /// replacing the registered ones.
    #[arg(long, value_name = "L1,L2,...", value_delimiter = ',')]
    l_vec: Option<Vec<usize>>,
    /// Stops after building the ideal, without running the GB backend.
    #[arg(long)]
    build_only: bool,
    /// Completeness only: writes the generating set and the goals to FILE
    /// before the GB backend runs, and appends the result and why each check
    /// holds (`CompletenessAnalysis::explain`) after it. Explaining reduces
    /// every check, so a run with `--dump` can take longer and use more
    /// memory than one without.
    #[arg(long, value_name = "FILE")]
    dump: Option<PathBuf>,
    /// Prints the protocols registered for the analysis, one per line, and
    /// exits; `analysis_all` sweeps those.
    #[arg(long)]
    list: bool,
    /// Added by `cargo bench`, even with `harness = false`.
    #[arg(long = "bench", hide = true)]
    _bench: bool,
}

/// The value of `--backend`.
#[derive(Clone, Copy, ValueEnum)]
enum Backend {
    #[value(alias = "Singular")]
    Singular,
    Default,
}

/// Parses a `--size` value, `NAME=VALUE`.
fn parse_size(spec: &str) -> Result<(String, usize), String> {
    let (name, value) = spec.split_once('=').ok_or("expected NAME=VALUE")?;
    let value = value.trim().parse().map_err(|e| format!("{e}"))?;
    Ok((name.trim().to_string(), value))
}

/// One run: what to analyse, and how.
struct Target {
    name: String,
    path: PathBuf,
    sizes: Vec<(String, usize)>,
    /// Special-soundness round parameters; always set for soundness.
    l_vec: Option<Vec<usize>>,
    analysis: Analysis,
    backend: GbBackendKind,
    memory_limit_mb: Option<u64>,
    build_only: bool,
    dump: Option<PathBuf>,
}

impl Target {
    /// A registered protocol supplies the source, sizes and round
    /// parameters; `--path`, `--size` and `--l-vec` replace what they name.
    /// Exits on a protocol it cannot resolve.
    fn resolve(cli: Cli) -> Self {
        let name = cli
            .protocol
            .expect("clap requires a protocol without --list");
        let registered = protocols::find(&name);

        let mut sizes: Vec<(String, usize)> = registered
            .map(|p| p.sizes.iter().map(|&(n, v)| (n.to_string(), v)).collect())
            .unwrap_or_default();
        for (n, v) in cli.sizes {
            match sizes.iter_mut().find(|(m, _)| *m == n) {
                Some(slot) => slot.1 = v,
                None => sizes.push((n, v)),
            }
        }

        let l_vec = cli
            .l_vec
            .or_else(|| registered.and_then(|p| p.soundness.map(<[usize]>::to_vec)));
        if cli.analysis == Analysis::Soundness && l_vec.is_none() {
            eprintln!("{name} has no registered soundness round parameters; pass --l-vec");
            std::process::exit(2);
        }
        if cli.analysis == Analysis::Soundness && cli.dump.is_some() {
            eprintln!("--dump is only supported for completeness");
            std::process::exit(2);
        }

        let path = match (cli.path, registered) {
            (Some(p), _) => p,
            (None, Some(p)) => PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(p.path),
            (None, None) => {
                eprintln!("unknown protocol: {name} (pass --path to analyse a file)");
                std::process::exit(2);
            }
        };

        Self {
            name,
            path,
            sizes,
            l_vec,
            analysis: cli.analysis,
            backend: match cli.backend {
                Backend::Singular => GbBackendKind::Singular,
                Backend::Default => GbBackendKind::default(),
            },
            memory_limit_mb: cli.memory_limit_mb,
            build_only: cli.build_only,
            dump: cli.dump,
        }
    }
}

/// Writes `text` to the dump file `path`, truncating it first unless
/// `append`. A failure is reported on stderr and otherwise ignored: the dump
/// is a side channel, not part of the measurement.
fn write_dump(path: &Path, text: &str, append: bool) {
    let result = OpenOptions::new()
        .create(true)
        .write(true)
        .append(append)
        .truncate(!append)
        .open(path)
        .and_then(|mut f| f.write_all(text.as_bytes()));
    if let Err(e) = result {
        eprintln!("warning: failed to write dump {}: {e}", path.display());
    }
}

/// What a dump starts with: the protocol, its sizes and its source, then
/// each of `sections`, a title and its polynomials, one per line.
fn dump_inputs(target: &Target, sections: &[(&str, &[Poly])]) -> String {
    let mut text = format!(
        "{} sizes={:?}\n{}\n",
        target.name,
        target.sizes,
        target.path.display()
    );
    for (title, polys) in sections {
        let _ = writeln!(text, "\n{title} ({}):", polys.len());
        for p in *polys {
            let _ = writeln!(text, "  {p}");
        }
    }
    text
}

/// Parses, concretizes and lowers the target's source to its first
/// protocol's DAG.
fn load_dag(target: &Target) -> Result<QDag<ArkBls12_381>, String> {
    let source = std::fs::read_to_string(&target.path).map_err(|e| format!("read failed: {e}"))?;

    let (module, diags) = UModule::parse(&source);
    if diags.iter().any(|d| d.severity == Severity::Error) {
        return Err("parse errors".to_string());
    }
    let module = module.ok_or("no module")?;

    let params = module.size_params();
    for (n, _) in &target.sizes {
        if !params.contains(&Tid::new(n)) {
            eprintln!(
                "warning: {} has no size parameter {n}; ignoring it",
                target.name
            );
        }
    }
    let ctx = target
        .sizes
        .iter()
        .map(|(n, v)| (Tid::new(n), *v))
        .collect();
    let concrete = module
        .concretize(&ctx)
        .map_err(|e| format!("concretize failed: {e}"))?;

    let gs = unwrap!(UDags::<ArkBls12_381>::from_module(concrete));
    let proto = gs
        .protocols()
        .into_iter()
        .next()
        .expect("no protocol found");
    Ok(QualifierPropagation::from_dag(proto))
}

/// Runs the target, printing partial lines, and returns the final line.
fn run_bench(target: &Target) -> String {
    let name = target.name.as_str();
    let dag = match load_dag(target) {
        Ok(dag) => dag,
        Err(e) => return BenchOutput::line(name, Status::Crashed, Some(e)),
    };

    // Stage 1: Emit graph_size — available before any analysis.
    let mut out = BenchOutput::new(name, dag.node_count());
    out.emit();

    // Closed explicitly, not on drop: unwinding from a panic would clear
    // `LIMIT_ACTIVE` before `main` reads it.
    let oom_line = BenchOutput::line(name, Status::Oom, None);
    let mut window = MemoryWindow::open(target.memory_limit_mb, oom_line);
    let result = match target.analysis {
        Analysis::Completeness => run_completeness(&dag, target, &mut out),
        Analysis::Soundness => run_soundness(&dag, target, &mut out),
    };
    window.close();

    match result {
        Ok(status) => out.finish(status, None),
        Err(e) => out.finish(Status::Failed, Some(e)),
    }
    out.into_line()
}

/// Stages 2–4 of a completeness run, recorded in `out`. Returns the
/// status, or the error that makes the run `failed`.
fn run_completeness(
    dag: &QDag<ArkBls12_381>,
    target: &Target,
    out: &mut BenchOutput,
) -> Result<Status, String> {
    // Stage 2: Build inputs, compute pre-GB metrics, emit.
    let start = Instant::now();
    let inputs = CompletenessAnalysis::<ArkBls12_381>::build_inputs(dag);
    out.build_ms = Some(elapsed_ms(start));
    out.record_inputs(&inputs.generating_set, &inputs.verifier);
    out.emit();
    // Written before the GB call, so it survives a timeout.
    if let Some(dump) = &target.dump {
        let sections = [
            ("generating set", inputs.generating_set.as_slice()),
            ("goals", inputs.verifier.as_slice()),
        ];
        write_dump(dump, &dump_inputs(target, &sections), false);
    }
    if target.build_only {
        return Ok(Status::Built);
    }

    // Stage 3: Compute GB (expensive — may hang).
    let start = Instant::now();
    let mut ca = CompletenessAnalysis::<ArkBls12_381>::from_inputs(inputs, target.backend);
    out.gb_ms = Some(elapsed_ms(start));

    // Emit post-GB metrics before run() — survives if run() hangs or is killed.
    out.record_basis(&ca.basis.polys);
    out.emit();

    // Stage 4: Reduce the verifier's checks.
    let start = Instant::now();
    let result = ca.run().map_err(|e| e.to_string());
    out.run_ms = Some(elapsed_ms(start));

    if let Some(dump) = &target.dump {
        let verdict = result.as_ref().err().map_or("complete", String::as_str);
        let text = format!("\nresult: {verdict}\n\nexplain:\n{}", ca.explain());
        write_dump(dump, &text, true);
    }
    result?;
    Ok(Status::Ok)
}

/// Stages 2–4 of a special-soundness run, recorded in `out`. Returns the
/// status, or the error that makes the run `failed`.
fn run_soundness(
    dag: &QDag<ArkBls12_381>,
    target: &Target,
    out: &mut BenchOutput,
) -> Result<Status, String> {
    let l_vec = target
        .l_vec
        .clone()
        .expect("`Target::resolve` sets round parameters for soundness");

    // Stage 2: Build inputs, compute pre-GB metrics, emit.
    let start = Instant::now();
    let inputs = SpecialSoundnessAnalysis::<ArkBls12_381>::build_inputs(dag, l_vec);
    out.build_ms = Some(elapsed_ms(start));
    let inputs = inputs.map_err(|e| e.to_string())?;
    out.record_inputs(
        &inputs.generating_set,
        &inputs.grev_rel_result.generating_set,
    );
    out.emit();
    if target.build_only {
        return Ok(Status::Built);
    }

    // Stage 3: Compute the search GB (expensive — may hang).
    let start = Instant::now();
    let sa = SpecialSoundnessAnalysis::<ArkBls12_381>::from_inputs(inputs, target.backend);
    out.gb_ms = Some(elapsed_ms(start));
    let mut sa = sa.map_err(|e| e.to_string())?;

    // Emit post-GB metrics before run() — survives if run() hangs or is killed.
    out.record_basis(&sa.search_gb.polys);
    out.emit();

    // Stage 4: Extract witnesses and check them against the validity GB.
    let start = Instant::now();
    let result = sa.run();
    out.run_ms = Some(elapsed_ms(start));
    result.map_err(|e| e.to_string())?;
    Ok(Status::Ok)
}

fn elapsed_ms(start: Instant) -> f64 {
    start.elapsed().as_secs_f64() * 1000.0
}

/// The message a panic was raised with.
fn panic_message(payload: &(dyn Any + Send)) -> String {
    payload
        .downcast_ref::<String>()
        .cloned()
        .or_else(|| payload.downcast_ref::<&str>().map(|s| (*s).to_string()))
        .unwrap_or_else(|| "thread panicked".to_string())
}

fn main() {
    let cli = Cli::parse();
    if cli.list {
        for p in PROTOCOLS.iter().filter(|p| p.runs(cli.analysis)) {
            println!("{}", p.name);
        }
        return;
    }
    let target = Target::resolve(cli);
    let name = target.name.clone();

    memory::install_oom_hook();
    // Run in a thread with a large stack to avoid stack overflow.
    let result = share::thread::run("analysis-bench", move || run_bench(&target)).unwrap_or_else(
        |payload| {
            // See `memory::LIMIT_ACTIVE` for what this checks.
            let status = if memory::limit_active() {
                Status::Oom
            } else {
                Status::Crashed
            };
            BenchOutput::line(&name, status, Some(panic_message(&*payload)))
        },
    );
    println!("{result}");
}
