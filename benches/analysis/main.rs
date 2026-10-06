//! Single-protocol analysis benchmark: completeness or special soundness.
//! Run with `--help` for the options.
//!
//! Prints JSON to stdout with timings, the shape of the generators, goals
//! and basis, and peak memory. Status is one of `ok`, `failed` (the
//! analysis did not establish the property, with the reason in `error`:
//! for completeness a verifier check that does not reduce to zero; for
//! soundness no extractor, a unit ideal, an extractor that does not
//! establish the relation, or a protocol that is not 2n+1-move for its
//! round parameters), `crashed` (a real bug/panic), `oom`, or `built` (with
//! `--build-only`).
//!
//! The goals are what the analysis checks against its basis: the verifier
//! polynomials for completeness, the relation polynomials for soundness.
//! `peak_rss_mib` is this process's peak resident memory, and
//! `singular_peak_rss_mib` that of its largest finished Singular run, absent
//! until one finishes (both `getrusage`'s `ru_maxrss`, unix only). Every JSON
//! line reports them as of that line, so a run killed at a timeout keeps its
//! last values.
//!
//! `--memory-limit-mb` caps virtual address space (`RLIMIT_AS`, unix only)
//! around `build_inputs` (ideal construction) and the GB backend calls —
//! not the whole process. See `LIMIT_ACTIVE` for the exact boundary and
//! why it's there, and `docs/DECISIONS.md` for a traced example of
//! `build_inputs` alone blowing up memory (a `where`-clause grand product).
//!
//! For batch runs across all protocols with timeout handling, use
//! `analysis_all` instead.

#![feature(alloc_error_hook)]

mod protocols;

use std::io::Write as _;
use std::path::PathBuf;
use std::sync::OnceLock;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::Instant;

use analyses::frontend::Polynomial;
use analyses::{
    CompletenessAnalysis, GbBackendKind, QualifierPropagation, SpecialSoundnessAnalysis,
};
use backend::{ArkBls12_381, ArkConfig};
use clap::{Parser, ValueEnum};
use graph::{QDag, UDags};
use lang::ast::UModule;
use lang::diagnostic::Severity;
use lang::id::Tid;
use serde::Serialize;
use share::Ctx;
use share::unwrap;

use protocols::{Analysis, PROTOCOLS};

type Poly = Polynomial<<ArkBls12_381 as ArkConfig>::F>;

/// True from right before `build_inputs` (ideal construction) to right
/// after the last GB backend call returns — the memory-constrained window.
/// That call is `from_inputs` for completeness, and `run` for soundness,
/// which computes a second (validity) basis. Parsing/concretizing/DAG
/// construction before it, and completeness's verifier-polynomial `run()`
/// after it, are unbounded: a failure there is unambiguously a real bug.
/// Read by `main`'s panic catch to decide `"crashed"` (panic outside this
/// window) vs `"oom"` (inside it). Under the limit, running out of memory
/// can also surface as a panic, e.g. a Singular that cannot start or dies
/// trips the backend's `expect`, so the window's panics are all `"oom"`.
/// For soundness that includes the extractor search between its two GB
/// calls.
static LIMIT_ACTIVE: AtomicBool = AtomicBool::new(false);

/// The final JSON line to print on a hard allocator abort, pre-built (while
/// allocation still works) before the memory limit goes into effect. The
/// allocation-error hook below must not allocate, so this is the only way
/// it can report anything.
static OOM_LINE: OnceLock<Vec<u8>> = OnceLock::new();

/// Allocation-error hook: writes the pre-built [`OOM_LINE`] (if any) with no
/// further allocation, then aborts — same as the default hook, but leaves a
/// real status line on stdout for `analysis_all` to pick up instead of a
/// silent death.
fn oom_alloc_error_hook(_layout: std::alloc::Layout) {
    if let Some(line) = OOM_LINE.get() {
        let mut out = std::io::stdout();
        let _ = out.write_all(line);
        let _ = out.write_all(b"\n");
        let _ = out.flush();
    }
    std::process::abort();
}

/// Cap the process's virtual address space at `limit_mb` megabytes
/// (`RLIMIT_AS`), inherited by child processes (e.g. Singular). Only
/// lowers the *soft* limit, leaving the hard limit untouched, so it can be
/// raised back via [`restore_memory_limit`] — lowering both would be a
/// one-way ratchet. Returns the previous soft limit on success, `None` if
/// the limit wasn't applied.
#[cfg(unix)]
fn apply_memory_limit(limit_mb: u64) -> Option<u64> {
    let bytes = limit_mb.saturating_mul(1024 * 1024) as libc::rlim_t;

    let mut current = libc::rlimit {
        rlim_cur: 0,
        rlim_max: 0,
    };
    if unsafe { libc::getrlimit(libc::RLIMIT_AS, &raw mut current) } != 0 {
        eprintln!(
            "warning: failed to read current memory limit: {}",
            std::io::Error::last_os_error()
        );
        return None;
    }

    let limit = libc::rlimit {
        rlim_cur: bytes.min(current.rlim_max),
        rlim_max: current.rlim_max,
    };
    if unsafe { libc::setrlimit(libc::RLIMIT_AS, &raw const limit) } == 0 {
        Some(current.rlim_cur)
    } else {
        eprintln!(
            "warning: failed to set {limit_mb} MB memory limit: {}",
            std::io::Error::last_os_error()
        );
        None
    }
}

#[cfg(not(unix))]
fn apply_memory_limit(limit_mb: u64) -> Option<u64> {
    eprintln!("warning: --memory-limit-mb is only supported on unix; ignoring {limit_mb} MB limit");
    None
}

/// Restore a soft `RLIMIT_AS` previously returned by [`apply_memory_limit`].
/// Best-effort: if it fails, the process just stays under the tighter
/// limit for the rest of its (already nearly-finished) run.
#[cfg(unix)]
fn restore_memory_limit(previous_soft: u64) {
    let mut current = libc::rlimit {
        rlim_cur: 0,
        rlim_max: 0,
    };
    if unsafe { libc::getrlimit(libc::RLIMIT_AS, &raw mut current) } != 0 {
        return;
    }
    let limit = libc::rlimit {
        rlim_cur: previous_soft as libc::rlim_t,
        rlim_max: current.rlim_max,
    };
    let _ = unsafe { libc::setrlimit(libc::RLIMIT_AS, &raw const limit) };
}

#[cfg(not(unix))]
fn restore_memory_limit(_previous_soft: u64) {}

/// The memory-constrained window (see `LIMIT_ACTIVE`): opened before
/// `build_inputs`, closed after the last GB backend call.
struct MemoryWindow {
    /// The soft limit to restore on close, if a limit was applied.
    previous: Option<u64>,
}

impl MemoryWindow {
    /// Applies `limit_mb`, if any, after pre-building the OOM line for
    /// `protocol`.
    fn open(protocol: &str, limit_mb: Option<u64>) -> Self {
        let Some(limit_mb) = limit_mb else {
            return Self { previous: None };
        };
        let oom_line = serde_json::to_string(&BenchOutput {
            protocol: protocol.to_string(),
            status: "oom".to_string(),
            ..Default::default()
        })
        .unwrap()
        .into_bytes();
        let _ = OOM_LINE.set(oom_line);

        let previous = apply_memory_limit(limit_mb);
        if previous.is_some() {
            LIMIT_ACTIVE.store(true, Ordering::SeqCst);
        }
        Self { previous }
    }

    /// Restores the previous limit. Closing twice is a no-op.
    fn close(&mut self) {
        if let Some(previous) = self.previous.take() {
            restore_memory_limit(previous);
            LIMIT_ACTIVE.store(false, Ordering::SeqCst);
        }
    }
}

/// Peak resident memory in MiB, from `getrusage`'s `ru_maxrss`: of this
/// process, or with `children` of its largest finished child (a Singular
/// run), `None` while no child has finished.
#[cfg(unix)]
fn peak_rss_mib(children: bool) -> Option<u64> {
    let who = if children {
        libc::RUSAGE_CHILDREN
    } else {
        libc::RUSAGE_SELF
    };
    let mut usage: libc::rusage = unsafe { std::mem::zeroed() };
    if unsafe { libc::getrusage(who, &raw mut usage) } != 0 {
        return None;
    }
    let maxrss = u64::try_from(usage.ru_maxrss).ok()?;
    if children && maxrss == 0 {
        return None;
    }
    // `ru_maxrss` is in bytes on macOS and in KiB elsewhere.
    let bytes = if cfg!(target_os = "macos") {
        maxrss
    } else {
        maxrss * 1024
    };
    Some(bytes / (1024 * 1024))
}

#[cfg(not(unix))]
fn peak_rss_mib(_children: bool) -> Option<u64> {
    None
}

/// JSON output emitted by the `analysis` bench. Partial lines (status
/// `"running"`) omit fields that aren't available yet. The final line
/// has the definitive status and all metrics.
#[derive(Serialize, Default)]
struct BenchOutput {
    protocol: String,
    status: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    build_ms: Option<f64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    gb_ms: Option<f64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    run_ms: Option<f64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    basis_size: Option<usize>,
    #[serde(skip_serializing_if = "Option::is_none")]
    max_degree: Option<usize>,
    #[serde(skip_serializing_if = "Option::is_none")]
    num_vars: Option<usize>,
    #[serde(skip_serializing_if = "Option::is_none")]
    graph_size: Option<usize>,
    #[serde(skip_serializing_if = "Option::is_none")]
    gen_set_size: Option<usize>,
    #[serde(skip_serializing_if = "Option::is_none")]
    gen_set_max_degree: Option<usize>,
    #[serde(skip_serializing_if = "Option::is_none")]
    gen_set_num_vars: Option<usize>,
    /// Terms over all generators.
    #[serde(skip_serializing_if = "Option::is_none")]
    gen_set_terms: Option<usize>,
    /// Terms of the largest generator.
    #[serde(skip_serializing_if = "Option::is_none")]
    gen_set_max_terms: Option<usize>,
    #[serde(skip_serializing_if = "Option::is_none")]
    goals: Option<usize>,
    #[serde(skip_serializing_if = "Option::is_none")]
    goal_max_degree: Option<usize>,
    /// Terms of the largest goal.
    #[serde(skip_serializing_if = "Option::is_none")]
    goal_max_terms: Option<usize>,
    #[serde(skip_serializing_if = "Option::is_none")]
    peak_rss_mib: Option<u64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    singular_peak_rss_mib: Option<u64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    error: Option<String>,
}

impl BenchOutput {
    /// Records the shape of the generating set and of the goals.
    fn record_inputs(&mut self, generators: &[Poly], goals: &[Poly]) {
        let generators = Shape::of(generators);
        self.gen_set_size = Some(generators.size);
        self.gen_set_max_degree = Some(generators.max_degree);
        self.gen_set_num_vars = Some(generators.num_vars);
        self.gen_set_terms = Some(generators.terms);
        self.gen_set_max_terms = Some(generators.max_terms);
        let goals = Shape::of(goals);
        self.goals = Some(goals.size);
        self.goal_max_degree = Some(goals.max_degree);
        self.goal_max_terms = Some(goals.max_terms);
    }

    /// Records the Gröbner basis's size, degree and number of variables.
    fn record_basis(&mut self, basis: &[Poly]) {
        let basis = Shape::of(basis);
        self.basis_size = Some(basis.size);
        self.max_degree = Some(basis.max_degree);
        self.num_vars = Some(basis.num_vars);
    }

    /// Records peak memory so far.
    fn record_memory(&mut self) {
        self.peak_rss_mib = peak_rss_mib(false);
        self.singular_peak_rss_mib = peak_rss_mib(true);
    }

    /// Sets the final status, with the error that explains it.
    fn finish(&mut self, status: &str, error: Option<String>) {
        self.status = status.to_string();
        self.error = error;
    }
}

/// Size measures of a list of polynomials, leaving out zero ones: they add
/// nothing to an ideal, and both analyses skip zero goals.
struct Shape {
    size: usize,
    max_degree: usize,
    num_vars: usize,
    terms: usize,
    max_terms: usize,
}

impl Shape {
    fn of(polys: &[Poly]) -> Self {
        let polys: Vec<&Poly> = polys.iter().filter(|p| !p.is_zero()).collect();
        Self {
            size: polys.len(),
            max_degree: polys.iter().map(|p| p.degree()).max().unwrap_or(0),
            num_vars: polys
                .iter()
                .flat_map(|p| p.vars().into_iter())
                .collect::<share::Set<analyses::Var>>()
                .len(),
            terms: polys.iter().map(|p| p.terms.len()).sum(),
            max_terms: polys.iter().map(|p| p.terms.len()).max().unwrap_or(0),
        }
    }
}

/// Prints `output` as one JSON line, with peak memory so far.
fn emit(output: &mut BenchOutput) {
    output.record_memory();
    println!("{}", serde_json::to_string(output).unwrap());
    let _ = std::io::stdout().flush();
}

fn elapsed_ms(start: Instant) -> f64 {
    start.elapsed().as_secs_f64() * 1000.0
}

fn build_sizes_ctx(sizes: &[(String, usize)]) -> Ctx<Tid, usize> {
    let mut ctx = Ctx::new();
    for (name, value) in sizes {
        ctx.insert(&Tid::new(name), value);
    }
    ctx
}

/// What to analyse: a registered protocol, or a file given with `--path`,
/// with any `--size` and `--l-vec` overrides applied.
struct Target {
    name: String,
    path: PathBuf,
    sizes: Vec<(String, usize)>,
    /// Special-soundness round parameters; `None` when neither registered
    /// nor given with `--l-vec`.
    l_vec: Option<Vec<usize>>,
}

fn run_bench(
    target: &Target,
    analysis: Analysis,
    backend: GbBackendKind,
    memory_limit_mb: Option<u64>,
    build_only: bool,
) -> String {
    let name = target.name.as_str();
    let source = match std::fs::read_to_string(&target.path) {
        Ok(s) => s,
        Err(e) => return json_error(name, &format!("read failed: {e}")),
    };

    let (module, diags) = UModule::parse(&source);
    let has_errors = diags.iter().any(|d| d.severity == Severity::Error);
    if has_errors {
        return json_error(name, "parse errors");
    }
    let Some(module) = module else {
        return json_error(name, "no module");
    };

    let params = module.size_params();
    for (n, _) in &target.sizes {
        if !params.contains(&Tid::new(n)) {
            eprintln!("warning: {name} has no size parameter {n}; ignoring it");
        }
    }

    let ctx = build_sizes_ctx(&target.sizes);
    let concrete = match module.concretize(&ctx) {
        Ok(c) => c,
        Err(e) => return json_error(name, &format!("concretize failed: {e}")),
    };

    let gs = unwrap!(UDags::<ArkBls12_381>::from_module(concrete));
    let proto = gs
        .protocols()
        .into_iter()
        .next()
        .expect("no protocol found");
    let dag = QualifierPropagation::from_dag(proto);

    // Stage 1: Emit graph_size — available before any analysis.
    let mut out = BenchOutput {
        protocol: name.to_string(),
        status: "running".to_string(),
        graph_size: Some(dag.node_count()),
        ..Default::default()
    };
    emit(&mut out);

    let mut window = MemoryWindow::open(name, memory_limit_mb);
    match analysis {
        Analysis::Completeness => {
            run_completeness(&dag, backend, build_only, &mut out, &mut window);
        }
        Analysis::Soundness => {
            let l_vec = target
                .l_vec
                .clone()
                .expect("main checks that soundness has round parameters");
            run_soundness(&dag, l_vec, backend, build_only, &mut out, &mut window);
        }
    }
    window.close();

    out.record_memory();
    serde_json::to_string(&out).unwrap()
}

/// Stages 2–4 of a completeness run, recorded in `out`.
fn run_completeness(
    dag: &QDag<ArkBls12_381>,
    backend: GbBackendKind,
    build_only: bool,
    out: &mut BenchOutput,
    window: &mut MemoryWindow,
) {
    // Stage 2: Build inputs, compute pre-GB metrics, emit.
    let start = Instant::now();
    let inputs = CompletenessAnalysis::<ArkBls12_381>::build_inputs(dag);
    out.build_ms = Some(elapsed_ms(start));
    out.record_inputs(&inputs.generating_set, &inputs.verifier);
    emit(out);
    if build_only {
        out.finish("built", None);
        return;
    }

    // Stage 3: Compute GB (expensive — may hang).
    let start = Instant::now();
    let mut ca = CompletenessAnalysis::<ArkBls12_381>::from_inputs(inputs, backend);
    out.gb_ms = Some(elapsed_ms(start));

    // See LIMIT_ACTIVE: the memory-constrained window ends here.
    window.close();

    // Emit post-GB metrics before run() — survives if run() hangs or is killed.
    out.record_basis(&ca.basis.polys);
    emit(out);

    // Stage 4: Reduce the verifier's checks.
    let start = Instant::now();
    let result = ca.run();
    out.run_ms = Some(elapsed_ms(start));
    match result {
        Ok(()) => out.finish("ok", None),
        Err(e) => out.finish("failed", Some(format!("{e}"))),
    }
}

/// Stages 2–4 of a special-soundness run, recorded in `out`.
fn run_soundness(
    dag: &QDag<ArkBls12_381>,
    l_vec: Vec<usize>,
    backend: GbBackendKind,
    build_only: bool,
    out: &mut BenchOutput,
    window: &mut MemoryWindow,
) {
    // Stage 2: Build inputs, compute pre-GB metrics, emit.
    let start = Instant::now();
    let inputs = SpecialSoundnessAnalysis::<ArkBls12_381>::build_inputs(dag, l_vec);
    out.build_ms = Some(elapsed_ms(start));
    let inputs = match inputs {
        Ok(inputs) => inputs,
        Err(e) => {
            out.finish("failed", Some(format!("{e}")));
            return;
        }
    };
    out.record_inputs(
        &inputs.generating_set,
        &inputs.grev_rel_result.generating_set,
    );
    emit(out);
    if build_only {
        out.finish("built", None);
        return;
    }

    // Stage 3: Compute the search GB (expensive — may hang).
    let start = Instant::now();
    let sa = SpecialSoundnessAnalysis::<ArkBls12_381>::from_inputs(inputs, backend);
    out.gb_ms = Some(elapsed_ms(start));
    let mut sa = match sa {
        Ok(sa) => sa,
        Err(e) => {
            out.finish("failed", Some(format!("{e}")));
            return;
        }
    };

    // Emit post-GB metrics before run() — survives if run() hangs or is killed.
    out.record_basis(&sa.search_gb.polys);
    emit(out);

    // Stage 4: Extract witnesses and check them against the validity GB.
    let start = Instant::now();
    let result = sa.run();
    out.run_ms = Some(elapsed_ms(start));

    // See LIMIT_ACTIVE: the memory-constrained window ends here.
    window.close();

    match result {
        Ok(()) => out.finish("ok", None),
        Err(e) => out.finish("failed", Some(format!("{e}"))),
    }
}

fn json_error(name: &str, error: &str) -> String {
    serde_json::to_string(&BenchOutput {
        protocol: name.to_string(),
        status: "crashed".to_string(),
        error: Some(error.to_string()),
        ..Default::default()
    })
    .unwrap()
}

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
    /// Caps virtual address space while the ideal is built and its bases
    /// computed (unix only).
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

fn main() {
    let cli = Cli::parse();
    let analysis = cli.analysis;

    if cli.list {
        for p in PROTOCOLS.iter().filter(|p| p.runs(analysis)) {
            println!("{}", p.name);
        }
        return;
    }
    let protocol_name = cli
        .protocol
        .as_deref()
        .expect("clap requires a protocol without --list");

    // A registered protocol supplies the source, sizes and round parameters;
    // `--path`, `--size` and `--l-vec` replace what they name.
    let registered = protocols::find(protocol_name);
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
    if analysis == Analysis::Soundness && l_vec.is_none() {
        eprintln!("{protocol_name} has no registered soundness round parameters; pass --l-vec");
        std::process::exit(2);
    }
    let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let path = match (cli.path, registered) {
        (Some(p), _) => p,
        (None, Some(p)) => manifest.join(p.path),
        (None, None) => {
            eprintln!("unknown protocol: {protocol_name} (pass --path to analyse a file)");
            std::process::exit(2);
        }
    };
    let target = Target {
        name: protocol_name.to_string(),
        path,
        sizes,
        l_vec,
    };

    std::alloc::set_alloc_error_hook(oom_alloc_error_hook);

    // Run in a thread with a large stack to avoid stack overflow.
    let protocol_clone = target.name.clone();
    let backend = match cli.backend {
        Backend::Singular => GbBackendKind::Singular,
        Backend::Default => GbBackendKind::default(),
    };
    let (memory_limit_mb, build_only) = (cli.memory_limit_mb, cli.build_only);
    let result = share::thread::run("analysis-bench", move || {
        run_bench(&target, analysis, backend, memory_limit_mb, build_only)
    })
    .unwrap_or_else(|payload| {
        let message = payload
            .downcast_ref::<String>()
            .cloned()
            .or_else(|| payload.downcast_ref::<&str>().map(|s| (*s).to_string()))
            .unwrap_or_else(|| "thread panicked".to_string());
        // See LIMIT_ACTIVE for what this checks.
        let status = if LIMIT_ACTIVE.load(Ordering::SeqCst) {
            "oom"
        } else {
            "crashed"
        };
        serde_json::to_string(&BenchOutput {
            protocol: protocol_clone,
            status: status.to_string(),
            error: Some(message),
            ..Default::default()
        })
        .unwrap()
    });

    println!("{result}");
}
