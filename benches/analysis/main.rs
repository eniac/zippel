//! Single-protocol analysis benchmark: completeness or special soundness.
//!
//! Usage:
//!   analysis [--analysis completeness|soundness] [--backend singular|default]
//!            [--memory-limit-mb MB] [--path FILE] [--size NAME=VALUE]...
//!            [--l-vec L1,L2,...] [--dump FILE] [--build-only] <`protocol_name`>
//!   analysis [--analysis completeness|soundness] --list
//!
//! Prints JSON to stdout with timing and basis size. Status is one of `ok`,
//! `incomplete` (completeness), `failed` (soundness: no extractor, a unit
//! ideal, or a protocol that is not 2n+1-move for its round parameters),
//! `crashed` (a real bug/panic), `oom`, or `built` (with `--build-only`).
//!
//! - `--analysis` defaults to `completeness`.
//! - `--list` prints the protocols registered for the analysis, one per
//!   line, and exits; `analysis_all` sweeps those.
//! - `--path FILE` analyses `FILE` instead of the protocol's registered
//!   source; the name then need not be registered.
//! - `--size NAME=VALUE` sets one size, replacing the registered value.
//! - `--l-vec L1,L2,...` sets the special-soundness round parameters, one
//!   per challenge round, replacing the registered ones (see `protocols.rs`).
//! - `--dump FILE` writes the generating set to `FILE` before the Gröbner
//!   basis computation, and appends the result after it: for completeness,
//!   the generators grouped by origin (`CompletenessInputs::describe`) and
//!   `CompletenessAnalysis::explain`; for soundness, the search basis.
//! - `--build-only` stops after building the ideal, without running the GB
//!   backend.
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

use std::fs::OpenOptions;
use std::io::Write as _;
use std::path::{Path, PathBuf};
use std::sync::OnceLock;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::Instant;

use analyses::frontend::Polynomial;
use analyses::{
    CompletenessAnalysis, GbBackendKind, QualifierPropagation, SpecialSoundnessAnalysis,
};
use backend::{ArkBls12_381, ArkConfig};
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
/// window) vs `"oom"` (inside it).
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
    #[serde(skip_serializing_if = "Option::is_none")]
    error: Option<String>,
}

impl BenchOutput {
    /// Records the generating set's size, degree and number of variables.
    fn record_generators(&mut self, generators: &[Poly]) {
        let (size, degree, vars) = shape(generators);
        self.gen_set_size = Some(size);
        self.gen_set_max_degree = Some(degree);
        self.gen_set_num_vars = Some(vars);
    }

    /// Records the Gröbner basis's size, degree and number of variables.
    fn record_basis(&mut self, basis: &[Poly]) {
        let (size, degree, vars) = shape(basis);
        self.basis_size = Some(size);
        self.max_degree = Some(degree);
        self.num_vars = Some(vars);
    }

    /// Sets the final status, with the error that explains it.
    fn finish(&mut self, status: &str, error: Option<String>) {
        self.status = status.to_string();
        self.error = error;
    }
}

/// The number of polynomials, their maximum degree, and how many variables
/// they mention.
fn shape(polys: &[Poly]) -> (usize, usize, usize) {
    let degree = polys.iter().map(Poly::degree).max().unwrap_or(0);
    let vars = polys
        .iter()
        .flat_map(|p| p.vars().into_iter())
        .collect::<share::Set<analyses::Var>>()
        .len();
    (polys.len(), degree, vars)
}

fn emit(output: &BenchOutput) {
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

/// Options that only affect what the run reports or how far it goes.
struct Diagnostics {
    dump: Option<PathBuf>,
    build_only: bool,
}

/// Write `text` to the dump file, appending after the first write. Failures
/// are reported on stderr and otherwise ignored: the dump is a side channel.
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

/// The first lines of a dump: what was analysed, and how.
fn dump_header(target: &Target, analysis: Analysis) -> String {
    format!(
        "{} {} sizes={:?}\n{}\n",
        target.name,
        analysis.name(),
        target.sizes,
        target.path.display()
    )
}

/// `title`, then one polynomial per line.
fn listing(title: &str, polys: &[Poly]) -> String {
    use std::fmt::Write as _;

    let mut text = format!("{title} ({}):\n", polys.len());
    for p in polys {
        let _ = writeln!(text, "  {p}");
    }
    text
}

fn run_bench(
    target: &Target,
    analysis: Analysis,
    backend: GbBackendKind,
    memory_limit_mb: Option<u64>,
    diagnostics: &Diagnostics,
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
    emit(&out);

    let mut window = MemoryWindow::open(name, memory_limit_mb);
    match analysis {
        Analysis::Completeness => {
            run_completeness(&dag, target, backend, diagnostics, &mut out, &mut window);
        }
        Analysis::Soundness => {
            run_soundness(&dag, target, backend, diagnostics, &mut out, &mut window);
        }
    }
    window.close();

    serde_json::to_string(&out).unwrap()
}

/// Stages 2–4 of a completeness run, recorded in `out`.
fn run_completeness(
    dag: &QDag<ArkBls12_381>,
    target: &Target,
    backend: GbBackendKind,
    diagnostics: &Diagnostics,
    out: &mut BenchOutput,
    window: &mut MemoryWindow,
) {
    // Stage 2: Build inputs, compute pre-GB metrics, emit.
    let start = Instant::now();
    let inputs = CompletenessAnalysis::<ArkBls12_381>::build_inputs(dag);
    out.build_ms = Some(elapsed_ms(start));
    out.record_generators(&inputs.generating_set);
    emit(out);

    // Written before the GB call, so it survives a timeout.
    if let Some(dump) = &diagnostics.dump {
        let header = dump_header(target, Analysis::Completeness);
        write_dump(dump, &(header + &inputs.describe()), false);
    }
    if diagnostics.build_only {
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
        Err(e) => out.finish("incomplete", Some(format!("{e}"))),
    }

    if let Some(dump) = &diagnostics.dump {
        let text = format!(
            "\n---- result: {} ----\n{}\n---- explain ----\n{}",
            out.status,
            out.error.as_deref().unwrap_or(""),
            ca.explain()
        );
        write_dump(dump, &text, true);
    }
}

/// Stages 2–4 of a special-soundness run, recorded in `out`.
fn run_soundness(
    dag: &QDag<ArkBls12_381>,
    target: &Target,
    backend: GbBackendKind,
    diagnostics: &Diagnostics,
    out: &mut BenchOutput,
    window: &mut MemoryWindow,
) {
    let l_vec = target
        .l_vec
        .clone()
        .expect("main checks that soundness has round parameters");
    let dump_result = |out: &BenchOutput, basis: &[Poly]| {
        if let Some(dump) = &diagnostics.dump {
            let text = format!(
                "\n---- result: {} ----\n{}\n{}",
                out.status,
                out.error.as_deref().unwrap_or(""),
                listing("search basis", basis)
            );
            write_dump(dump, &text, true);
        }
    };

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
    out.record_generators(&inputs.generating_set);
    emit(out);

    // Written before the GB call, so it survives a timeout.
    if let Some(dump) = &diagnostics.dump {
        let header = dump_header(target, Analysis::Soundness);
        write_dump(
            dump,
            &(header + &listing("generating set", &inputs.generating_set)),
            false,
        );
    }
    if diagnostics.build_only {
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
            dump_result(out, &[]);
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
    dump_result(out, &sa.search_gb.polys);
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

/// Parses a comma-separated list of round parameters, e.g. `2,2,2`.
fn parse_l_vec(spec: &str) -> Option<Vec<usize>> {
    spec.split(',').map(|l| l.trim().parse().ok()).collect()
}

fn main() {
    // cargo bench always injects `--bench` into the args (even with
    // harness = false). Filter it out.
    let args: Vec<String> = std::env::args()
        .skip(1)
        .filter(|a| a != "--bench")
        .collect();

    let mut analysis = Analysis::Completeness;
    let mut backend = GbBackendKind::default();
    let mut memory_limit_mb: Option<u64> = None;
    let mut protocol_name: Option<&str> = None;
    let mut path: Option<PathBuf> = None;
    let mut size_overrides: Vec<(String, usize)> = Vec::new();
    let mut l_vec_override: Option<Vec<usize>> = None;
    let mut list = false;
    let mut diagnostics = Diagnostics {
        dump: None,
        build_only: false,
    };

    // The value following the flag at `args[*i]`, advancing `i` past it.
    let value = |i: &mut usize, flag: &str, what: &str| -> String {
        *i += 1;
        args.get(*i).cloned().unwrap_or_else(|| {
            eprintln!("{flag} requires a value ({what})");
            std::process::exit(2);
        })
    };

    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--analysis" => {
                let name = value(&mut i, "--analysis", "completeness|soundness");
                analysis = Analysis::parse(&name).unwrap_or_else(|| {
                    eprintln!("unknown analysis: {name} (expected completeness|soundness)");
                    std::process::exit(2);
                });
            }
            "--path" => path = Some(PathBuf::from(value(&mut i, "--path", "a file"))),
            "--size" => {
                let spec = value(&mut i, "--size", "NAME=VALUE");
                let parsed = spec
                    .split_once('=')
                    .and_then(|(n, v)| Some((n.trim().to_string(), v.trim().parse().ok()?)));
                let Some(size) = parsed else {
                    eprintln!("invalid --size value: {spec} (expected NAME=VALUE)");
                    std::process::exit(2);
                };
                size_overrides.push(size);
            }
            "--l-vec" => {
                let spec = value(&mut i, "--l-vec", "L1,L2,...");
                let Some(l_vec) = parse_l_vec(&spec) else {
                    eprintln!("invalid --l-vec value: {spec} (expected L1,L2,...)");
                    std::process::exit(2);
                };
                l_vec_override = Some(l_vec);
            }
            "--dump" => diagnostics.dump = Some(PathBuf::from(value(&mut i, "--dump", "a file"))),
            "--build-only" => diagnostics.build_only = true,
            "--list" => list = true,
            "--backend" => {
                i += 1;
                if i >= args.len() {
                    eprintln!("--backend requires a value (singular|default)");
                    std::process::exit(2);
                }
                backend = match args[i].as_str() {
                    "singular" | "Singular" => GbBackendKind::Singular,
                    "default" => GbBackendKind::default(),
                    other => {
                        eprintln!("unknown backend: {other}");
                        std::process::exit(2);
                    }
                };
            }
            "--memory-limit-mb" => {
                i += 1;
                if i >= args.len() {
                    eprintln!("--memory-limit-mb requires a value (megabytes)");
                    std::process::exit(2);
                }
                memory_limit_mb = Some(args[i].parse().unwrap_or_else(|_| {
                    eprintln!("invalid --memory-limit-mb value: {}", args[i]);
                    std::process::exit(2);
                }));
            }
            other if protocol_name.is_none() => protocol_name = Some(other),
            other => {
                eprintln!("unexpected argument: {other}");
                std::process::exit(2);
            }
        }
        i += 1;
    }

    let registered_for = || PROTOCOLS.iter().filter(move |p| p.runs(analysis));
    if list {
        for p in registered_for() {
            println!("{}", p.name);
        }
        return;
    }

    let Some(protocol_name) = protocol_name else {
        eprintln!(
            "usage: analysis [--analysis completeness|soundness] [--backend singular|default] \
             [--memory-limit-mb MB] [--path FILE] [--size NAME=VALUE]... \
             [--l-vec L1,L2,...] [--dump FILE] [--build-only] <protocol_name>"
        );
        eprintln!("       analysis [--analysis completeness|soundness] --list");
        eprintln!();
        eprintln!("protocols registered for {}:", analysis.name());
        for p in registered_for() {
            eprintln!("  {}", p.name);
        }
        std::process::exit(2);
    };

    // A registered protocol supplies the source, sizes and round parameters;
    // `--path`, `--size` and `--l-vec` replace what they name.
    let registered = protocols::find(protocol_name);
    let mut sizes: Vec<(String, usize)> = registered
        .map(|p| p.sizes.iter().map(|&(n, v)| (n.to_string(), v)).collect())
        .unwrap_or_default();
    for (n, v) in size_overrides {
        match sizes.iter_mut().find(|(m, _)| *m == n) {
            Some(slot) => slot.1 = v,
            None => sizes.push((n, v)),
        }
    }
    let l_vec =
        l_vec_override.or_else(|| registered.and_then(|p| p.soundness.map(<[usize]>::to_vec)));
    if analysis == Analysis::Soundness && l_vec.is_none() {
        eprintln!("{protocol_name} has no registered soundness round parameters; pass --l-vec");
        std::process::exit(2);
    }
    let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let path = match (path, registered) {
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
    let result = share::thread::run("analysis-bench", move || {
        run_bench(&target, analysis, backend, memory_limit_mb, &diagnostics)
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
