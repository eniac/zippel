//! Batch benchmark: run one analysis, completeness or special soundness,
//! across all the protocols registered for it (`analysis --list`).
//!
//! Spawns the `analysis` bench binary as a subprocess for each protocol,
//! with per-run timeout. Writes incremental JSON results and a summary
//! table.
//!
//! Run with `cargo bench --bench analysis_all -- --help` for the options.
//!
//! `--analysis`, `--memory-limit-mb`, `--path`, `--size` and `--l-vec` are
//! forwarded to every `analysis` invocation verbatim.
//! `--path` and `--l-vec` need exactly one protocol in `--protocols`. `analysis`
//! decides `ok`/`failed`/`crashed`/`oom` for itself
//! (see `output::Status`) — `analysis_all` adds only `timeout`, which it
//! alone can observe.

use std::fs::{File, OpenOptions};
use std::io::{BufWriter, Read, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
#[cfg(unix)]
use std::sync::atomic::{AtomicI32, Ordering};
use std::time::{Duration, Instant};

use clap::Parser;
use process_wrap::std::*;

use serde::{Deserialize, Serialize};

/// Default `--memory-limit-mb`: 16 GiB per run. Generous enough not to
/// interfere with normal-sized protocols, but still bounds a runaway one
/// instead of letting it swap the machine to a halt.
const DEFAULT_MEMORY_LIMIT_MB: u64 = 16 * 1024;

/// One benchmark result row. Deserialized from `analysis` stdout (which
/// may emit multiple partial JSON lines) and serialized to the results
/// file. `wall_s` is added by `analysis_all` (not present in `analysis`
/// output).
#[derive(Clone, Default, Serialize, Deserialize)]
struct BenchResult {
    protocol: String,
    #[serde(default)]
    status: String,
    #[serde(skip_deserializing, default)]
    wall_s: f64,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    build_ms: Option<f64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    gb_ms: Option<f64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    run_ms: Option<f64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    basis_size: Option<usize>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    max_degree: Option<usize>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    num_vars: Option<usize>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    graph_size: Option<usize>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    gen_set_size: Option<usize>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    gen_set_max_degree: Option<usize>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    gen_set_num_vars: Option<usize>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    gen_set_terms: Option<usize>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    gen_set_max_terms: Option<usize>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    goals: Option<usize>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    goal_max_degree: Option<usize>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    goal_max_terms: Option<usize>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    peak_rss_mib: Option<u64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    singular_peak_rss_mib: Option<u64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    error: Option<String>,
}

impl BenchResult {
    /// Parse all JSON lines from stdout and merge: later lines take
    /// precedence for status/error, but metrics from earlier lines fill
    /// in missing values. This preserves pre-run metrics even when the
    /// final line (e.g. panic) omits them.
    fn from_stdout(stdout: &str, wall_s: f64) -> Self {
        let mut result = Self {
            wall_s,
            ..Default::default()
        };
        for line in stdout.lines().map(str::trim).filter(|l| !l.is_empty()) {
            if let Ok(partial) = serde_json::from_str::<Self>(line) {
                result.merge(&partial);
            }
        }
        result
    }

    /// Merge another result into self. Non-empty/non-None values from
    /// `other` overwrite self; None/empty values are skipped.
    fn merge(&mut self, other: &Self) {
        macro_rules! take {
            ($field:ident) => {
                if other.$field.is_some() {
                    self.$field = other.$field;
                }
            };
        }
        if !other.protocol.is_empty() {
            self.protocol.clone_from(&other.protocol);
        }
        if !other.status.is_empty() {
            self.status.clone_from(&other.status);
        }
        take!(build_ms);
        take!(gb_ms);
        take!(run_ms);
        take!(basis_size);
        take!(max_degree);
        take!(num_vars);
        take!(graph_size);
        take!(gen_set_size);
        take!(gen_set_max_degree);
        take!(gen_set_num_vars);
        take!(gen_set_terms);
        take!(gen_set_max_terms);
        take!(goals);
        take!(goal_max_degree);
        take!(goal_max_terms);
        take!(peak_rss_mib);
        take!(singular_peak_rss_mib);
        if other.error.is_some() {
            self.error.clone_from(&other.error);
        }
    }

    /// Total time = build + gb + run (missing values treated as 0).
    fn total_ms(&self) -> f64 {
        self.build_ms.unwrap_or(0.0) + self.gb_ms.unwrap_or(0.0) + self.run_ms.unwrap_or(0.0)
    }

    fn failed(protocol: &str, wall_s: f64, status: &str, msg: &str) -> Self {
        Self {
            protocol: protocol.to_string(),
            status: status.to_string(),
            wall_s,
            error: Some(msg.to_string()),
            ..Default::default()
        }
    }
}

/// Wrapper for the results JSON file.
#[derive(Serialize)]
struct ResultsFile<'a> {
    analysis: &'a str,
    timeout_s: u64,
    #[serde(skip_serializing_if = "Option::is_none")]
    memory_limit_mb: Option<u64>,
    results: Vec<BenchResult>,
}

/// Return `true` if the `Singular` binary is on `PATH`.
fn singular_available() -> bool {
    Command::new("Singular")
        .arg("-q")
        .arg("-c")
        .arg("ring r = (integer, 7), (x(1)), dp;")
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status()
        .is_ok()
}

/// Build the `analysis` bench binary and return its path.
///
/// Uses `cargo bench --no-run --message-format=json` to get the exact
/// artifact path from the compiler-artifact message. This lets `run_one`
/// invoke the binary directly instead of going through `cargo bench`,
/// so killing the child on timeout kills the actual process (not just a
/// `cargo` wrapper that leaves the bench binary orphaned).
fn build_analysis_binary(repo_root: &Path) -> PathBuf {
    println!("Building analysis (release)...");
    let output = Command::new("cargo")
        .args([
            "bench",
            "--bench",
            "analysis",
            "--no-run",
            "--message-format=json",
        ])
        .current_dir(repo_root)
        .output()
        .expect("failed to run cargo");
    if !output.status.success() {
        eprintln!("BUILD FAILED");
        let stderr = String::from_utf8_lossy(&output.stderr);
        eprintln!("{stderr}");
        std::process::exit(1);
    }

    // Parse JSON lines to find the compiler-artifact message with the
    // `analysis` bench executable path.
    let stdout = String::from_utf8_lossy(&output.stdout);
    for line in stdout.lines() {
        if let Ok(msg) = serde_json::from_str::<serde_json::Value>(line)
            && msg.get("reason").and_then(|v| v.as_str()) == Some("compiler-artifact")
            && msg
                .get("target")
                .and_then(|t| t.get("name"))
                .and_then(|v| v.as_str())
                == Some("analysis")
            && msg
                .get("target")
                .and_then(|t| t.get("src_path"))
                .and_then(|v| v.as_str())
                .is_some_and(|p| p.ends_with("benches/analysis/main.rs"))
            && let Some(exe) = msg.get("executable").and_then(|v| v.as_str())
        {
            let path = PathBuf::from(exe);
            println!("Build complete: {}", path.display());
            return path;
        }
    }
    eprintln!("ERROR: could not find analysis bench binary path in cargo output");
    std::process::exit(1);
}

/// The protocols `analysis --list` registers for `analysis`. Exits if the
/// binary rejects `analysis`.
fn registered_protocols(bin: &Path, analysis: &str) -> Vec<String> {
    let output = Command::new(bin)
        .args(["--analysis", analysis, "--list"])
        .output()
        .expect("failed to run the analysis bench binary");
    if !output.status.success() {
        eprint!("{}", String::from_utf8_lossy(&output.stderr));
        std::process::exit(2);
    }
    String::from_utf8_lossy(&output.stdout)
        .lines()
        .map(str::to_string)
        .collect()
}

/// Flags passed through to each `analysis` run.
struct Forwarded<'a> {
    analysis: &'a str,
    path: Option<&'a str>,
    sizes: &'a [String],
    l_vec: Option<&'a str>,
}

/// Run one benchmark with timeout. Returns the result and wall time.
fn run_one(
    bin: &Path,
    cwd: &Path,
    protocol: &str,
    timeout_secs: u64,
    memory_limit_mb: Option<u64>,
    forwarded: &Forwarded<'_>,
) -> BenchResult {
    let mut cmd = CommandWrap::with_new(bin, |cmd| {
        cmd.args([protocol, "--backend", "singular"])
            .args(["--analysis", forwarded.analysis])
            .current_dir(cwd)
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());
        if let Some(mb) = memory_limit_mb {
            cmd.args(["--memory-limit-mb", &mb.to_string()]);
        }
        if let Some(path) = forwarded.path {
            cmd.args(["--path", path]);
        }
        for size in forwarded.sizes {
            cmd.args(["--size", size]);
        }
        if let Some(l_vec) = forwarded.l_vec {
            cmd.args(["--l-vec", l_vec]);
        }
    });

    // ProcessGroup on Unix, JobObject on Windows — either way,
    // child.kill() kills the entire process tree (bench binary + Singular).
    #[cfg(unix)]
    {
        cmd.wrap(ProcessGroup::leader());
    }
    #[cfg(windows)]
    {
        cmd.wrap(JobObject);
    }

    let mut child = match cmd.spawn() {
        Ok(c) => c,
        Err(e) => {
            return BenchResult::failed(protocol, 0.0, "crashed", &format!("spawn failed: {e}"));
        }
    };

    // ProcessGroup::leader() makes this child the leader of its own new
    // group, so its PGID equals its own PID — record it so a SIGINT/SIGTERM
    // to `analysis_all` can clean it (and Singular) up too, instead of
    // Ctrl-C only killing `analysis_all` and orphaning the rest. Dropped
    // (and thus cleared) automatically on every exit path below.
    #[cfg(unix)]
    let _pgid_guard = {
        CURRENT_CHILD_PGID.store(child.id().cast_signed(), Ordering::SeqCst);
        ChildPgidGuard
    };

    let start = Instant::now();
    let deadline = start + Duration::from_secs(timeout_secs);

    // Poll for completion or timeout.
    loop {
        match child.try_wait() {
            Ok(Some(status)) => {
                let wall = start.elapsed().as_secs_f64();
                let stdout = read_stdout(&mut child);
                if !stdout.is_empty() {
                    let mut result = BenchResult::from_stdout(&stdout, wall);
                    // `analysis` reports its own status (including "oom")
                    // in its final JSON line whenever it can. If it couldn't —
                    // killed by something other than its own reporting path
                    // (e.g. SIGSEGV from an actual bug) — it died before
                    // emitting a final line, leaving only "running" stages
                    // in stdout. Override to "crashed" so "running" doesn't
                    // leak; this is deliberately not reclassified as "oom"
                    // here — `analysis` is the one that knows whether the
                    // limit was active when it died, not `analysis_all`.
                    if !status.success() && result.status == "running" {
                        let stderr = read_stderr(&mut child);
                        result.status = "crashed".to_string();
                        result.error = Some(format!(
                            "exit code {:?}, stderr: {}",
                            status.code(),
                            truncate(&stderr, 500),
                        ));
                    }
                    return result;
                }
                // No stdout — process crashed/panicked before emitting.
                let stderr = read_stderr(&mut child);
                let code = status.code().unwrap_or(-1);
                return BenchResult::failed(
                    protocol,
                    wall,
                    "crashed",
                    &format!("exit code {code}, stderr: {}", truncate(&stderr, 500)),
                );
            }
            Ok(None) => {
                if Instant::now() >= deadline {
                    // kill() sends SIGKILL to the process group (Unix) or
                    // terminates the job object (Windows), killing the
                    // bench binary and Singular together.
                    let _ = child.kill();
                    let _ = child.wait();
                    let wall = start.elapsed().as_secs_f64();
                    let stdout = read_stdout(&mut child);
                    if !stdout.is_empty() {
                        let mut result = BenchResult::from_stdout(&stdout, wall);
                        result.status = "timeout".to_string();
                        result.error = Some(format!("exceeded {timeout_secs}s timeout"));
                        return result;
                    }
                    return BenchResult::failed(
                        protocol,
                        wall,
                        "timeout",
                        &format!("exceeded {timeout_secs}s timeout"),
                    );
                }
                std::thread::sleep(Duration::from_millis(100));
            }
            Err(e) => {
                return BenchResult::failed(protocol, 0.0, "crashed", &format!("wait failed: {e}"));
            }
        }
    }
}

fn read_stdout(child: &mut Box<dyn ChildWrapper>) -> String {
    let mut s = String::new();
    if let Some(out) = child.stdout() {
        let _ = out.read_to_string(&mut s);
    }
    s.trim().to_string()
}

fn read_stderr(child: &mut Box<dyn ChildWrapper>) -> String {
    let mut s = String::new();
    if let Some(err) = child.stderr() {
        let _ = err.read_to_string(&mut s);
    }
    s
}

fn truncate(s: &str, max: usize) -> String {
    if s.len() > max {
        format!("{}...", &s[..max])
    } else {
        s.to_string()
    }
}

/// Write results to JSON file.
fn write_results(
    path: &Path,
    analysis: &str,
    timeout: u64,
    memory_limit_mb: Option<u64>,
    results: &[BenchResult],
) {
    let file = ResultsFile {
        analysis,
        timeout_s: timeout,
        memory_limit_mb,
        results: results.to_vec(),
    };
    let json = serde_json::to_string_pretty(&file).unwrap();
    let _ = std::fs::write(path, json);
}

/// Format a time for the summary table.
fn fmt_time(r: &BenchResult) -> String {
    if r.status != "ok" {
        return r.status.clone();
    }
    format!("{:.1}ms", r.total_ms())
}

/// Runs one analysis across all the protocols registered for it.
#[derive(Parser)]
#[command(name = "analysis_all", bin_name = "analysis_all")]
struct Args {
    /// `completeness` or `soundness`; `analysis --list` checks it.
    #[arg(long, default_value = "completeness")]
    analysis: String,
    /// Per-run timeout.
    #[arg(long, value_name = "SECS", default_value_t = 1200)]
    timeout: u64,
    /// [default: `<analysis>_results.json`]
    #[arg(long, value_name = "PATH")]
    output: Option<String>,
    /// [default: `<analysis>_all.log`]
    #[arg(long, value_name = "PATH")]
    log: Option<String>,
    /// The protocols to run, instead of all registered ones.
    #[arg(long, value_delimiter = ',')]
    protocols: Option<Vec<String>>,
    /// Per-run memory limit.
    #[arg(long, value_name = "MB", default_value_t = DEFAULT_MEMORY_LIMIT_MB)]
    memory_limit_mb: u64,
    /// Forwarded; needs exactly one protocol in `--protocols`.
    #[arg(long, value_name = "FILE")]
    path: Option<String>,
    /// Forwarded.
    #[arg(long = "size", value_name = "NAME=VALUE")]
    sizes: Vec<String>,
    /// Forwarded; needs exactly one protocol in `--protocols`.
    #[arg(long, value_name = "L1,L2,...")]
    l_vec: Option<String>,
    /// Added by `cargo bench`, even with `harness = false`.
    #[arg(long = "bench", hide = true)]
    _bench: bool,
}

fn main() {
    install_signal_handlers();

    let args = Args::parse();
    // A file or round parameters describe one protocol, not a sweep.
    if (args.path.is_some() || args.l_vec.is_some())
        && args.protocols.as_ref().is_none_or(|p| p.len() != 1)
    {
        eprintln!("--path and --l-vec need exactly one protocol in --protocols");
        std::process::exit(2);
    }
    let output = args
        .output
        .clone()
        .unwrap_or_else(|| format!("{}_results.json", args.analysis));
    let log_path = args
        .log
        .clone()
        .unwrap_or_else(|| format!("{}_all.log", args.analysis));
    let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));

    // analysis_all uses the Singular backend for every benchmark. Fail fast
    // with a clear message if it's not installed.
    if !singular_available() {
        eprintln!(
            "ERROR: Singular is not on PATH. analysis_all uses the Singular \
             GB backend for all benchmarks. Install Singular to run."
        );
        std::process::exit(1);
    }

    let analysis_bin = build_analysis_binary(&repo_root);
    // Also checks `--analysis`, before anything is written.
    let registered = registered_protocols(&analysis_bin, &args.analysis);
    let protocols = args.protocols.clone().unwrap_or(registered);

    // Open log file and tee output.
    let log_file = OpenOptions::new()
        .create(true)
        .write(true)
        .truncate(true)
        .open(&log_path)
        .expect("failed to open log file");
    let mut log = BufWriter::new(log_file);

    let tee = |log: &mut BufWriter<File>, msg: &str| {
        println!("{msg}");
        let _ = writeln!(log, "{msg}");
        let _ = log.flush();
    };

    let mut results: Vec<BenchResult> = Vec::new();

    let forwarded = Forwarded {
        analysis: &args.analysis,
        path: args.path.as_deref(),
        sizes: &args.sizes,
        l_vec: args.l_vec.as_deref(),
    };

    for proto in &protocols {
        let prefix = format!("[{proto:>30}] ... ");
        let result = run_one(
            &analysis_bin,
            &repo_root,
            proto,
            args.timeout,
            Some(args.memory_limit_mb),
            &forwarded,
        );

        let fmt_ms =
            |ms: Option<f64>| ms.map_or_else(|| "-".to_string(), |v| format!("{:.1}ms", v));
        let fmt_usize = |v: Option<usize>| v.map_or_else(|| "-".to_string(), |n| n.to_string());
        let fmt_mib = |v: Option<u64>| v.map_or_else(|| "-".to_string(), |n| format!("{n}MiB"));
        let total =
            if result.build_ms.is_some() && result.gb_ms.is_some() && result.run_ms.is_some() {
                format!("{:.1}ms", result.total_ms())
            } else {
                "-".to_string()
            };

        let line = format!(
            "{prefix}{:>12}  build={}  gb={}  run={}  total={}  basis={}  max_deg={}  vars={}  nodes={}  gen={}  gen_deg={}  gen_vars={}  gen_terms={}  gen_max_terms={}  goals={}  goal_deg={}  goal_max_terms={}  rss={}  singular_rss={}",
            result.status,
            fmt_ms(result.build_ms),
            fmt_ms(result.gb_ms),
            fmt_ms(result.run_ms),
            total,
            fmt_usize(result.basis_size),
            fmt_usize(result.max_degree),
            fmt_usize(result.num_vars),
            fmt_usize(result.graph_size),
            fmt_usize(result.gen_set_size),
            fmt_usize(result.gen_set_max_degree),
            fmt_usize(result.gen_set_num_vars),
            fmt_usize(result.gen_set_terms),
            fmt_usize(result.gen_set_max_terms),
            fmt_usize(result.goals),
            fmt_usize(result.goal_max_degree),
            fmt_usize(result.goal_max_terms),
            fmt_mib(result.peak_rss_mib),
            fmt_mib(result.singular_peak_rss_mib),
        );
        tee(&mut log, &line);

        results.push(result);
        write_results(
            Path::new(&output),
            &args.analysis,
            args.timeout,
            Some(args.memory_limit_mb),
            &results,
        );
    }

    // Summary table.
    tee(&mut log, "");
    let sep = "=".repeat(60);
    let dash = "-".repeat(60);
    tee(&mut log, &sep);
    tee(
        &mut log,
        &format!("{:>30} | {:>12} | {:>12}", "Protocol", "status", "time"),
    );
    tee(&mut log, &dash);

    for r in &results {
        tee(
            &mut log,
            &format!(
                "{:>30} | {:>12} | {:>12}",
                r.protocol,
                r.status,
                fmt_time(r)
            ),
        );
    }

    tee(&mut log, &sep);
    tee(&mut log, &format!("\nResults written to {output}"));
    tee(&mut log, &format!("Log written to {log_path}"));
}

// ---------------------------------------------------------------------
// Ctrl-C / SIGTERM cleanup.
//
// `run_one` puts each `analysis` child in its own new process group (see
// `ProcessGroup::leader()`) so a timeout can `killpg` just that child (and
// the Singular subprocess it spawns) without also killing `analysis_all`.
// That isolation has a side effect: the terminal's Ctrl-C delivers
// `SIGINT` only to `analysis_all`'s own (different) process group, never
// reaching the child — so without the handler below, `analysis_all` would
// just die and leave `analysis`/Singular running, orphaned.
// ---------------------------------------------------------------------

/// PGID of whichever `analysis` invocation is currently running, or `0` if
/// none. Read/written only via `Ordering::SeqCst` so the signal handler
/// (which may run on any thread, at any point) always sees an up-to-date
/// value.
#[cfg(unix)]
static CURRENT_CHILD_PGID: AtomicI32 = AtomicI32::new(0);

/// Signal handler for `SIGINT`/`SIGTERM`: kill the current child's process
/// group (if any) before exiting, so Ctrl-C actually cleans up `analysis`
/// and Singular instead of orphaning them. Must only call
/// async-signal-safe functions — `AtomicI32::load`, `killpg`, and `_exit`
/// all qualify; nothing here allocates or takes a lock.
#[cfg(unix)]
extern "C" fn kill_current_child_and_exit(_sig: libc::c_int) {
    let pgid = CURRENT_CHILD_PGID.load(Ordering::SeqCst);
    if pgid != 0 {
        unsafe {
            libc::killpg(pgid, libc::SIGKILL);
        }
    }
    unsafe {
        libc::_exit(130);
    }
}

/// Install the Ctrl-C/SIGTERM cleanup handler. Best-effort: on non-unix,
/// there's no separate child process group to orphan in the first place
/// (see `JobObject` in `run_one`), so nothing to install.
#[cfg(unix)]
fn install_signal_handlers() {
    unsafe {
        libc::signal(
            libc::SIGINT,
            kill_current_child_and_exit as *const () as libc::sighandler_t,
        );
        libc::signal(
            libc::SIGTERM,
            kill_current_child_and_exit as *const () as libc::sighandler_t,
        );
    }
}

#[cfg(not(unix))]
fn install_signal_handlers() {}

/// Clears [`CURRENT_CHILD_PGID`] when dropped, so it's reset on every exit
/// path out of `run_one` — normal completion, timeout, or an early error
/// return — not just the ones that happen to remember to do it.
#[cfg(unix)]
struct ChildPgidGuard;

#[cfg(unix)]
impl Drop for ChildPgidGuard {
    fn drop(&mut self) {
        CURRENT_CHILD_PGID.store(0, Ordering::SeqCst);
    }
}
