//! Batch benchmark: run completeness analysis across all protocols,
//! with and without pl-table inlining.
//!
//! Spawns the `inline` bench binary as a subprocess for each protocol ×
//! mode, with per-run timeout. Writes incremental JSON results and a
//! summary table.
//!
//! Usage (via cargo):
//!   cargo bench --bench `inline_all` -- [--timeout SECS] [--protocols a,b,...]
//!                                      [--output PATH] [--log PATH]
//!                                      [--memory-limit-mb MB] [--inline-only]
//!
//! Defaults:
//!   --timeout           1200   (20 minutes per run)
//!   --output            `inline_results.json`
//!   --log               `inline_all.log`
//!   --memory-limit-mb   16384  (16 GiB per run)
//!   --inline-only       off    (runs both inline and no-inline per protocol)
//!
//! `--memory-limit-mb` is forwarded to every `inline` invocation verbatim
//! (like `--backend`). `inline` decides `ok`/`incomplete`/`crashed`/`oom`
//! for itself (see its own module docs) — `inline_all` adds only
//! `timeout`, which it alone can observe.

use std::env;
use std::fs::{File, OpenOptions};
use std::io::{BufWriter, Read, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
#[cfg(unix)]
use std::sync::atomic::{AtomicI32, Ordering};
use std::time::{Duration, Instant};

use process_wrap::std::*;

use serde::{Deserialize, Serialize};

/// Default `--memory-limit-mb`: 16 GiB per run. Generous enough not to
/// interfere with normal-sized protocols, but still bounds a runaway one
/// instead of letting it swap the machine to a halt.
const DEFAULT_MEMORY_LIMIT_MB: u64 = 16 * 1024;

const PROTOCOLS: &[&str] = &[
    "sumcheck",
    "schnorr",
    "schnorr_3round",
    "okamoto",
    "cp",
    "cds",
    "hadamard",
    "coin_proof",
    "kzg",
    "mle_sumcheck",
    "pst13",
    "bccgp",
    "groth16",
    "ipa",
    "hyrax_podp",
    "hyrax_pop",
    "hyrax",
    "membership",
    "spartan",
    "dory",
    "r1cs_sigma",
    "hyperplonk_multiset",
    "hyperplonk_permutation",
    "hyperplonk_zerocheck",
    "hyperplonk_productcheck",
    "hyperplonk",
    "zk_kzg",
    "kzh",
    "dekart",
    "pari",
];

/// One benchmark result row. Deserialized from `inline` stdout (which
/// may emit multiple partial JSON lines) and serialized to the results
/// file. `wall_s` is added by `inline_all` (not present in `inline`
/// output).
#[derive(Clone, Default, Serialize, Deserialize)]
struct BenchResult {
    protocol: String,
    #[serde(default)]
    inline: i32,
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
        if other.inline != 0 || !other.status.is_empty() {
            self.inline = other.inline;
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
        if other.error.is_some() {
            self.error.clone_from(&other.error);
        }
    }

    /// Total time = build + gb + run (missing values treated as 0).
    fn total_ms(&self) -> f64 {
        self.build_ms.unwrap_or(0.0) + self.gb_ms.unwrap_or(0.0) + self.run_ms.unwrap_or(0.0)
    }

    fn failed(protocol: &str, inline: i32, wall_s: f64, status: &str, msg: &str) -> Self {
        Self {
            protocol: protocol.to_string(),
            inline,
            status: status.to_string(),
            wall_s,
            error: Some(msg.to_string()),
            ..Default::default()
        }
    }
}

/// Wrapper for the results JSON file.
#[derive(Serialize)]
struct ResultsFile {
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

/// Build the `inline` bench binary and return its path.
///
/// Uses `cargo bench --no-run --message-format=json` to get the exact
/// artifact path from the compiler-artifact message. This lets `run_one`
/// invoke the binary directly instead of going through `cargo bench`,
/// so killing the child on timeout kills the actual process (not just a
/// `cargo` wrapper that leaves the bench binary orphaned).
fn build_inline_binary(repo_root: &Path) -> PathBuf {
    println!("Building inline (release)...");
    let output = Command::new("cargo")
        .args([
            "bench",
            "--bench",
            "inline",
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
    // inline bench executable path.
    let stdout = String::from_utf8_lossy(&output.stdout);
    for line in stdout.lines() {
        if let Ok(msg) = serde_json::from_str::<serde_json::Value>(line)
            && msg.get("reason").and_then(|v| v.as_str()) == Some("compiler-artifact")
            && msg
                .get("target")
                .and_then(|t| t.get("name"))
                .and_then(|v| v.as_str())
                == Some("inline")
            && msg
                .get("target")
                .and_then(|t| t.get("src_path"))
                .and_then(|v| v.as_str())
                .is_some_and(|p| p.ends_with("benches/inline/main.rs"))
            && let Some(exe) = msg.get("executable").and_then(|v| v.as_str())
        {
            let path = PathBuf::from(exe);
            println!("Build complete: {}", path.display());
            return path;
        }
    }
    eprintln!("ERROR: could not find inline bench binary path in cargo output");
    std::process::exit(1);
}

/// Run one benchmark with timeout. Returns the result and wall time.
fn run_one(
    bin: &Path,
    cwd: &Path,
    protocol: &str,
    no_inline: bool,
    timeout_secs: u64,
    memory_limit_mb: Option<u64>,
) -> BenchResult {
    let mut cmd = CommandWrap::with_new(bin, |cmd| {
        cmd.args([protocol, "--backend", "singular"])
            .current_dir(cwd)
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());
        if no_inline {
            cmd.arg("--no-inline");
        }
        if let Some(mb) = memory_limit_mb {
            cmd.args(["--memory-limit-mb", &mb.to_string()]);
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

    let inline_flag = i32::from(!no_inline);

    let mut child = match cmd.spawn() {
        Ok(c) => c,
        Err(e) => {
            return BenchResult::failed(
                protocol,
                inline_flag,
                0.0,
                "crashed",
                &format!("spawn failed: {e}"),
            );
        }
    };

    // ProcessGroup::leader() makes this child the leader of its own new
    // group, so its PGID equals its own PID — record it so a SIGINT/SIGTERM
    // to inline_all can clean it (and Singular) up too, instead of Ctrl-C
    // only killing inline_all and orphaning the rest. Dropped (and thus
    // cleared) automatically on every exit path below.
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
                    // inline reports its own status (including "oom") in
                    // its final JSON line whenever it can. If it couldn't —
                    // killed by something other than its own reporting path
                    // (e.g. SIGSEGV from an actual bug) — it died before
                    // emitting a final line, leaving only "running" stages
                    // in stdout. Override to "crashed" so "running" doesn't
                    // leak; this is deliberately not reclassified as "oom"
                    // here — inline is the one that knows whether the limit
                    // was active when it died, not inline_all.
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
                    inline_flag,
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
                        inline_flag,
                        wall,
                        "timeout",
                        &format!("exceeded {timeout_secs}s timeout"),
                    );
                }
                std::thread::sleep(Duration::from_millis(100));
            }
            Err(e) => {
                return BenchResult::failed(
                    protocol,
                    inline_flag,
                    0.0,
                    "crashed",
                    &format!("wait failed: {e}"),
                );
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
fn write_results(path: &Path, timeout: u64, memory_limit_mb: Option<u64>, results: &[BenchResult]) {
    let file = ResultsFile {
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

/// Format the speedup column.
fn fmt_speedup(inline: &BenchResult, noinline: &BenchResult) -> String {
    if inline.status == "ok" && noinline.status == "ok" {
        let a = inline.total_ms();
        let b = noinline.total_ms();
        if a > 0.0 {
            return format!("{:.2}x", b / a);
        }
    }
    if inline.status == "ok" && noinline.status != "ok" {
        return "N/A (baseline failed)".to_string();
    }
    if inline.status != "ok" && noinline.status == "ok" {
        return "N/A (inline failed)".to_string();
    }
    "N/A".to_string()
}

struct Args {
    timeout: u64,
    output: String,
    log: String,
    protocols: Option<Vec<String>>,
    memory_limit_mb: Option<u64>,
    inline_only: bool,
}

fn parse_args() -> Args {
    let raw: Vec<String> = env::args().skip(1).collect();
    let mut timeout = 1200u64;
    let mut output = "inline_results.json".to_string();
    let mut log = "inline_all.log".to_string();
    let mut protocols: Option<Vec<String>> = None;
    let mut memory_limit_mb = Some(DEFAULT_MEMORY_LIMIT_MB);
    let mut inline_only = false;

    let mut i = 0;
    while i < raw.len() {
        match raw[i].as_str() {
            "--timeout" => {
                i += 1;
                if i < raw.len() {
                    timeout = raw[i].parse().unwrap_or(1200);
                }
            }
            "--output" => {
                i += 1;
                if i < raw.len() {
                    output.clone_from(&raw[i]);
                }
            }
            "--log" => {
                i += 1;
                if i < raw.len() {
                    log.clone_from(&raw[i]);
                }
            }
            "--protocols" => {
                i += 1;
                if i < raw.len() {
                    protocols = Some(raw[i].split(',').map(|s| s.trim().to_string()).collect());
                }
            }
            "--memory-limit-mb" => {
                i += 1;
                if i < raw.len() {
                    memory_limit_mb = raw[i].parse().ok();
                }
            }
            "--inline-only" => {
                inline_only = true;
            }
            _ => {}
        }
        i += 1;
    }
    Args {
        timeout,
        output,
        log,
        protocols,
        memory_limit_mb,
        inline_only,
    }
}

fn main() {
    install_signal_handlers();

    let args = parse_args();
    let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));

    // inline_all uses the Singular backend for every benchmark. Fail fast
    // with a clear message if it's not installed.
    if !singular_available() {
        eprintln!(
            "ERROR: Singular is not on PATH. inline_all uses the Singular \
             GB backend for all benchmarks. Install Singular to run."
        );
        std::process::exit(1);
    }

    // Open log file and tee output.
    let log_file = OpenOptions::new()
        .create(true)
        .write(true)
        .truncate(true)
        .open(&args.log)
        .expect("failed to open log file");
    let mut log = BufWriter::new(log_file);

    let tee = |log: &mut BufWriter<File>, msg: &str| {
        println!("{msg}");
        let _ = writeln!(log, "{msg}");
        let _ = log.flush();
    };

    let inline_bin = build_inline_binary(&repo_root);

    let protocols: Vec<&str> = args.protocols.as_ref().map_or_else(
        || PROTOCOLS.to_vec(),
        |list| list.iter().map(String::as_str).collect(),
    );

    let mut results: Vec<BenchResult> = Vec::new();

    let variants: &[(&str, bool)] = if args.inline_only {
        &[("inline", false)]
    } else {
        &[("inline", false), ("no_inline", true)]
    };

    for proto in &protocols {
        for &(label, no_inline) in variants {
            let prefix = format!("[{proto:>30}] {label:>9} ... ");
            let result = run_one(
                &inline_bin,
                &repo_root,
                proto,
                no_inline,
                args.timeout,
                args.memory_limit_mb,
            );

            let fmt_ms =
                |ms: Option<f64>| ms.map_or_else(|| "-".to_string(), |v| format!("{:.1}ms", v));
            let fmt_usize = |v: Option<usize>| v.map_or_else(|| "-".to_string(), |n| n.to_string());
            let total =
                if result.build_ms.is_some() && result.gb_ms.is_some() && result.run_ms.is_some() {
                    format!("{:.1}ms", result.total_ms())
                } else {
                    "-".to_string()
                };

            let line = format!(
                "{prefix}{:>12}  build={}  gb={}  run={}  total={}  basis={}  max_deg={}  vars={}  nodes={}  gen={}  gen_deg={}  gen_vars={}",
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
            );
            tee(&mut log, &line);

            results.push(result);
            write_results(
                Path::new(&args.output),
                args.timeout,
                args.memory_limit_mb,
                &results,
            );
        }
    }

    // Summary table.
    tee(&mut log, "");
    let sep = "=".repeat(116);
    let dash = "-".repeat(116);
    tee(&mut log, &sep);
    tee(
        &mut log,
        &format!(
            "{:>30} | {:>14} | {:>12} | {:>16} | {:>14} | {:>8}",
            "Protocol",
            "inline status",
            "inline time",
            "no-inline status",
            "no-inline time",
            "speedup"
        ),
    );
    tee(&mut log, &dash);

    for chunk in results.chunks(2) {
        let inline_r = &chunk[0];
        let noinline_r = chunk.get(1).unwrap_or(inline_r);
        tee(
            &mut log,
            &format!(
                "{:>30} | {:>14} | {:>12} | {:>16} | {:>14} | {:>8}",
                inline_r.protocol,
                inline_r.status,
                fmt_time(inline_r),
                noinline_r.status,
                fmt_time(noinline_r),
                fmt_speedup(inline_r, noinline_r),
            ),
        );
    }

    tee(&mut log, &sep);
    tee(&mut log, &format!("\nResults written to {}", args.output));
    tee(&mut log, &format!("Log written to {}", args.log));
}

// ---------------------------------------------------------------------
// Ctrl-C / SIGTERM cleanup.
//
// `run_one` puts each `inline` child in its own new process group (see
// `ProcessGroup::leader()`) so a timeout can `killpg` just that child (and
// the Singular subprocess it spawns) without also killing `inline_all`.
// That isolation has a side effect: the terminal's Ctrl-C delivers
// `SIGINT` only to `inline_all`'s own (different) process group, never
// reaching the child — so without the handler below, `inline_all` would
// just die and leave `inline`/Singular running, orphaned.
// ---------------------------------------------------------------------

/// PGID of whichever `inline` invocation is currently running, or `0` if
/// none. Read/written only via `Ordering::SeqCst` so the signal handler
/// (which may run on any thread, at any point) always sees an up-to-date
/// value.
#[cfg(unix)]
static CURRENT_CHILD_PGID: AtomicI32 = AtomicI32::new(0);

/// Signal handler for `SIGINT`/`SIGTERM`: kill the current child's process
/// group (if any) before exiting, so Ctrl-C actually cleans up `inline`
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
