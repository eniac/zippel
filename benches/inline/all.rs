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
//!
//! Defaults:
//!   --timeout   1200  (20 minutes per run)
//!   --output    `inline_results.json`
//!   --log       `inline_all.log`

use std::env;
use std::fs::{File, OpenOptions};
use std::io::{BufWriter, Read, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

use serde::{Deserialize, Serialize};

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
) -> BenchResult {
    let mut cmd = Command::new(bin);
    cmd.args([protocol, "--backend", "singular"])
        .current_dir(cwd)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());

    // Put the bench binary in its own process group so we can kill the
    // entire tree (bench binary → Singular) on timeout. child.kill()
    // only kills the bench binary, leaving Singular as an orphan.
    #[cfg(unix)]
    {
        use std::os::unix::process::CommandExt;
        cmd.process_group(0);
    }

    if no_inline {
        cmd.arg("--no-inline");
    }

    let inline_flag = i32::from(!no_inline);

    let mut child = match cmd.spawn() {
        Ok(c) => c,
        Err(e) => {
            return BenchResult::failed(
                protocol,
                inline_flag,
                0.0,
                "error",
                &format!("spawn failed: {e}"),
            );
        }
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
                    return BenchResult::from_stdout(&stdout, wall);
                }
                // No stdout — process crashed/panicked before emitting.
                let stderr = read_stderr(&mut child);
                let code = status.code().unwrap_or(-1);
                return BenchResult::failed(
                    protocol,
                    inline_flag,
                    wall,
                    "error",
                    &format!("exit code {code}, stderr: {}", truncate(&stderr, 500)),
                );
            }
            Ok(None) => {
                if Instant::now() >= deadline {
                    // Kill the entire process group: bench binary + Singular.
                    // process_group(0) made the bench binary a group leader,
                    // so its PID == PGID. kill(-pid) signals the whole group.
                    #[cfg(unix)]
                    {
                        let pgid: libc::pid_t = child.id().try_into().unwrap_or(-1);
                        unsafe {
                            libc::kill(-pgid, libc::SIGKILL);
                        }
                    }
                    // Windows: child.kill() only kills the bench binary, not
                    // Singular. The correct fix is Job Objects, but this
                    // project requires Singular (Unix-only), so this branch
                    // is a compile stub that is never exercised in practice.
                    #[cfg(not(unix))]
                    {
                        let _ = child.kill();
                    }
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
                    "error",
                    &format!("wait failed: {e}"),
                );
            }
        }
    }
}

fn read_stdout(child: &mut std::process::Child) -> String {
    let mut s = String::new();
    if let Some(mut out) = child.stdout.take() {
        let _ = out.read_to_string(&mut s);
    }
    s.trim().to_string()
}

fn read_stderr(child: &mut std::process::Child) -> String {
    let mut s = String::new();
    if let Some(mut err) = child.stderr.take() {
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
fn write_results(path: &Path, timeout: u64, results: &[BenchResult]) {
    let file = ResultsFile {
        timeout_s: timeout,
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
}

fn parse_args() -> Args {
    let raw: Vec<String> = env::args().skip(1).collect();
    let mut timeout = 1200u64;
    let mut output = "inline_results.json".to_string();
    let mut log = "inline_all.log".to_string();
    let mut protocols: Option<Vec<String>> = None;

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
            _ => {}
        }
        i += 1;
    }
    Args {
        timeout,
        output,
        log,
        protocols,
    }
}

fn main() {
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

    for proto in &protocols {
        for &(label, no_inline) in &[("inline", false), ("no_inline", true)] {
            let prefix = format!("[{proto:>30}] {label:>9} ... ");
            let result = run_one(&inline_bin, &repo_root, proto, no_inline, args.timeout);

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
            write_results(Path::new(&args.output), args.timeout, &results);
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
