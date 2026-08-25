//! Batch benchmark: run completeness analysis across all protocols,
//! with and without pl-table inlining.
//!
//! Spawns the `inline` bench binary as a subprocess for each protocol ×
//! mode, with per-run timeout and OOM detection. Writes incremental JSON
//! results and a summary table.
//!
//! Usage (via cargo):
//!   cargo bench --bench `inline_all` -- [--timeout SECS] [--protocols a,b,...]
//!                                      [--output PATH] [--log PATH]
//!                                      [--skip-build]
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
        if !other.protocol.is_empty() {
            self.protocol.clone_from(&other.protocol);
        }
        if other.inline != 0 || !other.status.is_empty() {
            self.inline = other.inline;
        }
        if !other.status.is_empty() {
            self.status.clone_from(&other.status);
        }
        if other.build_ms.is_some() {
            self.build_ms = other.build_ms;
        }
        if other.gb_ms.is_some() {
            self.gb_ms = other.gb_ms;
        }
        if other.run_ms.is_some() {
            self.run_ms = other.run_ms;
        }
        if other.basis_size.is_some() {
            self.basis_size = other.basis_size;
        }
        if other.max_degree.is_some() {
            self.max_degree = other.max_degree;
        }
        if other.num_vars.is_some() {
            self.num_vars = other.num_vars;
        }
        if other.graph_size.is_some() {
            self.graph_size = other.graph_size;
        }
        if other.gen_set_size.is_some() {
            self.gen_set_size = other.gen_set_size;
        }
        if other.gen_set_max_degree.is_some() {
            self.gen_set_max_degree = other.gen_set_max_degree;
        }
        if other.gen_set_num_vars.is_some() {
            self.gen_set_num_vars = other.gen_set_num_vars;
        }
        if other.error.is_some() {
            self.error.clone_from(&other.error);
        }
    }

    fn timeout(protocol: &str, inline: i32, wall_s: f64, timeout: u64) -> Self {
        Self {
            protocol: protocol.to_string(),
            inline,
            status: "timeout".to_string(),
            wall_s,
            error: Some(format!("exceeded {timeout}s timeout")),
            ..Default::default()
        }
    }

    fn killed(protocol: &str, inline: i32, wall_s: f64) -> Self {
        Self {
            protocol: protocol.to_string(),
            inline,
            status: "oom".to_string(),
            wall_s,
            error: Some("process killed (likely OOM)".to_string()),
            ..Default::default()
        }
    }

    fn error(protocol: &str, inline: i32, wall_s: f64, msg: &str) -> Self {
        Self {
            protocol: protocol.to_string(),
            inline,
            status: "error".to_string(),
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

/// Run `cargo bench --bench inline -- <protocol>` as a subprocess.
/// The `--no-run` check is skipped because cargo is smart enough to
/// reuse the already-built binary.
fn build_binaries(repo_root: &Path) {
    println!("Building inline (release)...");
    let status = Command::new("cargo")
        .args(["bench", "--bench", "inline", "--no-run"])
        .current_dir(repo_root)
        .status()
        .expect("failed to run cargo");
    if !status.success() {
        eprintln!("BUILD FAILED");
        std::process::exit(1);
    }
    println!("Build complete.");
}

/// Run one benchmark with timeout. Returns the result and wall time.
fn run_one(cwd: &Path, protocol: &str, no_inline: bool, timeout_secs: u64) -> BenchResult {
    let mut cmd = Command::new("cargo");
    cmd.args([
        "bench",
        "--bench",
        "inline",
        "--",
        protocol,
        "--backend",
        "singular",
    ])
    .current_dir(cwd)
    .stdout(Stdio::piped())
    .stderr(Stdio::piped());
    if no_inline {
        cmd.arg("--no-inline");
    }

    let inline_flag = i32::from(!no_inline);

    let mut child = match cmd.spawn() {
        Ok(c) => c,
        Err(e) => {
            return BenchResult::error(protocol, inline_flag, 0.0, &format!("spawn failed: {e}"));
        }
    };

    let start = Instant::now();
    let deadline = start + Duration::from_secs(timeout_secs);

    // Poll for completion or timeout.
    loop {
        match child.try_wait() {
            Ok(Some(status)) => {
                let wall = start.elapsed().as_secs_f64();
                let mut stdout = String::new();
                if let Some(mut out) = child.stdout.take() {
                    let _ = out.read_to_string(&mut stdout);
                }
                let mut stderr = String::new();
                if let Some(mut err) = child.stderr.take() {
                    let _ = err.read_to_string(&mut stderr);
                }

                let stdout = stdout.trim();

                // OOM kill: signal 9 on Linux → exit code 137 (or -9 from Rust).
                #[cfg(unix)]
                {
                    use std::os::unix::process::ExitStatusExt;
                    if status.signal() == Some(9) {
                        if !stdout.is_empty() {
                            let mut result = BenchResult::from_stdout(stdout, wall);
                            result.status = "oom".to_string();
                            result.error = Some("process killed (likely OOM)".to_string());
                            return result;
                        }
                        return BenchResult::killed(protocol, inline_flag, wall);
                    }
                }

                if stdout.is_empty() {
                    let code = status.code().unwrap_or(-1);
                    if code == 137 || code == -9 {
                        return BenchResult::killed(protocol, inline_flag, wall);
                    }
                    let err_trimmed = if stderr.len() > 500 {
                        format!("{}...", &stderr[..500])
                    } else {
                        stderr.clone()
                    };
                    return BenchResult::error(
                        protocol,
                        inline_flag,
                        wall,
                        &format!("exit code {code}, stderr: {err_trimmed}"),
                    );
                }

                return BenchResult::from_stdout(stdout, wall);
            }
            Ok(None) => {
                // Still running.
                if Instant::now() >= deadline {
                    let _ = child.kill();
                    let _ = child.wait();
                    let wall = start.elapsed().as_secs_f64();
                    // Read any partial output emitted before the kill.
                    let mut stdout = String::new();
                    if let Some(mut out) = child.stdout.take() {
                        let _ = out.read_to_string(&mut stdout);
                    }
                    let stdout = stdout.trim();
                    if !stdout.is_empty() {
                        let mut result = BenchResult::from_stdout(stdout, wall);
                        result.status = "timeout".to_string();
                        result.error = Some(format!("exceeded {timeout_secs}s timeout"));
                        return result;
                    }
                    return BenchResult::timeout(protocol, inline_flag, wall, timeout_secs);
                }
                std::thread::sleep(Duration::from_millis(100));
            }
            Err(e) => {
                return BenchResult::error(
                    protocol,
                    inline_flag,
                    0.0,
                    &format!("wait failed: {e}"),
                );
            }
        }
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
    let build = r.build_ms.unwrap_or(0.0);
    let gb = r.gb_ms.unwrap_or(0.0);
    let run = r.run_ms.unwrap_or(0.0);
    format!("{:.1}ms", build + gb + run)
}

/// Format the speedup column.
fn fmt_speedup(inline: &BenchResult, noinline: &BenchResult) -> String {
    if inline.status == "ok" && noinline.status == "ok" {
        let a = inline.build_ms.unwrap_or(0.0)
            + inline.gb_ms.unwrap_or(0.0)
            + inline.run_ms.unwrap_or(0.0);
        let b = noinline.build_ms.unwrap_or(0.0)
            + noinline.gb_ms.unwrap_or(0.0)
            + noinline.run_ms.unwrap_or(0.0);
        if a > 0.0 {
            return format!("{:.2}x", b / a);
        }
    }
    if inline.status == "ok" && matches!(noinline.status.as_str(), "timeout" | "oom") {
        return "N/A (baseline failed)".to_string();
    }
    if matches!(inline.status.as_str(), "timeout" | "oom") && noinline.status == "ok" {
        return "N/A (inline failed)".to_string();
    }
    "N/A".to_string()
}

struct Args {
    timeout: u64,
    output: String,
    log: String,
    skip_build: bool,
    protocols: Option<Vec<String>>,
}

fn parse_args() -> Args {
    let raw: Vec<String> = env::args().skip(1).collect();
    let mut timeout = 1200u64;
    let mut output = "inline_results.json".to_string();
    let mut log = "inline_all.log".to_string();
    let mut skip_build = false;
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
            "--skip-build" => {
                skip_build = true;
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
        skip_build,
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

    if !args.skip_build {
        build_binaries(&repo_root);
    }

    let protocols: Vec<&str> = args.protocols.as_ref().map_or_else(
        || PROTOCOLS.to_vec(),
        |list| list.iter().map(String::as_str).collect(),
    );

    let mut results: Vec<BenchResult> = Vec::new();

    for proto in &protocols {
        for &(label, no_inline) in &[("inline", false), ("no_inline", true)] {
            let prefix = format!("[{proto:>30}] {label:>9} ... ");
            let result = run_one(&repo_root, proto, no_inline, args.timeout);
            let status = &result.status;
            let build_ms = result
                .build_ms
                .map_or_else(|| "-".to_string(), |ms| format!("{:.1}ms", ms));
            let gb_ms = result
                .gb_ms
                .map_or_else(|| "-".to_string(), |ms| format!("{:.1}ms", ms));
            let run_ms = result
                .run_ms
                .map_or_else(|| "-".to_string(), |ms| format!("{:.1}ms", ms));
            let total = match (result.build_ms, result.gb_ms, result.run_ms) {
                (Some(b), Some(g), Some(r)) => format!("{:.1}ms", b + g + r),
                _ => "-".to_string(),
            };
            let basis = result
                .basis_size
                .map_or_else(|| "-".to_string(), |v| v.to_string());
            let max_degree = result
                .max_degree
                .map_or_else(|| "-".to_string(), |v| v.to_string());
            let num_vars = result
                .num_vars
                .map_or_else(|| "-".to_string(), |v| v.to_string());
            let graph_size = result
                .graph_size
                .map_or_else(|| "-".to_string(), |v| v.to_string());
            let gen_set = result
                .gen_set_size
                .map_or_else(|| "-".to_string(), |v| v.to_string());
            let gen_deg = result
                .gen_set_max_degree
                .map_or_else(|| "-".to_string(), |v| v.to_string());
            let gen_vars = result
                .gen_set_num_vars
                .map_or_else(|| "-".to_string(), |v| v.to_string());
            let line = format!(
                "{prefix}{status:>12}  build={build_ms}  gb={gb_ms}  run={run_ms}  total={total}  basis={basis}  max_deg={max_degree}  vars={num_vars}  nodes={graph_size}  gen={gen_set}  gen_deg={gen_deg}  gen_vars={gen_vars}"
            );
            tee(&mut log, &line);

            results.push(result);

            // Write incremental results.
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
