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

/// One benchmark result row, serialized as JSON.
#[derive(Clone)]
struct Result {
    protocol: String,
    inline: i32,
    status: String,
    wall_s: f64,
    from_input_ms: String,
    run_ms: String,
    basis_size: String,
    max_degree: String,
    num_vars: String,
    graph_size: String,
    error: String,
}

impl Result {
    fn from_json(json: &str, wall_s: f64) -> Self {
        // Minimal JSON parsing — the inline binary emits a flat object.
        let get = |key: &str| -> String {
            let pat = format!("\"{key}\":");
            json.find(&pat)
                .map(|i| {
                    let rest = &json[i + pat.len()..];
                    // Read until comma or closing brace.
                    let end = rest.find([',', '}']).unwrap_or(rest.len());
                    rest[..end].trim().trim_matches('"').to_string()
                })
                .unwrap_or_default()
        };
        Self {
            protocol: get("protocol"),
            inline: get("inline").parse().unwrap_or(-1),
            status: get("status"),
            wall_s,
            from_input_ms: get("from_input_ms"),
            run_ms: get("run_ms"),
            basis_size: get("basis_size"),
            max_degree: get("max_degree"),
            num_vars: get("num_vars"),
            graph_size: get("graph_size"),
            error: get("error"),
        }
    }

    fn timeout(protocol: &str, inline: i32, wall_s: f64, timeout: u64) -> Self {
        Self {
            protocol: protocol.to_string(),
            inline,
            status: "timeout".to_string(),
            wall_s,
            from_input_ms: String::new(),
            run_ms: String::new(),
            basis_size: String::new(),
            max_degree: String::new(),
            num_vars: String::new(),
            graph_size: String::new(),
            error: format!("exceeded {timeout}s timeout"),
        }
    }

    fn killed(protocol: &str, inline: i32, wall_s: f64) -> Self {
        Self {
            protocol: protocol.to_string(),
            inline,
            status: "oom".to_string(),
            wall_s,
            from_input_ms: String::new(),
            run_ms: String::new(),
            basis_size: String::new(),
            max_degree: String::new(),
            num_vars: String::new(),
            graph_size: String::new(),
            error: "process killed (likely OOM)".to_string(),
        }
    }

    fn error(protocol: &str, inline: i32, wall_s: f64, msg: &str) -> Self {
        Self {
            protocol: protocol.to_string(),
            inline,
            status: "error".to_string(),
            wall_s,
            from_input_ms: String::new(),
            run_ms: String::new(),
            basis_size: String::new(),
            max_degree: String::new(),
            num_vars: String::new(),
            graph_size: String::new(),
            error: msg.to_string(),
        }
    }

    /// Serialize to a JSON object string (for the results file).
    fn to_json(&self) -> String {
        format!(
            r#"{{"protocol":"{}","inline":{},"status":"{}","wall_s":{:.3},"from_input_ms":"{}","run_ms":"{}","basis_size":"{}","max_degree":"{}","num_vars":"{}","graph_size":"{}","error":"{}"}}"#,
            self.protocol,
            self.inline,
            self.status,
            self.wall_s,
            self.from_input_ms,
            self.run_ms,
            self.basis_size,
            self.max_degree,
            self.num_vars,
            self.graph_size,
            self.error.replace('"', "'"),
        )
    }
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
fn run_one(cwd: &Path, protocol: &str, no_inline: bool, timeout_secs: u64) -> Result {
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
            return Result::error(protocol, inline_flag, 0.0, &format!("spawn failed: {e}"));
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
                        return Result::killed(protocol, inline_flag, wall);
                    }
                }

                if stdout.is_empty() {
                    let code = status.code().unwrap_or(-1);
                    if code == 137 || code == -9 {
                        return Result::killed(protocol, inline_flag, wall);
                    }
                    let err_trimmed = if stderr.len() > 500 {
                        format!("{}...", &stderr[..500])
                    } else {
                        stderr.clone()
                    };
                    return Result::error(
                        protocol,
                        inline_flag,
                        wall,
                        &format!("exit code {code}, stderr: {err_trimmed}"),
                    );
                }

                let mut result = Result::from_json(stdout, wall);
                // Detect OOM even if we got JSON (panic after output).
                #[cfg(unix)]
                {
                    use std::os::unix::process::ExitStatusExt;
                    if status.signal() == Some(9) {
                        result.status = "oom".to_string();
                        result.error = "process killed (likely OOM)".to_string();
                    }
                }
                return result;
            }
            Ok(None) => {
                // Still running.
                if Instant::now() >= deadline {
                    let _ = child.kill();
                    let _ = child.wait();
                    let wall = start.elapsed().as_secs_f64();
                    return Result::timeout(protocol, inline_flag, wall, timeout_secs);
                }
                std::thread::sleep(Duration::from_millis(100));
            }
            Err(e) => {
                return Result::error(protocol, inline_flag, 0.0, &format!("wait failed: {e}"));
            }
        }
    }
}

/// Write results to JSON file.
fn write_results(path: &Path, timeout: u64, results: &[Result]) {
    let mut out = String::from("{\n  \"timeout_s\": ");
    out.push_str(&timeout.to_string());
    out.push_str(",\n  \"results\": [\n");
    for (i, r) in results.iter().enumerate() {
        let comma = if i + 1 < results.len() { "," } else { "" };
        out.push_str("    ");
        out.push_str(&r.to_json());
        out.push_str(comma);
        out.push('\n');
    }
    out.push_str("  ]\n}\n");
    let _ = std::fs::write(path, out);
}

/// Format a time for the summary table.
fn fmt_time(r: &Result) -> String {
    if r.status != "ok" {
        return r.status.clone();
    }
    let from: f64 = r.from_input_ms.parse().unwrap_or(0.0);
    let run: f64 = r.run_ms.parse().unwrap_or(0.0);
    format!("{:.1}ms", from + run)
}

/// Format the speedup column.
fn fmt_speedup(inline: &Result, noinline: &Result) -> String {
    if inline.status == "ok" && noinline.status == "ok" {
        let a: f64 =
            inline.from_input_ms.parse().unwrap_or(0.0) + inline.run_ms.parse().unwrap_or(0.0);
        let b: f64 =
            noinline.from_input_ms.parse().unwrap_or(0.0) + noinline.run_ms.parse().unwrap_or(0.0);
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

    let mut results: Vec<Result> = Vec::new();

    for proto in &protocols {
        for &(label, no_inline) in &[("inline", false), ("no_inline", true)] {
            let prefix = format!("[{proto:>30}] {label:>9} ... ");
            let result = run_one(&repo_root, proto, no_inline, args.timeout);
            let status = &result.status;
            let from_ms = if result.from_input_ms.is_empty() {
                "-".to_string()
            } else {
                format!(
                    "{:.1}ms",
                    result.from_input_ms.parse::<f64>().unwrap_or(0.0)
                )
            };
            let run_ms = if result.run_ms.is_empty() {
                "-".to_string()
            } else {
                format!("{:.1}ms", result.run_ms.parse::<f64>().unwrap_or(0.0))
            };
            let basis = &result.basis_size;
            let max_degree = &result.max_degree;
            let num_vars = &result.num_vars;
            let graph_size = &result.graph_size;
            let line = format!(
                "{prefix}{status:>12}  from_input={from_ms}  run={run_ms}  basis={basis}  max_deg={max_degree}  vars={num_vars}  nodes={graph_size}"
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
