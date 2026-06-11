use benchmarks::sumcheck_gate::{
    DEFAULT_SOURCE_PATH, GateIoError, GateOutcome, SumcheckCaptureConfig, SumcheckGatePolicy,
    SumcheckMergeConfig, capture_sumcheck_benchmark, compare_sumcheck_benchmark,
    merge_sumcheck_benchmark_runs, parse_seed, parse_usize_grid, read_benchmark_run,
    write_benchmark_run_atomic, write_json_report, write_markdown_report,
};
use clap::{Parser, Subcommand};
use std::path::PathBuf;
use std::process::ExitCode;

const EXIT_OK: u8 = 0;
const EXIT_INVALID: u8 = 2;
const EXIT_INCOMPARABLE: u8 = 3;
const EXIT_REGRESSION: u8 = 4;
const EXIT_BENCHMARK_FAILED: u8 = 5;
const EXIT_CORRECTNESS_MISMATCH: u8 = 6;
const EXIT_OPTIMIZER_EVIDENCE_MISMATCH: u8 = 7;
const DEFAULT_SUMCHECK_GATE_STACK_SIZE: usize = 64 * 1024 * 1024;
const SUMCHECK_GATE_STACK_ENV: &str = "ZIPPEL_SUMCHECK_GATE_STACK_SIZE";

#[derive(Parser, Debug)]
#[command(about = "Capture and compare schema-versioned sumcheck benchmark artifacts")]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

#[derive(Subcommand, Debug)]
enum Command {
    /// Capture deterministic sumcheck benchmark rows to JSON.
    Capture(CaptureArgs),
    /// Merge validated single-thread artifacts into a declared matrix.
    Merge(MergeArgs),
    /// Compare a baseline artifact against a candidate artifact.
    Compare(CompareArgs),
}

#[derive(Parser, Debug)]
struct CaptureArgs {
    /// Output artifact path.
    #[arg(long)]
    out: PathBuf,
    /// Comma-separated values and/or inclusive ranges, e.g. `4,8,12` or `3..20`.
    #[arg(long, default_value = "4,8,12")]
    num_vars: String,
    /// Comma-separated values and/or inclusive ranges.
    #[arg(long, default_value = "3")]
    max_degree: String,
    /// Number of measured samples per case.
    #[arg(long, default_value_t = 7)]
    repeats: usize,
    /// Number of unrecorded warmups per case.
    #[arg(long, default_value_t = 1)]
    warmups: usize,
    /// Deterministic base seed as decimal or hex (`0x...`).
    #[arg(long, default_value = "0x5eed5eed")]
    seed: String,
    /// Expected effective Rayon thread count. This does not resize Rayon.
    #[arg(long)]
    threads_label: Option<usize>,
    /// Zippel source path to compile for the Zippel side.
    #[arg(long, default_value = DEFAULT_SOURCE_PATH)]
    source_path: String,
    /// Stable logical source identity for an absolute source outside the repo.
    #[arg(long)]
    logical_source_path: Option<String>,
    /// Permit cases above the default safety cap.
    #[arg(long)]
    allow_large_cases: bool,
}

#[derive(Parser, Debug)]
struct MergeArgs {
    /// Output merged artifact path.
    #[arg(long)]
    out: PathBuf,
    /// Declared comma-separated values and/or inclusive ranges.
    #[arg(long)]
    num_vars: String,
    /// Declared comma-separated values and/or inclusive ranges.
    #[arg(long)]
    max_degree: String,
    /// Declared comma-separated thread counts.
    #[arg(long)]
    threads: String,
    /// Validated single-thread sumcheck-benchmark-v2.json artifacts.
    #[arg(required = true)]
    parts: Vec<PathBuf>,
}

#[derive(Parser, Debug)]
struct CompareArgs {
    /// Baseline sumcheck-benchmark-v2.json artifact.
    #[arg(long)]
    baseline: PathBuf,
    /// Candidate sumcheck-benchmark-v2.json artifact.
    #[arg(long)]
    candidate: PathBuf,
    /// Markdown report output path.
    #[arg(long)]
    report: PathBuf,
    /// Optional JSON report output path.
    #[arg(long)]
    json_report: Option<PathBuf>,
    #[arg(long, default_value_t = 7)]
    min_repeats: usize,
    #[arg(long, default_value_t = 1.0)]
    eligible_min_baseline_ms: f64,
    #[arg(long, default_value_t = 1.20)]
    per_case_ratio_limit: f64,
    #[arg(long, default_value_t = 0.50)]
    per_case_abs_slack_ms: f64,
    #[arg(long, default_value_t = 1.10)]
    aggregate_ratio_limit: f64,
    #[arg(long, default_value_t = 1.25)]
    native_drift_ratio_limit: f64,
    #[arg(long, default_value_t = 1.0e-9)]
    summary_mismatch_abs_tolerance_ms: f64,
    /// Require identical rustc/cargo/lockfile metadata.
    #[arg(long)]
    require_same_toolchain: bool,
}

fn main() -> ExitCode {
    let cli = Cli::parse();
    match cli.command {
        Command::Capture(args) => capture(args),
        Command::Merge(args) => merge(args),
        Command::Compare(args) => compare(args),
    }
}

fn capture(args: CaptureArgs) -> ExitCode {
    let stack_size = match sumcheck_gate_capture_stack_size_from_env() {
        Ok(stack_size) => stack_size,
        Err(err) => return invalid(err),
    };

    let worker = match std::thread::Builder::new()
        .name("zippel-sumcheck-gate-capture".to_string())
        .stack_size(stack_size)
        .spawn(move || capture_inner(args))
    {
        Ok(worker) => worker,
        Err(err) => {
            eprintln!(
                "failed to spawn sumcheck capture worker with stack size {stack_size} bytes: {err}"
            );
            return ExitCode::from(EXIT_BENCHMARK_FAILED);
        }
    };

    match worker.join() {
        Ok(code) => code,
        Err(payload) => {
            eprintln!("sumcheck capture worker panicked");
            if let Some(message) = payload.downcast_ref::<&str>() {
                eprintln!("panic message: {message}");
            } else if let Some(message) = payload.downcast_ref::<String>() {
                eprintln!("panic message: {message}");
            }
            ExitCode::from(EXIT_BENCHMARK_FAILED)
        }
    }
}

fn capture_inner(args: CaptureArgs) -> ExitCode {
    let num_vars = match parse_usize_grid(&args.num_vars) {
        Ok(values) => values,
        Err(err) => return invalid(format!("invalid --num-vars: {err}")),
    };
    let max_degrees = match parse_usize_grid(&args.max_degree) {
        Ok(values) => values,
        Err(err) => return invalid(format!("invalid --max-degree: {err}")),
    };
    let seed = match parse_seed(&args.seed) {
        Ok(seed) => seed,
        Err(err) => return invalid(err),
    };
    let threads_label = match args.threads_label {
        Some(0) => return invalid("--threads-label must be greater than zero"),
        Some(value) => value,
        None => default_threads_label(),
    };

    let config = SumcheckCaptureConfig {
        source_path: args.source_path,
        logical_source_path: args.logical_source_path,
        num_vars,
        max_degrees,
        threads: vec![threads_label],
        repeats: args.repeats,
        warmups: args.warmups,
        seed,
        allow_large_cases: args.allow_large_cases,
        command: std::env::args().collect::<Vec<_>>().join(" "),
    };

    match capture_sumcheck_benchmark(&config)
        .and_then(|run| write_benchmark_run_atomic(&args.out, &run).map(|()| run))
    {
        Ok(run) => {
            eprintln!(
                "captured {} sumcheck row(s), repeats={}, warmups={}, threads_label={} -> {}",
                run.rows.len(),
                run.config.repeats,
                run.config.warmups,
                threads_label,
                args.out.display()
            );
            ExitCode::from(EXIT_OK)
        }
        Err(GateIoError::InvalidConfig(err)) => invalid(err),
        Err(err) => {
            eprintln!("sumcheck capture failed: {err}");
            ExitCode::from(EXIT_BENCHMARK_FAILED)
        }
    }
}

fn merge(args: MergeArgs) -> ExitCode {
    let num_vars = match parse_usize_grid(&args.num_vars) {
        Ok(values) => values,
        Err(err) => return invalid(format!("invalid --num-vars: {err}")),
    };
    let max_degrees = match parse_usize_grid(&args.max_degree) {
        Ok(values) => values,
        Err(err) => return invalid(format!("invalid --max-degree: {err}")),
    };
    let threads = match parse_usize_grid(&args.threads) {
        Ok(values) => values,
        Err(err) => return invalid(format!("invalid --threads: {err}")),
    };

    let mut parts = Vec::new();
    for path in &args.parts {
        match read_benchmark_run(path) {
            Ok(run) => parts.push(run),
            Err(err) => {
                eprintln!("failed to read part artifact {}: {err}", path.display());
                return ExitCode::from(EXIT_INVALID);
            }
        }
    }

    let config = SumcheckMergeConfig {
        num_vars,
        max_degrees,
        threads,
        command: std::env::args().collect::<Vec<_>>().join(" "),
    };

    match merge_sumcheck_benchmark_runs(&parts, &config)
        .and_then(|run| write_benchmark_run_atomic(&args.out, &run).map(|()| run))
    {
        Ok(run) => {
            eprintln!(
                "merged {} part artifact(s) into {} row(s) -> {}",
                args.parts.len(),
                run.rows.len(),
                args.out.display()
            );
            ExitCode::from(EXIT_OK)
        }
        Err(GateIoError::InvalidConfig(err)) => invalid(format!("sumcheck merge failed: {err}")),
        Err(err) => {
            eprintln!("sumcheck merge failed: {err}");
            ExitCode::from(EXIT_BENCHMARK_FAILED)
        }
    }
}

fn compare(args: CompareArgs) -> ExitCode {
    if args.min_repeats == 0 {
        return invalid("--min-repeats must be greater than zero");
    }
    if !positive_ratio(args.per_case_ratio_limit, "--per-case-ratio-limit")
        || !positive_ratio(args.aggregate_ratio_limit, "--aggregate-ratio-limit")
        || !positive_ratio(args.native_drift_ratio_limit, "--native-drift-ratio-limit")
    {
        return ExitCode::from(EXIT_INVALID);
    }
    if args.eligible_min_baseline_ms < 0.0 || !args.eligible_min_baseline_ms.is_finite() {
        return invalid("--eligible-min-baseline-ms must be finite and non-negative");
    }
    if args.per_case_abs_slack_ms < 0.0 || !args.per_case_abs_slack_ms.is_finite() {
        return invalid("--per-case-abs-slack-ms must be finite and non-negative");
    }
    if args.summary_mismatch_abs_tolerance_ms < 0.0
        || !args.summary_mismatch_abs_tolerance_ms.is_finite()
    {
        return invalid("--summary-mismatch-abs-tolerance-ms must be finite and non-negative");
    }

    let baseline = match read_benchmark_run(&args.baseline) {
        Ok(run) => run,
        Err(err) => {
            eprintln!(
                "failed to read baseline artifact {}: {err}",
                args.baseline.display()
            );
            return ExitCode::from(EXIT_INVALID);
        }
    };
    let candidate = match read_benchmark_run(&args.candidate) {
        Ok(run) => run,
        Err(err) => {
            eprintln!(
                "failed to read candidate artifact {}: {err}",
                args.candidate.display()
            );
            return ExitCode::from(EXIT_INVALID);
        }
    };

    let policy = SumcheckGatePolicy {
        min_repeats: args.min_repeats,
        eligible_min_baseline_ms: args.eligible_min_baseline_ms,
        per_case_ratio_limit: args.per_case_ratio_limit,
        per_case_abs_slack_ms: args.per_case_abs_slack_ms,
        aggregate_ratio_limit: args.aggregate_ratio_limit,
        native_drift_ratio_limit: args.native_drift_ratio_limit,
        summary_mismatch_abs_tolerance_ms: args.summary_mismatch_abs_tolerance_ms,
        require_same_case_matrix: true,
        require_complete_declared_matrix: true,
        require_effective_threads: true,
        require_same_toolchain: args.require_same_toolchain,
    };
    let report = compare_sumcheck_benchmark(&baseline, &candidate, policy);

    if let Err(err) = write_markdown_report(&args.report, &report) {
        eprintln!(
            "failed to write markdown report {}: {err}",
            args.report.display()
        );
        return ExitCode::from(EXIT_BENCHMARK_FAILED);
    }
    if let Some(path) = args.json_report {
        if let Err(err) = write_json_report(&path, &report) {
            eprintln!("failed to write JSON report {}: {err}", path.display());
            return ExitCode::from(EXIT_BENCHMARK_FAILED);
        }
    }

    eprintln!(
        "sumcheck gate outcome: {:?}; report written to {}",
        report.outcome,
        args.report.display()
    );
    match report.outcome {
        GateOutcome::Pass => ExitCode::from(EXIT_OK),
        GateOutcome::Incomparable => ExitCode::from(EXIT_INCOMPARABLE),
        GateOutcome::Regression => ExitCode::from(EXIT_REGRESSION),
        GateOutcome::CorrectnessMismatch => ExitCode::from(EXIT_CORRECTNESS_MISMATCH),
        GateOutcome::OptimizerEvidenceMismatch => {
            ExitCode::from(EXIT_OPTIMIZER_EVIDENCE_MISMATCH)
        }
    }
}

fn invalid(message: impl AsRef<str>) -> ExitCode {
    eprintln!("{}", message.as_ref());
    ExitCode::from(EXIT_INVALID)
}

fn positive_ratio(value: f64, flag: &str) -> bool {
    if value.is_finite() && value > 0.0 {
        true
    } else {
        eprintln!("{flag} must be finite and greater than zero");
        false
    }
}

fn sumcheck_gate_capture_stack_size_from_env() -> Result<usize, String> {
    match std::env::var(SUMCHECK_GATE_STACK_ENV) {
        Ok(value) => parse_sumcheck_gate_stack_size(&value),
        Err(std::env::VarError::NotPresent) => Ok(DEFAULT_SUMCHECK_GATE_STACK_SIZE),
        Err(std::env::VarError::NotUnicode(_)) => Err(format!(
            "{SUMCHECK_GATE_STACK_ENV} must be a valid UTF-8 positive byte count"
        )),
    }
}

fn parse_sumcheck_gate_stack_size(value: &str) -> Result<usize, String> {
    let trimmed = value.trim();
    if trimmed.is_empty() {
        return Err(format!(
            "{SUMCHECK_GATE_STACK_ENV} must be a positive byte count"
        ));
    }
    let stack_size = trimmed.parse::<usize>().map_err(|_| {
        format!("{SUMCHECK_GATE_STACK_ENV} must be a positive byte count, got `{value}`")
    })?;
    if stack_size == 0 {
        return Err(format!(
            "{SUMCHECK_GATE_STACK_ENV} must be greater than zero"
        ));
    }
    Ok(stack_size)
}

fn default_threads_label() -> usize {
    rayon::current_num_threads()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sumcheck_gate_default_capture_stack_is_at_least_64_mib() {
        assert!(DEFAULT_SUMCHECK_GATE_STACK_SIZE >= 64 * 1024 * 1024);
    }

    #[test]
    fn sumcheck_gate_capture_stack_parser_accepts_positive_byte_count() {
        assert_eq!(parse_sumcheck_gate_stack_size("67108864").unwrap(), 67_108_864);
        assert_eq!(parse_sumcheck_gate_stack_size(" 1048576 ").unwrap(), 1_048_576);
    }

    #[test]
    fn sumcheck_gate_capture_stack_parser_rejects_zero_empty_and_invalid_values() {
        assert!(parse_sumcheck_gate_stack_size("0").is_err());
        assert!(parse_sumcheck_gate_stack_size("").is_err());
        assert!(parse_sumcheck_gate_stack_size("not-a-size").is_err());
    }
}
