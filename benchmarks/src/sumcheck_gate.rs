//! Sumcheck benchmark capture and comparison gate.
//!
//! This module deliberately keeps the gate's timed boundary aligned with
//! `sumcheck::{zippel_side,native_side}`: setup, compilation, and input
//! construction happen outside the prover/verifier timers.

use crate::sumcheck::{NativeTimedRun, ZippelTimedRun, native_side, zippel_side};
use backend::OptimizationStats;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

pub const SCHEMA_VERSION: u32 = 3;
pub const BENCHMARK_KIND: &str = "zippel.sumcheck.benchmark";
pub const REPORT_KIND: &str = "zippel.sumcheck.gate_report";
pub const DEFAULT_SOURCE_PATH: &str = "examples/sumcheck/sumcheck.zippel";
pub const TIMING_BOUNDARY: &str = "prove_verify_only";
pub const SUMMARY_SEMANTICS: &str = "cached_recomputed_from_samples";
pub const CORRECTNESS_SEMANTICS: &str = "deterministic_input_proof_verifier_subclaim_digests_v1";
pub const OPTIMIZATION_SEMANTICS: &str =
    "explicit_sumcheck_pre_materialization_hypercube_reduce_v1";

const SYSTEM_NAME: &str = "sumcheck";
const MIN_NUM_VARS: usize = 3;
const MAX_NUM_VARS_WITHOUT_ALLOW_LARGE: usize = 20;
const MAX_DEGREE_WITHOUT_ALLOW_LARGE: usize = 32;
const RATIO_EPSILON_MS: f64 = 1.0e-9;

#[derive(Debug)]
pub enum GateIoError {
    Io(std::io::Error),
    Json(serde_json::Error),
    InvalidConfig(String),
}

impl fmt::Display for GateIoError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            GateIoError::Io(err) => write!(f, "I/O error: {err}"),
            GateIoError::Json(err) => write!(f, "JSON error: {err}"),
            GateIoError::InvalidConfig(msg) => write!(f, "invalid sumcheck gate config: {msg}"),
        }
    }
}

impl std::error::Error for GateIoError {}

impl From<std::io::Error> for GateIoError {
    fn from(value: std::io::Error) -> Self {
        GateIoError::Io(value)
    }
}

impl From<serde_json::Error> for GateIoError {
    fn from(value: serde_json::Error) -> Self {
        GateIoError::Json(value)
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SumcheckBenchmarkRun {
    pub schema_version: u32,
    pub kind: String,
    pub metadata: RunMetadata,
    pub config: SumcheckRunConfig,
    pub capture_processes: Vec<CaptureProcessMetadata>,
    pub rows: Vec<SumcheckRow>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct RunMetadata {
    pub created_at: String,
    pub project: String,
    pub git: GitMetadata,
    pub toolchain: ToolchainMetadata,
    pub command: String,
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub struct GitMetadata {
    pub commit: Option<String>,
    pub branch: Option<String>,
    pub dirty: Option<bool>,
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub struct CaptureProcessMetadata {
    pub threads: usize,
    pub effective_rayon_threads: usize,
    pub rayon_num_threads_env: Option<String>,
    pub command: String,
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq)]
pub struct ToolchainMetadata {
    pub rustc: Option<String>,
    pub cargo: Option<String>,
    pub cargo_lock_sha256: Option<String>,
    pub benchmarks_cargo_lock_sha256: Option<String>,
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub struct SourceIdentity {
    pub logical_source_path: String,
    pub source_content_sha256: String,
    pub domain_separator_session: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub resolved_source_path: Option<String>,
}

#[derive(Clone, Debug)]
struct ResolvedSourceIdentity {
    identity: SourceIdentity,
    file_path: PathBuf,
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq)]
pub struct SumcheckRunConfig {
    pub source_path: String,
    pub source_identity: SourceIdentity,
    pub num_vars: Vec<usize>,
    pub max_degrees: Vec<usize>,
    pub threads: Vec<usize>,
    pub repeats: usize,
    pub warmups: usize,
    pub seed: String,
    pub timing_boundary: String,
    pub summary_semantics: String,
    pub correctness_semantics: String,
    pub optimization_semantics: String,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SumcheckRow {
    pub case_id: String,
    pub system: String,
    pub threads: usize,
    pub num_vars: usize,
    pub max_degree: usize,
    pub samples: Vec<SumcheckSample>,
    pub summary: SumcheckSummary,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SumcheckSample {
    pub sample_index: usize,
    /// Compatibility alias for the Zippel-side input digest used by the v2 spec.
    pub input_digest: String,
    pub zippel_input_digest: String,
    pub zippel_prove_ms: f64,
    pub zippel_verify_ms: f64,
    pub zippel_proof_digest: String,
    pub zippel_verifier_result_digest: String,
    pub native_input_digest: String,
    pub native_prove_ms: f64,
    pub native_verify_ms: f64,
    pub native_subclaim_digest: String,
    pub zippel_optimizer: OptimizationStats,
}

#[derive(Clone, Copy, Debug, Serialize, Deserialize)]
pub struct SumcheckSummary {
    pub zippel_prove_median_ms: f64,
    pub zippel_verify_median_ms: f64,
    pub native_prove_median_ms: f64,
    pub native_verify_median_ms: f64,
}

#[derive(Clone, Debug)]
pub struct SumcheckCaptureConfig {
    pub source_path: String,
    pub logical_source_path: Option<String>,
    pub num_vars: Vec<usize>,
    pub max_degrees: Vec<usize>,
    pub threads: Vec<usize>,
    pub repeats: usize,
    pub warmups: usize,
    pub seed: u64,
    pub allow_large_cases: bool,
    pub command: String,
}

impl Default for SumcheckCaptureConfig {
    fn default() -> Self {
        Self {
            source_path: DEFAULT_SOURCE_PATH.to_string(),
            logical_source_path: None,
            num_vars: vec![4, 8, 12],
            max_degrees: vec![3],
            threads: vec![1],
            repeats: 7,
            warmups: 1,
            seed: 0x5eed_5eed,
            allow_large_cases: false,
            command: String::new(),
        }
    }
}

#[derive(Clone, Debug)]
pub struct SumcheckMergeConfig {
    pub num_vars: Vec<usize>,
    pub max_degrees: Vec<usize>,
    pub threads: Vec<usize>,
    pub command: String,
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq)]
pub struct SumcheckGatePolicy {
    pub min_repeats: usize,
    pub eligible_min_baseline_ms: f64,
    pub per_case_ratio_limit: f64,
    pub per_case_abs_slack_ms: f64,
    pub aggregate_ratio_limit: f64,
    pub native_drift_ratio_limit: f64,
    pub summary_mismatch_abs_tolerance_ms: f64,
    pub require_same_case_matrix: bool,
    pub require_complete_declared_matrix: bool,
    pub require_effective_threads: bool,
    pub require_same_toolchain: bool,
}

impl Default for SumcheckGatePolicy {
    fn default() -> Self {
        Self {
            min_repeats: 7,
            eligible_min_baseline_ms: 1.0,
            per_case_ratio_limit: 1.20,
            per_case_abs_slack_ms: 0.50,
            aggregate_ratio_limit: 1.10,
            native_drift_ratio_limit: 1.25,
            summary_mismatch_abs_tolerance_ms: 1.0e-9,
            require_same_case_matrix: true,
            require_complete_declared_matrix: true,
            require_effective_threads: true,
            require_same_toolchain: false,
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "PascalCase")]
pub enum GateOutcome {
    Pass,
    Incomparable,
    Regression,
    CorrectnessMismatch,
    OptimizerEvidenceMismatch,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SumcheckGateReport {
    pub schema_version: u32,
    pub kind: String,
    pub outcome: GateOutcome,
    pub baseline_commit: Option<String>,
    pub candidate_commit: Option<String>,
    pub baseline_source_identity: SourceIdentity,
    pub candidate_source_identity: SourceIdentity,
    pub policy: SumcheckGatePolicy,
    pub row_results: Vec<RowComparison>,
    pub aggregate: AggregateComparison,
    pub refusal_reasons: Vec<String>,
    pub correctness_mismatch_reasons: Vec<String>,
    pub optimizer_evidence_mismatch_reasons: Vec<String>,
    pub regression_reasons: Vec<String>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct RowComparison {
    pub case_id: String,
    pub threads: usize,
    pub num_vars: usize,
    pub max_degree: usize,
    pub zippel_prove_ratio: f64,
    pub zippel_verify_ratio: f64,
    pub native_prove_drift_ratio: f64,
    pub native_verify_drift_ratio: f64,
    pub zippel_prove_delta_ms: f64,
    pub zippel_verify_delta_ms: f64,
    pub native_prove_delta_ms: f64,
    pub native_verify_delta_ms: f64,
    pub zippel_prove_eligible: bool,
    pub zippel_verify_eligible: bool,
    pub zippel_prove_regression: bool,
    pub zippel_verify_regression: bool,
    pub native_drift: bool,
    pub notes: Vec<String>,
}

#[derive(Clone, Copy, Debug, Serialize, Deserialize)]
pub struct AggregateComparison {
    pub zippel_prove_geomean_ratio: f64,
    pub zippel_verify_geomean_ratio: f64,
    pub zippel_combined_geomean_ratio: f64,
    pub native_prove_max_drift_ratio: f64,
    pub native_verify_max_drift_ratio: f64,
    pub compared_zippel_prove_metrics: usize,
    pub compared_zippel_verify_metrics: usize,
}

impl Default for AggregateComparison {
    fn default() -> Self {
        Self {
            zippel_prove_geomean_ratio: 1.0,
            zippel_verify_geomean_ratio: 1.0,
            zippel_combined_geomean_ratio: 1.0,
            native_prove_max_drift_ratio: 1.0,
            native_verify_max_drift_ratio: 1.0,
            compared_zippel_prove_metrics: 0,
            compared_zippel_verify_metrics: 0,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct CaseKey {
    threads: usize,
    num_vars: usize,
    max_degree: usize,
}

impl CaseKey {
    fn from_row(row: &SumcheckRow) -> Self {
        Self {
            threads: row.threads,
            num_vars: row.num_vars,
            max_degree: row.max_degree,
        }
    }
}

impl fmt::Display for CaseKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            case_id(self.num_vars, self.max_degree, self.threads)
        )
    }
}

pub fn case_id(num_vars: usize, max_degree: usize, threads: usize) -> String {
    format!("sumcheck/nv{num_vars}/deg{max_degree}/threads{threads}")
}

pub fn parse_seed(input: &str) -> Result<u64, String> {
    let trimmed = input.trim();
    if trimmed.is_empty() {
        return Err("seed must not be empty".to_string());
    }
    if let Some(hex) = trimmed
        .strip_prefix("0x")
        .or_else(|| trimmed.strip_prefix("0X"))
    {
        u64::from_str_radix(hex, 16).map_err(|err| format!("invalid hex seed `{input}`: {err}"))
    } else {
        trimmed
            .parse::<u64>()
            .map_err(|err| format!("invalid decimal seed `{input}`: {err}"))
    }
}

pub fn format_seed(seed: u64) -> String {
    format!("0x{seed:016x}")
}

pub fn parse_usize_grid(input: &str) -> Result<Vec<usize>, String> {
    let mut out = Vec::new();
    for raw in input.split(',') {
        let token = raw.trim();
        if token.is_empty() {
            return Err(format!("empty item in `{input}`"));
        }
        if let Some((start, end)) = token.split_once("..=") {
            push_range(&mut out, start, end, token)?;
        } else if let Some((start, end)) = token.split_once("..") {
            // CLI users usually expect `3..20` to mean the benchmark grid used
            // in prose, including 20. Treat both range spellings as inclusive.
            push_range(&mut out, start, end, token)?;
        } else {
            out.push(
                token
                    .parse::<usize>()
                    .map_err(|err| format!("invalid integer `{token}`: {err}"))?,
            );
        }
    }
    if out.is_empty() {
        Err("grid must not be empty".to_string())
    } else {
        Ok(out)
    }
}

fn push_range(out: &mut Vec<usize>, start: &str, end: &str, token: &str) -> Result<(), String> {
    let start = start
        .trim()
        .parse::<usize>()
        .map_err(|err| format!("invalid range start in `{token}`: {err}"))?;
    let end = end
        .trim()
        .parse::<usize>()
        .map_err(|err| format!("invalid range end in `{token}`: {err}"))?;
    if start > end {
        return Err(format!("range start exceeds end in `{token}`"));
    }
    out.extend(start..=end);
    Ok(())
}

pub fn capture_sumcheck_benchmark(
    config: &SumcheckCaptureConfig,
) -> Result<SumcheckBenchmarkRun, GateIoError> {
    validate_capture_config(config).map_err(GateIoError::InvalidConfig)?;

    let expected_threads = config.threads[0];
    let effective_threads = rayon::current_num_threads();
    let rayon_num_threads_env = std::env::var("RAYON_NUM_THREADS").ok();
    validate_effective_thread_count(
        expected_threads,
        effective_threads,
        rayon_num_threads_env.as_deref(),
    )
    .map_err(GateIoError::InvalidConfig)?;

    let source_identity = resolve_source_identity(config).map_err(GateIoError::InvalidConfig)?;
    let metadata = collect_metadata(config.command.clone());
    let run_config = SumcheckRunConfig {
        source_path: source_identity.identity.logical_source_path.clone(),
        source_identity: source_identity.identity.clone(),
        num_vars: config.num_vars.clone(),
        max_degrees: config.max_degrees.clone(),
        threads: vec![effective_threads],
        repeats: config.repeats,
        warmups: config.warmups,
        seed: format_seed(config.seed),
        timing_boundary: TIMING_BOUNDARY.to_string(),
        summary_semantics: SUMMARY_SEMANTICS.to_string(),
        correctness_semantics: CORRECTNESS_SEMANTICS.to_string(),
        optimization_semantics: OPTIMIZATION_SEMANTICS.to_string(),
    };

    let mut rows = Vec::new();
    let source_path = source_identity.file_path.clone();
    let domain_separator_session = source_identity.identity.domain_separator_session.clone();

    for &nv in &config.num_vars {
        for &md in &config.max_degrees {
            let mut zippel = zippel_side::Setup::new_with_source_identity(
                nv,
                md,
                &source_path,
                &domain_separator_session,
            );
            let native = native_side::Setup::new(nv, md);

            for warmup_index in 0..config.warmups {
                let seed = derive_sample_seed(
                    config.seed,
                    effective_threads,
                    nv,
                    md,
                    warmup_index as u64,
                    true,
                );
                let _ = zippel.time_protocol_with_seed(seed);
                let _ = native.time_protocol_with_seed(seed);
            }

            let mut samples = Vec::with_capacity(config.repeats);
            for sample_index in 0..config.repeats {
                let seed = derive_sample_seed(
                    config.seed,
                    effective_threads,
                    nv,
                    md,
                    sample_index as u64,
                    false,
                );
                let zt = zippel.run_protocol_with_seed(seed);
                let nt = native.run_protocol_with_seed(seed);
                samples.push(sample_from_runs(sample_index, zt, nt));
            }

            let summary = summarize_samples(&samples);
            rows.push(SumcheckRow {
                case_id: case_id(nv, md, effective_threads),
                system: SYSTEM_NAME.to_string(),
                threads: effective_threads,
                num_vars: nv,
                max_degree: md,
                samples,
                summary,
            });
        }
    }

    let run = SumcheckBenchmarkRun {
        schema_version: SCHEMA_VERSION,
        kind: BENCHMARK_KIND.to_string(),
        metadata,
        config: run_config,
        capture_processes: vec![CaptureProcessMetadata {
            threads: effective_threads,
            effective_rayon_threads: effective_threads,
            rayon_num_threads_env,
            command: config.command.clone(),
        }],
        rows,
    };

    let validation_policy = structural_validation_policy();
    let mut validation_errors = validate_run_artifact(&run, "capture", &validation_policy);
    for row in &run.rows {
        compare_optimizer_evidence(row, &mut validation_errors);
    }
    if validation_errors.is_empty() {
        Ok(run)
    } else {
        Err(GateIoError::InvalidConfig(format!(
            "captured artifact failed validation: {}",
            validation_errors.join("; ")
        )))
    }
}

pub fn write_benchmark_run_atomic(
    path: impl AsRef<Path>,
    run: &SumcheckBenchmarkRun,
) -> Result<(), GateIoError> {
    write_json_atomic(path.as_ref(), run)
}

pub fn read_benchmark_run(path: impl AsRef<Path>) -> Result<SumcheckBenchmarkRun, GateIoError> {
    let bytes = fs::read(path)?;
    Ok(serde_json::from_slice(&bytes)?)
}

pub fn merge_sumcheck_benchmark_runs(
    parts: &[SumcheckBenchmarkRun],
    config: &SumcheckMergeConfig,
) -> Result<SumcheckBenchmarkRun, GateIoError> {
    validate_merge_config(config).map_err(GateIoError::InvalidConfig)?;
    let first = parts.first().ok_or_else(|| {
        GateIoError::InvalidConfig("at least one part artifact is required".to_string())
    })?;

    let validation_policy = structural_validation_policy();
    for (idx, part) in parts.iter().enumerate() {
        let mut errors = validate_run_artifact(part, &format!("part[{idx}]"), &validation_policy);
        for row in &part.rows {
            compare_optimizer_evidence(row, &mut errors);
        }
        if !errors.is_empty() {
            return Err(GateIoError::InvalidConfig(format!(
                "part[{idx}] artifact validation failed: {}",
                errors.join("; ")
            )));
        }
        if unique_set(&part.config.threads).len() != 1 {
            return Err(GateIoError::InvalidConfig(format!(
                "part[{idx}] is not a single-thread artifact: config.threads={:?}",
                part.config.threads
            )));
        }
        if part.capture_processes.len() != 1 {
            return Err(GateIoError::InvalidConfig(format!(
                "part[{idx}] is not a single-process artifact: capture_processes={}",
                part.capture_processes.len()
            )));
        }
    }

    for (idx, part) in parts.iter().enumerate().skip(1) {
        let mut incompatibilities = Vec::new();
        if part.schema_version != first.schema_version {
            incompatibilities.push(format!(
                "schema_version {} != {}",
                part.schema_version, first.schema_version
            ));
        }
        if part.kind != first.kind {
            incompatibilities.push(format!("kind `{}` != `{}`", part.kind, first.kind));
        }
        merge_source_identity_incompatibilities(
            &first.config.source_identity,
            &part.config.source_identity,
            &mut incompatibilities,
        );
        if part.config.seed != first.config.seed {
            incompatibilities.push(format!(
                "seed `{}` != `{}`",
                part.config.seed, first.config.seed
            ));
        }
        if part.config.repeats != first.config.repeats {
            incompatibilities.push(format!(
                "repeats {} != {}",
                part.config.repeats, first.config.repeats
            ));
        }
        if part.config.warmups != first.config.warmups {
            incompatibilities.push(format!(
                "warmups {} != {}",
                part.config.warmups, first.config.warmups
            ));
        }
        if part.config.timing_boundary != first.config.timing_boundary {
            incompatibilities.push(format!(
                "timing_boundary `{}` != `{}`",
                part.config.timing_boundary, first.config.timing_boundary
            ));
        }
        if part.config.summary_semantics != first.config.summary_semantics {
            incompatibilities.push(format!(
                "summary_semantics `{}` != `{}`",
                part.config.summary_semantics, first.config.summary_semantics
            ));
        }
        if part.config.correctness_semantics != first.config.correctness_semantics {
            incompatibilities.push(format!(
                "correctness_semantics `{}` != `{}`",
                part.config.correctness_semantics, first.config.correctness_semantics
            ));
        }
        if part.config.optimization_semantics != first.config.optimization_semantics {
            incompatibilities.push(format!(
                "optimization_semantics `{}` != `{}`",
                part.config.optimization_semantics, first.config.optimization_semantics
            ));
        }
        if part.metadata.git != first.metadata.git {
            incompatibilities.push("git metadata differs".to_string());
        }
        if part.metadata.toolchain != first.metadata.toolchain {
            incompatibilities.push("toolchain metadata differs".to_string());
        }
        if !incompatibilities.is_empty() {
            return Err(GateIoError::InvalidConfig(format!(
                "part[{idx}] metadata/config is incompatible with part[0]: {}",
                incompatibilities.join("; ")
            )));
        }
    }

    let expected = expected_case_keys(&config.num_vars, &config.max_degrees, &config.threads);
    let mut counts: BTreeMap<CaseKey, Vec<String>> = BTreeMap::new();
    let mut rows = Vec::new();
    for (part_idx, part) in parts.iter().enumerate() {
        for (row_idx, row) in part.rows.iter().enumerate() {
            counts
                .entry(CaseKey::from_row(row))
                .or_default()
                .push(format!("part[{part_idx}].rows[{row_idx}]"));
            rows.push(row.clone());
        }
    }
    let actual = counts.keys().copied().collect::<BTreeSet<_>>();
    let mut matrix_errors = Vec::new();
    for (key, locations) in &counts {
        if locations.len() > 1 {
            matrix_errors.push(format!(
                "DuplicateCaseRow: duplicate merged case {key} at {}",
                locations.join(", ")
            ));
        }
    }
    for key in expected.difference(&actual) {
        matrix_errors.push(format!("MissingConfiguredCase: missing merged case {key}"));
    }
    for key in actual.difference(&expected) {
        matrix_errors.push(format!(
            "ExtraUnconfiguredCase: unexpected merged case {key}"
        ));
    }
    if !matrix_errors.is_empty() {
        return Err(GateIoError::InvalidConfig(matrix_errors.join("; ")));
    }

    let mut metadata = first.metadata.clone();
    metadata.created_at = current_unix_timestamp_string();
    metadata.command = config.command.clone();

    let mut capture_processes = Vec::new();
    for part in parts {
        capture_processes.extend(part.capture_processes.iter().cloned());
    }
    capture_processes.sort_by_key(|process| process.threads);
    rows.sort_by_key(CaseKey::from_row);

    let merged = SumcheckBenchmarkRun {
        schema_version: SCHEMA_VERSION,
        kind: BENCHMARK_KIND.to_string(),
        metadata,
        config: SumcheckRunConfig {
            source_path: first.config.source_identity.logical_source_path.clone(),
            source_identity: first.config.source_identity.clone(),
            num_vars: config.num_vars.clone(),
            max_degrees: config.max_degrees.clone(),
            threads: config.threads.clone(),
            repeats: first.config.repeats,
            warmups: first.config.warmups,
            seed: first.config.seed.clone(),
            timing_boundary: TIMING_BOUNDARY.to_string(),
            summary_semantics: SUMMARY_SEMANTICS.to_string(),
            correctness_semantics: CORRECTNESS_SEMANTICS.to_string(),
            optimization_semantics: OPTIMIZATION_SEMANTICS.to_string(),
        },
        capture_processes,
        rows,
    };

    let mut errors = validate_run_artifact(&merged, "merged", &validation_policy);
    for row in &merged.rows {
        compare_optimizer_evidence(row, &mut errors);
    }
    if errors.is_empty() {
        Ok(merged)
    } else {
        Err(GateIoError::InvalidConfig(format!(
            "merged artifact failed validation: {}",
            errors.join("; ")
        )))
    }
}

pub fn compare_sumcheck_benchmark(
    baseline: &SumcheckBenchmarkRun,
    candidate: &SumcheckBenchmarkRun,
    policy: SumcheckGatePolicy,
) -> SumcheckGateReport {
    let mut refusal_reasons = Vec::new();
    let mut correctness_mismatch_reasons = Vec::new();
    let mut optimizer_evidence_mismatch_reasons = Vec::new();
    let mut regression_reasons = Vec::new();

    refusal_reasons.extend(validate_run_artifact(baseline, "baseline", &policy));
    refusal_reasons.extend(validate_run_artifact(candidate, "candidate", &policy));
    let config_refusal_reasons = compare_run_configs(baseline, candidate, &policy);
    let source_identity_mismatch = config_refusal_reasons
        .iter()
        .any(|reason| reason.contains("SourceIdentityMismatch"));
    refusal_reasons.extend(config_refusal_reasons);

    let baseline_rows = collect_row_map(baseline, "baseline", &mut refusal_reasons);
    let candidate_rows = collect_row_map(candidate, "candidate", &mut refusal_reasons);

    if policy.require_same_case_matrix {
        let baseline_keys = baseline_rows.keys().copied().collect::<BTreeSet<_>>();
        let candidate_keys = candidate_rows.keys().copied().collect::<BTreeSet<_>>();
        if baseline_keys != candidate_keys {
            refusal_reasons.push(format!(
                "case matrix mismatch: baseline has {}, candidate has {} rows",
                baseline_keys.len(),
                candidate_keys.len()
            ));
        }
    }

    let mut row_results = Vec::new();
    for key in baseline_rows
        .keys()
        .filter(|key| candidate_rows.contains_key(key))
    {
        let baseline_row = &baseline.rows[baseline_rows[key]];
        let candidate_row = &candidate.rows[candidate_rows[key]];

        if baseline_row.samples.len() != candidate_row.samples.len() {
            refusal_reasons.push(format!(
                "sample count mismatch for {}: baseline={}, candidate={}",
                baseline_row.case_id,
                baseline_row.samples.len(),
                candidate_row.samples.len()
            ));
        }
        let sample_indices_match = sample_indices(baseline_row) == sample_indices(candidate_row);
        if !sample_indices_match {
            refusal_reasons.push(format!(
                "sample index mismatch for {}",
                baseline_row.case_id
            ));
        }
        if !source_identity_mismatch
            && baseline_row.samples.len() == candidate_row.samples.len()
            && sample_indices_match
        {
            compare_correctness_digests(
                baseline_row,
                candidate_row,
                &mut correctness_mismatch_reasons,
            );
            compare_optimizer_evidence(candidate_row, &mut optimizer_evidence_mismatch_reasons);
        }

        let Some(baseline_summary) = recompute_summary(baseline_row) else {
            refusal_reasons.push(format!(
                "SummaryMismatch: baseline row {} has no authoritative recomputable samples",
                baseline_row.case_id
            ));
            continue;
        };
        let Some(candidate_summary) = recompute_summary(candidate_row) else {
            refusal_reasons.push(format!(
                "SummaryMismatch: candidate row {} has no authoritative recomputable samples",
                candidate_row.case_id
            ));
            continue;
        };

        let row = compare_row(baseline_row, baseline_summary, candidate_summary, &policy);
        if row.native_drift && correctness_mismatch_reasons.is_empty() {
            refusal_reasons.push(format!(
                "native drift exceeded for {}: prove drift {:.3}x, verify drift {:.3}x (limit {:.3}x)",
                row.case_id,
                row.native_prove_drift_ratio,
                row.native_verify_drift_ratio,
                policy.native_drift_ratio_limit
            ));
        }
        row_results.push(row);
    }

    let aggregate = aggregate_rows(&row_results);

    if refusal_reasons.is_empty()
        && correctness_mismatch_reasons.is_empty()
        && optimizer_evidence_mismatch_reasons.is_empty()
    {
        for row in &row_results {
            if row.zippel_prove_regression {
                regression_reasons.push(format!(
                    "zippel prove regression for {}: ratio {:.3}x, delta {:.3}ms",
                    row.case_id, row.zippel_prove_ratio, row.zippel_prove_delta_ms
                ));
            }
            if row.zippel_verify_regression {
                regression_reasons.push(format!(
                    "zippel verify regression for {}: ratio {:.3}x, delta {:.3}ms",
                    row.case_id, row.zippel_verify_ratio, row.zippel_verify_delta_ms
                ));
            }
        }

        if aggregate.zippel_prove_geomean_ratio > policy.aggregate_ratio_limit {
            regression_reasons.push(format!(
                "aggregate zippel prove geomean regression: {:.3}x exceeds {:.3}x",
                aggregate.zippel_prove_geomean_ratio, policy.aggregate_ratio_limit
            ));
        }
        if aggregate.zippel_verify_geomean_ratio > policy.aggregate_ratio_limit {
            regression_reasons.push(format!(
                "aggregate zippel verify geomean regression: {:.3}x exceeds {:.3}x",
                aggregate.zippel_verify_geomean_ratio, policy.aggregate_ratio_limit
            ));
        }
        if aggregate.zippel_combined_geomean_ratio > policy.aggregate_ratio_limit {
            regression_reasons.push(format!(
                "aggregate zippel combined geomean regression: {:.3}x exceeds {:.3}x",
                aggregate.zippel_combined_geomean_ratio, policy.aggregate_ratio_limit
            ));
        }
    }

    let outcome = if !refusal_reasons.is_empty() {
        GateOutcome::Incomparable
    } else if !correctness_mismatch_reasons.is_empty() {
        GateOutcome::CorrectnessMismatch
    } else if !optimizer_evidence_mismatch_reasons.is_empty() {
        GateOutcome::OptimizerEvidenceMismatch
    } else if !regression_reasons.is_empty() {
        GateOutcome::Regression
    } else {
        GateOutcome::Pass
    };

    SumcheckGateReport {
        schema_version: SCHEMA_VERSION,
        kind: REPORT_KIND.to_string(),
        outcome,
        baseline_commit: baseline.metadata.git.commit.clone(),
        candidate_commit: candidate.metadata.git.commit.clone(),
        baseline_source_identity: baseline.config.source_identity.clone(),
        candidate_source_identity: candidate.config.source_identity.clone(),
        policy,
        row_results,
        aggregate,
        refusal_reasons,
        correctness_mismatch_reasons,
        optimizer_evidence_mismatch_reasons,
        regression_reasons,
    }
}

pub fn write_markdown_report(
    path: impl AsRef<Path>,
    report: &SumcheckGateReport,
) -> Result<(), GateIoError> {
    let mut out = String::new();
    out.push_str("# Sumcheck benchmark gate report\n\n");
    out.push_str(&format!("- outcome: **{:?}**\n", report.outcome));
    out.push_str(&format!(
        "- baseline commit: `{}`\n",
        report.baseline_commit.as_deref().unwrap_or("unknown")
    ));
    out.push_str(&format!(
        "- candidate commit: `{}`\n",
        report.candidate_commit.as_deref().unwrap_or("unknown")
    ));
    out.push_str(&format!(
        "- policy: per-case <= {:.3}x with {:.3}ms slack; aggregate <= {:.3}x; native drift <= {:.3}x; min repeats = {}; summary tolerance = {:.12}ms\n\n",
        report.policy.per_case_ratio_limit,
        report.policy.per_case_abs_slack_ms,
        report.policy.aggregate_ratio_limit,
        report.policy.native_drift_ratio_limit,
        report.policy.min_repeats,
        report.policy.summary_mismatch_abs_tolerance_ms,
    ));

    out.push_str("## Source identity\n\n");
    out.push_str("| field | baseline | candidate |\n|---|---|---|\n");
    out.push_str(&format!(
        "| logical_source_path | `{}` | `{}` |\n",
        report.baseline_source_identity.logical_source_path,
        report.candidate_source_identity.logical_source_path
    ));
    out.push_str(&format!(
        "| domain_separator_session | `{}` | `{}` |\n",
        report.baseline_source_identity.domain_separator_session,
        report.candidate_source_identity.domain_separator_session
    ));
    out.push_str(&format!(
        "| source_content_sha256 | `{}` | `{}` |\n",
        report.baseline_source_identity.source_content_sha256,
        report.candidate_source_identity.source_content_sha256
    ));
    out.push_str(&format!(
        "| resolved_source_path | `{}` | `{}` |\n\n",
        report
            .baseline_source_identity
            .resolved_source_path
            .as_deref()
            .unwrap_or("not recorded"),
        report
            .candidate_source_identity
            .resolved_source_path
            .as_deref()
            .unwrap_or("not recorded")
    ));

    out.push_str("## Correctness digests\n\n");
    if report.correctness_mismatch_reasons.is_empty() {
        out.push_str("- status: all compared sample digests match\n\n");
    } else {
        out.push_str("- status: mismatch detected before timing-regression classification\n");
        for reason in &report.correctness_mismatch_reasons {
            out.push_str(&format!("- {reason}\n"));
        }
        out.push('\n');
    }

    out.push_str("## Optimizer evidence\n\n");
    if report.optimizer_evidence_mismatch_reasons.is_empty() {
        out.push_str("- status: candidate canonical rows show fused hypercube reduction and no selected-eval materialization/interpolation fallback\n\n");
    } else {
        out.push_str("- status: optimizer evidence mismatch detected\n");
        for reason in &report.optimizer_evidence_mismatch_reasons {
            out.push_str(&format!("- {reason}\n"));
        }
        out.push('\n');
    }

    if !report.refusal_reasons.is_empty() {
        out.push_str("## Incomparability reasons\n\n");
        for reason in &report.refusal_reasons {
            out.push_str(&format!("- {reason}\n"));
        }
        out.push('\n');
    }

    if !report.regression_reasons.is_empty() {
        out.push_str("## Regression reasons\n\n");
        for reason in &report.regression_reasons {
            out.push_str(&format!("- {reason}\n"));
        }
        out.push('\n');
    }

    out.push_str("## Aggregate\n\n");
    out.push_str("| metric | value |\n|---|---:|\n");
    out.push_str(&format!(
        "| zippel prove geomean ratio | {:.3}x |\n",
        report.aggregate.zippel_prove_geomean_ratio
    ));
    out.push_str(&format!(
        "| zippel verify geomean ratio | {:.3}x |\n",
        report.aggregate.zippel_verify_geomean_ratio
    ));
    out.push_str(&format!(
        "| zippel combined geomean ratio | {:.3}x |\n",
        report.aggregate.zippel_combined_geomean_ratio
    ));
    out.push_str(&format!(
        "| native prove max drift | {:.3}x |\n",
        report.aggregate.native_prove_max_drift_ratio
    ));
    out.push_str(&format!(
        "| native verify max drift | {:.3}x |\n\n",
        report.aggregate.native_verify_max_drift_ratio
    ));

    out.push_str("## Rows\n\n");
    out.push_str("| case | zippel prove | zippel verify | native prove drift | native verify drift | flags |\n");
    out.push_str("|---|---:|---:|---:|---:|---|\n");
    for row in &report.row_results {
        let mut flags = Vec::new();
        if row.zippel_prove_regression {
            flags.push("zippel-prove-regression");
        }
        if row.zippel_verify_regression {
            flags.push("zippel-verify-regression");
        }
        if row.native_drift {
            flags.push("native-drift");
        }
        if flags.is_empty() {
            flags.push("ok");
        }
        out.push_str(&format!(
            "| {} | {:.3}x ({:+.3}ms) | {:.3}x ({:+.3}ms) | {:.3}x | {:.3}x | {} |\n",
            row.case_id,
            row.zippel_prove_ratio,
            row.zippel_prove_delta_ms,
            row.zippel_verify_ratio,
            row.zippel_verify_delta_ms,
            row.native_prove_drift_ratio,
            row.native_verify_drift_ratio,
            flags.join(", ")
        ));
    }

    if let Some(parent) = path.as_ref().parent() {
        if !parent.as_os_str().is_empty() {
            fs::create_dir_all(parent)?;
        }
    }
    fs::write(path, out)?;
    Ok(())
}

pub fn write_json_report(
    path: impl AsRef<Path>,
    report: &SumcheckGateReport,
) -> Result<(), GateIoError> {
    write_json_atomic(path.as_ref(), report)
}

fn resolve_source_identity(
    config: &SumcheckCaptureConfig,
) -> Result<ResolvedSourceIdentity, String> {
    let source_path_raw = config.source_path.trim();
    if source_path_raw.is_empty() {
        return Err("source path must not be empty".to_string());
    }

    let repo_root = repo_root();
    let source_path = path_from_user_input(source_path_raw);
    let (file_path, default_logical_source_path) = if source_path.is_absolute() {
        let canonical_repo_root = canonicalize_or_self(&repo_root);
        let canonical_source_path = canonicalize_or_self(&source_path);
        match canonical_source_path.strip_prefix(&canonical_repo_root) {
            Ok(relative) => (source_path, logical_path_from_relative_path(relative)?),
            Err(_) => {
                let logical_source_path = config.logical_source_path.as_deref().ok_or_else(|| {
                    "absolute --source-path outside the repository requires --logical-source-path"
                        .to_string()
                })?;
                (source_path, normalize_logical_path(logical_source_path)?)
            }
        }
    } else {
        let source_relative_logical_path = normalize_logical_path(source_path_raw)?;
        (
            repo_root.join(path_from_logical_path(&source_relative_logical_path)),
            source_relative_logical_path,
        )
    };

    let logical_source_path = match config.logical_source_path.as_deref() {
        Some(logical_source_path) => normalize_logical_path(logical_source_path)?,
        None => default_logical_source_path,
    };
    let source_content_sha256 = sha256_file_digest(&file_path)?;
    let resolved_source_path = Some(file_path.display().to_string());

    Ok(ResolvedSourceIdentity {
        identity: SourceIdentity {
            logical_source_path: logical_source_path.clone(),
            source_content_sha256,
            domain_separator_session: logical_source_path,
            resolved_source_path,
        },
        file_path,
    })
}

fn normalize_logical_path(raw: &str) -> Result<String, String> {
    let normalized_separators = raw.trim().replace('\\', "/");
    if normalized_separators.is_empty() {
        return Err("logical source path must not be empty".to_string());
    }
    if looks_like_absolute_path(&normalized_separators) {
        return Err(format!(
            "logical source path `{raw}` must be repository-relative, not absolute"
        ));
    }

    let mut components = Vec::new();
    for component in normalized_separators.split('/') {
        match component {
            "" | "." => {}
            ".." => {
                return Err(format!(
                    "logical source path `{raw}` must not contain `..` segments"
                ));
            }
            segment => components.push(segment.to_string()),
        }
    }

    if components.is_empty() {
        Err("logical source path must not be empty".to_string())
    } else {
        Ok(components.join("/"))
    }
}

fn logical_path_from_relative_path(path: &Path) -> Result<String, String> {
    let mut components = Vec::new();
    for component in path.components() {
        match component {
            std::path::Component::Normal(value) => {
                components.push(value.to_string_lossy().replace('\\', "/"));
            }
            std::path::Component::CurDir => {}
            std::path::Component::ParentDir => {
                return Err(format!(
                    "derived source path `{}` must not contain `..` segments",
                    path.display()
                ));
            }
            std::path::Component::Prefix(_) | std::path::Component::RootDir => {
                return Err(format!(
                    "derived source path `{}` must be repository-relative",
                    path.display()
                ));
            }
        }
    }
    normalize_logical_path(&components.join("/"))
}

fn path_from_user_input(raw: &str) -> PathBuf {
    PathBuf::from(raw.replace('\\', "/"))
}

fn path_from_logical_path(logical_path: &str) -> PathBuf {
    logical_path.split('/').collect()
}

fn canonicalize_or_self(path: &Path) -> PathBuf {
    fs::canonicalize(path).unwrap_or_else(|_| path.to_path_buf())
}

fn looks_like_absolute_path(value: &str) -> bool {
    value.starts_with('/') || value.starts_with("//") || value.as_bytes().get(1) == Some(&b':')
}

fn sha256_file_digest(path: &Path) -> Result<String, String> {
    let bytes = fs::read(path)
        .map_err(|err| format!("failed to read source file `{}`: {err}", path.display()))?;
    Ok(format!("sha256:{:x}", Sha256::digest(&bytes)))
}

fn validate_capture_config(config: &SumcheckCaptureConfig) -> Result<(), String> {
    if config.num_vars.is_empty() {
        return Err("num-vars grid must not be empty".to_string());
    }
    if config.max_degrees.is_empty() {
        return Err("max-degree grid must not be empty".to_string());
    }
    if config.threads.is_empty() {
        return Err("threads-label grid must not be empty".to_string());
    }
    if config.threads.len() != 1 {
        return Err(format!(
            "single capture process may record exactly one threads-label; got {} labels",
            config.threads.len()
        ));
    }
    if config.repeats == 0 {
        return Err("repeats must be greater than zero".to_string());
    }
    if config.source_path.trim().is_empty() {
        return Err("source path must not be empty".to_string());
    }

    let threads = config.threads[0];
    if threads == 0 {
        return Err("threads labels must be greater than zero".to_string());
    }
    let mut seen = BTreeSet::new();
    for &nv in &config.num_vars {
        if nv < MIN_NUM_VARS {
            return Err(format!(
                "num_vars={nv} is below the supported minimum {MIN_NUM_VARS}"
            ));
        }
        if !config.allow_large_cases && nv > MAX_NUM_VARS_WITHOUT_ALLOW_LARGE {
            return Err(format!(
                "num_vars={nv} exceeds {MAX_NUM_VARS_WITHOUT_ALLOW_LARGE}; pass --allow-large-cases to run it"
            ));
        }
        for &md in &config.max_degrees {
            if md == 0 {
                return Err("max_degree must be greater than zero".to_string());
            }
            if !config.allow_large_cases && md > MAX_DEGREE_WITHOUT_ALLOW_LARGE {
                return Err(format!(
                    "max_degree={md} exceeds {MAX_DEGREE_WITHOUT_ALLOW_LARGE}; pass --allow-large-cases to run it"
                ));
            }
            let key = CaseKey {
                threads,
                num_vars: nv,
                max_degree: md,
            };
            if !seen.insert(key) {
                return Err(format!("duplicate case ({nv}, {md}, threads={threads})"));
            }
        }
    }
    Ok(())
}

fn validate_merge_config(config: &SumcheckMergeConfig) -> Result<(), String> {
    validate_matrix_values(
        &config.num_vars,
        &config.max_degrees,
        &config.threads,
        "merge declared matrix",
    )
}

fn validate_effective_thread_count(
    expected_threads: usize,
    effective_threads: usize,
    rayon_num_threads_env: Option<&str>,
) -> Result<(), String> {
    if expected_threads == 0 {
        return Err(
            "ThreadCountMismatch: expected thread count must be greater than zero".to_string(),
        );
    }
    if effective_threads == 0 {
        return Err(
            "ThreadCountMismatch: effective Rayon thread count must be greater than zero"
                .to_string(),
        );
    }
    if expected_threads != effective_threads {
        return Err(format!(
            "ThreadCountMismatch: --threads-label expected {expected_threads}, but rayon::current_num_threads() reported {effective_threads}"
        ));
    }
    if let Some(raw) = rayon_num_threads_env {
        if let Ok(parsed) = raw.trim().parse::<usize>() {
            if parsed != effective_threads {
                return Err(format!(
                    "ThreadCountMismatch: RAYON_NUM_THREADS={raw:?} parses as {parsed}, but rayon::current_num_threads() reported {effective_threads}"
                ));
            }
        }
    }
    Ok(())
}

fn sample_from_runs(
    sample_index: usize,
    zippel: ZippelTimedRun,
    native: NativeTimedRun,
) -> SumcheckSample {
    SumcheckSample {
        sample_index,
        input_digest: zippel.observation.input_digest.clone(),
        zippel_input_digest: zippel.observation.input_digest,
        zippel_prove_ms: ms(zippel.timing.prove),
        zippel_verify_ms: ms(zippel.timing.verify),
        zippel_proof_digest: zippel.observation.proof_digest,
        zippel_verifier_result_digest: zippel.observation.verifier_result_digest,
        native_input_digest: native.observation.input_digest,
        native_prove_ms: ms(native.timing.prove),
        native_verify_ms: ms(native.timing.verify),
        native_subclaim_digest: native.observation.subclaim_digest,
        zippel_optimizer: zippel
            .optimizer
            .expect("Zippel timed run must include optimizer evidence"),
    }
}

fn summarize_samples(samples: &[SumcheckSample]) -> SumcheckSummary {
    let mut zippel_prove = samples
        .iter()
        .map(|sample| sample.zippel_prove_ms)
        .collect::<Vec<_>>();
    let mut zippel_verify = samples
        .iter()
        .map(|sample| sample.zippel_verify_ms)
        .collect::<Vec<_>>();
    let mut native_prove = samples
        .iter()
        .map(|sample| sample.native_prove_ms)
        .collect::<Vec<_>>();
    let mut native_verify = samples
        .iter()
        .map(|sample| sample.native_verify_ms)
        .collect::<Vec<_>>();
    SumcheckSummary {
        zippel_prove_median_ms: median(&mut zippel_prove),
        zippel_verify_median_ms: median(&mut zippel_verify),
        native_prove_median_ms: median(&mut native_prove),
        native_verify_median_ms: median(&mut native_verify),
    }
}

fn median(values: &mut [f64]) -> f64 {
    debug_assert!(!values.is_empty());
    values.sort_by(|a, b| a.total_cmp(b));
    let mid = values.len() / 2;
    if values.len() % 2 == 0 {
        (values[mid - 1] + values[mid]) / 2.0
    } else {
        values[mid]
    }
}

fn validate_run_artifact(
    run: &SumcheckBenchmarkRun,
    label: &str,
    policy: &SumcheckGatePolicy,
) -> Vec<String> {
    let mut reasons = Vec::new();
    if run.schema_version != SCHEMA_VERSION {
        reasons.push(format!(
            "{label} schema mismatch: got {}, expected {}",
            run.schema_version, SCHEMA_VERSION
        ));
    }
    if run.kind != BENCHMARK_KIND {
        reasons.push(format!(
            "{label} kind mismatch: got `{}`, expected `{}`",
            run.kind, BENCHMARK_KIND
        ));
    }
    if run.config.timing_boundary != TIMING_BOUNDARY {
        reasons.push(format!(
            "{label} timing boundary mismatch: got `{}`, expected `{}`",
            run.config.timing_boundary, TIMING_BOUNDARY
        ));
    }
    if run.config.summary_semantics != SUMMARY_SEMANTICS {
        reasons.push(format!(
            "{label} summary semantics mismatch: got `{}`, expected `{}`",
            run.config.summary_semantics, SUMMARY_SEMANTICS
        ));
    }
    if run.config.correctness_semantics != CORRECTNESS_SEMANTICS {
        reasons.push(format!(
            "{label} correctness semantics mismatch: got `{}`, expected `{}`",
            run.config.correctness_semantics, CORRECTNESS_SEMANTICS
        ));
    }
    if run.config.optimization_semantics != OPTIMIZATION_SEMANTICS {
        reasons.push(format!(
            "{label} optimization semantics mismatch: got `{}`, expected `{}`",
            run.config.optimization_semantics, OPTIMIZATION_SEMANTICS
        ));
    }
    validate_source_identity_fields(&run.config.source_identity, label, &mut reasons);
    if policy.summary_mismatch_abs_tolerance_ms < 0.0
        || !policy.summary_mismatch_abs_tolerance_ms.is_finite()
    {
        reasons.push(format!(
            "policy summary_mismatch_abs_tolerance_ms must be finite and non-negative, got {}",
            policy.summary_mismatch_abs_tolerance_ms
        ));
    }
    if let Err(err) = validate_matrix_values(
        &run.config.num_vars,
        &run.config.max_degrees,
        &run.config.threads,
        &format!("{label} config matrix"),
    ) {
        reasons.push(err);
    }
    if run.config.repeats < policy.min_repeats {
        reasons.push(format!(
            "{label} has insufficient repeats: {} < {}",
            run.config.repeats, policy.min_repeats
        ));
    }
    if run.rows.is_empty() {
        reasons.push(format!("{label} has no benchmark rows"));
    }
    if policy.require_effective_threads {
        validate_capture_processes(run, label, &mut reasons);
    }

    for row in &run.rows {
        if row.system != SYSTEM_NAME {
            reasons.push(format!(
                "{label} row {} has unexpected system `{}`",
                row.case_id, row.system
            ));
        }
        let expected_case_id = case_id(row.num_vars, row.max_degree, row.threads);
        if row.case_id != expected_case_id {
            reasons.push(format!(
                "{label} row case_id mismatch: got `{}`, expected `{expected_case_id}`",
                row.case_id
            ));
        }
        if row.samples.len() != run.config.repeats {
            reasons.push(format!(
                "{label} row {} sample count {} does not match config repeats {}",
                row.case_id,
                row.samples.len(),
                run.config.repeats
            ));
        }
        if row.samples.len() < policy.min_repeats {
            reasons.push(format!(
                "{label} row {} has insufficient samples: {} < {}",
                row.case_id,
                row.samples.len(),
                policy.min_repeats
            ));
        }
        for (expected, sample) in row.samples.iter().enumerate() {
            if sample.sample_index != expected {
                reasons.push(format!(
                    "{label} row {} sample index mismatch: got {}, expected {expected}",
                    row.case_id, sample.sample_index
                ));
            }
            validate_sample_digests(&mut reasons, label, &row.case_id, sample);
            validate_nonnegative_finite(
                &mut reasons,
                label,
                &row.case_id,
                "sample zippel_prove_ms",
                sample.zippel_prove_ms,
            );
            validate_nonnegative_finite(
                &mut reasons,
                label,
                &row.case_id,
                "sample zippel_verify_ms",
                sample.zippel_verify_ms,
            );
            validate_nonnegative_finite(
                &mut reasons,
                label,
                &row.case_id,
                "sample native_prove_ms",
                sample.native_prove_ms,
            );
            validate_nonnegative_finite(
                &mut reasons,
                label,
                &row.case_id,
                "sample native_verify_ms",
                sample.native_verify_ms,
            );
        }
        validate_nonnegative_finite(
            &mut reasons,
            label,
            &row.case_id,
            "summary zippel_prove_median_ms",
            row.summary.zippel_prove_median_ms,
        );
        validate_nonnegative_finite(
            &mut reasons,
            label,
            &row.case_id,
            "summary zippel_verify_median_ms",
            row.summary.zippel_verify_median_ms,
        );
        validate_nonnegative_finite(
            &mut reasons,
            label,
            &row.case_id,
            "summary native_prove_median_ms",
            row.summary.native_prove_median_ms,
        );
        validate_nonnegative_finite(
            &mut reasons,
            label,
            &row.case_id,
            "summary native_verify_median_ms",
            row.summary.native_verify_median_ms,
        );
        match recompute_summary(row) {
            Some(recomputed) => validate_summary_matches(
                &mut reasons,
                label,
                &row.case_id,
                row.summary,
                recomputed,
                policy.summary_mismatch_abs_tolerance_ms,
            ),
            None => reasons.push(format!(
                "SummaryMismatch: {label} row {} has no authoritative recomputable samples",
                row.case_id
            )),
        }
    }

    if policy.require_complete_declared_matrix {
        validate_complete_declared_matrix(run, label, &mut reasons);
    }

    reasons
}

fn validate_source_identity_fields(
    source_identity: &SourceIdentity,
    label: &str,
    reasons: &mut Vec<String>,
) {
    match normalize_logical_path(&source_identity.logical_source_path) {
        Ok(normalized) if normalized == source_identity.logical_source_path => {}
        Ok(normalized) => reasons.push(format!(
            "{label} source_identity.logical_source_path `{}` is not normalized; expected `{normalized}`",
            source_identity.logical_source_path
        )),
        Err(err) => reasons.push(format!(
            "{label} source_identity.logical_source_path is invalid: {err}"
        )),
    }
    if source_identity.domain_separator_session.trim().is_empty() {
        reasons.push(format!(
            "{label} source_identity.domain_separator_session must not be empty"
        ));
    }
    if looks_like_absolute_path(&source_identity.domain_separator_session.replace('\\', "/")) {
        reasons.push(format!(
            "{label} source_identity.domain_separator_session must not be an absolute checkout path"
        ));
    }
    if !is_sha256_digest(&source_identity.source_content_sha256) {
        reasons.push(format!(
            "{label} source_identity.source_content_sha256 `{}` is invalid (expected sha256:<64 hex>)",
            source_identity.source_content_sha256
        ));
    }
    if matches!(source_identity.resolved_source_path.as_deref(), Some("")) {
        reasons.push(format!(
            "{label} source_identity.resolved_source_path must not be empty when recorded"
        ));
    }
}

fn structural_validation_policy() -> SumcheckGatePolicy {
    SumcheckGatePolicy {
        min_repeats: 1,
        ..SumcheckGatePolicy::default()
    }
}

fn validate_matrix_values(
    num_vars: &[usize],
    max_degrees: &[usize],
    threads: &[usize],
    label: &str,
) -> Result<(), String> {
    validate_unique_positive_values(num_vars, "num_vars", label)?;
    validate_unique_positive_values(max_degrees, "max_degrees", label)?;
    validate_unique_positive_values(threads, "threads", label)?;
    Ok(())
}

fn validate_unique_positive_values(
    values: &[usize],
    field: &str,
    label: &str,
) -> Result<(), String> {
    if values.is_empty() {
        return Err(format!("{label} {field} must not be empty"));
    }
    let mut seen = BTreeSet::new();
    for &value in values {
        if value == 0 {
            return Err(format!("{label} {field} entries must be greater than zero"));
        }
        if !seen.insert(value) {
            return Err(format!("{label} {field} contains duplicate entry {value}"));
        }
    }
    Ok(())
}

fn unique_set(values: &[usize]) -> BTreeSet<usize> {
    values.iter().copied().collect()
}

fn expected_case_keys(
    num_vars: &[usize],
    max_degrees: &[usize],
    threads: &[usize],
) -> BTreeSet<CaseKey> {
    let mut out = BTreeSet::new();
    for &thread in threads {
        for &nv in num_vars {
            for &md in max_degrees {
                out.insert(CaseKey {
                    threads: thread,
                    num_vars: nv,
                    max_degree: md,
                });
            }
        }
    }
    out
}

fn validate_capture_processes(run: &SumcheckBenchmarkRun, label: &str, reasons: &mut Vec<String>) {
    if run.capture_processes.is_empty() {
        reasons.push(format!(
            "ThreadCountMismatch: {label} has no capture_processes metadata"
        ));
        return;
    }

    let config_threads = unique_set(&run.config.threads);
    let mut process_threads = BTreeSet::new();
    for (idx, process) in run.capture_processes.iter().enumerate() {
        let location = format!("{label} capture_processes[{idx}]");
        if process.threads == 0 {
            reasons.push(format!("ThreadCountMismatch: {location} threads is zero"));
        }
        if process.effective_rayon_threads == 0 {
            reasons.push(format!(
                "ThreadCountMismatch: {location} effective_rayon_threads is zero"
            ));
        }
        if process.threads != process.effective_rayon_threads {
            reasons.push(format!(
                "ThreadCountMismatch: {location} threads {} != effective_rayon_threads {}",
                process.threads, process.effective_rayon_threads
            ));
        }
        if let Some(raw) = &process.rayon_num_threads_env {
            if let Ok(parsed) = raw.trim().parse::<usize>() {
                if parsed != process.effective_rayon_threads {
                    reasons.push(format!(
                        "ThreadCountMismatch: {location} RAYON_NUM_THREADS={raw:?} parses as {parsed}, but effective_rayon_threads is {}",
                        process.effective_rayon_threads
                    ));
                }
            }
        }
        if !process_threads.insert(process.threads) {
            reasons.push(format!(
                "DuplicateCaptureProcessThread: {label} has multiple capture_processes for threads={}",
                process.threads
            ));
        }
    }

    for thread in config_threads.difference(&process_threads) {
        reasons.push(format!(
            "ThreadCountMismatch: {label} config declares threads={thread}, but no capture_process recorded it"
        ));
    }
    for thread in process_threads.difference(&config_threads) {
        reasons.push(format!(
            "ThreadCountMismatch: {label} capture_process records threads={thread}, but config does not declare it"
        ));
    }
    for row in &run.rows {
        if !process_threads.contains(&row.threads) {
            reasons.push(format!(
                "ThreadCountMismatch: {label} row {} uses threads={}, but no capture_process recorded it",
                row.case_id, row.threads
            ));
        }
    }
}

fn validate_complete_declared_matrix(
    run: &SumcheckBenchmarkRun,
    label: &str,
    reasons: &mut Vec<String>,
) {
    let expected = expected_case_keys(
        &run.config.num_vars,
        &run.config.max_degrees,
        &run.config.threads,
    );
    let mut counts: BTreeMap<CaseKey, Vec<usize>> = BTreeMap::new();
    for (idx, row) in run.rows.iter().enumerate() {
        counts.entry(CaseKey::from_row(row)).or_default().push(idx);
    }
    let actual = counts.keys().copied().collect::<BTreeSet<_>>();

    for (key, indexes) in &counts {
        if indexes.len() > 1 {
            reasons.push(format!(
                "DuplicateCaseRow: {label} duplicate row for case {key} at row indexes {:?}",
                indexes
            ));
        }
    }
    for key in expected.difference(&actual) {
        reasons.push(format!(
            "MissingConfiguredCase: {label} missing configured case {key}"
        ));
    }
    for key in actual.difference(&expected) {
        reasons.push(format!(
            "ExtraUnconfiguredCase: {label} has row outside declared matrix {key}"
        ));
    }
}

fn recompute_summary(row: &SumcheckRow) -> Option<SumcheckSummary> {
    if row.samples.is_empty() {
        return None;
    }
    if row.samples.iter().any(|sample| {
        !sample.zippel_prove_ms.is_finite()
            || sample.zippel_prove_ms < 0.0
            || !sample.zippel_verify_ms.is_finite()
            || sample.zippel_verify_ms < 0.0
            || !sample.native_prove_ms.is_finite()
            || sample.native_prove_ms < 0.0
            || !sample.native_verify_ms.is_finite()
            || sample.native_verify_ms < 0.0
    }) {
        return None;
    }
    Some(summarize_samples(&row.samples))
}

fn validate_summary_matches(
    reasons: &mut Vec<String>,
    label: &str,
    case_id: &str,
    cached: SumcheckSummary,
    recomputed: SumcheckSummary,
    tolerance_ms: f64,
) {
    let fields = [
        (
            "zippel_prove_median_ms",
            cached.zippel_prove_median_ms,
            recomputed.zippel_prove_median_ms,
        ),
        (
            "zippel_verify_median_ms",
            cached.zippel_verify_median_ms,
            recomputed.zippel_verify_median_ms,
        ),
        (
            "native_prove_median_ms",
            cached.native_prove_median_ms,
            recomputed.native_prove_median_ms,
        ),
        (
            "native_verify_median_ms",
            cached.native_verify_median_ms,
            recomputed.native_verify_median_ms,
        ),
    ];
    for (field, cached_value, recomputed_value) in fields {
        let delta = (cached_value - recomputed_value).abs();
        if delta > tolerance_ms {
            reasons.push(format!(
                "SummaryMismatch: {label} row {case_id} cached summary.{field}={cached_value:.12} differs from samples median {recomputed_value:.12} by {delta:.12}ms (tolerance {tolerance_ms:.12}ms)"
            ));
        }
    }
}

fn validate_nonnegative_finite(
    reasons: &mut Vec<String>,
    label: &str,
    case_id: &str,
    field: &str,
    value: f64,
) {
    if !value.is_finite() || value < 0.0 {
        reasons.push(format!(
            "{label} row {case_id} has invalid {field}: {value}"
        ));
    }
}

fn validate_sample_digests(
    reasons: &mut Vec<String>,
    label: &str,
    case_id: &str,
    sample: &SumcheckSample,
) {
    for (field, value) in sample_digest_fields(sample) {
        if !is_sha256_digest(value) {
            reasons.push(format!(
                "{label} row {case_id} sample {} has invalid digest {field}: `{value}` (expected sha256:<64 hex>)",
                sample.sample_index
            ));
        }
    }
}

fn sample_digest_fields(sample: &SumcheckSample) -> [(&'static str, &str); 6] {
    [
        ("input_digest", sample.input_digest.as_str()),
        ("zippel_input_digest", sample.zippel_input_digest.as_str()),
        ("zippel_proof_digest", sample.zippel_proof_digest.as_str()),
        (
            "zippel_verifier_result_digest",
            sample.zippel_verifier_result_digest.as_str(),
        ),
        ("native_input_digest", sample.native_input_digest.as_str()),
        (
            "native_subclaim_digest",
            sample.native_subclaim_digest.as_str(),
        ),
    ]
}

fn is_sha256_digest(value: &str) -> bool {
    let Some(hex) = value.strip_prefix("sha256:") else {
        return false;
    };
    hex.len() == 64 && hex.bytes().all(|byte| byte.is_ascii_hexdigit())
}

fn merge_source_identity_incompatibilities(
    baseline: &SourceIdentity,
    candidate: &SourceIdentity,
    reasons: &mut Vec<String>,
) {
    compare_source_identities(baseline, candidate, reasons);
    if baseline.source_content_sha256 != candidate.source_content_sha256 {
        reasons.push(format!(
            "SourceIdentityMismatch: source_content_sha256 `{}` != `{}`",
            candidate.source_content_sha256, baseline.source_content_sha256
        ));
    }
}

fn compare_source_identities(
    baseline: &SourceIdentity,
    candidate: &SourceIdentity,
    reasons: &mut Vec<String>,
) {
    if baseline.logical_source_path != candidate.logical_source_path {
        reasons.push(format!(
            "SourceIdentityMismatch: logical_source_path baseline `{}` candidate `{}`",
            baseline.logical_source_path, candidate.logical_source_path
        ));
    }
    if baseline.domain_separator_session != candidate.domain_separator_session {
        reasons.push(format!(
            "SourceIdentityMismatch: domain_separator_session baseline `{}` candidate `{}`",
            baseline.domain_separator_session, candidate.domain_separator_session
        ));
    }
}

fn compare_run_configs(
    baseline: &SumcheckBenchmarkRun,
    candidate: &SumcheckBenchmarkRun,
    policy: &SumcheckGatePolicy,
) -> Vec<String> {
    let mut reasons = Vec::new();
    compare_source_identities(
        &baseline.config.source_identity,
        &candidate.config.source_identity,
        &mut reasons,
    );
    if baseline.config.seed != candidate.config.seed {
        reasons.push(format!(
            "seed mismatch: baseline `{}`, candidate `{}`",
            baseline.config.seed, candidate.config.seed
        ));
    }
    if baseline.config.repeats != candidate.config.repeats {
        reasons.push(format!(
            "repeat count mismatch: baseline {}, candidate {}",
            baseline.config.repeats, candidate.config.repeats
        ));
    }
    if baseline.config.warmups != candidate.config.warmups {
        reasons.push(format!(
            "warmup count mismatch: baseline {}, candidate {}",
            baseline.config.warmups, candidate.config.warmups
        ));
    }
    if baseline.config.timing_boundary != candidate.config.timing_boundary {
        reasons.push(format!(
            "timing boundary mismatch: baseline `{}`, candidate `{}`",
            baseline.config.timing_boundary, candidate.config.timing_boundary
        ));
    }
    if baseline.config.summary_semantics != candidate.config.summary_semantics {
        reasons.push(format!(
            "summary semantics mismatch: baseline `{}`, candidate `{}`",
            baseline.config.summary_semantics, candidate.config.summary_semantics
        ));
    }
    if baseline.config.correctness_semantics != candidate.config.correctness_semantics {
        reasons.push(format!(
            "correctness semantics mismatch: baseline `{}`, candidate `{}`",
            baseline.config.correctness_semantics, candidate.config.correctness_semantics
        ));
    }
    if baseline.config.optimization_semantics != candidate.config.optimization_semantics {
        reasons.push(format!(
            "optimization semantics mismatch: baseline `{}`, candidate `{}`",
            baseline.config.optimization_semantics, candidate.config.optimization_semantics
        ));
    }
    if policy.require_same_case_matrix {
        if unique_set(&baseline.config.num_vars) != unique_set(&candidate.config.num_vars) {
            reasons.push(format!(
                "num-vars matrix mismatch: baseline {:?}, candidate {:?}",
                baseline.config.num_vars, candidate.config.num_vars
            ));
        }
        if unique_set(&baseline.config.max_degrees) != unique_set(&candidate.config.max_degrees) {
            reasons.push(format!(
                "max-degree matrix mismatch: baseline {:?}, candidate {:?}",
                baseline.config.max_degrees, candidate.config.max_degrees
            ));
        }
        if unique_set(&baseline.config.threads) != unique_set(&candidate.config.threads) {
            reasons.push(format!(
                "threads matrix mismatch: baseline {:?}, candidate {:?}",
                baseline.config.threads, candidate.config.threads
            ));
        }
    }
    if policy.require_same_toolchain && baseline.metadata.toolchain != candidate.metadata.toolchain
    {
        reasons.push("toolchain metadata mismatch under require_same_toolchain policy".to_string());
    }
    reasons
}

fn collect_row_map(
    run: &SumcheckBenchmarkRun,
    label: &str,
    reasons: &mut Vec<String>,
) -> BTreeMap<CaseKey, usize> {
    let mut map = BTreeMap::new();
    for (idx, row) in run.rows.iter().enumerate() {
        let key = CaseKey::from_row(row);
        if let Some(previous) = map.insert(key, idx) {
            reasons.push(format!(
                "DuplicateCaseRow: {label} duplicate row for case {} (rows {previous} and {idx})",
                row.case_id
            ));
        }
    }
    map
}

fn sample_indices(row: &SumcheckRow) -> Vec<usize> {
    row.samples
        .iter()
        .map(|sample| sample.sample_index)
        .collect()
}

fn compare_correctness_digests(
    baseline: &SumcheckRow,
    candidate: &SumcheckRow,
    mismatches: &mut Vec<String>,
) {
    for (baseline_sample, candidate_sample) in baseline.samples.iter().zip(&candidate.samples) {
        for (field, baseline_value, candidate_value) in
            digest_comparison_fields(baseline_sample, candidate_sample)
        {
            if baseline_value != candidate_value {
                mismatches.push(format!(
                    "CorrectnessMismatch: {} sample {} field {field} differs: baseline `{}` candidate `{}`",
                    baseline.case_id,
                    baseline_sample.sample_index,
                    baseline_value,
                    candidate_value
                ));
            }
        }
    }
}

fn compare_optimizer_evidence(row: &SumcheckRow, mismatches: &mut Vec<String>) {
    for sample in &row.samples {
        let stats = sample.zippel_optimizer;
        let prefix = format!(
            "OptimizerEvidenceMismatch: {} sample {}",
            row.case_id, sample.sample_index
        );
        if stats.canonical_sumcheck_rows_seen == 0 {
            mismatches.push(format!(
                "{prefix} has canonical_sumcheck_rows_seen == 0; expected canonical explicit sumcheck rows"
            ));
        }
        if stats.canonical_sumcheck_rows_fused != stats.canonical_sumcheck_rows_seen {
            mismatches.push(format!(
                "{prefix} fused {} canonical rows but saw {}",
                stats.canonical_sumcheck_rows_fused, stats.canonical_sumcheck_rows_seen
            ));
        }
        if stats.selected_eval_terms_materialized != 0 {
            mismatches.push(format!(
                "{prefix} materialized {} selected-eval term(s); expected zero on the canonical path",
                stats.selected_eval_terms_materialized
            ));
        }
        if stats.selected_eval_interpolation_fallback != 0 {
            mismatches.push(format!(
                "{prefix} used {} selected-eval interpolation fallback(s); expected zero on the canonical path",
                stats.selected_eval_interpolation_fallback
            ));
        }
        if stats.reduce_univariate_post_materialization != 0 {
            mismatches.push(format!(
                "{prefix} used {} post-materialization univariate reduce fallback(s); expected zero on the canonical path",
                stats.reduce_univariate_post_materialization
            ));
        }
    }
}

fn digest_comparison_fields<'a>(
    baseline: &'a SumcheckSample,
    candidate: &'a SumcheckSample,
) -> [(&'static str, &'a str, &'a str); 6] {
    [
        (
            "input_digest",
            baseline.input_digest.as_str(),
            candidate.input_digest.as_str(),
        ),
        (
            "zippel_input_digest",
            baseline.zippel_input_digest.as_str(),
            candidate.zippel_input_digest.as_str(),
        ),
        (
            "zippel_proof_digest",
            baseline.zippel_proof_digest.as_str(),
            candidate.zippel_proof_digest.as_str(),
        ),
        (
            "zippel_verifier_result_digest",
            baseline.zippel_verifier_result_digest.as_str(),
            candidate.zippel_verifier_result_digest.as_str(),
        ),
        (
            "native_input_digest",
            baseline.native_input_digest.as_str(),
            candidate.native_input_digest.as_str(),
        ),
        (
            "native_subclaim_digest",
            baseline.native_subclaim_digest.as_str(),
            candidate.native_subclaim_digest.as_str(),
        ),
    ]
}

fn compare_row(
    baseline: &SumcheckRow,
    baseline_summary: SumcheckSummary,
    candidate_summary: SumcheckSummary,
    policy: &SumcheckGatePolicy,
) -> RowComparison {
    let bp = baseline_summary.zippel_prove_median_ms;
    let cp = candidate_summary.zippel_prove_median_ms;
    let bv = baseline_summary.zippel_verify_median_ms;
    let cv = candidate_summary.zippel_verify_median_ms;
    let bnp = baseline_summary.native_prove_median_ms;
    let cnp = candidate_summary.native_prove_median_ms;
    let bnv = baseline_summary.native_verify_median_ms;
    let cnv = candidate_summary.native_verify_median_ms;

    let zippel_prove_ratio = slowdown_ratio(cp, bp);
    let zippel_verify_ratio = slowdown_ratio(cv, bv);
    let native_prove_drift_ratio = drift_ratio(cnp, bnp);
    let native_verify_drift_ratio = drift_ratio(cnv, bnv);
    let zippel_prove_delta_ms = cp - bp;
    let zippel_verify_delta_ms = cv - bv;
    let native_prove_delta_ms = cnp - bnp;
    let native_verify_delta_ms = cnv - bnv;
    let zippel_prove_eligible = bp >= policy.eligible_min_baseline_ms;
    let zippel_verify_eligible = bv >= policy.eligible_min_baseline_ms;

    let zippel_prove_regression = metric_regressed(
        zippel_prove_ratio,
        zippel_prove_delta_ms,
        zippel_prove_eligible,
        policy,
    );
    let zippel_verify_regression = metric_regressed(
        zippel_verify_ratio,
        zippel_verify_delta_ms,
        zippel_verify_eligible,
        policy,
    );
    let native_drift = native_prove_drift_ratio > policy.native_drift_ratio_limit
        || native_verify_drift_ratio > policy.native_drift_ratio_limit;

    let mut notes = Vec::new();
    if !zippel_prove_eligible {
        notes.push(format!(
            "zippel prove baseline {:.3}ms below ratio eligibility floor {:.3}ms",
            bp, policy.eligible_min_baseline_ms
        ));
    }
    if !zippel_verify_eligible {
        notes.push(format!(
            "zippel verify baseline {:.3}ms below ratio eligibility floor {:.3}ms",
            bv, policy.eligible_min_baseline_ms
        ));
    }

    RowComparison {
        case_id: baseline.case_id.clone(),
        threads: baseline.threads,
        num_vars: baseline.num_vars,
        max_degree: baseline.max_degree,
        zippel_prove_ratio,
        zippel_verify_ratio,
        native_prove_drift_ratio,
        native_verify_drift_ratio,
        zippel_prove_delta_ms,
        zippel_verify_delta_ms,
        native_prove_delta_ms,
        native_verify_delta_ms,
        zippel_prove_eligible,
        zippel_verify_eligible,
        zippel_prove_regression,
        zippel_verify_regression,
        native_drift,
        notes,
    }
}

fn metric_regressed(
    ratio: f64,
    delta_ms: f64,
    eligible: bool,
    policy: &SumcheckGatePolicy,
) -> bool {
    if delta_ms <= 0.0 {
        return false;
    }
    if eligible {
        ratio > policy.per_case_ratio_limit && delta_ms > policy.per_case_abs_slack_ms
    } else {
        delta_ms > policy.per_case_abs_slack_ms
    }
}

fn aggregate_rows(rows: &[RowComparison]) -> AggregateComparison {
    if rows.is_empty() {
        return AggregateComparison::default();
    }

    let mut prove_ratios = Vec::new();
    let mut verify_ratios = Vec::new();
    let mut native_prove_max: f64 = 1.0;
    let mut native_verify_max: f64 = 1.0;

    for row in rows {
        if row.zippel_prove_eligible {
            prove_ratios.push(row.zippel_prove_ratio.max(RATIO_EPSILON_MS));
        }
        if row.zippel_verify_eligible {
            verify_ratios.push(row.zippel_verify_ratio.max(RATIO_EPSILON_MS));
        }
        native_prove_max = native_prove_max.max(row.native_prove_drift_ratio);
        native_verify_max = native_verify_max.max(row.native_verify_drift_ratio);
    }

    let mut combined = prove_ratios.clone();
    combined.extend(verify_ratios.iter().copied());

    AggregateComparison {
        zippel_prove_geomean_ratio: geomean(&prove_ratios),
        zippel_verify_geomean_ratio: geomean(&verify_ratios),
        zippel_combined_geomean_ratio: geomean(&combined),
        native_prove_max_drift_ratio: native_prove_max,
        native_verify_max_drift_ratio: native_verify_max,
        compared_zippel_prove_metrics: prove_ratios.len(),
        compared_zippel_verify_metrics: verify_ratios.len(),
    }
}

fn geomean(values: &[f64]) -> f64 {
    if values.is_empty() {
        1.0
    } else {
        (values
            .iter()
            .map(|v| v.max(RATIO_EPSILON_MS).ln())
            .sum::<f64>()
            / values.len() as f64)
            .exp()
    }
}

fn slowdown_ratio(candidate: f64, baseline: f64) -> f64 {
    candidate.max(RATIO_EPSILON_MS) / baseline.max(RATIO_EPSILON_MS)
}

fn drift_ratio(candidate: f64, baseline: f64) -> f64 {
    let ratio = slowdown_ratio(candidate, baseline);
    ratio.max(1.0 / ratio)
}

fn collect_metadata(command: String) -> RunMetadata {
    let repo_root = repo_root();
    RunMetadata {
        created_at: current_unix_timestamp_string(),
        project: "zippel".to_string(),
        git: GitMetadata {
            commit: command_stdout_in(&repo_root, "git", &["rev-parse", "HEAD"]),
            branch: command_stdout_in(&repo_root, "git", &["rev-parse", "--abbrev-ref", "HEAD"]),
            dirty: git_dirty(&repo_root),
        },
        toolchain: ToolchainMetadata {
            rustc: command_stdout("rustc", &["--version"]),
            cargo: command_stdout("cargo", &["--version"]),
            cargo_lock_sha256: sha256_file(&repo_root.join("Cargo.lock")),
            benchmarks_cargo_lock_sha256: sha256_file(
                &repo_root.join("benchmarks").join("Cargo.lock"),
            ),
        },
        command,
    }
}

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap_or_else(|| Path::new(env!("CARGO_MANIFEST_DIR")))
        .to_path_buf()
}

fn current_unix_timestamp_string() -> String {
    match SystemTime::now().duration_since(UNIX_EPOCH) {
        Ok(duration) => format!("unix:{}", duration.as_secs()),
        Err(_) => "unix:0".to_string(),
    }
}

fn command_stdout(program: &str, args: &[&str]) -> Option<String> {
    Command::new(program)
        .args(args)
        .output()
        .ok()
        .filter(|output| output.status.success())
        .map(|output| String::from_utf8_lossy(&output.stdout).trim().to_string())
        .filter(|s| !s.is_empty())
}

fn command_stdout_in(dir: &Path, program: &str, args: &[&str]) -> Option<String> {
    Command::new(program)
        .current_dir(dir)
        .args(args)
        .output()
        .ok()
        .filter(|output| output.status.success())
        .map(|output| String::from_utf8_lossy(&output.stdout).trim().to_string())
        .filter(|s| !s.is_empty())
}

fn git_dirty(repo_root: &Path) -> Option<bool> {
    Command::new("git")
        .current_dir(repo_root)
        .args(["status", "--porcelain"])
        .output()
        .ok()
        .filter(|output| output.status.success())
        .map(|output| !output.stdout.is_empty())
}

fn sha256_file(path: &Path) -> Option<String> {
    let bytes = fs::read(path).ok()?;
    Some(format!("{:x}", Sha256::digest(&bytes)))
}

fn write_json_atomic<T: Serialize>(path: &Path, value: &T) -> Result<(), GateIoError> {
    if let Some(parent) = path.parent() {
        if !parent.as_os_str().is_empty() {
            fs::create_dir_all(parent)?;
        }
    }

    let tmp = temporary_path_for(path);
    let bytes = serde_json::to_vec_pretty(value)?;
    fs::write(&tmp, bytes)?;
    if path.exists() {
        fs::remove_file(path)?;
    }
    fs::rename(&tmp, path)?;
    Ok(())
}

fn temporary_path_for(path: &Path) -> PathBuf {
    let mut name = path
        .file_name()
        .map(|name| name.to_os_string())
        .unwrap_or_else(|| "sumcheck-gate".into());
    name.push(format!(".tmp.{}", std::process::id()));
    match path.parent() {
        Some(parent) if !parent.as_os_str().is_empty() => parent.join(name),
        _ => PathBuf::from(name),
    }
}

fn ms(duration: std::time::Duration) -> f64 {
    duration.as_secs_f64() * 1000.0
}

fn derive_sample_seed(
    base_seed: u64,
    threads: usize,
    num_vars: usize,
    max_degree: usize,
    sample_index: u64,
    warmup: bool,
) -> u64 {
    let mut state = base_seed;
    state = mix_u64(state ^ threads as u64);
    state = mix_u64(state ^ ((num_vars as u64) << 17));
    state = mix_u64(state ^ ((max_degree as u64) << 33));
    state = mix_u64(state ^ sample_index);
    if warmup {
        state = mix_u64(state ^ 0xa5a5_a5a5_a5a5_a5a5);
    }
    state
}

fn mix_u64(mut x: u64) -> u64 {
    // splitmix64 finalizer: deterministic and cheap, not used for crypto.
    x = x.wrapping_add(0x9e37_79b9_7f4a_7c15);
    x = (x ^ (x >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    x = (x ^ (x >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    x ^ (x >> 31)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn policy() -> SumcheckGatePolicy {
        SumcheckGatePolicy {
            min_repeats: 3,
            ..SumcheckGatePolicy::default()
        }
    }

    fn default_source_identity() -> SourceIdentity {
        SourceIdentity {
            logical_source_path: DEFAULT_SOURCE_PATH.to_string(),
            source_content_sha256: test_digest("source-content", 0),
            domain_separator_session: DEFAULT_SOURCE_PATH.to_string(),
            resolved_source_path: Some("C:/checkout/examples/sumcheck/sumcheck.zippel".to_string()),
        }
    }

    fn run_with_row(summary: SumcheckSummary) -> SumcheckBenchmarkRun {
        run_with_case(10, 3, 1, summary)
    }

    fn run_with_case(
        num_vars: usize,
        max_degree: usize,
        threads: usize,
        summary: SumcheckSummary,
    ) -> SumcheckBenchmarkRun {
        run_with_rows(
            vec![num_vars],
            vec![max_degree],
            vec![threads],
            vec![row_from_summary(num_vars, max_degree, threads, summary)],
        )
    }

    fn run_with_rows(
        num_vars: Vec<usize>,
        max_degrees: Vec<usize>,
        threads: Vec<usize>,
        rows: Vec<SumcheckRow>,
    ) -> SumcheckBenchmarkRun {
        SumcheckBenchmarkRun {
            schema_version: SCHEMA_VERSION,
            kind: BENCHMARK_KIND.to_string(),
            metadata: test_metadata(),
            config: SumcheckRunConfig {
                source_path: DEFAULT_SOURCE_PATH.to_string(),
                source_identity: default_source_identity(),
                num_vars,
                max_degrees,
                threads: threads.clone(),
                repeats: 3,
                warmups: 1,
                seed: format_seed(0x5eed_5eed),
                timing_boundary: TIMING_BOUNDARY.to_string(),
                summary_semantics: SUMMARY_SEMANTICS.to_string(),
                correctness_semantics: CORRECTNESS_SEMANTICS.to_string(),
                optimization_semantics: OPTIMIZATION_SEMANTICS.to_string(),
            },
            capture_processes: threads
                .into_iter()
                .map(|thread| CaptureProcessMetadata {
                    threads: thread,
                    effective_rayon_threads: thread,
                    rayon_num_threads_env: Some(thread.to_string()),
                    command: "test capture".to_string(),
                })
                .collect(),
            rows,
        }
    }

    fn test_metadata() -> RunMetadata {
        RunMetadata {
            created_at: "test".to_string(),
            project: "zippel".to_string(),
            git: GitMetadata {
                commit: Some("abc".to_string()),
                branch: Some("test".to_string()),
                dirty: Some(false),
            },
            toolchain: ToolchainMetadata {
                rustc: Some("rustc test".to_string()),
                cargo: Some("cargo test".to_string()),
                cargo_lock_sha256: Some("root".to_string()),
                benchmarks_cargo_lock_sha256: Some("benchmarks".to_string()),
            },
            command: "test".to_string(),
        }
    }

    fn row_from_summary(
        num_vars: usize,
        max_degree: usize,
        threads: usize,
        summary: SumcheckSummary,
    ) -> SumcheckRow {
        let samples = samples_from_summary(summary);
        SumcheckRow {
            case_id: case_id(num_vars, max_degree, threads),
            system: SYSTEM_NAME.to_string(),
            threads,
            num_vars,
            max_degree,
            samples,
            summary,
        }
    }

    fn samples_from_summary(summary: SumcheckSummary) -> Vec<SumcheckSample> {
        (0..3)
            .map(|sample_index| SumcheckSample {
                sample_index,
                input_digest: test_digest("zippel-input", sample_index),
                zippel_input_digest: test_digest("zippel-input", sample_index),
                zippel_prove_ms: summary.zippel_prove_median_ms,
                zippel_verify_ms: summary.zippel_verify_median_ms,
                zippel_proof_digest: test_digest("zippel-proof", sample_index),
                zippel_verifier_result_digest: test_digest("zippel-verifier", sample_index),
                native_input_digest: test_digest("native-input", sample_index),
                native_prove_ms: summary.native_prove_median_ms,
                native_verify_ms: summary.native_verify_median_ms,
                native_subclaim_digest: test_digest("native-subclaim", sample_index),
                zippel_optimizer: test_optimizer_evidence(),
            })
            .collect::<Vec<_>>()
    }

    fn test_optimizer_evidence() -> OptimizationStats {
        OptimizationStats {
            selected_eval_terms_materialized: 0,
            selected_eval_interpolation_fallback: 0,
            reduce_univariate_post_materialization: 0,
            canonical_sumcheck_rows_seen: 1,
            canonical_sumcheck_rows_fused: 1,
        }
    }

    fn test_digest(label: &str, sample_index: usize) -> String {
        let mut hasher = Sha256::new();
        hasher.update(label.as_bytes());
        hasher.update([0]);
        hasher.update((sample_index as u64).to_le_bytes());
        format!("sha256:{:x}", hasher.finalize())
    }

    fn replacement_digest(label: &str) -> String {
        test_digest(label, 99)
    }

    fn example_source_absolute_path() -> PathBuf {
        repo_root().join(DEFAULT_SOURCE_PATH)
    }

    fn external_source_copy() -> (tempfile::TempDir, PathBuf) {
        let temp_dir = tempfile::tempdir().unwrap();
        let source_path = temp_dir.path().join("sumcheck-copy.zippel");
        fs::copy(example_source_absolute_path(), &source_path).unwrap();
        (temp_dir, source_path)
    }

    fn summary(zp: f64, zv: f64, np: f64, nv: f64) -> SumcheckSummary {
        SumcheckSummary {
            zippel_prove_median_ms: zp,
            zippel_verify_median_ms: zv,
            native_prove_median_ms: np,
            native_verify_median_ms: nv,
        }
    }

    #[test]
    fn source_identity_from_relative_source_path_is_repo_logical() {
        let config = SumcheckCaptureConfig {
            source_path: DEFAULT_SOURCE_PATH.to_string(),
            repeats: 1,
            ..SumcheckCaptureConfig::default()
        };
        let resolved = resolve_source_identity(&config).unwrap();
        assert_eq!(resolved.identity.logical_source_path, DEFAULT_SOURCE_PATH);
        assert_eq!(
            resolved.identity.domain_separator_session,
            DEFAULT_SOURCE_PATH
        );
        assert!(is_sha256_digest(&resolved.identity.source_content_sha256));
        assert!(resolved.file_path.is_absolute());
    }

    #[test]
    fn source_identity_from_absolute_repo_path_is_repo_relative() {
        let config = SumcheckCaptureConfig {
            source_path: example_source_absolute_path().display().to_string(),
            repeats: 1,
            ..SumcheckCaptureConfig::default()
        };
        let resolved = resolve_source_identity(&config).unwrap();
        assert_eq!(resolved.identity.logical_source_path, DEFAULT_SOURCE_PATH);
        assert_eq!(
            resolved.identity.domain_separator_session,
            DEFAULT_SOURCE_PATH
        );
        assert!(is_sha256_digest(&resolved.identity.source_content_sha256));
    }

    #[test]
    fn source_identity_requires_logical_path_for_external_absolute_source() {
        let (_temp_dir, source_path) = external_source_copy();
        let config = SumcheckCaptureConfig {
            source_path: source_path.display().to_string(),
            logical_source_path: None,
            repeats: 1,
            ..SumcheckCaptureConfig::default()
        };
        let err = resolve_source_identity(&config).unwrap_err();
        assert!(err.contains("requires --logical-source-path"), "{err}");
    }

    #[test]
    fn source_identity_accepts_external_source_with_logical_path() {
        let (_temp_dir, source_path) = external_source_copy();
        let config = SumcheckCaptureConfig {
            source_path: source_path.display().to_string(),
            logical_source_path: Some("logical/sumcheck.zippel".to_string()),
            repeats: 1,
            ..SumcheckCaptureConfig::default()
        };
        let resolved = resolve_source_identity(&config).unwrap();
        assert_eq!(
            resolved.identity.logical_source_path,
            "logical/sumcheck.zippel"
        );
        assert_eq!(
            resolved.identity.domain_separator_session,
            "logical/sumcheck.zippel"
        );
    }

    #[test]
    fn source_identity_normalizes_backslashes() {
        let config = SumcheckCaptureConfig {
            source_path: DEFAULT_SOURCE_PATH.replace('/', "\\"),
            repeats: 1,
            ..SumcheckCaptureConfig::default()
        };
        let resolved = resolve_source_identity(&config).unwrap();
        assert_eq!(resolved.identity.logical_source_path, DEFAULT_SOURCE_PATH);
    }

    #[test]
    fn source_identity_rejects_parent_segments() {
        let (_temp_dir, source_path) = external_source_copy();
        let config = SumcheckCaptureConfig {
            source_path: source_path.display().to_string(),
            logical_source_path: Some("logical/../sumcheck.zippel".to_string()),
            repeats: 1,
            ..SumcheckCaptureConfig::default()
        };
        let err = resolve_source_identity(&config).unwrap_err();
        assert!(err.contains("must not contain `..`"), "{err}");
    }

    #[test]
    fn compare_identical_artifacts_passes() {
        let baseline = run_with_row(summary(10.0, 5.0, 8.0, 4.0));
        let candidate = baseline.clone();
        let report = compare_sumcheck_benchmark(&baseline, &candidate, policy());
        assert_eq!(report.outcome, GateOutcome::Pass);
        assert!(report.refusal_reasons.is_empty());
        assert!(report.regression_reasons.is_empty());
    }

    #[test]
    fn schema_mismatch_is_incomparable() {
        let baseline = run_with_row(summary(10.0, 5.0, 8.0, 4.0));
        let mut candidate = baseline.clone();
        candidate.schema_version = 1;
        let report = compare_sumcheck_benchmark(&baseline, &candidate, policy());
        assert_eq!(report.outcome, GateOutcome::Incomparable);
        assert!(
            report
                .refusal_reasons
                .iter()
                .any(|reason| reason.contains("schema mismatch"))
        );
    }

    #[test]
    fn matrix_mismatch_is_incomparable() {
        let baseline = run_with_row(summary(10.0, 5.0, 8.0, 4.0));
        let mut candidate = baseline.clone();
        candidate.rows[0].num_vars = 12;
        candidate.rows[0].case_id = case_id(12, 3, 1);
        candidate.config.num_vars = vec![12];
        let report = compare_sumcheck_benchmark(&baseline, &candidate, policy());
        assert_eq!(report.outcome, GateOutcome::Incomparable);
        assert!(
            report
                .refusal_reasons
                .iter()
                .any(|reason| reason.contains("matrix mismatch"))
        );
    }

    #[test]
    fn sample_count_mismatch_is_incomparable() {
        let baseline = run_with_row(summary(10.0, 5.0, 8.0, 4.0));
        let mut candidate = baseline.clone();
        candidate.rows[0].samples.pop();
        let report = compare_sumcheck_benchmark(&baseline, &candidate, policy());
        assert_eq!(report.outcome, GateOutcome::Incomparable);
        assert!(
            report
                .refusal_reasons
                .iter()
                .any(|reason| reason.contains("sample count"))
        );
    }

    #[test]
    fn stale_summary_is_rejected_and_samples_drive_row_ratios() {
        let baseline = run_with_row(summary(10.0, 5.0, 8.0, 4.0));
        let mut candidate = baseline.clone();
        for sample in &mut candidate.rows[0].samples {
            sample.zippel_prove_ms = 30.0;
        }
        // Deliberately leave candidate.rows[0].summary at 10ms. The cached
        // summary claims parity, but the authoritative samples are 3x slower.
        let report = compare_sumcheck_benchmark(&baseline, &candidate, policy());
        assert_eq!(report.outcome, GateOutcome::Incomparable);
        assert!(
            report
                .refusal_reasons
                .iter()
                .any(|reason| reason.contains("SummaryMismatch"))
        );
        assert_eq!(report.row_results.len(), 1);
        assert!((report.row_results[0].zippel_prove_ratio - 3.0).abs() < 1.0e-12);
    }

    #[test]
    fn missing_configured_row_is_rejected() {
        let run = run_with_rows(
            vec![10, 12],
            vec![3],
            vec![1],
            vec![row_from_summary(10, 3, 1, summary(1.0, 1.0, 1.0, 1.0))],
        );
        let reasons = validate_run_artifact(&run, "test", &policy());
        assert!(
            reasons
                .iter()
                .any(|reason| reason.contains("MissingConfiguredCase"))
        );
    }

    #[test]
    fn extra_unconfigured_row_is_rejected() {
        let run = run_with_rows(
            vec![10],
            vec![3],
            vec![1],
            vec![
                row_from_summary(10, 3, 1, summary(1.0, 1.0, 1.0, 1.0)),
                row_from_summary(12, 3, 1, summary(1.0, 1.0, 1.0, 1.0)),
            ],
        );
        let reasons = validate_run_artifact(&run, "test", &policy());
        assert!(
            reasons
                .iter()
                .any(|reason| reason.contains("ExtraUnconfiguredCase"))
        );
    }

    #[test]
    fn duplicate_case_row_is_rejected() {
        let row = row_from_summary(10, 3, 1, summary(1.0, 1.0, 1.0, 1.0));
        let run = run_with_rows(vec![10], vec![3], vec![1], vec![row.clone(), row]);
        let reasons = validate_run_artifact(&run, "test", &policy());
        assert!(
            reasons
                .iter()
                .any(|reason| reason.contains("DuplicateCaseRow"))
        );
    }

    #[test]
    fn multi_thread_capture_config_is_rejected() {
        let config = SumcheckCaptureConfig {
            threads: vec![1, 2],
            repeats: 1,
            ..SumcheckCaptureConfig::default()
        };
        let err = validate_capture_config(&config).unwrap_err();
        assert!(err.contains("exactly one threads-label"));
    }

    #[test]
    fn effective_thread_mismatch_is_rejected() {
        let err = validate_effective_thread_count(1, 2, Some("2")).unwrap_err();
        assert!(err.contains("ThreadCountMismatch"));
        assert!(err.contains("--threads-label"));
    }

    #[test]
    fn rayon_env_thread_mismatch_is_rejected() {
        let err = validate_effective_thread_count(2, 2, Some("1")).unwrap_err();
        assert!(err.contains("RAYON_NUM_THREADS"));
    }

    #[test]
    fn artifact_thread_metadata_mismatch_is_rejected() {
        let mut run = run_with_row(summary(1.0, 1.0, 1.0, 1.0));
        run.capture_processes[0].effective_rayon_threads = 2;
        let reasons = validate_run_artifact(&run, "test", &policy());
        assert!(
            reasons
                .iter()
                .any(|reason| reason.contains("ThreadCountMismatch"))
        );
    }

    #[test]
    fn native_drift_is_incomparable_not_regression() {
        let baseline = run_with_row(summary(10.0, 5.0, 8.0, 4.0));
        let candidate = run_with_row(summary(10.0, 5.0, 20.1, 4.0));
        let report = compare_sumcheck_benchmark(&baseline, &candidate, policy());
        assert_eq!(report.outcome, GateOutcome::Incomparable);
        assert!(report.regression_reasons.is_empty());
        assert!(
            report
                .refusal_reasons
                .iter()
                .any(|reason| reason.contains("native drift"))
        );
    }

    #[test]
    fn zippel_regression_exceeding_ratio_and_slack_fails() {
        let baseline = run_with_row(summary(10.0, 5.0, 8.0, 4.0));
        let candidate = run_with_row(summary(12.5, 5.0, 8.0, 4.0));
        let report = compare_sumcheck_benchmark(&baseline, &candidate, policy());
        assert_eq!(report.outcome, GateOutcome::Regression);
        assert!(
            report
                .regression_reasons
                .iter()
                .any(|reason| reason.contains("zippel prove regression"))
        );
    }

    #[test]
    fn invalid_correctness_digest_is_rejected() {
        let mut run = run_with_row(summary(10.0, 5.0, 8.0, 4.0));
        run.rows[0].samples[1].zippel_proof_digest = "not-a-sha256-digest".to_string();
        let reasons = validate_run_artifact(&run, "test", &policy());
        assert!(
            reasons.iter().any(|reason| {
                reason.contains("invalid digest zippel_proof_digest")
                    && reason.contains("sha256:<64 hex>")
            }),
            "expected invalid digest rejection, got {reasons:?}"
        );
    }

    #[test]
    fn invalid_source_identity_digest_is_rejected() {
        let mut run = run_with_row(summary(10.0, 5.0, 8.0, 4.0));
        run.config.source_identity.source_content_sha256 = "not-a-sha256-digest".to_string();
        let reasons = validate_run_artifact(&run, "test", &policy());
        assert!(
            reasons.iter().any(|reason| {
                reason.contains("source_identity.source_content_sha256")
                    && reason.contains("sha256:<64 hex>")
            }),
            "expected invalid source identity digest rejection, got {reasons:?}"
        );
    }

    #[test]
    fn missing_correctness_digest_is_a_parse_error() {
        let mut value = serde_json::to_value(run_with_row(summary(1.0, 1.0, 1.0, 1.0))).unwrap();
        value["rows"][0]["samples"][0]
            .as_object_mut()
            .unwrap()
            .remove("zippel_proof_digest");
        let parsed = serde_json::from_value::<SumcheckBenchmarkRun>(value);
        assert!(parsed.is_err());
    }

    #[test]
    fn missing_optimizer_evidence_is_a_parse_error() {
        let mut value = serde_json::to_value(run_with_row(summary(1.0, 1.0, 1.0, 1.0))).unwrap();
        value["rows"][0]["samples"][0]
            .as_object_mut()
            .unwrap()
            .remove("zippel_optimizer");
        let parsed = serde_json::from_value::<SumcheckBenchmarkRun>(value);
        assert!(parsed.is_err());
    }

    #[test]
    fn selected_eval_materialization_evidence_is_optimizer_mismatch() {
        let baseline = run_with_row(summary(10.0, 5.0, 8.0, 4.0));
        let mut candidate = baseline.clone();
        candidate.rows[0].samples[0]
            .zippel_optimizer
            .selected_eval_terms_materialized = 1;
        let report = compare_sumcheck_benchmark(&baseline, &candidate, policy());
        assert_eq!(report.outcome, GateOutcome::OptimizerEvidenceMismatch);
        assert!(report.optimizer_evidence_mismatch_reasons.iter().any(|reason| {
            reason.contains("materialized 1 selected-eval")
        }));
    }

    #[test]
    fn interpolation_fallback_evidence_is_optimizer_mismatch() {
        let baseline = run_with_row(summary(10.0, 5.0, 8.0, 4.0));
        let mut candidate = baseline.clone();
        candidate.rows[0].samples[0]
            .zippel_optimizer
            .selected_eval_interpolation_fallback = 1;
        let report = compare_sumcheck_benchmark(&baseline, &candidate, policy());
        assert_eq!(report.outcome, GateOutcome::OptimizerEvidenceMismatch);
        assert!(report.optimizer_evidence_mismatch_reasons.iter().any(|reason| {
            reason.contains("interpolation fallback")
        }));
    }

    #[test]
    fn mixed_fused_and_post_materialization_reduce_evidence_is_optimizer_mismatch() {
        let baseline = run_with_row(summary(10.0, 5.0, 8.0, 4.0));
        let mut candidate = baseline.clone();
        candidate.rows[0].samples[0]
            .zippel_optimizer
            .reduce_univariate_post_materialization = 1;
        let report = compare_sumcheck_benchmark(&baseline, &candidate, policy());
        assert_eq!(report.outcome, GateOutcome::OptimizerEvidenceMismatch);
        assert!(report.optimizer_evidence_mismatch_reasons.iter().any(|reason| {
            reason.contains("post-materialization univariate reduce fallback")
        }));
    }

    #[test]
    fn zippel_input_digest_mismatch_is_correctness_mismatch() {
        let baseline = run_with_row(summary(10.0, 5.0, 8.0, 4.0));
        let mut candidate = baseline.clone();
        candidate.rows[0].samples[0].zippel_input_digest = replacement_digest("changed-input");
        let report = compare_sumcheck_benchmark(&baseline, &candidate, policy());
        assert_eq!(report.outcome, GateOutcome::CorrectnessMismatch);
        assert!(report.regression_reasons.is_empty());
        assert!(
            report
                .correctness_mismatch_reasons
                .iter()
                .any(|reason| reason.contains("zippel_input_digest"))
        );
    }

    #[test]
    fn source_identity_mismatch_is_incomparable_not_correctness_mismatch() {
        let baseline = run_with_row(summary(10.0, 5.0, 8.0, 4.0));
        let mut candidate = baseline.clone();
        candidate.config.source_identity.logical_source_path = "other/sumcheck.zippel".to_string();
        candidate.rows[0].samples[0].zippel_proof_digest = replacement_digest("changed-proof");
        let report = compare_sumcheck_benchmark(&baseline, &candidate, policy());
        assert_eq!(report.outcome, GateOutcome::Incomparable);
        assert!(
            report
                .refusal_reasons
                .iter()
                .any(|reason| reason.contains("SourceIdentityMismatch")),
            "expected SourceIdentityMismatch, got {:?}",
            report.refusal_reasons
        );
        assert!(report.correctness_mismatch_reasons.is_empty());
    }

    #[test]
    fn resolved_source_path_difference_does_not_affect_compare() {
        let baseline = run_with_row(summary(10.0, 5.0, 8.0, 4.0));
        let mut candidate = baseline.clone();
        candidate.config.source_path =
            "D:/different-checkout/examples/sumcheck/sumcheck.zippel".to_string();
        candidate.config.source_identity.resolved_source_path =
            Some("D:/different-checkout/examples/sumcheck/sumcheck.zippel".to_string());
        let report = compare_sumcheck_benchmark(&baseline, &candidate, policy());
        assert_eq!(report.outcome, GateOutcome::Pass);
    }

    #[test]
    fn correctness_mismatch_beats_timing_regression() {
        let baseline = run_with_row(summary(10.0, 5.0, 8.0, 4.0));
        let mut candidate = run_with_row(summary(20.0, 5.0, 8.0, 4.0));
        candidate.rows[0].samples[0].zippel_proof_digest = replacement_digest("changed-proof");
        let report = compare_sumcheck_benchmark(&baseline, &candidate, policy());
        assert_eq!(report.outcome, GateOutcome::CorrectnessMismatch);
        assert!(report.regression_reasons.is_empty());
        assert!(
            report
                .correctness_mismatch_reasons
                .iter()
                .any(|reason| reason.contains("zippel_proof_digest"))
        );
    }

    #[test]
    fn native_subclaim_digest_mismatch_is_correctness_mismatch() {
        let baseline = run_with_row(summary(10.0, 5.0, 8.0, 4.0));
        let mut candidate = baseline.clone();
        candidate.rows[0].samples[2].native_subclaim_digest =
            replacement_digest("changed-native-subclaim");
        let report = compare_sumcheck_benchmark(&baseline, &candidate, policy());
        assert_eq!(report.outcome, GateOutcome::CorrectnessMismatch);
        assert!(
            report
                .correctness_mismatch_reasons
                .iter()
                .any(|reason| reason.contains("native_subclaim_digest"))
        );
    }

    #[test]
    fn tiny_ratio_only_does_not_fail_until_abs_slack_exceeded() {
        let baseline = run_with_row(summary(0.10, 0.10, 8.0, 4.0));
        let candidate = run_with_row(summary(0.19, 0.19, 8.0, 4.0));
        let report = compare_sumcheck_benchmark(&baseline, &candidate, policy());
        assert_eq!(report.outcome, GateOutcome::Pass);

        let candidate = run_with_row(summary(0.70, 0.10, 8.0, 4.0));
        let report = compare_sumcheck_benchmark(&baseline, &candidate, policy());
        assert_eq!(report.outcome, GateOutcome::Regression);
    }

    #[test]
    fn merge_single_thread_parts_successfully() {
        let part1 = run_with_case(10, 3, 1, summary(1.0, 1.0, 1.0, 1.0));
        let part2 = run_with_case(10, 3, 2, summary(2.0, 1.0, 1.0, 1.0));
        let merged = merge_sumcheck_benchmark_runs(
            &[part1, part2],
            &SumcheckMergeConfig {
                num_vars: vec![10],
                max_degrees: vec![3],
                threads: vec![1, 2],
                command: "test merge".to_string(),
            },
        )
        .unwrap();
        assert_eq!(merged.config.threads, vec![1, 2]);
        assert_eq!(merged.capture_processes.len(), 2);
        assert_eq!(merged.rows.len(), 2);
    }

    #[test]
    fn merge_rejects_source_content_digest_mismatch() {
        let part1 = run_with_case(10, 3, 1, summary(1.0, 1.0, 1.0, 1.0));
        let mut part2 = run_with_case(10, 3, 2, summary(2.0, 1.0, 1.0, 1.0));
        part2.config.source_identity.source_content_sha256 = replacement_digest("changed-source");
        let err = merge_sumcheck_benchmark_runs(
            &[part1, part2],
            &SumcheckMergeConfig {
                num_vars: vec![10],
                max_degrees: vec![3],
                threads: vec![1, 2],
                command: "test merge".to_string(),
            },
        )
        .unwrap_err();
        assert!(err.to_string().contains("SourceIdentityMismatch"));
    }

    #[test]
    fn merge_ignores_resolved_source_path_difference() {
        let part1 = run_with_case(10, 3, 1, summary(1.0, 1.0, 1.0, 1.0));
        let mut part2 = run_with_case(10, 3, 2, summary(2.0, 1.0, 1.0, 1.0));
        part2.config.source_identity.resolved_source_path =
            Some("D:/different-checkout/examples/sumcheck/sumcheck.zippel".to_string());
        let merged = merge_sumcheck_benchmark_runs(
            &[part1, part2],
            &SumcheckMergeConfig {
                num_vars: vec![10],
                max_degrees: vec![3],
                threads: vec![1, 2],
                command: "test merge".to_string(),
            },
        )
        .unwrap();
        assert_eq!(merged.rows.len(), 2);
    }

    #[test]
    fn merge_rejects_duplicate_case_rows() {
        let part1 = run_with_case(10, 3, 1, summary(1.0, 1.0, 1.0, 1.0));
        let err = merge_sumcheck_benchmark_runs(
            &[part1.clone(), part1],
            &SumcheckMergeConfig {
                num_vars: vec![10],
                max_degrees: vec![3],
                threads: vec![1],
                command: "test merge".to_string(),
            },
        )
        .unwrap_err();
        assert!(err.to_string().contains("DuplicateCaseRow"));
    }

    #[test]
    fn merge_rejects_missing_declared_cases() {
        let part1 = run_with_case(10, 3, 1, summary(1.0, 1.0, 1.0, 1.0));
        let err = merge_sumcheck_benchmark_runs(
            &[part1],
            &SumcheckMergeConfig {
                num_vars: vec![10],
                max_degrees: vec![3],
                threads: vec![1, 2],
                command: "test merge".to_string(),
            },
        )
        .unwrap_err();
        assert!(err.to_string().contains("MissingConfiguredCase"));
    }

    #[test]
    fn merge_rejects_extra_unconfigured_cases() {
        let part1 = run_with_case(10, 3, 1, summary(1.0, 1.0, 1.0, 1.0));
        let part2 = run_with_case(10, 3, 2, summary(2.0, 1.0, 1.0, 1.0));
        let err = merge_sumcheck_benchmark_runs(
            &[part1, part2],
            &SumcheckMergeConfig {
                num_vars: vec![10],
                max_degrees: vec![3],
                threads: vec![1],
                command: "test merge".to_string(),
            },
        )
        .unwrap_err();
        assert!(err.to_string().contains("ExtraUnconfiguredCase"));
    }

    #[test]
    fn merge_rejects_incompatible_metadata() {
        let part1 = run_with_case(10, 3, 1, summary(1.0, 1.0, 1.0, 1.0));
        let mut part2 = run_with_case(10, 3, 2, summary(2.0, 1.0, 1.0, 1.0));
        part2.metadata.git.commit = Some("def".to_string());
        let err = merge_sumcheck_benchmark_runs(
            &[part1, part2],
            &SumcheckMergeConfig {
                num_vars: vec![10],
                max_degrees: vec![3],
                threads: vec![1, 2],
                command: "test merge".to_string(),
            },
        )
        .unwrap_err();
        assert!(err.to_string().contains("git metadata differs"));
    }

    #[test]
    fn missing_max_degree_is_a_parse_error() {
        let mut value = serde_json::to_value(run_with_row(summary(1.0, 1.0, 1.0, 1.0))).unwrap();
        value["rows"][0]
            .as_object_mut()
            .unwrap()
            .remove("max_degree");
        let parsed = serde_json::from_value::<SumcheckBenchmarkRun>(value);
        assert!(parsed.is_err());
    }

    #[test]
    fn parses_comma_lists_and_inclusive_ranges() {
        assert_eq!(parse_usize_grid("4,8,12").unwrap(), vec![4, 8, 12]);
        assert_eq!(parse_usize_grid("3..5").unwrap(), vec![3, 4, 5]);
        assert_eq!(parse_usize_grid("3..=5").unwrap(), vec![3, 4, 5]);
    }
}
