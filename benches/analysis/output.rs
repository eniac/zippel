//! The JSON lines the `analysis` bench prints.
//!
//! The goals are what the analysis checks against its basis: the verifier
//! polynomials for completeness, the relation polynomials for soundness.
//! Every line reports peak memory as of that line (see
//! `memory::peak_rss_mib`), so a run killed at a timeout keeps its last
//! values.

use std::io::Write as _;

use analyses::frontend::Polynomial;
use backend::{ArkBls12_381, ArkConfig};
use serde::Serialize;

use crate::memory::peak_rss_mib;

pub type Poly = Polynomial<<ArkBls12_381 as ArkConfig>::F>;

/// The status of a run.
#[derive(Serialize, Default, Clone, Copy)]
#[serde(rename_all = "lowercase")]
pub enum Status {
    /// A partial line: the run has not finished.
    #[default]
    Running,
    /// The analysis established the property.
    Ok,
    /// The analysis did not establish the property, with the reason in
    /// `error`: for completeness a verifier check that does not reduce to
    /// zero; for soundness no extractor, a unit ideal, an extractor that does
    /// not establish the relation, or a protocol that is not 2n+1-move for
    /// its round parameters.
    Failed,
    /// Stopped after building the ideal (`--build-only`).
    Built,
    /// A real bug or panic.
    Crashed,
    /// Out of memory under `--memory-limit-mb`.
    Oom,
}

/// JSON output emitted by the `analysis` bench. Partial lines (status
/// `"running"`) omit fields that aren't available yet. The final line
/// has the final status.
#[derive(Serialize, Default)]
pub struct BenchOutput {
    protocol: String,
    status: Status,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub build_ms: Option<f64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub gb_ms: Option<f64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub run_ms: Option<f64>,
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
    /// A `running` output for `protocol`, whose DAG has `graph_size` nodes.
    pub fn new(protocol: &str, graph_size: usize) -> Self {
        Self {
            protocol: protocol.to_string(),
            graph_size: Some(graph_size),
            ..Default::default()
        }
    }

    /// A line with only a protocol, a status and an error. It carries no
    /// metrics; `analysis_all` merges in those from earlier lines.
    pub fn line(protocol: &str, status: Status, error: Option<String>) -> String {
        serde_json::to_string(&Self {
            protocol: protocol.to_string(),
            status,
            error,
            ..Default::default()
        })
        .unwrap()
    }

    /// Records the shape of the generating set and of the goals.
    pub fn record_inputs(&mut self, generators: &[Poly], goals: &[Poly]) {
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
    pub fn record_basis(&mut self, basis: &[Poly]) {
        let basis = Shape::of(basis);
        self.basis_size = Some(basis.size);
        self.max_degree = Some(basis.max_degree);
        self.num_vars = Some(basis.num_vars);
    }

    /// Sets the final status, with the error that explains it.
    pub fn finish(&mut self, status: Status, error: Option<String>) {
        self.status = status;
        self.error = error;
    }

    /// Prints this as one JSON line, with peak memory so far.
    pub fn emit(&mut self) {
        println!("{}", self.json_line());
        let _ = std::io::stdout().flush();
    }

    /// This as one JSON line, with peak memory so far.
    pub fn into_line(mut self) -> String {
        self.json_line()
    }

    fn json_line(&mut self) -> String {
        self.peak_rss_mib = peak_rss_mib(false);
        self.singular_peak_rss_mib = peak_rss_mib(true);
        serde_json::to_string(self).unwrap()
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
