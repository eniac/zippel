use serde::{Deserialize, Serialize};
use std::sync::atomic::{AtomicU64, Ordering};

/// Process-global optimizer counters used by benchmark capture to prove which
/// private sumcheck optimization paths actually executed.
///
/// The counters are intentionally global atomics rather than thread-locals so
/// Rayon worker activity is included in before/after snapshots around a
/// protocol run. Callers should treat snapshots as monotonically increasing and
/// compute deltas with [`OptimizationStats::delta_since`].
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct OptimizationStats {
    /// Number of `Value::value_eval_selected` calls, i.e. selected-eval terms
    /// that were actually materialized into a restricted polynomial.
    pub selected_eval_terms_materialized: u64,
    /// Number of selected-eval restrictions that had to go through the generic
    /// Lagrange-interpolation path instead of a specialized variable fixing.
    pub selected_eval_interpolation_fallback: u64,
    /// Number of `Value::value_reduce(BinOp::Add)` calls whose operands were
    /// all univariate polynomials and were summed coefficient-wise rather than
    /// through the generic parallel `Value` fold.
    pub reduce_univariate_post_materialization: u64,
    /// Number of `Value::value_hypercube_reduce_selected` calls, i.e. sumcheck
    /// rounds that reached the fused selected-eval + hypercube-sum entry point.
    pub canonical_sumcheck_rows_seen: u64,
    /// Number of those rounds that produced a round polynomial through the
    /// fused path, whether by the MLE-product fast path or the shared
    /// evaluate-and-sum fallback.
    pub canonical_sumcheck_rows_fused: u64,
}

impl OptimizationStats {
    /// Field-wise difference between this snapshot and an earlier one.
    ///
    /// Saturating subtraction, so an out-of-order pair of snapshots yields
    /// zeros rather than wrapping. Counters are only ever incremented or reset
    /// wholesale, so a non-zero delta means those code paths ran between the
    /// two snapshots.
    pub fn delta_since(self, before: OptimizationStats) -> OptimizationStats {
        OptimizationStats {
            selected_eval_terms_materialized: self
                .selected_eval_terms_materialized
                .saturating_sub(before.selected_eval_terms_materialized),
            selected_eval_interpolation_fallback: self
                .selected_eval_interpolation_fallback
                .saturating_sub(before.selected_eval_interpolation_fallback),
            reduce_univariate_post_materialization: self
                .reduce_univariate_post_materialization
                .saturating_sub(before.reduce_univariate_post_materialization),
            canonical_sumcheck_rows_seen: self
                .canonical_sumcheck_rows_seen
                .saturating_sub(before.canonical_sumcheck_rows_seen),
            canonical_sumcheck_rows_fused: self
                .canonical_sumcheck_rows_fused
                .saturating_sub(before.canonical_sumcheck_rows_fused),
        }
    }
}

static SELECTED_EVAL_TERMS_MATERIALIZED: AtomicU64 = AtomicU64::new(0);
static SELECTED_EVAL_INTERPOLATION_FALLBACK: AtomicU64 = AtomicU64::new(0);
static REDUCE_UNIVARIATE_POST_MATERIALIZATION: AtomicU64 = AtomicU64::new(0);
static CANONICAL_SUMCHECK_ROWS_SEEN: AtomicU64 = AtomicU64::new(0);
static CANONICAL_SUMCHECK_ROWS_FUSED: AtomicU64 = AtomicU64::new(0);

/// Reads all optimizer counters into a single [`OptimizationStats`].
///
/// The five loads are independent relaxed atomic reads, so a snapshot taken
/// while worker threads are running is not a consistent cut. Take snapshots
/// around a quiesced protocol run to get meaningful deltas.
pub fn optimization_stats_snapshot() -> OptimizationStats {
    OptimizationStats {
        selected_eval_terms_materialized: SELECTED_EVAL_TERMS_MATERIALIZED.load(Ordering::Relaxed),
        selected_eval_interpolation_fallback: SELECTED_EVAL_INTERPOLATION_FALLBACK
            .load(Ordering::Relaxed),
        reduce_univariate_post_materialization: REDUCE_UNIVARIATE_POST_MATERIALIZATION
            .load(Ordering::Relaxed),
        canonical_sumcheck_rows_seen: CANONICAL_SUMCHECK_ROWS_SEEN.load(Ordering::Relaxed),
        canonical_sumcheck_rows_fused: CANONICAL_SUMCHECK_ROWS_FUSED.load(Ordering::Relaxed),
    }
}

/// Zeroes every optimizer counter.
///
/// Intended to be called once before a measured run; it affects the whole
/// process, so concurrent measurements interfere with each other.
pub fn reset_optimization_stats() {
    SELECTED_EVAL_TERMS_MATERIALIZED.store(0, Ordering::Relaxed);
    SELECTED_EVAL_INTERPOLATION_FALLBACK.store(0, Ordering::Relaxed);
    REDUCE_UNIVARIATE_POST_MATERIALIZATION.store(0, Ordering::Relaxed);
    CANONICAL_SUMCHECK_ROWS_SEEN.store(0, Ordering::Relaxed);
    CANONICAL_SUMCHECK_ROWS_FUSED.store(0, Ordering::Relaxed);
}

pub(crate) fn record_selected_eval_term_materialized() {
    SELECTED_EVAL_TERMS_MATERIALIZED.fetch_add(1, Ordering::Relaxed);
}

pub(crate) fn record_selected_eval_interpolation_fallback() {
    SELECTED_EVAL_INTERPOLATION_FALLBACK.fetch_add(1, Ordering::Relaxed);
}

pub(crate) fn record_reduce_univariate_post_materialization() {
    REDUCE_UNIVARIATE_POST_MATERIALIZATION.fetch_add(1, Ordering::Relaxed);
}

pub(crate) fn record_canonical_sumcheck_rows_fused() {
    CANONICAL_SUMCHECK_ROWS_FUSED.fetch_add(1, Ordering::Relaxed);
}

pub(crate) fn record_canonical_sumcheck_rows_seen() {
    CANONICAL_SUMCHECK_ROWS_SEEN.fetch_add(1, Ordering::Relaxed);
}
