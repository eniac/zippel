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
    pub hypercube_reduce_fused: u64,
    pub hypercube_reduce_cache_hits: u64,
    pub hypercube_reduce_cache_misses: u64,
    pub selected_eval_terms_materialized: u64,
    pub selected_eval_interpolation_fallback: u64,
    pub reduce_univariate_post_materialization: u64,
    pub canonical_sumcheck_rows_seen: u64,
    pub canonical_sumcheck_rows_fused: u64,
}

impl OptimizationStats {
    pub fn delta_since(self, before: OptimizationStats) -> OptimizationStats {
        OptimizationStats {
            hypercube_reduce_fused: self
                .hypercube_reduce_fused
                .saturating_sub(before.hypercube_reduce_fused),
            hypercube_reduce_cache_hits: self
                .hypercube_reduce_cache_hits
                .saturating_sub(before.hypercube_reduce_cache_hits),
            hypercube_reduce_cache_misses: self
                .hypercube_reduce_cache_misses
                .saturating_sub(before.hypercube_reduce_cache_misses),
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

static HYPERCUBE_REDUCE_FUSED: AtomicU64 = AtomicU64::new(0);
static HYPERCUBE_REDUCE_CACHE_HITS: AtomicU64 = AtomicU64::new(0);
static HYPERCUBE_REDUCE_CACHE_MISSES: AtomicU64 = AtomicU64::new(0);
static SELECTED_EVAL_TERMS_MATERIALIZED: AtomicU64 = AtomicU64::new(0);
static SELECTED_EVAL_INTERPOLATION_FALLBACK: AtomicU64 = AtomicU64::new(0);
static REDUCE_UNIVARIATE_POST_MATERIALIZATION: AtomicU64 = AtomicU64::new(0);
static CANONICAL_SUMCHECK_ROWS_SEEN: AtomicU64 = AtomicU64::new(0);
static CANONICAL_SUMCHECK_ROWS_FUSED: AtomicU64 = AtomicU64::new(0);

pub fn optimization_stats_snapshot() -> OptimizationStats {
    OptimizationStats {
        hypercube_reduce_fused: HYPERCUBE_REDUCE_FUSED.load(Ordering::Relaxed),
        hypercube_reduce_cache_hits: HYPERCUBE_REDUCE_CACHE_HITS.load(Ordering::Relaxed),
        hypercube_reduce_cache_misses: HYPERCUBE_REDUCE_CACHE_MISSES.load(Ordering::Relaxed),
        selected_eval_terms_materialized: SELECTED_EVAL_TERMS_MATERIALIZED.load(Ordering::Relaxed),
        selected_eval_interpolation_fallback: SELECTED_EVAL_INTERPOLATION_FALLBACK
            .load(Ordering::Relaxed),
        reduce_univariate_post_materialization: REDUCE_UNIVARIATE_POST_MATERIALIZATION
            .load(Ordering::Relaxed),
        canonical_sumcheck_rows_seen: CANONICAL_SUMCHECK_ROWS_SEEN.load(Ordering::Relaxed),
        canonical_sumcheck_rows_fused: CANONICAL_SUMCHECK_ROWS_FUSED.load(Ordering::Relaxed),
    }
}

pub fn reset_optimization_stats() {
    HYPERCUBE_REDUCE_FUSED.store(0, Ordering::Relaxed);
    HYPERCUBE_REDUCE_CACHE_HITS.store(0, Ordering::Relaxed);
    HYPERCUBE_REDUCE_CACHE_MISSES.store(0, Ordering::Relaxed);
    SELECTED_EVAL_TERMS_MATERIALIZED.store(0, Ordering::Relaxed);
    SELECTED_EVAL_INTERPOLATION_FALLBACK.store(0, Ordering::Relaxed);
    REDUCE_UNIVARIATE_POST_MATERIALIZATION.store(0, Ordering::Relaxed);
    CANONICAL_SUMCHECK_ROWS_SEEN.store(0, Ordering::Relaxed);
    CANONICAL_SUMCHECK_ROWS_FUSED.store(0, Ordering::Relaxed);
}

pub(crate) fn record_hypercube_reduce_fused() {
    HYPERCUBE_REDUCE_FUSED.fetch_add(1, Ordering::Relaxed);
    // There is no cache in the iteration-6 helper yet; record the execution as
    // a miss so artifacts distinguish real fused work from a zeroed counter set.
    HYPERCUBE_REDUCE_CACHE_MISSES.fetch_add(1, Ordering::Relaxed);
    CANONICAL_SUMCHECK_ROWS_SEEN.fetch_add(1, Ordering::Relaxed);
    CANONICAL_SUMCHECK_ROWS_FUSED.fetch_add(1, Ordering::Relaxed);
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
