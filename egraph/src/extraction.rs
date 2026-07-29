//! Extraction: EGraph → RecExpr.
//!
//! Uses tree-based `Extractor` (no native solver needed).
//! DAG-optimal `LpExtractor` will be available when the `lp` feature
//! and a native solver (cbc/highs) are configured.

use backend::ArkConfig;
use egg::{EGraph, Extractor, Id, RecExpr};

use crate::lang::{RAnalysis, RIR, RIRCost, ZAnalysis, ZIR, ZIRCost};

/// Extract the best RecExpr<ZIR> from the e-graph (tree-based).
pub fn extract_zir<C: ArkConfig + std::fmt::Debug>(
    egraph: &EGraph<ZIR<C>, ZAnalysis<C>>,
    root: Id,
) -> RecExpr<ZIR<C>> {
    let extractor = Extractor::new(egraph, ZIRCost);
    extractor.find_best(root).1
}

/// Extract the best RecExpr<RIR> from the e-graph (tree-based).
pub fn extract_rir<C: ArkConfig + std::fmt::Debug>(
    egraph: &EGraph<RIR<C>, RAnalysis<C>>,
    root: Id,
) -> RecExpr<RIR<C>> {
    let extractor = Extractor::new(egraph, RIRCost);
    extractor.find_best(root).1
}
