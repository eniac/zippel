//! Shared test utilities for rewrite tests.

use backend::ArkBls12_381;
use egg::{EGraph, Runner};

use crate::lang::{ZAnalysis, ZIR};
use crate::rewrites::all_zir_rewrites;

pub type ZEgraph = EGraph<ZIR<ArkBls12_381>, ZAnalysis<ArkBls12_381>>;

/// Helper: run all rewrites to saturation on an e-graph.
pub fn saturate(egraph: &mut ZEgraph) {
    let rules = all_zir_rewrites::<ArkBls12_381>();
    let runner = Runner::default()
        .with_egraph(std::mem::take(egraph))
        .run(&rules);
    *egraph = runner.egraph;
}
