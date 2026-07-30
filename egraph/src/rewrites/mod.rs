//! Rewrite module — programmatic rewrites for ZIR e-graphs.
//!
//! All rewrites are constructed via `Rewrite::new(name, lhs, rhs)` with
//! `Pattern` (no `rewrite!` macro — no `FromOp`). See
//! `docs/egraph-design-log.md` §4.2 for API notes.

pub mod const_prop;
pub mod licm;
pub mod map_fusion;
pub mod pairing;
pub mod record;
pub mod reduce_dot;
pub mod seq;
pub mod syntactic;

#[cfg(test)]
mod test_utils;

use crate::lang::ZIR;
use backend::ArkConfig;
use egg::{ENodeOrVar, Pattern, PatternAst, Var};

/// Helper: build a `PatternAst` from a vec of `ENodeOrVar` nodes.
pub fn pat_ast<C: ArkConfig>(nodes: Vec<ENodeOrVar<ZIR<C>>>) -> PatternAst<ZIR<C>> {
    PatternAst::from(nodes)
}

/// Helper: build a `Pattern` (implements both `Searcher` and `Applier`)
/// from a vec of `ENodeOrVar` nodes.
pub fn pat<C: ArkConfig + std::fmt::Debug>(nodes: Vec<ENodeOrVar<ZIR<C>>>) -> Pattern<ZIR<C>> {
    Pattern::new(pat_ast(nodes))
}

/// Helper: parse a `Var` from a string like `"?a"`.
pub fn v(s: &str) -> Var {
    s.parse().expect("valid var")
}

/// Collect all ZIR rewrites for Phases 2–3.
pub fn all_zir_rewrites<C: ArkConfig + std::fmt::Debug + Clone + 'static>()
-> Vec<egg::Rewrite<ZIR<C>, crate::lang::ZAnalysis<C>>> {
    let mut rules = vec![];
    rules.extend(syntactic::rewrites::<C>());
    rules.extend(seq::rewrites::<C>());
    rules.extend(record::rewrites::<C>());
    rules.extend(pairing::rewrites::<C>());
    rules.extend(reduce_dot::rewrites::<C>());
    rules.extend(licm::rewrites::<C>());
    rules.extend(map_fusion::rewrites::<C>());
    rules.extend(const_prop::rewrites::<C>());
    rules
}
