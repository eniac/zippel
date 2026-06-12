//! End-to-end completeness (Gröbner `CompletenessAnalysis`) checks for the
//! example protocols whose round-polynomial comprehensions lower to a generic
//! materialized `Op::ReduceMap` (sumcheck, mle_sumcheck) or whose `where`
//! clause folds loop-index exponents to constants (kzg).
//!
//! Each protocol is compiled and analyzed inside a large-stack worker thread:
//! `compile()` spawns its own bounded stack, but `analyze_completeness()` runs
//! the deep Gröbner recursion on the calling thread, which overflows the
//! default `cargo test` stack for these instances.

use backend::ArkBls12_381;
use lang::id::Tid;
use share::Ctx;
use std::path::PathBuf;
use zippel::{ZippelArgs, ZippelHandler};

const ANALYSIS_STACK_SIZE: usize = 256 * 1024 * 1024;

/// Compile `rel_path` (relative to the crate root) with the given concrete size
/// assignments and report whether `CompletenessAnalysis` succeeds. Runs on a
/// dedicated 256 MiB worker thread so the Gröbner recursion does not overflow.
fn analyze_complete(rel_path: &'static str, sizes: Vec<(&'static str, usize)>) -> bool {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(rel_path);
    std::thread::Builder::new()
        .name("zippel-completeness-test".to_string())
        .stack_size(ANALYSIS_STACK_SIZE)
        .spawn(move || {
            let mut handler: ZippelHandler<ArkBls12_381> =
                ZippelHandler::new(ZippelArgs::new(path));
            let mut ctx = Ctx::new();
            for &(name, value) in &sizes {
                ctx.insert(&Tid::new(name), &value);
            }
            handler.compile(&ctx);
            handler.analyze_completeness().is_ok()
        })
        .expect("failed to spawn completeness worker thread")
        .join()
        .expect("completeness worker thread panicked")
}

#[test]
#[ignore = "reduce-all completeness needs extractors for verifier-local ReduceMap/selected-eval intermediates; debugging separately with div_q"]
fn sumcheck_completeness() {
    // MAX_DEGREE_CONST = 1 keeps the completeness Gröbner basis tractable for
    // CI. The analysis now *models* the materialized hypercube reduce and
    // selected eval at any degree (no more `uncovered_op`), but a degree-2
    // multivariate basis with the recursive challenge products is
    // computationally heavy to fully reduce. Degree-2 hypercube *extraction*
    // is covered by the focused `canonical_hypercube_reduce_*` graph tests.
    assert!(analyze_complete(
        "examples/sumcheck/sumcheck.zippel",
        vec![("NUM_VARS_CONST", 3), ("MAX_DEGREE_CONST", 1)],
    ));
}

#[test]
#[ignore = "reduce-all completeness needs extractors for verifier-local ReduceMap/selected-eval intermediates; debugging separately with div_q"]
fn mle_sumcheck_completeness() {
    assert!(analyze_complete(
        "examples/mle_sumcheck/mle_sumcheck.zippel",
        vec![("NUM_VARS", 3), ("MAX_DEGREE_CONST", 1)],
    ));
}

#[test]
fn kzg_completeness() {
    assert!(analyze_complete("examples/kzg/kzg.zippel", vec![("N", 2)]));
}
