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
fn sumcheck_completeness() {
    // Recursive sumcheck: the verifier recomputes round polynomials via
    // materialized hypercube reduce-maps and selected evaluations. These
    // verifier-local intermediates reduce once the same DAG node-slot maps to a
    // single Gröbner variable across the prover/relation/verifier
    // sub-projections (see `canonicalize_node_slot_vars`). MAX_DEGREE_CONST=1.
    assert!(analyze_complete(
        "examples/sumcheck/sumcheck.zippel",
        vec![("NUM_VARS_CONST", 3), ("MAX_DEGREE_CONST", 1)],
    ));
}

#[test]
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

#[test]
fn membership_completeness() {
    // div_r incompleteness resolved: the membership statement `f(0) in S`, i.e.
    // `reduce(*, [f_coeffs[0] - r for r in s]) == 0` (= g(0)==0), is now part of
    // the `where` relation, so the verifier's `prod_eval == h_eval*alpha` check
    // reduces against it instead of leaving the `g_poly / poly_x` remainder
    // free. Also exercises the `Op::ReduceMap` Mul degree-widening fix: N=2,
    // M=2 fold Uni(1)*Uni(1) -> Uni(2) (L=2, S=2).
    assert!(analyze_complete(
        "examples/membership/membership.zippel",
        vec![("N", 2), ("M", 2), ("S", 2)],
    ));
}
