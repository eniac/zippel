//! Characterization tests for the redundant `infer` removals in `graph/src/lib.rs`.
//!
//! The `CExp::Pair` and `CExp::Bin` arms in `Dag::add_exp` historically called
//! `a.infer(...)?; b.infer(...)?;` on their children with the results discarded.
//! These calls are unreachable for error-propagation purposes:
//!
//! 1. `UDag::add_decl` runs `body.typecheck(...)?` (`graph/src/lib.rs:1133`) before
//!    invoking `add_exp`, so the entire body has already been type-inferred via the
//!    matching arms in `lang/src/typ/infer.rs` (e.g. the `CExp::Pair` arm at
//!    `:652-662` and the `CExp::Bin` arms at `:665+`, both of which recursively
//!    `infer` each child with `TypeError::next(TypeError::exp(parent), child_err)`
//!    provenance).
//! 2. The loop-top `exp.infer(...)?` at `add_exp` line `1329` re-validates each
//!    sub-expression on the way down, with the same parent-provenance wrapping.
//!
//! These tests pin the observable error behavior so the deletion of the discarded
//! calls cannot silently regress diagnostics: any ill-typed Pair/Bin must still
//! surface as a `GraphError::Type(_)` from `UDags::from_module`.

use crate::{GraphError, UDags};
use backend::ArkBls12_381;
use lang::ast::UModule;
use share::Ctx;

type B = ArkBls12_381;

fn try_parse_and_build(src: &str) -> Result<UDags<B>, GraphError> {
    let m = UModule::from_str(src)
        .unwrap()
        .concretize(&Ctx::new())
        .unwrap();
    UDags::<B>::from_module(m)
}

/// `pair(a, b)` where `a: F` (a field scalar) and `b: G2` (a group element) is a
/// type error: `lub_pair` requires both arguments to be elements of pairing-friendly
/// groups. After removing the discarded `a.infer()?; b.infer()?;` lines from the
/// `CExp::Pair` arm in `add_exp`, this must still surface as `GraphError::Type(_)`.
#[test]
fn pair_type_mismatch_propagates_as_type_error() {
    let src = r#"
        fn f<F: Field, G1: Group, G2: Group, GT: Pairing<G1, G2>>(public a: F, public b: G2) -> GT {
            pair(a, b)
        }
    "#;
    match try_parse_and_build(src) {
        Err(GraphError::Type(_)) => {}
        Err(e) => panic!("Expected GraphError::Type, got: {}", e),
        Ok(_) => panic!("Expected ill-typed pair(F, G2) to fail"),
    }
}

/// `a + b` where `a: F` and `b: G` cannot be unified by `lub_add`. After removing
/// the discarded `a.infer()?; b.infer()?;` lines from the `CExp::Bin` arm in
/// `add_exp`, this must still surface as `GraphError::Type(_)`.
#[test]
fn bin_type_mismatch_propagates_as_type_error() {
    let src = r#"
        fn f<F: Field, G: Group>(public a: F, public b: G) -> G {
            a + b
        }
    "#;
    match try_parse_and_build(src) {
        Err(GraphError::Type(_)) => {}
        Err(e) => panic!("Expected GraphError::Type, got: {}", e),
        Ok(_) => panic!("Expected ill-typed F + G to fail"),
    }
}
