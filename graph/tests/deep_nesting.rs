//! Deeply nested expressions: every stage from parsing to projection must take stack bounded by
//! a small thread's and time linear in the nesting depth (issue #252).

use backend::ArkBls12_381;
use graph::UDags;
use lang::ast::UModule;
use share::Ctx;

/// Nesting depth of each expression.
const DEPTH: usize = 10_000;

/// A Schnorr-shaped proto whose blinding `s` is `exp`, an expression in `r`.
fn proto(exp: &str) -> String {
    format!(
        "proto p<G: Group, F: Scalar<G>>(witness x: F, instance g: G, instance h: G) \
         where h == g * x {{\n    let r = random<F>;\n    let s = {exp};\n    u <- g * s;\n    \
         c <- challenge<F>;\n    z <- s + x * c;\n    verify(g * z == u + h * c)\n}}\n"
    )
}

/// Parses, checks, lowers and projects `proto(exp)` on a 2 MiB thread.
fn compiles_on_small_stack(exp: String) {
    std::thread::Builder::new()
        .stack_size(2 << 20)
        .spawn(move || {
            let (module, diags) = UModule::parse(&proto(&exp));
            assert!(diags.is_empty(), "{diags:?}");
            let module = module
                .expect("parses")
                .concretize(&Ctx::new())
                .expect("concretizes");
            let diags = module.typecheck();
            assert!(diags.is_empty(), "{diags:?}");
            let dags = UDags::<ArkBls12_381>::from_module(module).expect("lowers");
            let dag = &dags.protocols()[0];
            dag.project_prover();
            dag.project_verifier().expect("projects");
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn left_nested_sum() {
    compiles_on_small_stack(vec!["r"; DEPTH].join(" + "));
}

#[test]
fn right_nested_sum() {
    compiles_on_small_stack(format!("{}r{}", "r + (".repeat(DEPTH), ")".repeat(DEPTH)));
}

#[test]
fn nested_parens() {
    compiles_on_small_stack(format!("{}r{}", "(".repeat(DEPTH), ")".repeat(DEPTH)));
}

#[test]
fn nested_negation() {
    compiles_on_small_stack(format!("{}r", "- ".repeat(DEPTH)));
}

#[test]
fn nested_blocks() {
    let open: String = (0..DEPTH).rev().map(|i| format!("(let b{i} = ")).collect();
    let close: String = (0..DEPTH).map(|i| format!("; b{i})")).collect();
    compiles_on_small_stack(format!("{open}r{close}"));
}
