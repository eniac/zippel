//! Pinning tests for the `from_module` transformation.
//!
//! Each test parses a `.zippel` source string, builds a graph via `from_module`,
//! then builds an expected graph manually and asserts structural equality
//! via the `PartialEq` (graph isomorphism) implementation.

use super::test_helpers::parse_and_concretize;
use crate::node::ArgKind;
use crate::{Dep, DepType, GOp, GraphError, HOp, Node, Nothing, Ref, UDag, UDags, mk};
use backend::{ATyp, ArkBls12_381};
use lang::ast::BinOp;
use lang::id::Vid;
use lang::typ::{Distribution, Qualifier};
use petgraph::Direction;
use petgraph::graph::NodeIndex;
use petgraph::visit::EdgeRef;
use share::Ctx;

type B = ArkBls12_381;

/// Parse a `.zippel` source string and build graphs via from_module.
fn parse_and_build(src: &str) -> UDags<B> {
    let m = parse_and_concretize(src, &Ctx::new());
    UDags::<B>::from_module(m).unwrap()
}

/// Parse and build, returning Result to allow testing error paths.
fn try_parse_and_build(src: &str) -> Result<UDags<B>, GraphError> {
    let m = parse_and_concretize(src, &Ctx::new());
    UDags::<B>::from_module(m)
}

/// Phase B: an `Inp`/`Rel` marker is followed by one `Node::Arg` per source
/// argument, connected via a `Dep::data()` edge from marker to arg.
/// `expected_inp` mirrors what `add_decl` produces for the protocol/function
/// implementation (so `ArgKind::Input`); `expected_rel` mirrors the relation
/// half of a `proto` (so `ArgKind::Relation`).
type ArgSpec = (Vid, ATyp, Qualifier, Distribution);

fn expected_inp(g: &mut UDag<B>, name: &str, args: &[ArgSpec]) -> (NodeIndex, Vec<NodeIndex>) {
    let inp = g.add_node(Node::inp(Vid::new(name)));
    let mut idxs = Vec::with_capacity(args.len());
    for (n, t, q, d) in args {
        let a = g.add_node(Node::arg(n.clone(), t.clone(), *q, *d, ArgKind::Input));
        g.add_edge(inp, a, Dep::data());
        idxs.push(a);
    }
    (inp, idxs)
}

fn expected_rel(g: &mut UDag<B>, name: &str, args: &[ArgSpec]) -> (NodeIndex, Vec<NodeIndex>) {
    let rel = g.add_node(Node::rel(Vid::new(name)));
    let mut idxs = Vec::with_capacity(args.len());
    for (n, t, q, d) in args {
        let a = g.add_node(Node::arg(n.clone(), t.clone(), *q, *d, ArgKind::Relation));
        g.add_edge(rel, a, Dep::data());
        idxs.push(a);
    }
    (rel, idxs)
}

/// Per-test arg-spec helpers used by the transformed test bodies.
fn instance_s(name: &str) -> ArgSpec {
    (
        Vid::new(name),
        ATyp::scalar(),
        Qualifier::Instance,
        Distribution::Nonuniform,
    )
}
fn witness_s(name: &str) -> ArgSpec {
    (
        Vid::new(name),
        ATyp::scalar(),
        Qualifier::Witness,
        Distribution::Nonuniform,
    )
}
fn instance_t(name: &str, typ: ATyp) -> ArgSpec {
    (
        Vid::new(name),
        typ,
        Qualifier::Instance,
        Distribution::Nonuniform,
    )
}

// ============================================================================
// Group 1: Declaration Types
// ============================================================================

/// Func declaration returning a bare literal — `1` infers to `Fin<1>` but
/// the function-body return check now goes through `CTyp::lub_equ`
/// (`lang/src/ast/decl.rs:292`), so the scalar-fallback arm in `lub_equ`
/// (`lang/src/typ/lub.rs:510-517`) lifts `Fin<1>` to `Base(F)` to match
/// the declared return type. Regression test for the strict-`==` →
/// `lub_equ` switch.
#[test]
fn pin_func_lit_return() {
    let gs = parse_and_build("fn f<F: Field>() -> F { 1 }");

    let mut expected = UDag::<B>::new();
    let _ = expected_inp(&mut expected, "f", &[]);
    let lit_1 = GOp::<B>::Value(backend::Value::Index(1));
    let _ret = expected.add_node(Node::Op(crate::mk::<B>(lit_1), lang::typ::Nothing));

    assert!(gs[0] == expected);
}

/// Func declaration returning sum with a literal — exercises Lit coercion.
/// Tests: CBody::Func, CExp::Bin with literal operand.
#[test]
fn pin_func_lit_in_binop() {
    // `a + 1` exercises CExp::Lit(1) as an operand in a Bin expression.
    // `1` alone can also be returned from `-> F` now that the body return
    // check uses `lub_equ` instead of strict `==`; see `pin_func_lit_return`.
    let gs = parse_and_build("fn f<F: Field>(instance a: F) -> F { a + 1 }");

    let mut expected = UDag::<B>::new();
    let a = Vid::new("a");
    let s = ATyp::scalar();
    let (_inp, _inp_args) = expected_inp(&mut expected, "f", &[instance_s("a")]);
    let arg_a = _inp_args[0];
    let var_a = GOp::<B>::var(&a, arg_a, s.clone());
    let lit_1 = GOp::<B>::Value(backend::Value::Index(1));
    let bin = expected.add_node(Node::bin(BinOp::Add, &var_a, &lit_1, &s));
    expected.add_edges(DepType::Data, bin, var_a);

    assert!(gs[0] == expected);
}

/// Func declaration returning its argument.
/// Tests: CExp::Var resolves to a `Ref(arg)` op; since `Op::is_ref()` holds,
/// `add_top_exp` short-circuits and emits no `Ret` node.
#[test]
fn pin_func_var() {
    let gs = parse_and_build("fn f<F: Field>(instance a: F) -> F { a }");

    let mut expected = UDag::<B>::new();
    let a = Vid::new("a");
    let (_inp, _inp_args) = expected_inp(&mut expected, "f", &[instance_s("a")]);
    let _arg_a = _inp_args[0];
    // Body `a` resolves to a Ref → add_top_exp does not add a Ret
    // (`if !op.is_ref() { add Ret }` short-circuits).
    let _ = a;

    assert!(gs[0] == expected);
}

/// Proto declaration with body and relation.
/// Tests: CBody::Proto, Inp node, Rel node, Assert in relation, verify in body.
#[test]
fn pin_proto_simple() {
    let src = r#"
        proto foo<F: Field>(witness s: F) where s == s {
            verify(s == s)
        }
    "#;
    let gs = parse_and_build(src);

    let mut expected = UDag::<B>::new();
    let s = Vid::new("s");

    // Body: Inp + Verify(var_s, var_s) + Ret(Lit(0))
    let (_inp, _inp_args) = expected_inp(&mut expected, "foo", &[witness_s("s")]);
    let arg_s = _inp_args[0];
    let var_s_body = GOp::<B>::var(&s, arg_s, ATyp::scalar());

    let equ = expected.add_node(Node::bin(
        BinOp::Equ,
        &var_s_body,
        &var_s_body,
        &ATyp::bool(),
    ));
    expected.add_edges(DepType::Data, equ, var_s_body.clone());
    expected.add_edges(DepType::Data, equ, var_s_body);
    let equ_ref = GOp::<B>::underscore(equ, ATyp::bool());
    let check = expected.add_node(Node::verify(&equ_ref));
    expected.add_edges(DepType::Data, check, equ_ref);

    // Continuation Lit(0) → Ret(Value::Unit)
    let unit = GOp::<B>::Value(backend::Value::Unit);
    let ret = expected.add_node(Node::ret(&unit));
    expected.add_edges(DepType::Data, ret, unit);

    // Relation: Rel + Equ(var_s_rel, var_s_rel) + Assert(equ_rel_ref)
    let (_rel, _rel_args) = expected_rel(&mut expected, "foo", &[witness_s("s")]);
    let rel_arg_s = _rel_args[0];
    let var_s_rel = GOp::<B>::var(&s, rel_arg_s, ATyp::scalar());
    let equ_rel = expected.add_node(Node::bin(BinOp::Equ, &var_s_rel, &var_s_rel, &ATyp::bool()));
    expected.add_edges(DepType::Data, equ_rel, var_s_rel.clone());
    expected.add_edges(DepType::Data, equ_rel, var_s_rel);
    let equ_rel_ref = GOp::<B>::underscore(equ_rel, ATyp::bool());
    let assert_rel = expected.add_node(Node::assert(&equ_rel_ref));
    expected.add_edges(DepType::Data, assert_rel, equ_rel_ref);

    assert!(gs[0] == expected);
}

// ============================================================================
// Group 2: Basic Values
// ============================================================================

/// CExp::Range produces a GOp::Range value, wrapped in ret by add_top_exp.
#[test]
fn pin_range() {
    let src = r#"
        fn f<F: Field>(instance a: [F; 10]) -> [F; 5] {
            a[0..5]
        }
    "#;
    let gs = parse_and_build(src);

    // a[0..5] is Ram(Var(a), Range(0..5))
    let mut expected = UDag::<B>::new();
    let a = Vid::new("a");
    let vs10 = ATyp::vec_scalar(10);
    let (_inp, _inp_args) = expected_inp(&mut expected, "f", &[instance_t("a", vs10.clone())]);
    let arg_a = _inp_args[0];
    let var_a = GOp::<B>::var(&a, arg_a, vs10);
    let ram_op = GOp::<B>::ram(var_a, GOp::<B>::range(lang::ast::CRange::from_raw(0, 1, 5)));

    // add_exp returned a non-Ref op → add_top_exp adds a Ret node.
    let ret = expected.add_node(Node::ret(&ram_op));
    expected.add_edges(DepType::Data, ret, ram_op);

    assert!(gs[0] == expected);
}

// ============================================================================
// Group 3: Binary Operations
// ============================================================================

/// Helper to test a binary operation between two scalar arguments.
fn assert_binop(op_str: &str, binop: BinOp, result_typ: ATyp) {
    let src = format!(
        "fn f<F: Field>(instance a: F, instance b: F) -> F {{ a {} b }}",
        op_str
    );
    let gs = parse_and_build(&src);

    let mut expected = UDag::<B>::new();
    let a = Vid::new("a");
    let b = Vid::new("b");
    let (_inp, _inp_args) = expected_inp(&mut expected, "f", &[instance_s("a"), instance_s("b")]);
    let arg_a = _inp_args[0];
    let arg_b = _inp_args[1];
    let var_a = GOp::<B>::var(&a, arg_a, ATyp::scalar());
    let var_b = GOp::<B>::var(&b, arg_b, ATyp::scalar());
    let bin = expected.add_node(Node::bin(binop, &var_a, &var_b, &result_typ));
    expected.add_edges(DepType::Data, bin, var_a);
    expected.add_edges(DepType::Data, bin, var_b);

    assert!(gs[0] == expected);
}

#[test]
fn pin_bin_add() {
    assert_binop("+", BinOp::Add, ATyp::scalar());
}

#[test]
fn pin_bin_sub() {
    assert_binop("-", BinOp::Sub, ATyp::scalar());
}

#[test]
fn pin_bin_mul() {
    assert_binop("*", BinOp::Mul, ATyp::scalar());
}

#[test]
fn pin_bin_div() {
    assert_binop("/", BinOp::Div, ATyp::scalar());
}

// ============================================================================
// Group 4: Crypto Operations
// ============================================================================

/// Random scalar, no transcript edge.
/// Tests: CExp::Random, Node::random.
#[test]
fn pin_random() {
    let src = "fn f<F: Field>(instance a: F) -> F { random<F> }";
    let gs = parse_and_build(src);

    let mut expected = UDag::<B>::new();
    let (_inp, __inp_args) = expected_inp(&mut expected, "f", &[instance_s("a")]);
    let _arg_a = __inp_args[0];
    let _rand = expected.add_node(Node::random(&ATyp::scalar(), false));

    assert!(gs[0] == expected);
}

/// Random non-zero scalar.
#[test]
fn pin_random_nz() {
    let src = "fn f<F: Field>(instance a: F) -> F { random<F*> }";
    let gs = parse_and_build(src);

    let mut expected = UDag::<B>::new();
    let (_inp, __inp_args) = expected_inp(&mut expected, "f", &[instance_s("a")]);
    let _arg_a = __inp_args[0];
    let _rand = expected.add_node(Node::random(&ATyp::scalar(), true));

    assert!(gs[0] == expected);
}

/// Challenge creates a transcript edge from the start node.
/// Tests: CExp::Challenge, Node::challenge, transcript edge.
#[test]
fn pin_challenge() {
    let src = "fn f<F: Field>(instance a: F) -> F { challenge<F> }";
    let gs = parse_and_build(src);

    let mut expected = UDag::<B>::new();
    let (inp, _inp_args) = expected_inp(&mut expected, "f", &[instance_s("a")]);
    let _arg_a = _inp_args[0];
    let ch = expected.add_node(Node::challenge(&ATyp::scalar(), false));
    expected.add_edge(inp, ch, Dep::transcript());

    assert!(gs[0] == expected);
}

/// Challenge non-zero.
#[test]
fn pin_challenge_nz() {
    let src = "fn f<F: Field>(instance a: F) -> F { challenge<F*> }";
    let gs = parse_and_build(src);

    let mut expected = UDag::<B>::new();
    let (inp, _inp_args) = expected_inp(&mut expected, "f", &[instance_s("a")]);
    let _arg_a = _inp_args[0];
    let ch = expected.add_node(Node::challenge(&ATyp::scalar(), true));
    expected.add_edge(inp, ch, Dep::transcript());

    assert!(gs[0] == expected);
}

// ============================================================================
// Group 5: Control Flow
// ============================================================================

/// Let binding: `let c = a + b; c`.
/// Tests: CExp::Let(Some), variable context update, op_from_var maps Vid → Ref(arg_or_node).
#[test]
fn pin_let_named() {
    let src = r#"
        fn f<F: Field>(instance a: F, instance b: F) -> F {
            let c = a + b;
            c
        }
    "#;
    let gs = parse_and_build(src);

    let mut expected = UDag::<B>::new();
    let a = Vid::new("a");
    let b = Vid::new("b");
    let c = Vid::new("c");
    let s = ATyp::scalar();
    let (_inp, _inp_args) = expected_inp(&mut expected, "f", &[instance_s("a"), instance_s("b")]);
    let arg_a = _inp_args[0];
    let arg_b = _inp_args[1];
    let var_a = GOp::<B>::var(&a, arg_a, s.clone());
    let var_b = GOp::<B>::var(&b, arg_b, s.clone());

    // a + b creates a bin node
    let bin = expected.add_node(Node::bin(BinOp::Add, &var_a, &var_b, &s));
    expected.add_edges(DepType::Data, bin, var_a);
    expected.add_edges(DepType::Data, bin, var_b);

    // `c` resolves to Ref(bin); since the body is a Ref, add_top_exp does
    // not add a Ret node.
    // let-binding registers the name in vctx and marks it as non-transcript.
    expected.vctx.insert(&bin, &c);
    expected.transcript_vars.insert(&bin, &false);

    assert!(gs[0] == expected);
}

/// Anonymous let: `let _ = a + b; a * b`.
/// Tests: CExp::Let(None), both sides evaluated, second is the result.
#[test]
fn pin_let_anon() {
    let src = r#"
        fn f<F: Field>(instance a: F, instance b: F) -> F {
            let _ = a + b;
            a * b
        }
    "#;
    let gs = parse_and_build(src);

    let mut expected = UDag::<B>::new();
    let a = Vid::new("a");
    let b = Vid::new("b");
    let s = ATyp::scalar();
    let (_inp, _inp_args) = expected_inp(&mut expected, "f", &[instance_s("a"), instance_s("b")]);
    let arg_a = _inp_args[0];
    let arg_b = _inp_args[1];
    let var_a = GOp::<B>::var(&a, arg_a, s.clone());
    let var_b = GOp::<B>::var(&b, arg_b, s.clone());

    // let _ = a + b → Bin(Add) node (result discarded)
    let add = expected.add_node(Node::bin(BinOp::Add, &var_a, &var_b, &s));
    expected.add_edges(DepType::Data, add, var_a.clone());
    expected.add_edges(DepType::Data, add, var_b.clone());
    // let-binding registers the name in vctx and marks it as non-transcript.
    expected.vctx.insert(&add, &Vid::new("_"));
    expected.transcript_vars.insert(&add, &false);

    // a * b → Bin(Mul) node (this is the return value; add_exp returns Ref(mul) so add_top_exp skips Ret)
    let mul = expected.add_node(Node::bin(BinOp::Mul, &var_a, &var_b, &s));
    expected.add_edges(DepType::Data, mul, var_a);
    expected.add_edges(DepType::Data, mul, var_b);

    assert!(gs[0] == expected);
}

/// Assert expression.
#[test]
fn pin_assert() {
    let src = r#"
        fn f<F: Field>(instance a: F, instance b: F) -> Unit {
            assert(a == b)
        }
    "#;
    let gs = parse_and_build(src);

    let mut expected = UDag::<B>::new();
    let a = Vid::new("a");
    let b = Vid::new("b");
    let (_inp, _inp_args) = expected_inp(&mut expected, "f", &[instance_s("a"), instance_s("b")]);
    let arg_a = _inp_args[0];
    let arg_b = _inp_args[1];
    let var_a = GOp::<B>::var(&a, arg_a, ATyp::scalar());
    let var_b = GOp::<B>::var(&b, arg_b, ATyp::scalar());

    // assert(a == b) → Equ(var_a, var_b) node, then Assert(equ_ref) node
    // Assert is prover-side — no transcript edge.
    let equ = expected.add_node(Node::bin(BinOp::Equ, &var_a, &var_b, &ATyp::bool()));
    expected.add_edges(DepType::Data, equ, var_a);
    expected.add_edges(DepType::Data, equ, var_b);
    let equ_ref = GOp::<B>::underscore(equ, ATyp::bool());
    let check = expected.add_node(Node::assert(&equ_ref));
    expected.add_edges(DepType::Data, check, equ_ref);

    // Continuation Lit(0) → Ret(Value::Unit)
    let unit = GOp::<B>::Value(backend::Value::Unit);
    let ret = expected.add_node(Node::ret(&unit));
    expected.add_edges(DepType::Data, ret, unit);

    assert!(gs[0] == expected);
}

/// Verify expression (same structure as assert).
/// Tests: CExp::Verify, Node::verify.
#[test]
fn pin_verify() {
    let src = r#"
        fn f<F: Field>(instance a: F, instance b: F) -> Unit {
            verify(a == b)
        }
    "#;
    let gs = parse_and_build(src);

    let mut expected = UDag::<B>::new();
    let a = Vid::new("a");
    let b = Vid::new("b");
    let (_inp, _inp_args) = expected_inp(&mut expected, "f", &[instance_s("a"), instance_s("b")]);
    let arg_a = _inp_args[0];
    let arg_b = _inp_args[1];
    let var_a = GOp::<B>::var(&a, arg_a, ATyp::scalar());
    let var_b = GOp::<B>::var(&b, arg_b, ATyp::scalar());

    let equ = expected.add_node(Node::bin(BinOp::Equ, &var_a, &var_b, &ATyp::bool()));
    expected.add_edges(DepType::Data, equ, var_a);
    expected.add_edges(DepType::Data, equ, var_b);
    let equ_ref = GOp::<B>::underscore(equ, ATyp::bool());
    let check = expected.add_node(Node::verify(&equ_ref));
    expected.add_edges(DepType::Data, check, equ_ref);

    // Continuation Lit(0) → Ret(Value::Unit)
    let unit = GOp::<B>::Value(backend::Value::Unit);
    let ret = expected.add_node(Node::ret(&unit));
    expected.add_edges(DepType::Data, ret, unit);

    assert!(gs[0] == expected);
}

// ============================================================================
// Group 6: Log (Transcript Interaction)
// ============================================================================

/// Log with existing node reference: `a <- s + s; verify(a == s)`.
/// Tests: CExp::Log (first branch), set_transcript, Node::Transcr.
#[test]
fn pin_log_node_ref() {
    let src = r#"
        proto foo<F: Field>(witness s: F) where s == s {
            a <- s + s;
            verify(a == s)
        }
    "#;
    let gs = parse_and_build(src);

    let mut expected = UDag::<B>::new();
    let s_vid = Vid::new("s");
    let a_vid = Vid::new("a");

    // Body
    let (inp, _inp_args) = expected_inp(&mut expected, "foo", &[witness_s("s")]);
    let arg_s = _inp_args[0];
    let var_s = GOp::<B>::var(&s_vid, arg_s, ATyp::scalar());

    // s + s → Bin(Add) node, then set_transcript converts it to Transcr
    let bin_add = expected.add_node(Node::bin(BinOp::Add, &var_s, &var_s, &ATyp::scalar()));
    expected.add_edges(DepType::Data, bin_add, var_s.clone());
    expected.add_edges(DepType::Data, bin_add, var_s.clone());

    let bin_add_ref = GOp::<B>::underscore(bin_add, ATyp::scalar());
    let transcr_op = GOp::<B>::Ref(Ref(bin_add), ATyp::scalar());
    let transcr = expected.add_node(Node::transcr(&transcr_op));
    expected.add_edges(DepType::Data, transcr, bin_add_ref.clone());
    expected.add_edge(inp, transcr, Dep::transcript());
    expected.vctx.insert(&transcr, &a_vid);
    expected.transcript_vars.insert(&transcr, &true);
    // a == s → Equ(var_a, var_s) node, then Verify(equ_ref) node
    let var_a = GOp::<B>::var(&a_vid, transcr, ATyp::scalar());
    let equ = expected.add_node(Node::bin(BinOp::Equ, &var_a, &var_s, &ATyp::bool()));
    expected.add_edges(DepType::Data, equ, var_a);
    expected.add_edges(DepType::Data, equ, var_s);
    let equ_ref = GOp::<B>::underscore(equ, ATyp::bool());
    let check = expected.add_node(Node::verify(&equ_ref));
    expected.add_edges(DepType::Data, check, equ_ref);

    // Continuation Lit(0) → Ret(Value::Unit)
    let unit = GOp::<B>::Value(backend::Value::Unit);
    let ret = expected.add_node(Node::ret(&unit));
    expected.add_edges(DepType::Data, ret, unit);

    // Relation: Rel + Equ(var_s_rel, var_s_rel) + Assert(equ_rel_ref)
    let (_rel, _rel_args) = expected_rel(&mut expected, "foo", &[witness_s("s")]);
    let rel_arg_s = _rel_args[0];
    let var_s_rel = GOp::<B>::var(&s_vid, rel_arg_s, ATyp::scalar());
    let equ_rel = expected.add_node(Node::bin(BinOp::Equ, &var_s_rel, &var_s_rel, &ATyp::bool()));
    expected.add_edges(DepType::Data, equ_rel, var_s_rel.clone());
    expected.add_edges(DepType::Data, equ_rel, var_s_rel);
    let equ_rel_ref = GOp::<B>::underscore(equ_rel, ATyp::bool());
    let assert_rel = expected.add_node(Node::assert(&equ_rel_ref));
    expected.add_edges(DepType::Data, assert_rel, equ_rel_ref);

    assert!(gs[0] == expected);
}

/// Log with non-node value: `a <- 1; verify(s == s)`.
/// Tests: CExp::Log (second branch), new Transcr node creation.
#[test]
fn pin_log_new_transcr() {
    let src = r#"
        proto foo<F: Field>(witness s: F) where s == s {
            a <- 1;
            verify(s == s)
        }
    "#;
    let gs = parse_and_build(src);

    let mut expected = UDag::<B>::new();
    let s_vid = Vid::new("s");
    let a_vid = Vid::new("a");

    // Body
    let (inp, _inp_args) = expected_inp(&mut expected, "foo", &[witness_s("s")]);
    let arg_s = _inp_args[0];

    // `1` is Value(Index(1)), not a Ref → second branch of Log: creates new Transcr node
    let lit_op = GOp::<B>::Value(backend::Value::Index(1));
    let transcr = expected.add_node(Node::transcr(&lit_op));
    expected[transcr].set_transcript();
    // transcript edge from inp to transcr
    expected.add_edge(inp, transcr, Dep::transcript());
    expected.vctx.insert(&transcr, &a_vid);
    expected.transcript_vars.insert(&transcr, &true);
    let var_s = GOp::<B>::var(&s_vid, arg_s, ATyp::scalar());
    let equ = expected.add_node(Node::bin(BinOp::Equ, &var_s, &var_s, &ATyp::bool()));
    expected.add_edges(DepType::Data, equ, var_s.clone());
    expected.add_edges(DepType::Data, equ, var_s);
    let equ_ref = GOp::<B>::underscore(equ, ATyp::bool());
    let check = expected.add_node(Node::verify(&equ_ref));
    expected.add_edges(DepType::Data, check, equ_ref);

    // Continuation Lit(0) → Ret(Value::Unit)
    let unit = GOp::<B>::Value(backend::Value::Unit);
    let ret = expected.add_node(Node::ret(&unit));
    expected.add_edges(DepType::Data, ret, unit);

    // Relation: Rel + Equ(var_s_rel, var_s_rel) + Assert(equ_rel_ref)
    let (_rel, _rel_args) = expected_rel(&mut expected, "foo", &[witness_s("s")]);
    let rel_arg_s = _rel_args[0];
    let var_s_rel = GOp::<B>::var(&s_vid, rel_arg_s, ATyp::scalar());
    let equ_rel = expected.add_node(Node::bin(BinOp::Equ, &var_s_rel, &var_s_rel, &ATyp::bool()));
    expected.add_edges(DepType::Data, equ_rel, var_s_rel.clone());
    expected.add_edges(DepType::Data, equ_rel, var_s_rel);
    let equ_rel_ref = GOp::<B>::underscore(equ_rel, ATyp::bool());
    let assert_rel = expected.add_node(Node::assert(&equ_rel_ref));
    expected.add_edges(DepType::Data, assert_rel, equ_rel_ref);

    assert!(gs[0] == expected);
}

// ============================================================================
// Group 7: Polynomial & MLE Operations
// ============================================================================

/// Poly operation on a vector argument.
/// Tests: CExp::Poly, Node::poly.
#[test]
fn pin_poly() {
    let src = r#"
        fn f<F: Field>(instance a: [F; 4]) -> Uni<F, 3> {
            poly(a)
        }
    "#;
    let gs = parse_and_build(src);

    let mut expected = UDag::<B>::new();
    let a = Vid::new("a");
    let vec_typ = ATyp::vec_scalar(4);
    let (_inp, _inp_args) = expected_inp(&mut expected, "f", &[instance_t("a", vec_typ.clone())]);
    let arg_a = _inp_args[0];
    let var_a = GOp::<B>::var(&a, arg_a, vec_typ);

    let poly = expected.add_node(Node::poly(&var_a));
    expected.add_edges(DepType::Data, poly, var_a);

    assert!(gs[0] == expected);
}

/// Coef operation on a polynomial argument.
/// Tests: CExp::Coef, Node::coef.
#[test]
fn pin_coef() {
    let src = r#"
        fn f<F: Field>(instance a: Uni<F, 4>) -> [F; 5] {
            coef(a)
        }
    "#;
    let gs = parse_and_build(src);

    let mut expected = UDag::<B>::new();
    let a = Vid::new("a");
    let poly_typ = ATyp::Uni(4);
    let (_inp, _inp_args) = expected_inp(&mut expected, "f", &[instance_t("a", poly_typ.clone())]);
    let arg_a = _inp_args[0];
    let var_a = GOp::<B>::var(&a, arg_a, poly_typ);

    let coef_node = expected.add_node(Node::coef(&var_a));
    expected.add_edges(DepType::Data, coef_node, var_a);

    assert!(gs[0] == expected);
}

/// Interpolate operation: vector → polynomial (interpolation).
/// Tests: CExp::Interpolate, Node::interpolate.
#[test]
fn pin_interpolate() {
    // 4 (point, eval) pairs uniquely determine a polynomial of max degree 3
    // (4 coefficients under the m+1 convention), so the result type is
    // Uni<F, 3>.
    let src = r#"
        fn f<F: Field>(instance a: [F; 4]) -> Uni<F, 3> {
            interpolate([0,1,2,3], a)
        }
    "#;
    let gs = parse_and_build(src);

    let mut expected = UDag::<B>::new();
    let a = Vid::new("a");
    let vec_typ = ATyp::vec_scalar(4);
    let (_inp, _inp_args) = expected_inp(&mut expected, "f", &[instance_t("a", vec_typ.clone())]);
    let arg_a = _inp_args[0];
    let var_a = GOp::<B>::var(&a, arg_a, vec_typ);

    let points = GOp::<B>::vec(vec![
        GOp::index(0),
        GOp::index(1),
        GOp::index(2),
        GOp::index(3),
    ]);
    // add_exp materializes the Vec, creating a node for it
    let points_node = expected.add_node(Node::Op(mk::<B>(points.clone()), Nothing));
    let points_typ = points.typ();
    let points_ref = GOp::underscore(points_node, points_typ);
    expected.add_edges(DepType::Data, points_node, points);
    let interpolate_node = expected.add_node(Node::interpolate(&points_ref, &var_a));
    expected.add_edges(DepType::Data, interpolate_node, points_ref);
    expected.add_edges(DepType::Data, interpolate_node, var_a);

    assert!(gs[0] == expected);
}

/// FFT-grid eval operation: polynomial → vector (evaluation on the FFT grid).
/// Surface syntax: `eval(p)` (unary) lowers to merged Op::Evaluate(_, None, None).
/// Tests: CExp::Evaluate(_, None, None), GOp::evaluate_grid.
#[test]
fn pin_fft() {
    // Phase 14 m+1 convention + issue #116: Uni<F, 3> has 4 coefficients
    // (pow2 — required for FFT-grid eval to typecheck). eval() returns a
    // length-4 vector matching the coefficient count.
    let src = r#"
        fn f<F: Field>(instance a: Uni<F, 3>) -> [F; 4] {
            eval(a)
        }
    "#;
    let gs = parse_and_build(src);

    let mut expected = UDag::<B>::new();
    let a = Vid::new("a");
    let poly_typ = ATyp::Uni(3);
    let (_inp, _inp_args) = expected_inp(&mut expected, "f", &[instance_t("a", poly_typ.clone())]);
    let arg_a = _inp_args[0];
    let var_a = GOp::<B>::var(&a, arg_a, poly_typ);

    let eval_node = expected.add_node(Node::evaluate_grid(&var_a));
    expected.add_edges(DepType::Data, eval_node, var_a);

    assert!(gs[0] == expected);
}

#[test]
fn grid_eval_let_reuse_materializes_one_node() {
    let src = r#"
        fn f<F: Field>(instance p: Uni<F, 3>) -> F {
            let evs = eval(p);
            evs[0] + evs[1]
        }
    "#;
    let gs = parse_and_build(src);
    let dag = &gs[0];

    let grid_nodes = dag
        .graph
        .node_indices()
        .filter(|&idx| {
            matches!(
                dag.graph[idx].op(),
                Some(op) if matches!(op.get(), crate::Op::Evaluate(_, None, None))
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(grid_nodes.len(), 1, "expected one scheduled grid eval node");
    let grid_node = grid_nodes[0];

    let ram_bases = dag
        .graph
        .node_weights()
        .filter_map(|node| node.op())
        .flat_map(|op| ram_bases_referring_to_grid_eval(op.get(), grid_node))
        .collect::<Vec<_>>();
    assert_eq!(
        ram_bases.len(),
        2,
        "expected both evs[0] and evs[1] to read from the scheduled grid eval node"
    );

    let inline_grid_evals_under_consumers = dag
        .graph
        .node_indices()
        .filter(|&idx| idx != grid_node)
        .filter_map(|idx| dag.graph[idx].op())
        .map(|op| inline_grid_eval_count_inside_consumers(op.get()))
        .sum::<usize>();
    assert_eq!(
        inline_grid_evals_under_consumers, 0,
        "downstream consumers should reference the materialized grid eval, not embed inline eval(p) ops"
    );
}

fn ram_bases_referring_to_grid_eval(op: &GOp<B>, grid_node: NodeIndex) -> Vec<NodeIndex> {
    match op {
        crate::Op::Ram(base, index) => {
            let mut refs = ram_bases_referring_to_grid_eval(base.get(), grid_node);
            refs.extend(ram_bases_referring_to_grid_eval(index.get(), grid_node));
            if matches!(base.get(), crate::Op::Ref(Ref(node), _) if *node == grid_node) {
                refs.push(grid_node);
            }
            refs
        }
        crate::Op::Bin(_, left, right, _) | crate::Op::Pair(left, right, _) => {
            let mut refs = ram_bases_referring_to_grid_eval(left.get(), grid_node);
            refs.extend(ram_bases_referring_to_grid_eval(right.get(), grid_node));
            refs
        }
        crate::Op::Vec(children) => children
            .iter()
            .flat_map(|child| ram_bases_referring_to_grid_eval(child.get(), grid_node))
            .collect(),
        _ => Vec::new(),
    }
}

fn inline_grid_eval_count_inside_consumers(op: &GOp<B>) -> usize {
    match op {
        crate::Op::Evaluate(_, None, None) => 1,
        crate::Op::Ram(base, index) => {
            inline_grid_eval_count_inside_consumers(base.get())
                + inline_grid_eval_count_inside_consumers(index.get())
        }
        crate::Op::Bin(_, left, right, _) | crate::Op::Pair(left, right, _) => {
            inline_grid_eval_count_inside_consumers(left.get())
                + inline_grid_eval_count_inside_consumers(right.get())
        }
        crate::Op::Vec(children) => children
            .iter()
            .map(|child| inline_grid_eval_count_inside_consumers(child.get()))
            .sum(),
        _ => 0,
    }
}

/// Mle operation.
/// Tests: CExp::Mle, Node::mle.
#[test]
fn pin_mle() {
    let src = r#"
        fn f<F: Field>(instance a: [F; 4]) -> Mle<F, 2> {
            mle(a)
        }
    "#;
    let gs = parse_and_build(src);

    let mut expected = UDag::<B>::new();
    let a = Vid::new("a");
    let vec_typ = ATyp::vec_scalar(4);
    let (_inp, _inp_args) = expected_inp(&mut expected, "f", &[instance_t("a", vec_typ.clone())]);
    let arg_a = _inp_args[0];
    let var_a = GOp::<B>::var(&a, arg_a, vec_typ);

    let mle_node = expected.add_node(Node::mle(&var_a));
    expected.add_edges(DepType::Data, mle_node, var_a);

    assert!(gs[0] == expected);
}

// ============================================================================
// Group 8: Collections
// ============================================================================

/// Vec expression creates a GOp::Vec value.
/// Tests: CExp::Vec.
#[test]
fn pin_vec() {
    let src = r#"
        fn f<F: Field>(instance a: F, instance b: F) -> [F; 2] {
            [a, b]
        }
    "#;
    let gs = parse_and_build(src);

    // [a, b] produces GOp::Vec([Ref(Var(a, inp)), Ref(Var(b, inp))])
    // add_exp returned a non-Ref op, so add_top_exp creates a Ret node.
    let mut expected = UDag::<B>::new();
    let a = Vid::new("a");
    let b = Vid::new("b");
    let s = ATyp::scalar();
    let (_inp, _inp_args) = expected_inp(&mut expected, "f", &[instance_s("a"), instance_s("b")]);
    let arg_a = _inp_args[0];
    let arg_b = _inp_args[1];
    let var_a = GOp::<B>::var(&a, arg_a, s.clone());
    let var_b = GOp::<B>::var(&b, arg_b, s.clone());
    let vec_op = GOp::<B>::vec(vec![var_a.clone(), var_b.clone()]);
    let ret = expected.add_node(Node::ret(&vec_op));
    expected.add_edges(DepType::Data, ret, vec_op);

    assert!(gs[0] == expected);
}

// ============================================================================
// Group 9: Records
// ============================================================================

/// Record creation produces GOp::Record.
/// Tests: CExp::Record.
#[test]
fn pin_record() {
    let src = r#"
        fn f<F: Field>(instance a: F, instance b: F) -> { x: F, y: F } {
            {| x: a, y: b |}
        }
    "#;
    let gs = parse_and_build(src);

    // {| x: a, y: b |} produces GOp::Record({x: Var(a, inp), y: Var(b, inp)})
    // Not a Ref → ret node created
    let mut expected = UDag::<B>::new();
    let s = ATyp::scalar();
    let (_inp, _inp_args) = expected_inp(&mut expected, "f", &[instance_s("a"), instance_s("b")]);
    let arg_a = _inp_args[0];
    let arg_b = _inp_args[1];
    let var_a = GOp::<B>::var(&Vid::new("a"), arg_a, s.clone());
    let var_b = GOp::<B>::var(&Vid::new("b"), arg_b, s.clone());

    let mut rec_fields = Ctx::<String, HOp<B>>::new();
    rec_fields.insert(&"x".to_string(), &mk::<B>(var_a));
    rec_fields.insert(&"y".to_string(), &mk::<B>(var_b));
    let record_op = GOp::<B>::Record(rec_fields);

    let ret = expected.add_node(Node::ret(&record_op));
    expected.add_edges(DepType::Data, ret, record_op);

    assert!(gs[0] == expected);
}

/// Projection on record literal extracts the field directly.
/// Tests: CExp::Proj on CExp::Record.
#[test]
fn pin_proj_record_literal() {
    let src = r#"
        fn f<F: Field>(instance a: F, instance b: F) -> F {
            {| x: a, y: b |}.x
        }
    "#;
    let gs = parse_and_build(src);

    // { x: a, y: b }.x reduces directly to `a`, which is a Ref → no Ret.
    let mut expected = UDag::<B>::new();
    let _a = Vid::new("a");
    let (_inp, _inp_args) = expected_inp(&mut expected, "f", &[instance_s("a"), instance_s("b")]);

    assert!(gs[0] == expected);
}

// ============================================================================
// Group 10: Function Application
// ============================================================================

/// Function call inlines the body.
/// Tests: CExp::App (function call branch).
#[test]
fn pin_app_function() {
    let src = r#"
        fn double<F: Field>(instance x: F) -> F { x + x }
        fn f<F: Field>(instance a: F) -> F { double(a) }
    "#;
    let gs = parse_and_build(src);

    // f(a) inlines double(a) → a + a
    // gs[0] is the graph for `double`, gs[1] is for `f`
    // For `f`: the body after inlining is `a + a`
    assert!(gs.len() == 2);

    // Verify the `f` graph: should have Inp + Bin(Add, a, a)
    let mut expected_f = UDag::<B>::new();
    let a = Vid::new("a");
    let s = ATyp::scalar();
    let (_inp, _inp_args) = expected_inp(&mut expected_f, "f", &[instance_s("a")]);
    let arg_a = _inp_args[0];
    let var_a = GOp::<B>::var(&a, arg_a, s.clone());
    let bin = expected_f.add_node(Node::bin(BinOp::Add, &var_a, &var_a, &s));
    expected_f.add_edges(DepType::Data, bin, var_a.clone());
    expected_f.add_edges(DepType::Data, bin, var_a);

    assert!(gs[1] == expected_f);
}

// ============================================================================
// Group 11: Full Protocol Test
// ============================================================================

/// Full protocol test matching the existing graph_foo test.
/// Tests: proto with random, challenge, log, multiply, add, verify — all together.
#[test]
fn pin_proto_full() {
    let src = r#"
        proto foo<F: Field>(witness s: F, instance v: [F; 10]) where s == s {
            let r = random<F>;
            c <- challenge<F>;
            a <- r * c;
            b <- r + c + s;
            x <- v[1..5];
            verify(a * s == b * x[3])
        }
    "#;
    let gs = parse_and_build(src);
    // Just verify it builds successfully — this exercises many paths together
    assert!(gs.len() == 1);
}

// ============================================================================
// Group 12: Remaining Binary Operations
// ============================================================================

/// Power operator: `a ^ 2` creates Bin(Pow) node.
/// Tests: CExp::Bin(Pow) → GOp::pow fallthrough.
#[test]
fn pin_bin_pow() {
    let src = r#"
        fn f<F: Field>(instance a: F) -> F { a ^ 2 }
    "#;
    let gs = parse_and_build(src);

    let mut expected = UDag::<B>::new();
    let a = Vid::new("a");
    let s = ATyp::scalar();

    let (_inp, _inp_args) = expected_inp(&mut expected, "f", &[instance_s("a")]);
    let arg_a = _inp_args[0];
    let var_a = GOp::<B>::var(&a, arg_a, s.clone());
    let lit_2 = GOp::<B>::Value(backend::Value::Index(2));

    let bin = expected.add_node(Node::bin(BinOp::Pow, &var_a, &lit_2, &s));
    expected.add_edges(DepType::Data, bin, var_a);
    // lit_2 is Value, no references → no edge

    assert!(gs[0] == expected);
}

/// Dot product: `dot(a, b)` creates Bin(Dot) node.
/// Tests: CExp::Bin(Dot) → GOp::dot fallthrough for Ref operands.
#[test]
fn pin_bin_dot() {
    let src = r#"
        fn f<F: Field>(instance a: [F; 2], instance b: [F; 2]) -> F { dot(a, b) }
    "#;
    let gs = parse_and_build(src);

    let mut expected = UDag::<B>::new();
    let a = Vid::new("a");
    let b = Vid::new("b");
    let vs2 = ATyp::vec_scalar(2);
    let s = ATyp::scalar();

    let (_inp, _inp_args) = expected_inp(
        &mut expected,
        "f",
        &[instance_t("a", vs2.clone()), instance_t("b", vs2.clone())],
    );
    let arg_a = _inp_args[0];
    let arg_b = _inp_args[1];
    let var_a = GOp::<B>::var(&a, arg_a, vs2.clone());
    let var_b = GOp::<B>::var(&b, arg_b, vs2.clone());

    let dot_node = expected.add_node(Node::bin(BinOp::Dot, &var_a, &var_b, &s));
    expected.add_edges(DepType::Data, dot_node, var_a);
    expected.add_edges(DepType::Data, dot_node, var_b);

    assert!(gs[0] == expected);
}

/// Concatenation: `a ++ b` creates Bin(Concat) node.
/// Tests: CExp::Bin(Concat) → GOp::concat fallthrough for Ref operands.
#[test]
fn pin_bin_concat() {
    let src = r#"
        fn f<F: Field>(instance a: [F; 2], instance b: [F; 2]) -> [F; 4] { a ++ b }
    "#;
    let gs = parse_and_build(src);

    let mut expected = UDag::<B>::new();
    let a = Vid::new("a");
    let b = Vid::new("b");
    let vs2 = ATyp::vec_scalar(2);
    let vs4 = ATyp::vec_scalar(4);

    let (_inp, _inp_args) = expected_inp(
        &mut expected,
        "f",
        &[instance_t("a", vs2.clone()), instance_t("b", vs2.clone())],
    );
    let arg_a = _inp_args[0];
    let arg_b = _inp_args[1];
    let var_a = GOp::<B>::var(&a, arg_a, vs2.clone());
    let var_b = GOp::<B>::var(&b, arg_b, vs2.clone());

    let concat_node = expected.add_node(Node::bin(BinOp::Concat, &var_a, &var_b, &vs4));
    expected.add_edges(DepType::Data, concat_node, var_a);
    expected.add_edges(DepType::Data, concat_node, var_b);

    assert!(gs[0] == expected);
}

/// Remainder: `a % b` on polynomials creates Bin(Rem) node.
/// Tests: CExp::Bin(Rem) → GOp::rem fallthrough for Ref operands.
#[test]
fn pin_bin_rem() {
    let src = r#"
        fn f<F: Field>(instance a: Uni<F, 3>, instance b: Uni<F, 2>) -> Uni<F, 1> { a % b }
    "#;
    let gs = parse_and_build(src);

    let mut expected = UDag::<B>::new();
    let a = Vid::new("a");
    let b = Vid::new("b");
    let at_a = ATyp::Uni(3);
    let at_b = ATyp::Uni(2);
    let at_res = ATyp::Uni(1);

    let (_inp, _inp_args) = expected_inp(
        &mut expected,
        "f",
        &[instance_t("a", at_a.clone()), instance_t("b", at_b.clone())],
    );
    let arg_a = _inp_args[0];
    let arg_b = _inp_args[1];
    let var_a = GOp::<B>::var(&a, arg_a, at_a);
    let var_b = GOp::<B>::var(&b, arg_b, at_b);

    let rem_node = expected.add_node(Node::bin(BinOp::Rem, &var_a, &var_b, &at_res));
    expected.add_edges(DepType::Data, rem_node, var_a);
    expected.add_edges(DepType::Data, rem_node, var_b);

    assert!(gs[0] == expected);
}

/// Polynomial division: `a / b` on univariates creates a Bin(Div) node whose
/// result keeps the dividend's declared degree bound.
/// Tests: CExp::Bin(Div) → GOp::div fallthrough for polynomial Ref operands.
#[test]
fn pin_bin_poly_div() {
    let src = r#"
        fn f<F: Field>(instance a: Uni<F, 3>, instance b: Uni<F, 2>) -> Uni<F, 3> { a / b }
    "#;
    let gs = parse_and_build(src);

    let mut expected = UDag::<B>::new();
    let a = Vid::new("a");
    let b = Vid::new("b");
    let at_a = ATyp::Uni(3);
    let at_b = ATyp::Uni(2);
    let at_res = ATyp::Uni(3);

    let (_inp, _inp_args) = expected_inp(
        &mut expected,
        "f",
        &[instance_t("a", at_a.clone()), instance_t("b", at_b.clone())],
    );
    let arg_a = _inp_args[0];
    let arg_b = _inp_args[1];
    let var_a = GOp::<B>::var(&a, arg_a, at_a);
    let var_b = GOp::<B>::var(&b, arg_b, at_b);

    let div_node = expected.add_node(Node::bin(BinOp::Div, &var_a, &var_b, &at_res));
    expected.add_edges(DepType::Data, div_node, var_a);
    expected.add_edges(DepType::Data, div_node, var_b);

    assert!(gs[0] == expected);
}

// ============================================================================
// Group 13: Map, Ram, Eval
// ============================================================================

/// Map expression: `[x + x for x in a]` unrolls to per-element Bin(Add) nodes.
/// Tests: CExp::Map loop unrolling with Ram indexing.
#[test]
fn pin_map() {
    let src = r#"
        fn f<F: Field>(instance a: [F; 2]) -> [F; 2] { [x + x for x in a] }
    "#;
    let gs = parse_and_build(src);

    let mut expected = UDag::<B>::new();
    let a = Vid::new("a");
    let vs2 = ATyp::vec_scalar(2);
    let s = ATyp::scalar();

    let (_inp, _inp_args) = expected_inp(&mut expected, "f", &[instance_t("a", vs2.clone())]);
    let arg_a = _inp_args[0];
    let var_a = GOp::<B>::var(&a, arg_a, vs2);

    // `[x + x for x in a]` lowers to a single persistent `Op::Map` whose
    // domain references `a` and whose body is `loop_param#0 + loop_param#0`.
    let body = GOp::<B>::bin(
        BinOp::Add,
        GOp::<B>::loop_param(0, s.clone()),
        GOp::<B>::loop_param(0, s.clone()),
        s,
    );
    let map_op = GOp::<B>::map(var_a, body);
    let map_node = expected.add_node(Node::ret(&map_op));
    expected.add_edges(DepType::Data, map_node, map_op);

    assert!(gs[0] == expected);
}

/// Map over a polynomial vector must materialize the loop binder as the
/// input element type, even when the map body returns scalars.
#[test]
fn pin_map_poly_to_scalar_binder_type() {
    let src = r#"
        fn first_coef<F: Field>(p: Uni<F, 3>) -> F {
            let c = coef(p);
            c[0]
        }
        fn f<F: Field>(instance pv: [Uni<F, 3>; 2]) -> [F; 2] {
            [first_coef(x) for x in pv]
        }
    "#;
    let gs = parse_and_build(src);
    let dag = &gs[0];
    let ram_node_types: Vec<_> = dag
        .graph
        .node_weights()
        .filter_map(|node| match node {
            Node::Op(op, _) if matches!(op.get(), GOp::Ram(_, _)) => Some(op.typ()),
            _ => None,
        })
        .collect();

    assert_eq!(
        ram_node_types
            .iter()
            .filter(|typ| **typ == ATyp::Uni(3))
            .count(),
        2,
        "map binders over pv must be materialized as Uni<F, 3>, not as the scalar result type"
    );
}

/// Ram expression: `a[0]` produces nested Ram op, no graph node.
/// Tests: CExp::Ram → GOp::ram producing compound op in ret node.
#[test]
fn pin_ram_expr() {
    let src = r#"
        fn f<F: Field>(instance a: [F; 4]) -> F { a[0] }
    "#;
    let gs = parse_and_build(src);

    let mut expected = UDag::<B>::new();
    let a = Vid::new("a");
    let vs4 = ATyp::vec_scalar(4);

    let (_inp, _inp_args) = expected_inp(&mut expected, "f", &[instance_t("a", vs4.clone())]);
    let arg_a = _inp_args[0];
    let var_a = GOp::<B>::var(&a, arg_a, vs4);

    // a[0] → Ram(var_a, Value(Index(0))) — no graph node created
    let ram_op = GOp::<B>::ram(var_a, GOp::<B>::index(0));
    // Not a Ref → ret node created
    let ret = expected.add_node(Node::ret(&ram_op));
    expected.add_edges(DepType::Data, ret, ram_op);

    assert!(gs[0] == expected);
}

/// Eval expression: `eval(p, x)` produces nested Evaluate op, no graph node.
/// Tests: CExp::Evaluate(p, None, Some(x)) → GOp::evaluate wrapping two Refs in ret node.
#[test]
fn pin_eval() {
    let src = r#"
        fn f<F: Field>(instance p: Uni<F, 4>, instance x: F) -> F { eval(p, x) }
    "#;
    let gs = parse_and_build(src);

    let mut expected = UDag::<B>::new();
    let p = Vid::new("p");
    let x = Vid::new("x");
    let at_p = ATyp::Uni(4);
    let at_x = ATyp::scalar();

    let (_inp, _inp_args) = expected_inp(
        &mut expected,
        "f",
        &[instance_t("p", at_p.clone()), instance_t("x", at_x.clone())],
    );
    let arg_p = _inp_args[0];
    let arg_x = _inp_args[1];
    let var_p = GOp::<B>::var(&p, arg_p, at_p);
    let var_x = GOp::<B>::var(&x, arg_x, at_x);

    // evaluate(p, x) → Evaluate(var_p, var_x) — no graph node
    let eval_op = GOp::<B>::evaluate(var_p, var_x);
    // Not a Ref → ret node created
    let ret = expected.add_node(Node::ret(&eval_op));
    expected.add_edges(DepType::Data, ret, eval_op);

    assert!(gs[0] == expected);
}

// ============================================================================
// Group 14: Bilinear Pairing
// ============================================================================

/// Bilinear pairing: `pair(a, b)` produces Pair op, no graph node.
/// Tests: CExp::Pair → GOp::pair fallthrough for Ref operands.
#[test]
fn pin_pair() {
    let src = r#"
        fn f<G1: Group, G2: Group, GT: Pairing<G1, G2>>(instance a: G1, instance b: G2) -> GT {
            pair(a, b)
        }
    "#;
    let gs = parse_and_build(src);

    let mut expected = UDag::<B>::new();
    let a = Vid::new("a");
    let b = Vid::new("b");

    let (_inp, _inp_args) = expected_inp(
        &mut expected,
        "f",
        &[instance_t("a", ATyp::g1()), instance_t("b", ATyp::g2())],
    );
    let arg_a = _inp_args[0];
    let arg_b = _inp_args[1];
    let var_a = GOp::<B>::var(&a, arg_a, ATyp::g1());
    let var_b = GOp::<B>::var(&b, arg_b, ATyp::g2());

    // pair(a, b) → Pair(var_a, var_b, gt()) — no graph node
    let pair_op = GOp::<B>::pair(var_a, var_b, ATyp::gt());
    let ret = expected.add_node(Node::ret(&pair_op));
    expected.add_edges(DepType::Data, ret, pair_op);

    assert!(gs[0] == expected);
}

// ============================================================================
// Group 15: Record Projection from Variable & Set Record
// ============================================================================

/// Record projection from variable: `r.x` returns Ref(Var(r, inp), scalar).
/// Tests: CExp::Proj + CExp::Var → GOp::Ref(Ref(arg)) with field type.
#[test]
fn pin_proj_var() {
    let src = r#"
        fn f<F: Field>(instance r: { x: F, y: F }) -> F { r.x }
    "#;
    let gs = parse_and_build(src);

    let mut expected = UDag::<B>::new();
    let s = ATyp::scalar();

    let mut record_fields = Ctx::<String, ATyp>::new();
    record_fields.insert(&"x".to_string(), &s);
    record_fields.insert(&"y".to_string(), &s);
    let record_typ = ATyp::Record(record_fields);

    let (_inp, _inp_args) = expected_inp(&mut expected, "f", &[instance_t("r", record_typ)]);
    let _arg_r = _inp_args[0];

    // r.x → Ref(arg_r); since the body is a Ref, no Ret is added.

    assert!(gs[0] == expected);
}

/// SetRecord: `r.set(x, v)` desugars to Record({ x: v, y: r.y }).
/// Tests: CExp::SetRecord → desugaring into CExp::Record with Proj for unchanged fields.
#[test]
fn pin_set_record() {
    let src = r#"
        fn f<F: Field>(instance r: { x: F, y: F }, instance v: F) -> { x: F, y: F } {
            r.set(x, v)
        }
    "#;
    let gs = parse_and_build(src);

    let mut expected = UDag::<B>::new();
    let s = ATyp::scalar();

    let mut record_fields = Ctx::<String, ATyp>::new();
    record_fields.insert(&"x".to_string(), &s);
    record_fields.insert(&"y".to_string(), &s);
    let record_typ = ATyp::Record(record_fields);

    let (_inp, _inp_args) = expected_inp(
        &mut expected,
        "f",
        &[instance_t("r", record_typ), instance_s("v")],
    );
    let arg_r = _inp_args[0];
    let arg_v = _inp_args[1];

    // SetRecord desugars to: Record({ x: v, y: r.y })
    // x field: CExp::Var(v) → Ref(Var(v, inp), scalar)
    // y field: CExp::Proj(CExp::Var(r), "y") → Ref(Var(r, inp), scalar)
    let var_v = GOp::<B>::Ref(Ref(arg_v), s.clone());
    let var_r = GOp::<B>::Ref(Ref(arg_r), s.clone());

    let mut rec_fields = Ctx::<String, HOp<B>>::new();
    rec_fields.insert(&"x".to_string(), &mk::<B>(var_v));
    rec_fields.insert(&"y".to_string(), &mk::<B>(var_r));
    let record_op = GOp::<B>::Record(rec_fields);

    // Not a Ref → ret node
    let ret = expected.add_node(Node::ret(&record_op));
    expected.add_edges(DepType::Data, ret, record_op);

    assert!(gs[0] == expected);
}

// ============================================================================
// Group 16: Log on a let-bound name (vs. an inline op)
// ============================================================================

/// Log with a let-bound name: `Vid` is resolved via `op_from_var` to a `Ref(arg_or_node)`.
/// Companion test `pin_log_node_ref` exercises Log on an inline op result.
#[test]
fn pin_log_var_ref() {
    let src = r#"
        proto foo<F: Field>(witness s: F) where s == s {
            let x = s + s;
            a <- x;
            verify(a == s)
        }
    "#;
    let gs = parse_and_build(src);

    let mut expected = UDag::<B>::new();
    let s_vid = Vid::new("s");
    let a_vid = Vid::new("a");
    // Body
    let (inp, _inp_args) = expected_inp(&mut expected, "foo", &[witness_s("s")]);
    let arg_s = _inp_args[0];
    let var_s = GOp::<B>::var(&s_vid, arg_s, ATyp::scalar());

    // let x = s + s → Bin(Add) node
    let bin_add = expected.add_node(Node::bin(BinOp::Add, &var_s, &var_s, &ATyp::scalar()));
    expected.add_edges(DepType::Data, bin_add, var_s.clone());
    expected.add_edges(DepType::Data, bin_add, var_s.clone());
    // let-binding registers the name in vctx and marks it as non-transcript.
    expected.vctx.insert(&bin_add, &Vid::new("x"));
    expected.transcript_vars.insert(&bin_add, &false);
    let transcr_op = GOp::<B>::Ref(Ref(bin_add), ATyp::scalar());
    let transcr = expected.add_node(Node::transcr(&transcr_op));
    expected[transcr].set_transcript();
    expected.add_edges(DepType::Data, transcr, transcr_op.clone());
    expected.add_edge(inp, transcr, Dep::transcript());
    expected.vctx.insert(&transcr, &a_vid);
    expected.transcript_vars.insert(&transcr, &true);
    // because Log's first arm uses `ol.clone()` which is op_from_var(x) = GOp::Ref(Ref(bin_add), scalar)
    let var_a = GOp::<B>::var(&a_vid, transcr, ATyp::scalar());
    let equ = expected.add_node(Node::bin(BinOp::Equ, &var_a, &var_s, &ATyp::bool()));
    expected.add_edges(DepType::Data, equ, var_a);
    expected.add_edges(DepType::Data, equ, var_s);
    let equ_ref = GOp::<B>::underscore(equ, ATyp::bool());
    let check = expected.add_node(Node::verify(&equ_ref));
    expected.add_edges(DepType::Data, check, equ_ref);

    // Continuation Lit(0) → Ret(Value::Unit)
    let unit = GOp::<B>::Value(backend::Value::Unit);
    let ret = expected.add_node(Node::ret(&unit));
    expected.add_edges(DepType::Data, ret, unit);

    // Relation: Rel + Equ(var_s_rel, var_s_rel) + Assert(equ_rel_ref)
    let (_rel, _rel_args) = expected_rel(&mut expected, "foo", &[witness_s("s")]);
    let rel_arg_s = _rel_args[0];
    let var_s_rel = GOp::<B>::var(&s_vid, rel_arg_s, ATyp::scalar());
    let equ_rel = expected.add_node(Node::bin(BinOp::Equ, &var_s_rel, &var_s_rel, &ATyp::bool()));
    expected.add_edges(DepType::Data, equ_rel, var_s_rel.clone());
    expected.add_edges(DepType::Data, equ_rel, var_s_rel);
    let equ_rel_ref = GOp::<B>::underscore(equ_rel, ATyp::bool());
    let assert_rel = expected.add_node(Node::assert(&equ_rel_ref));
    expected.add_edges(DepType::Data, assert_rel, equ_rel_ref);

    assert!(gs[0] == expected);
}

// ========================================================================
// Group 12: Additional coverage tests
// ========================================================================

/// Let(None, ...) from multi-statement body (semicolon separator).
/// Proj(Var) where the var binds to a GOp::Record (direct field extraction).
/// `let r = {| x: a, y: b |}; r.x` → Record is stored in vars, r.x extracts field directly.
/// Tests: L1472-1478 — GOp::Record(record_fields) branch in Proj.
#[test]
fn pin_proj_var_record() {
    let src = r#"
        fn f<F: Field>(instance a: F, instance b: F) -> F {
            let r = {| x: a, y: b |};
            r.x
        }
    "#;
    let gs = parse_and_build(src);

    let mut expected = UDag::<B>::new();
    let s = ATyp::scalar();

    let (_inp, _inp_args) = expected_inp(&mut expected, "f", &[instance_s("a"), instance_s("b")]);
    let _arg_a = _inp_args[0];
    let _arg_b = _inp_args[1];

    // r = {| x: a, y: b |} — materialized into a Record node with edges to arg refs
    let ref_a = GOp::<B>::underscore(_arg_a, s.clone());
    let ref_b = GOp::<B>::underscore(_arg_b, s.clone());
    let mut fields = Ctx::<String, HOp<B>>::new();
    fields.insert(&"x".to_string(), &mk::<B>(ref_a.clone()));
    fields.insert(&"y".to_string(), &mk::<B>(ref_b.clone()));
    let rec_node = expected.add_node(Node::Op(mk::<B>(GOp::Record(fields)), Nothing));
    expected.add_edges(DepType::Data, rec_node, ref_a);
    expected.add_edges(DepType::Data, rec_node, ref_b);
    // let-binding registers the name in vctx and marks it as non-transcript.
    expected.vctx.insert(&rec_node, &Vid::new("r"));
    expected.transcript_vars.insert(&rec_node, &false);

    // r.x — Proj derefs Ref(Record) to extract field x, returns Ref(arg_a) directly.
    // The return value is a Ref, so no ret node is added.
    // The Record node remains in the graph as a structural dependency.

    assert!(gs[0] == expected);
}

/// Univariate polynomial application: `p(x)` where `p: Uni<F, 2>`.
/// Phase B: desugars to `evaluate(p, x)` using `Op::Evaluate`. The
/// pre-Phase-B desugaring (`dot(p, [x^0, x^1, x^2])`) was removed because
/// it relied on the now-removed `lub_dot(Poly, Vec)` arm.
/// Tests: CExp::App univariate path (graph/src/lib.rs ~L1620).
#[test]
fn pin_app_univariate_poly() {
    let src = r#"
        fn f<F: Field>(instance p: Uni<F, 2>, instance x: F) -> F { p(x) }
    "#;
    let gs = parse_and_build(src);

    let mut expected = UDag::<B>::new();
    let s = ATyp::scalar();

    let (_inp, _inp_args) = expected_inp(
        &mut expected,
        "f",
        &[instance_t("p", ATyp::Uni(2)), instance_t("x", s.clone())],
    );
    let arg_p = _inp_args[0];
    let arg_x = _inp_args[1];

    let var_p = GOp::<B>::var(&Vid::new("p"), arg_p, ATyp::Uni(2));
    let var_x = GOp::<B>::var(&Vid::new("x"), arg_x, s.clone());

    // p(x) lowers directly to evaluate(p, x).
    let eval = expected.add_node(Node::evaluate(&var_p, &var_x));
    expected.add_edges(DepType::Data, eval, var_p);
    expected.add_edges(DepType::Data, eval, var_x);

    assert!(gs[0] == expected);
}

/// Fun expression (polynomial literal): `fun(x) => x`.
/// Creates Value::Poly(VirtualPolynomial) representing the identity polynomial [0, 1].
/// Tests: CExp::Fun path (L1407-1419).
#[test]
fn pin_fun_lit() {
    use ark_ff::{One, Zero};
    use ark_poly::DenseUVPolynomial;
    use ark_poly::univariate::DensePolynomial;
    use backend::{PolyVariant, Value, VirtualPolynomial};
    type F = <B as backend::ArkConfig>::F;

    let src = r#"
        fn f<F: Field>() -> Uni<F, 1> { fun(x) => x }
    "#;
    let gs = parse_and_build(src);

    let mut expected = UDag::<B>::new();

    let (_inp, _) = expected_inp(&mut expected, "f", &[]);

    // fun(x) => x → DensePolynomial [0, 1] representing the identity
    let poly = DensePolynomial::from_coefficients_vec(vec![F::zero(), F::one()]);
    let pv = PolyVariant::DenseUni(poly);
    let vp = VirtualPolynomial::from_poly(pv);
    let val = GOp::<B>::Value(Value::Poly(vp));

    // Value is not a Ref → add_top_exp creates ret node
    let ret = expected.add_node(Node::ret(&val));
    // Value has no references → no edges
    expected.add_edges(DepType::Data, ret, val);

    assert!(gs[0] == expected);
}

// ============================================================================
// Group B: Graph Decomposition Tests
// ============================================================================

/// get_prover extracts the prover subgraph from transcript nodes backward.
/// Tests: get_prover() returns correct subgraph with inputs and computation up to transcripts.
#[test]
fn pin_get_prover_basic() {
    let src = r#"
        proto foo<F: Field>(witness s: F, instance v: F) where s == s {
            a <- s + v;
            verify(a == v)
        }
    "#;
    let gs = parse_and_build(src);
    let dag = &gs[0];

    let (prover, node_map) = dag.get_prover();

    // The prover should have an input node
    assert!(prover.node_count() > 0);
    // The prover should contain the input node mapping
    assert!(node_map.contains_key(&dag.input_node()));
    // The prover name matches
    assert_eq!(prover.name(), Vid::new("foo"));
    // Prover should have the computation leading to the transcript (s + v)
    // but NOT the verify check node
    assert!(prover.find_verify().is_empty());
}

/// get_verifier extracts the verifier subgraph.
/// Tests: get_verifier() produces subgraph with instance inputs, transcript vars, challenges, check node.
#[test]
fn pin_get_verifier_basic() {
    let src = r#"
        proto foo<F: Field>(witness s: F, instance v: F) where s == s {
            a <- s + v;
            verify(a == v)
        }
    "#;
    let gs = parse_and_build(src);
    let dag = &gs[0];

    let verifier = dag.get_verifier().unwrap();

    // Verifier must have a check node
    assert!(!verifier.find_verify().is_empty());
    // Verifier name matches
    assert_eq!(verifier.name(), Vid::new("foo"));
    // Verifier should not have witness-only computations
    // Verifier args should only include instance inputs (v) and transcript vars (a)
    let args: Vec<bool> = verifier
        .input_args()
        .into_iter()
        .filter_map(|n| match &verifier[n] {
            Node::Arg(_, _, qual, _, _) => Some(qual.is_instance()),
            _ => None,
        })
        .collect();
    assert!(args.iter().all(|is_instance| *is_instance));
}

/// get_relation extracts the relation subgraph from the Rel node.
/// Tests: get_relation() returns the relation subgraph for a protocol with `where` clause.
#[test]
fn pin_get_relation_basic() {
    let src = r#"
        proto foo<F: Field>(witness s: F, instance v: F) where s == v {
            verify(s == v)
        }
    "#;
    let gs = parse_and_build(src);
    let dag = &gs[0];

    let relation = dag.get_relation().unwrap();

    // Relation should have the Rel node
    assert!(relation.relation_node().is_some());
    // Relation should have the Equ operation from `s == v`
    assert!(!relation.op_nodes().is_empty());
}

/// Regression: get_relation had a duplicate outgoing-edge loop that doubled
/// the number of nodes explored. Verify edge count is reasonable.
#[test]
fn pin_get_relation_no_duplicate_edges() {
    let src = r#"
        proto foo<F: Field>(witness s: F, instance v: F) where s == v {
            verify(s == v)
        }
    "#;
    let gs = parse_and_build(src);
    let dag = &gs[0];

    let relation = dag.get_relation().unwrap();
    // A simple `s == v` relation should have ≤ 5 edges:
    // Rel→Arg(s), Rel→Arg(v), Arg(s)→Equ, Arg(v)→Equ, Equ→Assert
    assert!(
        relation.edge_count() <= 5,
        "get_relation has {} edges, expected ≤ 5 (duplicate loop bug?)",
        relation.edge_count()
    );
}

/// get_verifier returns error when verifier body references a witness input directly.
/// Tests: GraphError::NonInstanceNodeInVerifier.
#[test]
fn pin_get_verifier_witness_leak() {
    let src = r#"
        proto foo<F: Field>(witness s: F) where s == s {
            verify(s == s)
        }
    "#;
    let gs = parse_and_build(src);
    let dag = &gs[0];

    // The verifier assertion `s == s` directly uses witness `s`.
    let result = dag.get_verifier();
    match result {
        Err(GraphError::NonInstanceNodeInVerifier(_, _)) => {}
        Err(e) => panic!("Expected NonInstanceNodeInVerifier, got: {}", e),
        Ok(_) => panic!("Expected error but got Ok"),
    }
}

/// get_relation returns error for a function (no `where` clause).
/// Tests: GraphError::RelationNotFound.
#[test]
fn pin_get_relation_no_relation() {
    let src = r#"
        fn f<F: Field>(instance a: F) -> F { a }
    "#;
    let gs = parse_and_build(src);
    let dag = &gs[0];

    let result = dag.get_relation();
    match result {
        Err(GraphError::RelationNotFound(_)) => {}
        Err(e) => panic!("Expected RelationNotFound, got: {}", e),
        Ok(_) => panic!("Expected error but got Ok"),
    }
}

// ============================================================================
// Group C: Graph Query Method Tests
// ============================================================================

/// Verify node_count and edge_count return correct values.
#[test]
fn pin_node_edge_counts() {
    let src = r#"
        fn f<F: Field>(instance a: F, instance b: F) -> F { a + b }
    "#;
    let gs = parse_and_build(src);
    let dag = &gs[0];

    // Phase B: Inp marker + Arg(a) + Arg(b) + Bin(Add) = 4 nodes
    assert_eq!(dag.node_count(), 4);
    // Edges: Inp→Arg(a), Inp→Arg(b), Arg(a)→Bin, Arg(b)→Bin = 4 data edges
    assert_eq!(dag.edge_count(), 4);
}

/// op_nodes returns only operation nodes, excluding Inp and Rel.
#[test]
fn pin_op_nodes_filter() {
    let src = r#"
        proto foo<F: Field>(witness s: F) where s == s {
            verify(s == s)
        }
    "#;
    let gs = parse_and_build(src);
    let dag = &gs[0];

    let op_nodes = dag.op_nodes();
    // All op_nodes should be operation nodes (not Inp or Rel)
    for n in &op_nodes {
        assert!(dag[*n].is_op());
        assert!(!dag[*n].is_input());
        assert!(!dag[*n].is_relation());
    }
    // Should have at least the Equ and Verify nodes in the body, plus Equ in relation
    assert!(op_nodes.len() >= 2);
}

/// find_var returns the Vid for a node; find_ref returns a `Ref(node)` reference.
#[test]
fn pin_find_var_find_ref() {
    let src = r#"
        proto foo<F: Field>(witness a: F, witness b: F) where a == b {
            c <- a + b;
            verify(c == a)
        }
    "#;
    let gs = parse_and_build(src);
    let dag = &gs[0];

    // find_var now uses the vctx dictionary (Ctx<NodeIndex, Vid>) on the Dag.
    // `c <- a + b` creates a transcript node and registers it in vctx.
    let op_nodes = dag.op_nodes();
    // The transcript node should be findable as variable `c`
    let has_c = op_nodes
        .iter()
        .any(|n| dag.find_var(*n) == Some(Vid::new("c")));
    assert!(has_c, "Expected to find variable 'c' on an op node");
}

/// transcript_nodes returns nodes in topological order.
#[test]
fn pin_transcript_nodes_order() {
    let src = r#"
        proto foo<F: Field>(witness s: F) where s == s {
            a <- s + s;
            c <- challenge<F>;
            verify(a == c)
        }
    "#;
    let gs = parse_and_build(src);
    let dag = &gs[0];

    let tnodes = dag.transcript_nodes();
    // `a <- s + s` creates a Bin(Add) → set_transcript, `c <- challenge<F>` creates Transcr(Challenge)
    assert_eq!(tnodes.len(), 2);
    // Topological ordering: `a` transcript node comes before `c`
    for i in 1..tnodes.len() {
        let edge = dag.transcript_edge(tnodes[i], Direction::Incoming);
        if let Some(e) = edge {
            let parent = e.source();
            let parent_pos = tnodes.iter().position(|&n| n == parent);
            assert!(
                parent_pos.is_some() && parent_pos.unwrap() < i,
                "Transcript node {:?} parent {:?} should appear earlier",
                tnodes[i],
                parent
            );
        }
    }
}

/// get_proof_nodes and get_challenge_nodes partition transcript nodes correctly.
#[test]
fn pin_proof_vs_challenge_nodes() {
    let src = r#"
        proto foo<F: Field>(witness s: F) where s == s {
            a <- s + s;
            c <- challenge<F>;
            verify(a == c)
        }
    "#;
    let gs = parse_and_build(src);
    let dag = &gs[0];

    let proof_nodes = dag.get_proof_nodes();
    let challenge_nodes = dag.get_challenge_nodes();

    // `a <- s + s` creates a proof transcript, `c <- challenge<F>` creates a challenge
    assert_eq!(proof_nodes.len(), 1, "Expected 1 proof node");
    assert_eq!(challenge_nodes.len(), 1, "Expected 1 challenge node");

    // They should not overlap
    for p in &proof_nodes {
        assert!(!challenge_nodes.contains(p));
    }
}

/// Regression for issue #157: transcript ordering must retain all post-challenge
/// transcript binds, even when they re-log earlier transcript nodes via `Ref`.
#[test]
fn pin_transcript_nodes_preserve_post_challenge_relogs_issue_157() {
    let src = r#"
        proto repro<F: Field>(witness s: F) where s == s {
            c <- challenge<F>;
            a <- c;
            b <- a;
            d <- c;
            e <- c;
            f <- c;
            g <- c;
            verify(a == g)
        }
    "#;
    let gs = parse_and_build(src);
    let dag = &gs[0];

    const EXPECTED_TRANSCRIPT_NODES: usize = 7;
    const EXPECTED_PROOF_NODES: usize = 6;
    const EXPECTED_CHALLENGE_NODES: usize = 1;

    let transcript_nodes = dag.transcript_nodes();
    let proof_nodes = dag.get_proof_nodes();
    let challenge_nodes = dag.get_challenge_nodes();
    let (prover, _) = dag.get_prover();
    let verifier = dag.get_verifier().unwrap();

    assert_eq!(
        transcript_nodes.len(),
        EXPECTED_TRANSCRIPT_NODES,
        "Issue #157 repro should keep all 7 transcript nodes in order"
    );
    assert_eq!(
        proof_nodes.len(),
        EXPECTED_PROOF_NODES,
        "Issue #157 repro should expose 6 proof transcript nodes"
    );
    assert_eq!(
        challenge_nodes.len(),
        EXPECTED_CHALLENGE_NODES,
        "Issue #157 repro should expose exactly one challenge node"
    );
    assert_eq!(
        prover.transcript_nodes().len(),
        EXPECTED_TRANSCRIPT_NODES,
        "Issue #157 repro should preserve all transcript nodes in prover projection"
    );
    assert_eq!(
        verifier.transcript_nodes().len(),
        EXPECTED_TRANSCRIPT_NODES,
        "Issue #157 repro should preserve all transcript nodes in verifier projection"
    );
}

/// trc computes transitive-reflexive closure correctly.
#[test]
fn pin_trc_reachability() {
    let src = r#"
        fn f<F: Field>(instance a: F, instance b: F) -> F {
            let c = a + b;
            c * c
        }
    "#;
    let gs = parse_and_build(src);
    let dag = &gs[0];

    // Graph: Inp → Add(a,b) → Mul(c,c)
    // trc from Inp (outgoing) should reach all nodes
    let inp = dag.input_node();
    let forward = dag.trc(inp, Direction::Outgoing);
    assert_eq!(
        forward.len(),
        dag.node_count(),
        "Forward closure from inp should reach all nodes"
    );

    // trc from the last op (incoming) should also reach all nodes
    let max = dag.max_node();
    let backward = dag.trc(max, Direction::Incoming);
    assert_eq!(
        backward.len(),
        dag.node_count(),
        "Backward closure from max should reach all nodes"
    );
}

/// find_verify finds Verify nodes in a protocol and returns an empty Vec for a function.
#[test]
fn pin_find_verify() {
    let proto_src = r#"
        proto foo<F: Field>(witness s: F) where s == s {
            verify(s == s)
        }
    "#;
    let proto_gs = parse_and_build(proto_src);
    assert!(
        !proto_gs[0].find_verify().is_empty(),
        "Protocol should have a check node"
    );

    let fn_src = r#"
        fn f<F: Field>(instance a: F) -> F { a + a }
    "#;
    let fn_gs = parse_and_build(fn_src);
    assert!(
        fn_gs[0].find_verify().is_empty(),
        "Function should not have a check node"
    );
}

/// find_verify finds multiple Verify nodes in a protocol with multiple verify statements.
#[test]
fn pin_find_verify_multiple() {
    // Two separate verify statements produce two Verify nodes
    let src = r#"
        proto two_verify<F: Field>(witness x: F, witness y: F) where 1 == 1 {
            verify(x == x);
            verify(y == y)
        }
    "#;
    let gs = parse_and_build(src);
    let checks = gs[0].find_verify();
    assert_eq!(
        checks.len(),
        2,
        "Protocol with two verify statements should have two check nodes"
    );

    // Three separate verify statements produce three Verify nodes
    let src3 = r#"
        proto three_verify<F: Field>(witness x: F, witness y: F, witness z: F) where 1 == 1 {
            verify(x == x);
            verify(y == y);
            verify(z == z)
        }
    "#;
    let gs3 = parse_and_build(src3);
    let checks3 = gs3[0].find_verify();
    assert_eq!(
        checks3.len(),
        3,
        "Protocol with three verify statements should have three check nodes"
    );
}

/// get_verifier works correctly with multiple check nodes.
/// Tests: verifier subgraph includes all check nodes from a multi-verify protocol.
#[test]
fn pin_get_verifier_multiple_checks() {
    let src = r#"
        proto two_verify<F: Field>(witness s: F, witness t: F, instance v: F) where 1 == 1 {
            a <- s + v;
            b <- t + v;
            verify(a == v);
            verify(b == v)
        }
    "#;
    let gs = parse_and_build(src);
    let dag = &gs[0];

    let verifier = dag.get_verifier().unwrap();

    // Verifier must have one check node for each verify in this protocol
    let checks = verifier.find_verify();
    assert!(
        checks.len() == 2,
        "Verifier should have exactly 2 check nodes for a protocol with two verify statements, got {}",
        checks.len()
    );
    // Verifier name matches
    assert_eq!(verifier.name(), Vid::new("two_verify"));
    // Verifier args should only include instance inputs
    let args: Vec<bool> = verifier
        .input_args()
        .into_iter()
        .filter_map(|n| match &verifier[n] {
            Node::Arg(_, _, qual, _, _) => Some(qual.is_instance()),
            _ => None,
        })
        .collect();
    assert!(args.iter().all(|is_instance| *is_instance));
}

/// get_prover works correctly with multiple check nodes.
/// Tests: prover subgraph excludes all verify check nodes in a multi-verify protocol.
#[test]
fn pin_get_prover_multiple_checks() {
    let src = r#"
        proto two_verify<F: Field>(witness s: F, witness t: F, instance v: F) where 1 == 1 {
            a <- s + v;
            b <- t + v;
            verify(a == v);
            verify(b == v)
        }
    "#;
    let gs = parse_and_build(src);
    let dag = &gs[0];

    let (prover, _node_map) = dag.get_prover();

    // Prover should have computation nodes but NO verify check nodes
    assert!(
        prover.find_verify().is_empty(),
        "Prover should not have any check nodes"
    );
    // Prover name matches
    assert_eq!(prover.name(), Vid::new("two_verify"));
}

/// find_verify correctly identifies verify nodes scattered throughout a protocol body.
#[test]
fn pin_find_verify_scattered() {
    let src = r#"
        proto scattered<F: Field>(witness s: F, instance v: F) where 1 == 1 {
            a <- s + v;
            verify(a == a);
            b <- a * 2;
            verify(b == b)
        }
    "#;
    let gs = parse_and_build(src);
    let dag = &gs[0];

    let checks = dag.find_verify();
    assert_eq!(
        checks.len(),
        2,
        "Scattered verify statements should produce 2 check nodes, got {}",
        checks.len()
    );
}

/// find_verify correctly identifies verify nodes interleaved with challenge generation.
#[test]
fn pin_find_verify_interleaved_with_challenge() {
    let src = r#"
        proto interleaved<F: Field>(witness s: F, instance v: F) where 1 == 1 {
            a <- s + v;
            verify(a == a);
            c <- challenge<F>;
            z <- a + c;
            verify(z == z)
        }
    "#;
    let gs = parse_and_build(src);
    let dag = &gs[0];

    let checks = dag.find_verify();
    assert_eq!(
        checks.len(),
        2,
        "Interleaved verify+challenge should produce 2 check nodes, got {}",
        checks.len()
    );
}

/// Verifier subgraph from a protocol with scattered verify statements includes all
/// necessary dependencies and all args are instance.
#[test]
fn pin_get_verifier_scattered_checks() {
    let src = r#"
        proto scattered<F: Field>(witness s: F, instance v: F) where 1 == 1 {
            a <- s + v;
            verify(a == a);
            b <- a * 2;
            verify(b == b)
        }
    "#;
    let gs = parse_and_build(src);
    let dag = &gs[0];

    let verifier = dag.get_verifier().unwrap();
    let checks = verifier.find_verify();
    assert!(
        checks.len() >= 2,
        "Verifier should have at least 2 check nodes for scattered verify statements, got {}",
        checks.len()
    );

    // Verifier args should only include instance inputs
    let args: Vec<bool> = verifier
        .input_args()
        .into_iter()
        .filter_map(|n| match &verifier[n] {
            Node::Arg(_, _, qual, _, _) => Some(qual.is_instance()),
            _ => None,
        })
        .collect();
    assert!(
        args.iter().all(|is_instance| *is_instance),
        "All verifier args should be instance"
    );
}

/// Prover subgraph from a protocol with scattered verify statements excludes ALL check nodes.
#[test]
fn pin_get_prover_scattered_checks() {
    let src = r#"
        proto scattered<F: Field>(witness s: F, instance v: F) where 1 == 1 {
            a <- s + v;
            verify(a == a);
            b <- a * 2;
            verify(b == b)
        }
    "#;
    let gs = parse_and_build(src);
    let dag = &gs[0];

    let (prover, _node_map) = dag.get_prover();
    assert!(
        prover.find_verify().is_empty(),
        "Prover should not have any check nodes, even with scattered verify statements"
    );
}

/// Dags::protocols() and Dags::functions() correctly classify protocols with multiple
/// verify statements versus pure functions.
#[test]
fn pin_dags_multiple_verify_protocols() {
    let src = r#"
        fn helper<F: Field>(instance x: F) -> F { x }
        fn with_verify<F: Field>(x: F) -> F {
            verify(x == x);
            x
        }
        proto two_verify<F: Field>(witness s: F, instance v: F) where 1 == 1 {
            verify(s == s);
            verify(v == v)
        }
    "#;
    let gs = parse_and_build(src);

    let funcs = gs.functions();
    assert_eq!(gs.protocols().len(), 1, "Should have exactly 1 protocol");
    assert_eq!(
        funcs.len(),
        2,
        "Should have exactly 2 functions (including one with verify)"
    );
    assert_eq!(
        gs.protocols()[0].find_verify().len(),
        2,
        "Protocol with two verify statements should have 2 check nodes"
    );

    // A function with verify is still a function — it has no relation node
    let fn_with_verify = funcs
        .iter()
        .find(|g| g.name() == Vid::new("with_verify"))
        .unwrap();
    assert!(
        !fn_with_verify.find_verify().is_empty(),
        "Function with verify should have check nodes in its DAG"
    );
}

/// Inlined verify from a function call creates a Verify node that IS terminal
/// in the full DAG — the verify result is discarded by Let(None, ...), so nothing
/// consumes it. Both the inlined and protocol's own verify are found by find_verify.
#[test]
fn pin_find_verify_cross_function_verify() {
    let src = r#"
        fn with_verify<F: Field>(x: F) -> F {
            verify(x == x);
            x
        }
        proto caller<F: Field>(witness s: F, instance v: F) where s == v {
            a <- with_verify(v);
            verify(a == v)
        }
    "#;
    let gs = parse_and_build(src);

    let protos = gs.protocols();
    assert_eq!(protos.len(), 1, "Should have exactly 1 protocol");
    let proto = protos[0];
    // Both the inlined verify and the protocol's own verify are terminal
    assert_eq!(
        proto.find_verify().len(),
        2,
        "Full DAG should have 2 terminal checks: one inlined from function, one from protocol"
    );
    // Verifier subgraph: both checks are also present
    let verifier = proto.clone().rename_inner_nodes().get_verifier().unwrap();
    assert!(
        verifier.find_verify().len() >= 2,
        "Verifier should have both inlined and protocol check nodes, got {}",
        verifier.find_verify().len()
    );
}

// ============================================================================
// Group D: Graph Transformation Tests
// ============================================================================

/// erase_ann strips annotations from a DAG.
#[test]
fn pin_erase_ann() {
    let src = r#"
        fn f<F: Field>(instance a: F, instance b: F) -> F { a + b }
    "#;
    let gs = parse_and_build(src);
    let dag = &gs[0];

    // Map annotations to a string
    let annotated: crate::Dag<B, String> = dag.map_annotations(&|_op, _ann| "test".to_string());
    // Erase back to UDag
    let erased = annotated.erase_ann();

    // Should have same structure as original
    assert_eq!(erased.node_count(), dag.node_count());
    assert_eq!(erased.edge_count(), dag.edge_count());
    // Isomorphism check
    assert!(erased == *dag);
}

/// combine_dag merges two DAGs into one.
#[test]
fn pin_combine_dag() {
    let src = r#"
        fn f<F: Field>(instance a: F) -> F { a + a }
        fn g<F: Field>(instance b: F) -> F { b + b }
    "#;
    let gs = parse_and_build(src);
    let dag_f = &gs[0];
    let dag_g = &gs[1];

    let combined = dag_f.combine_dag(dag_g);

    // Combined should have sum of nodes and edges
    assert_eq!(
        combined.node_count(),
        dag_f.node_count() + dag_g.node_count()
    );
    assert_eq!(
        combined.edge_count(),
        dag_f.edge_count() + dag_g.edge_count()
    );
}

/// map_annotations transforms annotations on a DAG.
#[test]
fn pin_map_annotations_dag() {
    let src = r#"
        fn f<F: Field>(instance a: F, instance b: F) -> F { a + b }
    "#;
    let gs = parse_and_build(src);
    let dag = &gs[0];

    // Map Nothing annotations to a counter
    let annotated: crate::Dag<B, usize> = dag.map_annotations(&|_op, _ann| 42);

    // Structure should be preserved
    assert_eq!(annotated.node_count(), dag.node_count());
    assert_eq!(annotated.edge_count(), dag.edge_count());
    // Check that op nodes have the annotation value
    for n in annotated.op_nodes() {
        assert_eq!(annotated[n].clone().into_ann(), 42);
    }
}

// ============================================================================
// Group E: Dags Collection Tests
// ============================================================================

/// protocols() returns only protos, functions() returns only fns.
#[test]
fn pin_dags_protocols_vs_functions() {
    let src = r#"
        fn double<F: Field>(instance x: F) -> F { x + x }
        proto foo<F: Field>(witness s: F) where s == s {
            verify(s == s)
        }
    "#;
    let gs = parse_and_build(src);

    let protos = gs.protocols();
    let funcs = gs.functions();

    assert_eq!(protos.len(), 1, "Should have exactly 1 protocol");
    assert_eq!(funcs.len(), 1, "Should have exactly 1 function");
    assert_eq!(gs.len(), 2);

    // Protocol should have a check node
    assert!(!protos[0].find_verify().is_empty());
    // Function should not
    assert!(funcs[0].find_verify().is_empty());
}

/// get_proto finds a protocol by name.
#[test]
fn pin_dags_get_proto() {
    let src = r#"
        fn helper<F: Field>(instance x: F) -> F { x }
        proto bar<F: Field>(witness s: F) where s == s {
            verify(s == s)
        }
    "#;
    let gs = parse_and_build(src);

    // Find by name
    let bar = gs.get_proto(&"bar".to_string());
    assert!(bar.is_some(), "Should find protocol 'bar'");
    assert_eq!(bar.unwrap().name(), Vid::new("bar"));

    // Non-existent name
    let missing = gs.get_proto(&"nonexistent".to_string());
    assert!(missing.is_none(), "Should not find non-existent protocol");
}

// ============================================================================
// Group F: Error Path Tests
// ============================================================================

/// Non-polynomial Fun body triggers NonPolynomialFun error.
/// Power is not allowed in polynomial expressions (only Add, Sub, Mul).
#[test]
fn pin_error_non_polynomial_fun() {
    let src = r#"
        fn f<F: Field>(instance a: F) -> Uni<F, 2> { fun(x) => x ^ 2 }
    "#;
    let result = try_parse_and_build(src);
    match result {
        Err(GraphError::NonPolynomialFun(_)) => {}
        Err(e) => panic!("Expected NonPolynomialFun, got: {}", e),
        Ok(_) => panic!("Expected error but got Ok"),
    }
}

/// Unbound variable in Fun body triggers an error.
#[test]
fn pin_error_fun_unbound_var() {
    let src = r#"
        fn f<F: Field>(instance a: F) -> Uni<F, 1> { fun(x) => y }
    "#;
    // This may fail at parse/typecheck (unwrap in try_parse_and_build) or at graph building
    let result = std::panic::catch_unwind(|| try_parse_and_build(src));
    // Either it panics or returns Err — either way it should not succeed
    if let Ok(Ok(_)) = result {
        panic!("Unbound variable in Fun should fail");
    }
}

// ============================================================================
// Group G: Complex / Compositional Tests
// ============================================================================

/// Deep nested let chain: verifies correct dependency chain.
/// Tests: multiple CExp::Let(Some, ...) in sequence.
#[test]
fn pin_nested_let_chain() {
    let src = r#"
        fn f<F: Field>(instance x: F, instance y: F) -> F {
            let a = x + y;
            let b = a + x;
            let c = b + y;
            c
        }
    "#;
    let gs = parse_and_build(src);

    let mut expected = UDag::<B>::new();
    let s = ATyp::scalar();
    let (_inp, _inp_args) = expected_inp(&mut expected, "f", &[instance_s("x"), instance_s("y")]);
    let arg_x = _inp_args[0];
    let arg_y = _inp_args[1];
    let var_x = GOp::<B>::var(&Vid::new("x"), arg_x, s.clone());
    let var_y = GOp::<B>::var(&Vid::new("y"), arg_y, s.clone());

    // a = x + y
    let add_a = expected.add_node(Node::bin(BinOp::Add, &var_x, &var_y, &s));
    expected.add_edges(DepType::Data, add_a, var_x.clone());
    expected.add_edges(DepType::Data, add_a, var_y.clone());
    expected.vctx.insert(&add_a, &Vid::new("a"));
    expected.transcript_vars.insert(&add_a, &false);

    // b = a + x
    let ref_a = GOp::<B>::var(&Vid::new("a"), add_a, s.clone());
    let add_b = expected.add_node(Node::bin(BinOp::Add, &ref_a, &var_x, &s));
    expected.add_edges(DepType::Data, add_b, ref_a);
    expected.add_edges(DepType::Data, add_b, var_x);
    expected.vctx.insert(&add_b, &Vid::new("b"));
    expected.transcript_vars.insert(&add_b, &false);

    // c = b + y
    let ref_b = GOp::<B>::var(&Vid::new("b"), add_b, s.clone());
    let add_c = expected.add_node(Node::bin(BinOp::Add, &ref_b, &var_y, &s));
    expected.add_edges(DepType::Data, add_c, ref_b);
    expected.add_edges(DepType::Data, add_c, var_y);
    expected.vctx.insert(&add_c, &Vid::new("c"));
    expected.transcript_vars.insert(&add_c, &false);

    // `c` resolves to Ref(add_c); since the body is a Ref, add_top_exp
    // does not add a Ret node.
    let _ = add_c;

    assert!(gs[0] == expected);
}

/// Protocol with 3 transcript interactions verifies edge chain ordering.
/// Tests: multiple transcript edges in sequence.
#[test]
fn pin_multi_transcript() {
    let src = r#"
        proto foo<F: Field>(witness s: F) where s == s {
            a <- s + s;
            c <- challenge<F>;
            b <- s + c;
            verify(b == b)
        }
    "#;
    let gs = parse_and_build(src);
    let dag = &gs[0];

    // `a <- s + s` → set_transcript on Bin(Add) node
    // `c <- challenge<F>` → Challenge transcript node
    // `b <- s + c` → set_transcript on Bin(Add) node
    let tnodes = dag.transcript_nodes();
    assert_eq!(tnodes.len(), 3, "Expected 3 transcript nodes");

    // Verify second and third transcript nodes have incoming transcript edges
    assert!(
        dag.transcript_edge(tnodes[1], Direction::Incoming)
            .is_some(),
        "Second transcript should have incoming edge"
    );
    assert!(
        dag.transcript_edge(tnodes[2], Direction::Incoming)
            .is_some(),
        "Third transcript should have incoming edge"
    );
}

/// Multilinear Fun: `fun(x, y) => x + y` creates DenseMle.
/// Tests: CExp::Fun with multiple variables (multilinear path).
#[test]
fn pin_fun_multilinear() {
    use ark_ff::{One, Zero};
    use ark_poly::evaluations::multivariate::multilinear::DenseMultilinearExtension;
    use backend::{PolyVariant, Value, VirtualPolynomial};
    type F = <B as backend::ArkConfig>::F;

    let src = r#"
        fn f<F: Field>() -> Mle<F, 2> { fun(x, y) => x + y }
    "#;
    let gs = parse_and_build(src);

    let mut expected = UDag::<B>::new();
    let (_inp, _) = expected_inp(&mut expected, "f", &[]);

    // fun(x, y) => x + y
    // x is variable 0, y is variable 1
    // x: evaluations [0,1,0,1], y: evaluations [0,0,1,1]
    // x + y: evaluations [0,1,1,2]
    let evals = vec![F::zero(), F::one(), F::one(), F::from(2u64)];
    let mle = DenseMultilinearExtension::from_evaluations_vec(2, evals);
    let pv = PolyVariant::DenseMle(mle);
    let vp = VirtualPolynomial::from_poly(pv);
    let val = GOp::<B>::Value(Value::Poly(vp));

    let ret = expected.add_node(Node::ret(&val));
    expected.add_edges(DepType::Data, ret, val);

    assert!(gs[0] == expected);
}

/// Map with compound body: `[x * x + x for x in a]`.
/// Tests: CExp::Map with multiple operations per iteration.
#[test]
fn pin_map_nested_binop() {
    let src = r#"
        fn f<F: Field>(instance a: [F; 2]) -> [F; 2] { [x * x + x for x in a] }
    "#;
    let gs = parse_and_build(src);

    let mut expected = UDag::<B>::new();
    let a = Vid::new("a");
    let vs2 = ATyp::vec_scalar(2);
    let s = ATyp::scalar();
    let (_inp, _inp_args) = expected_inp(&mut expected, "f", &[instance_t("a", vs2.clone())]);
    let arg_a = _inp_args[0];
    let var_a = GOp::<B>::var(&a, arg_a, vs2);

    // `[x * x + x for x in a]` lowers to one `Op::Map` whose body is
    // `(loop_param#0 * loop_param#0) + loop_param#0`.
    let mul = GOp::<B>::bin(
        BinOp::Mul,
        GOp::<B>::loop_param(0, s.clone()),
        GOp::<B>::loop_param(0, s.clone()),
        s.clone(),
    );
    let body = GOp::<B>::bin(BinOp::Add, mul, GOp::<B>::loop_param(0, s.clone()), s);
    let map_op = GOp::<B>::map(var_a, body);
    let map_node = expected.add_node(Node::ret(&map_op));
    expected.add_edges(DepType::Data, map_node, map_op);

    assert!(gs[0] == expected);
}

/// Diamond DAG: `let c = a + b; c * c` — same node feeds both operands.
/// Tests: Ref sharing across operands of a binary op.
#[test]
fn pin_diamond_dag() {
    let src = r#"
        fn f<F: Field>(instance a: F, instance b: F) -> F {
            let c = a + b;
            c * c
        }
    "#;
    let gs = parse_and_build(src);

    let mut expected = UDag::<B>::new();
    let s = ATyp::scalar();
    let (_inp, _inp_args) = expected_inp(&mut expected, "f", &[instance_s("a"), instance_s("b")]);
    let arg_a = _inp_args[0];
    let arg_b = _inp_args[1];
    let var_a = GOp::<B>::var(&Vid::new("a"), arg_a, s.clone());
    let var_b = GOp::<B>::var(&Vid::new("b"), arg_b, s.clone());

    // c = a + b
    let add = expected.add_node(Node::bin(BinOp::Add, &var_a, &var_b, &s));
    expected.add_edges(DepType::Data, add, var_a);
    expected.add_edges(DepType::Data, add, var_b);
    expected.vctx.insert(&add, &Vid::new("c"));
    expected.transcript_vars.insert(&add, &false);

    // c * c  — both operands ref the same node
    let ref_c = GOp::<B>::var(&Vid::new("c"), add, s.clone());
    let mul = expected.add_node(Node::bin(BinOp::Mul, &ref_c, &ref_c, &s));
    expected.add_edges(DepType::Data, mul, ref_c.clone());
    expected.add_edges(DepType::Data, mul, ref_c);

    assert!(gs[0] == expected);
}

/// Three declarations: verify Dags ordering and cross-referencing.
#[test]
fn pin_three_declarations() {
    let src = r#"
        fn add1<F: Field>(instance x: F) -> F { x + 1 }
        fn double<F: Field>(instance x: F) -> F { x + x }
        fn composed<F: Field>(instance a: F) -> F { double(add1(a)) }
    "#;
    let gs = parse_and_build(src);

    assert_eq!(gs.len(), 3, "Should have 3 declarations");
    // All should be functions (no check node)
    assert_eq!(gs.functions().len(), 3);
    assert_eq!(gs.protocols().len(), 0);
    // The composed function inlines both calls
    assert!(gs[2].node_count() > 1);
}

/// MLE application: `p(x)` where `p: Mle<F, 2>`.
/// Tests: CExp::App with multilinear extension type (the untested App MLE path).
#[test]
fn pin_app_mle() {
    let src = r#"
        fn f<F: Field>(instance p: Mle<F, 2>, instance x: F) -> Mle<F, 1> { p(x) }
    "#;
    let gs = parse_and_build(src);

    let dag = &gs[0];
    // MLE application desugars to: mle_l + (mle_r - mle_l) * x
    // where mle_l = p[0..1], mle_r = p[1..2]
    // This should produce several nodes for the arithmetic
    assert!(
        dag.node_count() > 2,
        "MLE app should produce multiple nodes"
    );
    // Verify it's a function (no check node)
    assert!(dag.find_verify().is_empty());
}

// ── Stress tests (verify no stack overflow with iterative builder) ──

// ── Reduce operation tests ──

/// Reduce with addition: `reduce(+, [a, b, c])` creates a single Reduce node.
#[test]
fn pin_reduce_add() {
    let src = r#"
        fn f<F: Field>(instance v: [F; 3]) -> F {
            reduce(+, v)
        }
    "#;
    let gs = parse_and_build(src);
    let _dag = &gs[0];

    let mut expected = UDag::<B>::new();
    let (_inp, _inp_args) =
        expected_inp(&mut expected, "f", &[instance_t("v", ATyp::vec_scalar(3))]);
    let arg_v = _inp_args[0];
    let var_v = GOp::<B>::var(&Vid::new("v"), arg_v, ATyp::vec_scalar(3));

    let reduce = expected.add_node(Node::ret(&GOp::reduce(BinOp::Add, var_v.clone())));
    expected.add_edges(DepType::Data, reduce, var_v);

    assert!(gs[0] == expected);
}

/// Reduce with multiplication: `reduce(*, [a, b, c])`.
#[test]
fn pin_reduce_mul() {
    let src = r#"
        fn f<F: Field>(instance v: [F; 4]) -> F {
            reduce(*, v)
        }
    "#;
    let gs = parse_and_build(src);
    let _dag = &gs[0];

    let mut expected = UDag::<B>::new();
    let (_inp, _inp_args) =
        expected_inp(&mut expected, "f", &[instance_t("v", ATyp::vec_scalar(4))]);
    let arg_v = _inp_args[0];
    let var_v = GOp::<B>::var(&Vid::new("v"), arg_v, ATyp::vec_scalar(4));

    let reduce = expected.add_node(Node::ret(&GOp::reduce(BinOp::Mul, var_v.clone())));
    expected.add_edges(DepType::Data, reduce, var_v);

    assert!(gs[0] == expected);
}

/// Reduce with subtraction (non-commutative): `reduce(-, [a, b, c])`.
#[test]
fn pin_reduce_sub() {
    let src = r#"
        fn f<F: Field>(instance v: [F; 3]) -> F {
            reduce(-, v)
        }
    "#;
    let gs = parse_and_build(src);
    let _dag = &gs[0];

    let mut expected = UDag::<B>::new();
    let (_inp, _inp_args) =
        expected_inp(&mut expected, "f", &[instance_t("v", ATyp::vec_scalar(3))]);
    let arg_v = _inp_args[0];
    let var_v = GOp::<B>::var(&Vid::new("v"), arg_v, ATyp::vec_scalar(3));

    let reduce = expected.add_node(Node::ret(&GOp::reduce(BinOp::Sub, var_v.clone())));
    expected.add_edges(DepType::Data, reduce, var_v);

    assert!(gs[0] == expected);
}
