//! Pinning tests for the `from_module` transformation.
//!
//! Each test parses a `.zippel` source string, builds a graph via `from_module`,
//! then builds an expected graph manually and asserts structural equality
//! via the `PartialEq` (graph isomorphism) implementation.

use crate::{UDag, UDags, Node, GOp, HOp, Dep, DepType, PRef, Ref, GraphError, mk};
use backend::{ArkBls12_381, ATyp};
use lang::ast::{UModule, BinOp};
use lang::id::Vid;
use lang::typ::{Qualifier, Distribution};
use petgraph::graph::NodeIndex;
use petgraph::visit::EdgeRef;
use petgraph::Direction;
use share::Ctx;

type B = ArkBls12_381;

/// Parse a `.zippel` source string and build graphs via from_module.
fn parse_and_build(src: &str) -> UDags<B> {
    let m = UModule::from_str(src).unwrap().concretize(&Ctx::new()).unwrap();
    UDags::<B>::from_module(m).unwrap()
}

/// Parse and build, returning Result to allow testing error paths.
fn try_parse_and_build(src: &str) -> Result<UDags<B>, GraphError> {
    let m = UModule::from_str(src).unwrap().concretize(&Ctx::new()).unwrap();
    UDags::<B>::from_module(m)
}

/// Helper to build a PRef for a Public scalar argument.
fn pub_scalar_pref(name: &str) -> PRef {
    PRef::from_var(
        Vid::new(name),
        NodeIndex::new(0),
        ATyp::scalar(),
        0,
        Qualifier::Public,
        Distribution::Nonuniform,
    )
}

/// Helper to build a PRef for a Private scalar argument.
fn priv_scalar_pref(name: &str) -> PRef {
    PRef::from_var(
        Vid::new(name),
        NodeIndex::new(0),
        ATyp::scalar(),
        0,
        Qualifier::Private,
        Distribution::Nonuniform,
    )
}

/// Helper to build a PRef for a Public argument with a custom type.
fn pub_pref(name: &str, typ: ATyp) -> PRef {
    PRef::from_var(
        Vid::new(name),
        NodeIndex::new(0),
        typ,
        0,
        Qualifier::Public,
        Distribution::Nonuniform,
    )
}

// ============================================================================
// Group 1: Declaration Types
// ============================================================================

/// Func declaration returning sum with a literal — exercises Lit coercion.
/// Tests: CBody::Func, CExp::Bin with literal operand.
#[test]
fn pin_func_lit_in_binop() {
    // `a + 1` exercises CExp::Lit(1) as an operand in a Bin expression.
    // `1` alone can't be returned from `-> F` because it types as Fin, not Field.
    let gs = parse_and_build("fn f<F: Field>(public a: F) -> F { a + 1 }");

    let mut expected = UDag::<B>::new();
    let a = Vid::new("a");
    let s = ATyp::scalar();
    let inp = expected.add_node(Node::inp(Vid::new("f"), vec![pub_scalar_pref("a")]));
    let var_a = GOp::<B>::var(&a, inp, s.clone());
    let lit_1 = GOp::<B>::Value(backend::Value::Index(1));
    let bin = expected.add_node(Node::bin(BinOp::Add, &var_a, &lit_1, &s));
    expected.add_edges(DepType::Data, bin, var_a);

    assert!(gs[0] == expected);
}

/// Func declaration returning its argument.
/// Tests: CExp::Var, op_from_var (Ref::Var passthrough), ret-node with data edge.
#[test]
fn pin_func_var() {
    let gs = parse_and_build("fn f<F: Field>(public a: F) -> F { a }");

    let mut expected = UDag::<B>::new();
    let a = Vid::new("a");
    let inp = expected.add_node(Node::inp(Vid::new("f"), vec![pub_scalar_pref("a")]));
    let var_a = GOp::<B>::var(&a, inp, ATyp::scalar());
    let ret = expected.add_node(Node::ret(&var_a));
    expected.add_edges(DepType::Data, ret, var_a);

    assert!(gs[0] == expected);
}

/// Proto declaration with body and relation.
/// Tests: CBody::Proto, Inp node, Rel node, Bin(Equ) in relation, verify in body.
/// Note: Proto body and relation must BOTH type to Bool.
#[test]
fn pin_proto_simple() {
    let src = r#"
        proto foo<F: Field>(private s: F) where s == s {
            verify(s == s)
        }
    "#;
    let gs = parse_and_build(src);

    let mut expected = UDag::<B>::new();
    let s = Vid::new("s");
    let pref_s = priv_scalar_pref("s");

    // Body: Inp + Bin(Equ) + Check
    let inp = expected.add_node(Node::inp(Vid::new("foo"), vec![pref_s.clone()]));
    let var_s_body = GOp::<B>::var(&s, inp, ATyp::scalar());

    let equ_body = expected.add_node(Node::bin(BinOp::Equ, &var_s_body, &var_s_body, &ATyp::bool()));
    expected.add_edges(DepType::Data, equ_body, var_s_body.clone());
    expected.add_edges(DepType::Data, equ_body, var_s_body);

    let equ_ref = GOp::<B>::underscore(equ_body, ATyp::bool());
    let check = expected.add_node(Node::check(&equ_ref));
    expected.add_edges(DepType::Data, check, equ_ref);

    // Relation: Rel + Bin(Equ, s, s)
    let rel = expected.add_node(Node::rel(Vid::new("foo"), vec![pref_s]));
    let var_s_rel = GOp::<B>::var(&s, rel, ATyp::scalar());
    let equ_rel = expected.add_node(Node::bin(BinOp::Equ, &var_s_rel, &var_s_rel, &ATyp::bool()));
    expected.add_edges(DepType::Data, equ_rel, var_s_rel.clone());
    expected.add_edges(DepType::Data, equ_rel, var_s_rel);

    assert!(gs[0] == expected);
}

// ============================================================================
// Group 2: Basic Values
// ============================================================================

/// CExp::Bool produces a GOp::Value(Bool), wrapped in ret by add_top_exp.
#[test]
fn pin_bool() {
    let src = r#"
        fn f<F: Field>(public a: F) -> F {
            let _ = true;
            a
        }
    "#;
    let gs = parse_and_build(src);

    // `let _ = true; a` — the `true` evaluates to Value(Bool(true)) but
    // doesn't create a node (Let(None) just evaluates both sides).
    // Only `a` matters for the graph structure.
    let mut expected = UDag::<B>::new();
    let a = Vid::new("a");
    let inp = expected.add_node(Node::inp(Vid::new("f"), vec![pub_scalar_pref("a")]));
    let var_a = GOp::<B>::var(&a, inp, ATyp::scalar());
    let ret = expected.add_node(Node::ret(&var_a));
    expected.add_edges(DepType::Data, ret, var_a);

    assert!(gs[0] == expected);
}

/// CExp::Range produces a GOp::Range value, wrapped in ret by add_top_exp.
#[test]
fn pin_range() {
    let src = r#"
        fn f<F: Field>(public a: [F; 10]) -> [F; 5] {
            a[0..5]
        }
    "#;
    let gs = parse_and_build(src);

    // a[0..5] is Ram(Var(a), Range(0..5))
    let mut expected = UDag::<B>::new();
    let a = Vid::new("a");
    let vs10 = ATyp::vec_scalar(10);
    let pref_a = PRef::from_var(a.clone(), NodeIndex::new(0), vs10.clone(), 0, Qualifier::Public, Distribution::Nonuniform);
    let inp = expected.add_node(Node::inp(Vid::new("f"), vec![pref_a]));
    let var_a = GOp::<B>::var(&a, inp, vs10);
    let ram_op = GOp::<B>::ram(var_a, GOp::<B>::range(lang::typ::CRange::new(0, 5)));

    // Not Ref::Node → ret node
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
        "fn f<F: Field>(public a: F, public b: F) -> {} {{ a {} b }}",
        if result_typ == ATyp::bool() { "Bool" } else { "F" },
        op_str
    );
    let gs = parse_and_build(&src);

    let mut expected = UDag::<B>::new();
    let a = Vid::new("a");
    let b = Vid::new("b");
    let inp = expected.add_node(Node::inp(
        Vid::new("f"),
        vec![pub_scalar_pref("a"), pub_scalar_pref("b")],
    ));
    let var_a = GOp::<B>::var(&a, inp, ATyp::scalar());
    let var_b = GOp::<B>::var(&b, inp, ATyp::scalar());
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

#[test]
fn pin_bin_equ() {
    assert_binop("==", BinOp::Equ, ATyp::bool());
}

// ============================================================================
// Group 4: Crypto Operations
// ============================================================================

/// Random scalar, no transcript edge.
/// Tests: CExp::Random, Node::random.
#[test]
fn pin_random() {
    let src = "fn f<F: Field>(public a: F) -> F { random<F> }";
    let gs = parse_and_build(src);

    let mut expected = UDag::<B>::new();
    let _inp = expected.add_node(Node::inp(Vid::new("f"), vec![pub_scalar_pref("a")]));
    let _rand = expected.add_node(Node::random(&ATyp::scalar(), false));

    assert!(gs[0] == expected);
}

/// Random non-zero scalar.
#[test]
fn pin_random_nz() {
    let src = "fn f<F: Field>(public a: F) -> F { random<F*> }";
    let gs = parse_and_build(src);

    let mut expected = UDag::<B>::new();
    let _inp = expected.add_node(Node::inp(Vid::new("f"), vec![pub_scalar_pref("a")]));
    let _rand = expected.add_node(Node::random(&ATyp::scalar(), true));

    assert!(gs[0] == expected);
}

/// Challenge creates a transcript edge from the start node.
/// Tests: CExp::Challenge, Node::challenge, transcript edge.
#[test]
fn pin_challenge() {
    let src = "fn f<F: Field>(public a: F) -> F { challenge<F> }";
    let gs = parse_and_build(src);

    let mut expected = UDag::<B>::new();
    let inp = expected.add_node(Node::inp(Vid::new("f"), vec![pub_scalar_pref("a")]));
    let ch = expected.add_node(Node::challenge(&ATyp::scalar(), false));
    expected.add_edge(inp, ch, Dep::transcript());

    assert!(gs[0] == expected);
}

/// Challenge non-zero.
#[test]
fn pin_challenge_nz() {
    let src = "fn f<F: Field>(public a: F) -> F { challenge<F*> }";
    let gs = parse_and_build(src);

    let mut expected = UDag::<B>::new();
    let inp = expected.add_node(Node::inp(Vid::new("f"), vec![pub_scalar_pref("a")]));
    let ch = expected.add_node(Node::challenge(&ATyp::scalar(), true));
    expected.add_edge(inp, ch, Dep::transcript());

    assert!(gs[0] == expected);
}

// ============================================================================
// Group 5: Control Flow
// ============================================================================

/// Let binding: `let c = a + b; c`.
/// Tests: CExp::Let(Some), variable context update, op_from_var Ref::Node->Ref::Var.
#[test]
fn pin_let_named() {
    let src = r#"
        fn f<F: Field>(public a: F, public b: F) -> F {
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
    let inp = expected.add_node(Node::inp(
        Vid::new("f"),
        vec![pub_scalar_pref("a"), pub_scalar_pref("b")],
    ));
    let var_a = GOp::<B>::var(&a, inp, s.clone());
    let var_b = GOp::<B>::var(&b, inp, s.clone());

    // a + b creates a bin node
    let bin = expected.add_node(Node::bin(BinOp::Add, &var_a, &var_b, &s));
    expected.add_edges(DepType::Data, bin, var_a);
    expected.add_edges(DepType::Data, bin, var_b);

    // `c` resolves to Ref::Var("c", bin) via op_from_var, triggers ret node
    let var_c = GOp::<B>::var(&c, bin, s.clone());
    let ret = expected.add_node(Node::ret(&var_c));
    expected.add_edges(DepType::Data, ret, var_c);

    assert!(gs[0] == expected);
}

/// Anonymous let: `let _ = a + b; a * b`.
/// Tests: CExp::Let(None), both sides evaluated, second is the result.
#[test]
fn pin_let_anon() {
    let src = r#"
        fn f<F: Field>(public a: F, public b: F) -> F {
            let _ = a + b;
            a * b
        }
    "#;
    let gs = parse_and_build(src);

    let mut expected = UDag::<B>::new();
    let a = Vid::new("a");
    let b = Vid::new("b");
    let s = ATyp::scalar();
    let inp = expected.add_node(Node::inp(
        Vid::new("f"),
        vec![pub_scalar_pref("a"), pub_scalar_pref("b")],
    ));
    let var_a = GOp::<B>::var(&a, inp, s.clone());
    let var_b = GOp::<B>::var(&b, inp, s.clone());

    // let _ = a + b → Bin(Add) node (result discarded)
    let add = expected.add_node(Node::bin(BinOp::Add, &var_a, &var_b, &s));
    expected.add_edges(DepType::Data, add, var_a.clone());
    expected.add_edges(DepType::Data, add, var_b.clone());

    // a * b → Bin(Mul) node (this is the return value, Ref::Node so no ret)
    let mul = expected.add_node(Node::bin(BinOp::Mul, &var_a, &var_b, &s));
    expected.add_edges(DepType::Data, mul, var_a);
    expected.add_edges(DepType::Data, mul, var_b);

    assert!(gs[0] == expected);
}

/// Assert expression.
/// Tests: CExp::Assert, Node::check, check node with data edge.
#[test]
fn pin_assert() {
    let src = r#"
        fn f<F: Field>(public a: F, public b: F) -> Bool {
            assert(a == b)
        }
    "#;
    let gs = parse_and_build(src);

    let mut expected = UDag::<B>::new();
    let a = Vid::new("a");
    let b = Vid::new("b");
    let inp = expected.add_node(Node::inp(
        Vid::new("f"),
        vec![pub_scalar_pref("a"), pub_scalar_pref("b")],
    ));
    let var_a = GOp::<B>::var(&a, inp, ATyp::scalar());
    let var_b = GOp::<B>::var(&b, inp, ATyp::scalar());

    // a == b → Bin(Equ) node
    let equ = expected.add_node(Node::bin(BinOp::Equ, &var_a, &var_b, &ATyp::bool()));
    expected.add_edges(DepType::Data, equ, var_a);
    expected.add_edges(DepType::Data, equ, var_b);

    // assert(...) → Check node
    let equ_ref = GOp::<B>::underscore(equ, ATyp::bool());
    let check = expected.add_node(Node::check(&equ_ref));
    expected.add_edges(DepType::Data, check, equ_ref);

    assert!(gs[0] == expected);
}

/// Verify expression (same structure as assert).
/// Tests: CExp::Verify, Node::check.
#[test]
fn pin_verify() {
    let src = r#"
        fn f<F: Field>(public a: F, public b: F) -> Bool {
            verify(a == b)
        }
    "#;
    let gs = parse_and_build(src);

    let mut expected = UDag::<B>::new();
    let a = Vid::new("a");
    let b = Vid::new("b");
    let inp = expected.add_node(Node::inp(
        Vid::new("f"),
        vec![pub_scalar_pref("a"), pub_scalar_pref("b")],
    ));
    let var_a = GOp::<B>::var(&a, inp, ATyp::scalar());
    let var_b = GOp::<B>::var(&b, inp, ATyp::scalar());

    let equ = expected.add_node(Node::bin(BinOp::Equ, &var_a, &var_b, &ATyp::bool()));
    expected.add_edges(DepType::Data, equ, var_a);
    expected.add_edges(DepType::Data, equ, var_b);

    let equ_ref = GOp::<B>::underscore(equ, ATyp::bool());
    let check = expected.add_node(Node::check(&equ_ref));
    expected.add_edges(DepType::Data, check, equ_ref);

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
        proto foo<F: Field>(private s: F) where s == s {
            a <- s + s;
            verify(a == s)
        }
    "#;
    let gs = parse_and_build(src);

    let mut expected = UDag::<B>::new();
    let s_vid = Vid::new("s");
    let a_vid = Vid::new("a");

    // Body
    let inp = expected.add_node(Node::inp(Vid::new("foo"), vec![priv_scalar_pref("s")]));
    let var_s = GOp::<B>::var(&s_vid, inp, ATyp::scalar());

    // s + s → Bin(Add) node, then set_transcript converts it to Transcr
    let bin_add = expected.add_node(Node::bin(BinOp::Add, &var_s, &var_s, &ATyp::scalar()));
    expected.add_edges(DepType::Data, bin_add, var_s.clone());
    expected.add_edges(DepType::Data, bin_add, var_s.clone());

    let bin_add_ref = GOp::<B>::underscore(bin_add, ATyp::scalar());
    let transcr_op = GOp::<B>::Ref(Ref::Node(bin_add), ATyp::scalar());
    let transcr = expected.add_node(Node::transcr(&transcr_op));
    expected.add_edges(DepType::Data, transcr, bin_add_ref.clone());
    expected.add_edge(inp, transcr, Dep::transcript());
    expected.vctx.insert(&transcr, &a_vid);
    expected.transcript_vars.insert(&transcr, &true);
    // a == s → Bin(Equ)
    let var_a = GOp::<B>::var(&a_vid, transcr, ATyp::scalar());
    let equ = expected.add_node(Node::bin(BinOp::Equ, &var_a, &var_s, &ATyp::bool()));
    expected.add_edges(DepType::Data, equ, var_a);
    expected.add_edges(DepType::Data, equ, var_s);

    // verify(...) → Check node
    let equ_ref = GOp::<B>::underscore(equ, ATyp::bool());
    let check = expected.add_node(Node::check(&equ_ref));
    expected.add_edges(DepType::Data, check, equ_ref);

    // Relation: Rel + Bin(Equ, s, s)
    let rel = expected.add_node(Node::rel(Vid::new("foo"), vec![priv_scalar_pref("s")]));
    let var_s_rel = GOp::<B>::var(&s_vid, rel, ATyp::scalar());
    let equ_rel = expected.add_node(Node::bin(BinOp::Equ, &var_s_rel, &var_s_rel, &ATyp::bool()));
    expected.add_edges(DepType::Data, equ_rel, var_s_rel.clone());
    expected.add_edges(DepType::Data, equ_rel, var_s_rel);

    assert!(gs[0] == expected);
}

/// Log with non-node value: `a <- 1; verify(s == s)`.
/// Tests: CExp::Log (second branch), new Transcr node creation.
#[test]
fn pin_log_new_transcr() {
    let src = r#"
        proto foo<F: Field>(private s: F) where s == s {
            a <- 1;
            verify(s == s)
        }
    "#;
    let gs = parse_and_build(src);

    let mut expected = UDag::<B>::new();
    let s_vid = Vid::new("s");
    let a_vid = Vid::new("a");

    // Body
    let inp = expected.add_node(Node::inp(Vid::new("foo"), vec![priv_scalar_pref("s")]));

    // `1` is Value(Index(1)), not a Ref → second branch of Log: creates new Transcr node
    let lit_op = GOp::<B>::Value(backend::Value::Index(1));
    let transcr = expected.add_node(Node::transcr(&lit_op));
    expected[transcr].set_transcript();
    // transcript edge from inp to transcr
    expected.add_edge(inp, transcr, Dep::transcript());
    expected.vctx.insert(&transcr, &a_vid);
    expected.transcript_vars.insert(&transcr, &true);
    let var_s = GOp::<B>::var(&s_vid, inp, ATyp::scalar());
    let equ_body = expected.add_node(Node::bin(BinOp::Equ, &var_s, &var_s, &ATyp::bool()));
    expected.add_edges(DepType::Data, equ_body, var_s.clone());
    expected.add_edges(DepType::Data, equ_body, var_s);

    let equ_ref = GOp::<B>::underscore(equ_body, ATyp::bool());
    let check = expected.add_node(Node::check(&equ_ref));
    expected.add_edges(DepType::Data, check, equ_ref);

    // Relation: Rel + Bin(Equ, s, s)
    let rel = expected.add_node(Node::rel(Vid::new("foo"), vec![priv_scalar_pref("s")]));
    let var_s_rel = GOp::<B>::var(&s_vid, rel, ATyp::scalar());
    let equ = expected.add_node(Node::bin(BinOp::Equ, &var_s_rel, &var_s_rel, &ATyp::bool()));
    expected.add_edges(DepType::Data, equ, var_s_rel.clone());
    expected.add_edges(DepType::Data, equ, var_s_rel);

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
        fn f<F: Field>(public a: [F; 4]) -> Uni<F, 4> {
            poly(a)
        }
    "#;
    let gs = parse_and_build(src);

    let mut expected = UDag::<B>::new();
    let a = Vid::new("a");
    let vec_typ = ATyp::vec_scalar(4);
    let pref_a = PRef::from_var(
        a.clone(),
        NodeIndex::new(0),
        vec_typ.clone(),
        0,
        Qualifier::Public,
        Distribution::Nonuniform,
    );
    let inp = expected.add_node(Node::inp(Vid::new("f"), vec![pref_a]));
    let var_a = GOp::<B>::var(&a, inp, vec_typ);

    let poly = expected.add_node(Node::poly(&var_a));
    expected.add_edges(DepType::Data, poly, var_a);

    assert!(gs[0] == expected);
}

/// Coef operation on a polynomial argument.
/// Tests: CExp::Coef, Node::coef.
#[test]
fn pin_coef() {
    let src = r#"
        fn f<F: Field>(public a: Uni<F, 4>) -> [F; 4] {
            coef(a)
        }
    "#;
    let gs = parse_and_build(src);

    let mut expected = UDag::<B>::new();
    let a = Vid::new("a");
    let poly_typ = ATyp::vpoly(1, 4);
    let pref_a = PRef::from_var(a.clone(), NodeIndex::new(0), poly_typ.clone(), 0, Qualifier::Public, Distribution::Nonuniform);
    let inp = expected.add_node(Node::inp(Vid::new("f"), vec![pref_a]));
    let var_a = GOp::<B>::var(&a, inp, poly_typ);

    let coef_node = expected.add_node(Node::coef(&var_a));
    expected.add_edges(DepType::Data, coef_node, var_a);

    assert!(gs[0] == expected);
}

/// Ifft operation: vector → polynomial (interpolation).
/// Tests: CExp::Ifft, Node::ifft.
#[test]
fn pin_ifft() {
    let src = r#"
        fn f<F: Field>(public a: [F; 4]) -> Uni<F, 4> {
            ifft(a)
        }
    "#;
    let gs = parse_and_build(src);

    let mut expected = UDag::<B>::new();
    let a = Vid::new("a");
    let vec_typ = ATyp::vec_scalar(4);
    let pref_a = PRef::from_var(a.clone(), NodeIndex::new(0), vec_typ.clone(), 0, Qualifier::Public, Distribution::Nonuniform);
    let inp = expected.add_node(Node::inp(Vid::new("f"), vec![pref_a]));
    let var_a = GOp::<B>::var(&a, inp, vec_typ);

    let ifft_node = expected.add_node(Node::ifft(&var_a));
    expected.add_edges(DepType::Data, ifft_node, var_a);

    assert!(gs[0] == expected);
}

/// Fft operation: polynomial → vector (evaluation).
/// Tests: CExp::Fft, Node::fft.
#[test]
fn pin_fft() {
    let src = r#"
        fn f<F: Field>(public a: Uni<F, 4>) -> [F; 4] {
            fft(a)
        }
    "#;
    let gs = parse_and_build(src);

    let mut expected = UDag::<B>::new();
    let a = Vid::new("a");
    let poly_typ = ATyp::vpoly(1, 4);
    let pref_a = PRef::from_var(a.clone(), NodeIndex::new(0), poly_typ.clone(), 0, Qualifier::Public, Distribution::Nonuniform);
    let inp = expected.add_node(Node::inp(Vid::new("f"), vec![pref_a]));
    let var_a = GOp::<B>::var(&a, inp, poly_typ);

    let fft_node = expected.add_node(Node::fft(&var_a));
    expected.add_edges(DepType::Data, fft_node, var_a);

    assert!(gs[0] == expected);
}

/// Mle operation.
/// Tests: CExp::Mle, Node::mle.
#[test]
fn pin_mle() {
    let src = r#"
        fn f<F: Field>(public a: [F; 4]) -> Mle<F, 2> {
            mle(a)
        }
    "#;
    let gs = parse_and_build(src);

    let mut expected = UDag::<B>::new();
    let a = Vid::new("a");
    let vec_typ = ATyp::vec_scalar(4);
    let pref_a = PRef::from_var(a.clone(), NodeIndex::new(0), vec_typ.clone(), 0, Qualifier::Public, Distribution::Nonuniform);
    let inp = expected.add_node(Node::inp(Vid::new("f"), vec![pref_a]));
    let var_a = GOp::<B>::var(&a, inp, vec_typ);

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
        fn f<F: Field>(public a: F, public b: F) -> [F; 2] {
            [a, b]
        }
    "#;
    let gs = parse_and_build(src);

    // [a, b] produces GOp::Vec([Ref(Var(a, inp)), Ref(Var(b, inp))])
    // This is not a Ref::Node, so add_top_exp creates a ret node.
    let mut expected = UDag::<B>::new();
    let a = Vid::new("a");
    let b = Vid::new("b");
    let s = ATyp::scalar();
    let inp = expected.add_node(Node::inp(
        Vid::new("f"),
        vec![pub_scalar_pref("a"), pub_scalar_pref("b")],
    ));
    let var_a = GOp::<B>::var(&a, inp, s.clone());
    let var_b = GOp::<B>::var(&b, inp, s.clone());
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
        fn f<F: Field>(public a: F, public b: F) -> { x: F, y: F } {
            {| x: a, y: b |}
        }
    "#;
    let gs = parse_and_build(src);

    // {| x: a, y: b |} produces GOp::Record({x: Var(a, inp), y: Var(b, inp)})
    // Not a Ref::Node → ret node created
    let mut expected = UDag::<B>::new();
    let s = ATyp::scalar();
    let inp = expected.add_node(Node::inp(
        Vid::new("f"),
        vec![pub_scalar_pref("a"), pub_scalar_pref("b")],
    ));
    let var_a = GOp::<B>::var(&Vid::new("a"), inp, s.clone());
    let var_b = GOp::<B>::var(&Vid::new("b"), inp, s.clone());

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
        fn f<F: Field>(public a: F, public b: F) -> F {
            {| x: a, y: b |}.x
        }
    "#;
    let gs = parse_and_build(src);

    // { x: a, y: b }.x → reduces to just `a` (direct field extraction)
    // So the graph should be the same as pin_func_var
    let mut expected = UDag::<B>::new();
    let a = Vid::new("a");
    let inp = expected.add_node(Node::inp(
        Vid::new("f"),
        vec![pub_scalar_pref("a"), pub_scalar_pref("b")],
    ));
    let var_a = GOp::<B>::var(&a, inp, ATyp::scalar());
    let ret = expected.add_node(Node::ret(&var_a));
    expected.add_edges(DepType::Data, ret, var_a);

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
        fn double<F: Field>(public x: F) -> F { x + x }
        fn f<F: Field>(public a: F) -> F { double(a) }
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
    let inp = expected_f.add_node(Node::inp(Vid::new("f"), vec![pub_scalar_pref("a")]));
    let var_a = GOp::<B>::var(&a, inp, s.clone());
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
        proto foo<F: Field>(private s: F, public v: [F; 10]) where s == s {
            let r = random<F>;
            c <- challenge<F>;
            a <- r * c;
            b <- r + c + s;
            x <- v[1..5];
            verify(a * s == b * x[3]);
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
        fn f<F: Field>(public a: F) -> F { a ^ 2 }
    "#;
    let gs = parse_and_build(src);

    let mut expected = UDag::<B>::new();
    let a = Vid::new("a");
    let s = ATyp::scalar();

    let inp = expected.add_node(Node::inp(Vid::new("f"), vec![pub_scalar_pref("a")]));
    let var_a = GOp::<B>::var(&a, inp, s.clone());
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
        fn f<F: Field>(public a: [F; 2], public b: [F; 2]) -> F { dot(a, b) }
    "#;
    let gs = parse_and_build(src);

    let mut expected = UDag::<B>::new();
    let a = Vid::new("a");
    let b = Vid::new("b");
    let vs2 = ATyp::vec_scalar(2);
    let s = ATyp::scalar();

    let pref_a = PRef::from_var(Vid::new("a"), NodeIndex::new(0), vs2.clone(), 0, Qualifier::Public, Distribution::Nonuniform);
    let pref_b = PRef::from_var(Vid::new("b"), NodeIndex::new(0), vs2.clone(), 0, Qualifier::Public, Distribution::Nonuniform);

    let inp = expected.add_node(Node::inp(Vid::new("f"), vec![pref_a, pref_b]));
    let var_a = GOp::<B>::var(&a, inp, vs2.clone());
    let var_b = GOp::<B>::var(&b, inp, vs2.clone());

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
        fn f<F: Field>(public a: [F; 2], public b: [F; 2]) -> [F; 4] { a ++ b }
    "#;
    let gs = parse_and_build(src);

    let mut expected = UDag::<B>::new();
    let a = Vid::new("a");
    let b = Vid::new("b");
    let vs2 = ATyp::vec_scalar(2);
    let vs4 = ATyp::vec_scalar(4);

    let pref_a = PRef::from_var(Vid::new("a"), NodeIndex::new(0), vs2.clone(), 0, Qualifier::Public, Distribution::Nonuniform);
    let pref_b = PRef::from_var(Vid::new("b"), NodeIndex::new(0), vs2.clone(), 0, Qualifier::Public, Distribution::Nonuniform);

    let inp = expected.add_node(Node::inp(Vid::new("f"), vec![pref_a, pref_b]));
    let var_a = GOp::<B>::var(&a, inp, vs2.clone());
    let var_b = GOp::<B>::var(&b, inp, vs2.clone());

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
        fn f<F: Field>(public a: Uni<F, 3>, public b: Uni<F, 2>) -> Uni<F, 1> { a % b }
    "#;
    let gs = parse_and_build(src);

    let mut expected = UDag::<B>::new();
    let a = Vid::new("a");
    let b = Vid::new("b");
    let at_a = ATyp::vpoly(1, 3);
    let at_b = ATyp::vpoly(1, 2);
    let at_res = ATyp::vpoly(1, 1);

    let pref_a = PRef::from_var(Vid::new("a"), NodeIndex::new(0), at_a.clone(), 0, Qualifier::Public, Distribution::Nonuniform);
    let pref_b = PRef::from_var(Vid::new("b"), NodeIndex::new(0), at_b.clone(), 0, Qualifier::Public, Distribution::Nonuniform);

    let inp = expected.add_node(Node::inp(Vid::new("f"), vec![pref_a, pref_b]));
    let var_a = GOp::<B>::var(&a, inp, at_a);
    let var_b = GOp::<B>::var(&b, inp, at_b);

    let rem_node = expected.add_node(Node::bin(BinOp::Rem, &var_a, &var_b, &at_res));
    expected.add_edges(DepType::Data, rem_node, var_a);
    expected.add_edges(DepType::Data, rem_node, var_b);

    assert!(gs[0] == expected);
}

/// Logical AND: `(a == b) && (a == b)` creates 2×Bin(Equ) + 1×Bin(And).
/// Tests: CExp::Bin(And) → GOp::and fallthrough for Ref operands.
#[test]
fn pin_bin_and() {
    let src = r#"
        fn f<F: Field>(public a: F, public b: F) -> Bool {
            (a == b) && (a == b)
        }
    "#;
    let gs = parse_and_build(src);

    let mut expected = UDag::<B>::new();
    let a = Vid::new("a");
    let b = Vid::new("b");
    let s = ATyp::scalar();
    let bl = ATyp::bool();

    let inp = expected.add_node(Node::inp(Vid::new("f"), vec![pub_scalar_pref("a"), pub_scalar_pref("b")]));
    let var_a = GOp::<B>::var(&a, inp, s.clone());
    let var_b = GOp::<B>::var(&b, inp, s.clone());

    // First: a == b → Bin(Equ)
    let equ1 = expected.add_node(Node::bin(BinOp::Equ, &var_a, &var_b, &bl));
    expected.add_edges(DepType::Data, equ1, var_a.clone());
    expected.add_edges(DepType::Data, equ1, var_b.clone());

    // Second: a == b → another Bin(Equ)
    let equ2 = expected.add_node(Node::bin(BinOp::Equ, &var_a, &var_b, &bl));
    expected.add_edges(DepType::Data, equ2, var_a);
    expected.add_edges(DepType::Data, equ2, var_b);

    // (equ1) && (equ2) → Bin(And)
    let ref_equ1 = GOp::<B>::underscore(equ1, bl.clone());
    let ref_equ2 = GOp::<B>::underscore(equ2, bl.clone());
    let and_node = expected.add_node(Node::bin(BinOp::And, &ref_equ1, &ref_equ2, &bl));
    expected.add_edges(DepType::Data, and_node, ref_equ1);
    expected.add_edges(DepType::Data, and_node, ref_equ2);

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
        fn f<F: Field>(public a: [F; 2]) -> [F; 2] { [x + x for x in a] }
    "#;
    let gs = parse_and_build(src);

    let mut expected = UDag::<B>::new();
    let a = Vid::new("a");
    let vs2 = ATyp::vec_scalar(2);
    let s = ATyp::scalar();

    let pref_a = PRef::from_var(Vid::new("a"), NodeIndex::new(0), vs2.clone(), 0, Qualifier::Public, Distribution::Nonuniform);
    let inp = expected.add_node(Node::inp(Vid::new("f"), vec![pref_a]));
    let var_a = GOp::<B>::var(&a, inp, vs2);

    // Iteration 0: x = Ram(var_a, Index(0)); x + x → Bin(Add)
    let ram0 = GOp::<B>::ram(var_a.clone(), GOp::<B>::index(0));
    let bin0 = expected.add_node(Node::bin(BinOp::Add, &ram0, &ram0, &s));
    expected.add_edges(DepType::Data, bin0, ram0.clone());
    expected.add_edges(DepType::Data, bin0, ram0);

    // Iteration 1: x = Ram(var_a, Index(1)); x + x → Bin(Add)
    let ram1 = GOp::<B>::ram(var_a.clone(), GOp::<B>::index(1));
    let bin1 = expected.add_node(Node::bin(BinOp::Add, &ram1, &ram1, &s));
    expected.add_edges(DepType::Data, bin1, ram1.clone());
    expected.add_edges(DepType::Data, bin1, ram1);

    // Result: Vec([ref_bin0, ref_bin1]) — not Ref::Node → ret node
    let ref_bin0 = GOp::<B>::underscore(bin0, s.clone());
    let ref_bin1 = GOp::<B>::underscore(bin1, s.clone());
    let vec_op = GOp::<B>::vec(vec![ref_bin0, ref_bin1]);
    let ret = expected.add_node(Node::ret(&vec_op));
    expected.add_edges(DepType::Data, ret, vec_op);

    assert!(gs[0] == expected);
}

/// Ram expression: `a[0]` produces nested Ram op, no graph node.
/// Tests: CExp::Ram → GOp::ram producing compound op in ret node.
#[test]
fn pin_ram_expr() {
    let src = r#"
        fn f<F: Field>(public a: [F; 4]) -> F { a[0] }
    "#;
    let gs = parse_and_build(src);

    let mut expected = UDag::<B>::new();
    let a = Vid::new("a");
    let vs4 = ATyp::vec_scalar(4);

    let pref_a = PRef::from_var(Vid::new("a"), NodeIndex::new(0), vs4.clone(), 0, Qualifier::Public, Distribution::Nonuniform);
    let inp = expected.add_node(Node::inp(Vid::new("f"), vec![pref_a]));
    let var_a = GOp::<B>::var(&a, inp, vs4);

    // a[0] → Ram(var_a, Value(Index(0))) — no graph node created
    let ram_op = GOp::<B>::ram(var_a, GOp::<B>::index(0));
    // Not Ref::Node → ret node created
    let ret = expected.add_node(Node::ret(&ram_op));
    expected.add_edges(DepType::Data, ret, ram_op);

    assert!(gs[0] == expected);
}

/// Eval expression: `eval(p, x)` produces nested Eval op, no graph node.
/// Tests: CExp::Eval → GOp::eval wrapping two Refs in ret node.
#[test]
fn pin_eval() {
    let src = r#"
        fn f<F: Field>(public p: Uni<F, 4>, public x: [F; 2]) -> [F; 2] { eval(p, x) }
    "#;
    let gs = parse_and_build(src);

    let mut expected = UDag::<B>::new();
    let p = Vid::new("p");
    let x = Vid::new("x");
    let at_p = ATyp::vpoly(1, 4);
    let at_x = ATyp::vec_scalar(2);

    let pref_p = PRef::from_var(Vid::new("p"), NodeIndex::new(0), at_p.clone(), 0, Qualifier::Public, Distribution::Nonuniform);
    let pref_x = PRef::from_var(Vid::new("x"), NodeIndex::new(0), at_x.clone(), 0, Qualifier::Public, Distribution::Nonuniform);

    let inp = expected.add_node(Node::inp(Vid::new("f"), vec![pref_p, pref_x]));
    let var_p = GOp::<B>::var(&p, inp, at_p);
    let var_x = GOp::<B>::var(&x, inp, at_x);

    // eval(p, x) → Eval(var_p, var_x) — no graph node
    let eval_op = GOp::<B>::eval(var_p, var_x);
    // Not Ref::Node → ret node created
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
        fn f<G1: Group, G2: Group, GT: Pairing<G1, G2>>(public a: G1, public b: G2) -> GT {
            pair(a, b)
        }
    "#;
    let gs = parse_and_build(src);

    let mut expected = UDag::<B>::new();
    let a = Vid::new("a");
    let b = Vid::new("b");

    let pref_a = PRef::from_var(Vid::new("a"), NodeIndex::new(0), ATyp::g1(), 0, Qualifier::Public, Distribution::Nonuniform);
    let pref_b = PRef::from_var(Vid::new("b"), NodeIndex::new(0), ATyp::g2(), 0, Qualifier::Public, Distribution::Nonuniform);

    let inp = expected.add_node(Node::inp(Vid::new("f"), vec![pref_a, pref_b]));
    let var_a = GOp::<B>::var(&a, inp, ATyp::g1());
    let var_b = GOp::<B>::var(&b, inp, ATyp::g2());

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
/// Tests: CExp::Proj + CExp::Var → GOp::Ref(Ref::Var) with field type.
#[test]
fn pin_proj_var() {
    let src = r#"
        fn f<F: Field>(public r: { x: F, y: F }) -> F { r.x }
    "#;
    let gs = parse_and_build(src);

    let mut expected = UDag::<B>::new();
    let s = ATyp::scalar();

    let mut record_fields = Ctx::<String, ATyp>::new();
    record_fields.insert(&"x".to_string(), &s);
    record_fields.insert(&"y".to_string(), &s);
    let record_typ = ATyp::Record(record_fields);

    let pref_r = PRef::from_var(Vid::new("r"), NodeIndex::new(0), record_typ, 0, Qualifier::Public, Distribution::Nonuniform);

    let inp = expected.add_node(Node::inp(Vid::new("f"), vec![pref_r]));

    // r.x → Ref(Var(r, inp), scalar) — not Ref::Node → ret node
    let proj_result = GOp::<B>::var(&Vid::new("r"), inp, s);
    let ret = expected.add_node(Node::ret(&proj_result));
    expected.add_edges(DepType::Data, ret, proj_result);

    assert!(gs[0] == expected);
}

/// SetRecord: `r.set(x, v)` desugars to Record({ x: v, y: r.y }).
/// Tests: CExp::SetRecord → desugaring into CExp::Record with Proj for unchanged fields.
#[test]
fn pin_set_record() {
    let src = r#"
        fn f<F: Field>(public r: { x: F, y: F }, public v: F) -> { x: F, y: F } {
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

    let pref_r = PRef::from_var(Vid::new("r"), NodeIndex::new(0), record_typ, 0, Qualifier::Public, Distribution::Nonuniform);
    let pref_v = pub_scalar_pref("v");

    let inp = expected.add_node(Node::inp(Vid::new("f"), vec![pref_r, pref_v]));

    // SetRecord desugars to: Record({ x: v, y: r.y })
    // x field: CExp::Var(v) → Ref(Var(v, inp), scalar)
    // y field: CExp::Proj(CExp::Var(r), "y") → Ref(Var(r, inp), scalar)
    let var_v = GOp::<B>::Ref(Ref::Var(Vid::new("v"), inp), s.clone());
    let var_r = GOp::<B>::Ref(Ref::Var(Vid::new("r"), inp), s.clone());

    let mut rec_fields = Ctx::<String, HOp<B>>::new();
    rec_fields.insert(&"x".to_string(), &mk::<B>(var_v));
    rec_fields.insert(&"y".to_string(), &mk::<B>(var_r));
    let record_op = GOp::<B>::Record(rec_fields);

    // Not Ref::Node → ret node
    let ret = expected.add_node(Node::ret(&record_op));
    expected.add_edges(DepType::Data, ret, record_op);

    assert!(gs[0] == expected);
}

// ============================================================================
// Group 16: Log with Var reference (tests Ref::Var branch of Log match)
// ============================================================================

/// Log with a let-bound variable exercises the Ref::Var path in Log's match.
/// Tests: CExp::Log match arm `Ref::Var(_, n)` (vs `Ref::Node(n)` in pin_log_node_ref).
#[test]
fn pin_log_var_ref() {
    let src = r#"
        proto foo<F: Field>(private s: F) where s == s {
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
    let inp = expected.add_node(Node::inp(Vid::new("foo"), vec![priv_scalar_pref("s")]));
    let var_s = GOp::<B>::var(&s_vid, inp, ATyp::scalar());

    // let x = s + s → Bin(Add) node
    let bin_add = expected.add_node(Node::bin(BinOp::Add, &var_s, &var_s, &ATyp::scalar()));
    expected.add_edges(DepType::Data, bin_add, var_s.clone());
    expected.add_edges(DepType::Data, bin_add, var_s.clone());
    let transcr_op = GOp::<B>::Ref(Ref::Var(Vid::new("x"), bin_add), ATyp::scalar());
    let transcr = expected.add_node(Node::transcr(&transcr_op));
    expected[transcr].set_transcript();
    expected.add_edges(DepType::Data, transcr, transcr_op.clone());
    expected.add_edge(inp, transcr, Dep::transcript());
    expected.vctx.insert(&transcr, &a_vid);
    expected.transcript_vars.insert(&transcr, &true);
    // because Log's first arm uses `ol.clone()` which is op_from_var(x) = Ref(Var(x, bin_add), scalar)
    let var_a = GOp::<B>::var(&a_vid, transcr, ATyp::scalar());
    let equ = expected.add_node(Node::bin(BinOp::Equ, &var_a, &var_s, &ATyp::bool()));
    expected.add_edges(DepType::Data, equ, var_a);
    expected.add_edges(DepType::Data, equ, var_s);

    // verify(...)
    let equ_ref = GOp::<B>::underscore(equ, ATyp::bool());
    let check = expected.add_node(Node::check(&equ_ref));
    expected.add_edges(DepType::Data, check, equ_ref);

    // Relation: Rel + Bin(Equ, s, s)
    let rel = expected.add_node(Node::rel(Vid::new("foo"), vec![priv_scalar_pref("s")]));
    let var_s_rel = GOp::<B>::var(&s_vid, rel, ATyp::scalar());
    let equ_rel = expected.add_node(Node::bin(BinOp::Equ, &var_s_rel, &var_s_rel, &ATyp::bool()));
    expected.add_edges(DepType::Data, equ_rel, var_s_rel.clone());
    expected.add_edges(DepType::Data, equ_rel, var_s_rel);

    assert!(gs[0] == expected);
}

// ========================================================================
// Group 12: Additional coverage tests
// ========================================================================

/// Let(None, ...) from multi-statement body (semicolon separator).
/// `a + a; b + b` desugars to `Let(None, Bin(Add,a,a), Bin(Add,b,b))`.
/// Both Bin(Add) nodes are created, but only the second is the function result.
/// Tests: CExp::Let(None, ...) path (L1350-1352).
#[test]
fn pin_let_seq() {
    let src = r#"
        fn f<F: Field>(public a: F, public b: F) -> F { a + a; b + b }
    "#;
    let gs = parse_and_build(src);

    let mut expected = UDag::<B>::new();
    let s = ATyp::scalar();

    let inp = expected.add_node(Node::inp(Vid::new("f"), vec![
        pub_scalar_pref("a"),
        pub_scalar_pref("b"),
    ]));

    let var_a = GOp::<B>::var(&Vid::new("a"), inp, s.clone());
    let var_b = GOp::<B>::var(&Vid::new("b"), inp, s.clone());

    // First statement: a + a → Bin(Add) node (result discarded by Let(None))
    let add_a = expected.add_node(Node::bin(BinOp::Add, &var_a, &var_a, &s));
    expected.add_edges(DepType::Data, add_a, var_a.clone());
    expected.add_edges(DepType::Data, add_a, var_a);

    // Second statement: b + b → Bin(Add) node (the function result)
    let add_b = expected.add_node(Node::bin(BinOp::Add, &var_b, &var_b, &s));
    expected.add_edges(DepType::Data, add_b, var_b.clone());
    expected.add_edges(DepType::Data, add_b, var_b);

    // Result is Ref(Node(add_b), scalar) → no ret node
    assert!(gs[0] == expected);
}

/// Proj(Var) where the var binds to a GOp::Record (direct field extraction).
/// `let r = {| x: a, y: b |}; r.x` → Record is stored in vars, r.x extracts field directly.
/// Tests: L1472-1478 — GOp::Record(record_fields) branch in Proj.
#[test]
fn pin_proj_var_record() {
    let src = r#"
        fn f<F: Field>(public a: F, public b: F) -> F {
            let r = {| x: a, y: b |};
            r.x
        }
    "#;
    let gs = parse_and_build(src);

    let mut expected = UDag::<B>::new();
    let s = ATyp::scalar();

    let inp = expected.add_node(Node::inp(Vid::new("f"), vec![
        pub_scalar_pref("a"),
        pub_scalar_pref("b"),
    ]));

    // r.x extracts field x from the Record, which is Ref(Var(a, inp), scalar)
    // Since that's Ref::Var (not Ref::Node), add_top_exp creates a ret node
    let var_a = GOp::<B>::var(&Vid::new("a"), inp, s);
    let ret = expected.add_node(Node::ret(&var_a));
    expected.add_edges(DepType::Data, ret, var_a);

    assert!(gs[0] == expected);
}

/// Univariate polynomial application: `p(x)` where `p: Uni<F, 2>`.
/// Desugars to `dot(p, [x^0, x^1])` where x^0→Value(Scalar(one)), x^1→var_x.
/// Tests: CExp::App univariate path (L1250-1266).
#[test]
fn pin_app_univariate_poly() {
    use ark_ff::One;
    use backend::Value;
    type F = <B as backend::ArkConfig>::F;

    let src = r#"
        fn f<F: Field>(public p: Uni<F, 2>, public x: F) -> F { p(x) }
    "#;
    let gs = parse_and_build(src);

    let mut expected = UDag::<B>::new();
    let s = ATyp::scalar();

    let inp = expected.add_node(Node::inp(Vid::new("f"), vec![
        PRef::from_var(Vid::new("p"), NodeIndex::new(0), ATyp::vpoly(1, 2), 0, Qualifier::Public, Distribution::Nonuniform),
        PRef::from_var(Vid::new("x"), NodeIndex::new(0), s.clone(), 0, Qualifier::Public, Distribution::Nonuniform),
    ]));

    let var_p = GOp::<B>::var(&Vid::new("p"), inp, ATyp::vpoly(1, 2));
    let var_x = GOp::<B>::var(&Vid::new("x"), inp, s.clone());

    // x^0 simplifies to Value(Scalar(one)), x^1 simplifies to var_x
    let one_scalar = GOp::<B>::Value(Value::Scalar(F::one()));
    let x_powers = GOp::<B>::vec(vec![one_scalar, var_x.clone()]);

    // dot(p, [1, x]) → Bin(Dot) node
    let dot = expected.add_node(Node::bin(BinOp::Dot, &var_p, &x_powers, &s));
    // Edge from inp for var_p
    expected.add_edges(DepType::Data, dot, var_p);
    // Edge from inp for var_x (inside the Vec)
    expected.add_edges(DepType::Data, dot, x_powers);

    // Result is Ref(Node(dot), scalar) → no ret node
    assert!(gs[0] == expected);
}

/// Fun expression (polynomial literal): `fun x => x`.
/// Creates Value::Poly(VirtualPolynomial) representing the identity polynomial [0, 1].
/// Tests: CExp::Fun path (L1407-1419).
#[test]
fn pin_fun_lit() {
    use ark_ff::{Zero, One};
    use ark_poly::DenseUVPolynomial;
    use ark_poly::univariate::DensePolynomial;
    use backend::{Value, PolyVariant, VirtualPolynomial};
    type F = <B as backend::ArkConfig>::F;

    let src = r#"
        fn f<F: Field>() -> Uni<F, 1> { fun x => x }
    "#;
    let gs = parse_and_build(src);

    let mut expected = UDag::<B>::new();

    let inp = expected.add_node(Node::inp(Vid::new("f"), vec![]));

    // fun x => x → DensePolynomial [0, 1] representing the identity
    let poly = DensePolynomial::from_coefficients_vec(vec![F::zero(), F::one()]);
    let pv = PolyVariant::DenseUni(poly);
    let vp = VirtualPolynomial::from_poly(pv);
    let val = GOp::<B>::Value(Value::Poly(vp));

    // Value is not Ref::Node → add_top_exp creates ret node
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
        proto foo<F: Field>(private s: F, public v: F) where s == s {
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
    assert!(prover.find_check().is_none());
}

/// get_verifier extracts the verifier subgraph.
/// Tests: get_verifier() produces subgraph with public inputs, transcript vars, challenges, check node.
#[test]
fn pin_get_verifier_basic() {
    let src = r#"
        proto foo<F: Field>(private s: F, public v: F) where s == s {
            a <- s + v;
            verify(a == v)
        }
    "#;
    let gs = parse_and_build(src);
    let dag = &gs[0];

    let verifier = dag.get_verifier().unwrap();

    // Verifier must have a check node
    assert!(verifier.find_check().is_some());
    // Verifier name matches
    assert_eq!(verifier.name(), Vid::new("foo"));
    // Verifier should not have private-only computations
    // Verifier args should only include public inputs (v) and transcript vars (a)
    let args = verifier.args();
    assert!(args.iter().all(|a| a.is_public()));
}

/// get_relation extracts the relation subgraph from the Rel node.
/// Tests: get_relation() returns the relation subgraph for a protocol with `where` clause.
#[test]
fn pin_get_relation_basic() {
    let src = r#"
        proto foo<F: Field>(private s: F, public v: F) where s == v {
            verify(s == v)
        }
    "#;
    let gs = parse_and_build(src);
    let dag = &gs[0];

    let relation = dag.get_relation().unwrap();

    // Relation should have the Rel node
    assert!(relation.relation_node().is_some());
    // Relation should have the Equ operation from `s == v`
    assert!(relation.op_nodes().len() > 0);
}

/// Regression: get_relation had a duplicate outgoing-edge loop that doubled
/// the number of nodes explored. Verify edge count is reasonable.
#[test]
fn pin_get_relation_no_duplicate_edges() {
    let src = r#"
        proto foo<F: Field>(private s: F, public v: F) where s == v {
            verify(s == v)
        }
    "#;
    let gs = parse_and_build(src);
    let dag = &gs[0];

    let relation = dag.get_relation().unwrap();
    // A simple `s == v` relation should have ≤ 4 edges (Rel→Equ, Equ←s, Equ←v)
    assert!(relation.edge_count() <= 4,
        "get_relation has {} edges, expected ≤ 4 (duplicate loop bug?)", relation.edge_count());
}

/// get_verifier returns error when verifier body references a private input directly.
/// Tests: GraphError::PrivateNodeInVerifier.
#[test]
fn pin_get_verifier_private_leak() {
    let src = r#"
        proto foo<F: Field>(private s: F) where s == s {
            verify(s == s)
        }
    "#;
    let gs = parse_and_build(src);
    let dag = &gs[0];

    // The verifier assertion `s == s` directly uses private `s`.
    let result = dag.get_verifier();
    match result {
        Err(GraphError::PrivateNodeInVerifier(_, _)) => {},
        Err(e) => panic!("Expected PrivateNodeInVerifier, got: {}", e),
        Ok(_) => panic!("Expected error but got Ok"),
    }
}

/// get_relation returns error for a function (no `where` clause).
/// Tests: GraphError::RelationNotFound.
#[test]
fn pin_get_relation_no_relation() {
    let src = r#"
        fn f<F: Field>(public a: F) -> F { a }
    "#;
    let gs = parse_and_build(src);
    let dag = &gs[0];

    let result = dag.get_relation();
    match result {
        Err(GraphError::RelationNotFound(_)) => {},
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
        fn f<F: Field>(public a: F, public b: F) -> F { a + b }
    "#;
    let gs = parse_and_build(src);
    let dag = &gs[0];

    // Inp node + Bin(Add) node = 2 nodes
    assert_eq!(dag.node_count(), 2);
    // Two data edges: a→bin, b→bin
    assert_eq!(dag.edge_count(), 2);
}

/// op_nodes returns only operation nodes, excluding Inp and Rel.
#[test]
fn pin_op_nodes_filter() {
    let src = r#"
        proto foo<F: Field>(private s: F) where s == s {
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
    // Should have at least the Equ and Check nodes in the body, plus Equ in relation
    assert!(op_nodes.len() >= 2);
}

/// find_var returns the Vid for a node, find_ref returns Ref::Var or Ref::Node.
#[test]
fn pin_find_var_find_ref() {
    let src = r#"
        proto foo<F: Field>(private a: F, private b: F) where a == b {
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
    let has_c = op_nodes.iter().any(|n| dag.find_var(*n) == Some(Vid::new("c")));
    assert!(has_c, "Expected to find variable 'c' on an op node");
}

/// transcript_nodes returns nodes in topological order.
#[test]
fn pin_transcript_nodes_order() {
    let src = r#"
        proto foo<F: Field>(private s: F) where s == s {
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
            assert!(parent_pos.is_some() && parent_pos.unwrap() < i,
                "Transcript node {:?} parent {:?} should appear earlier", tnodes[i], parent);
        }
    }
}

/// get_proof_nodes and get_challenge_nodes partition transcript nodes correctly.
#[test]
fn pin_proof_vs_challenge_nodes() {
    let src = r#"
        proto foo<F: Field>(private s: F) where s == s {
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

/// trc computes transitive-reflexive closure correctly.
#[test]
fn pin_trc_reachability() {
    let src = r#"
        fn f<F: Field>(public a: F, public b: F) -> F {
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
    assert_eq!(forward.len(), dag.node_count(), "Forward closure from inp should reach all nodes");

    // trc from the last op (incoming) should also reach all nodes
    let max = dag.max_node();
    let backward = dag.trc(max, Direction::Incoming);
    assert_eq!(backward.len(), dag.node_count(), "Backward closure from max should reach all nodes");
}

/// find_check finds a Check node in a protocol and returns None for a function.
#[test]
fn pin_find_check() {
    let proto_src = r#"
        proto foo<F: Field>(private s: F) where s == s {
            verify(s == s)
        }
    "#;
    let proto_gs = parse_and_build(proto_src);
    assert!(proto_gs[0].find_check().is_some(), "Protocol should have a check node");

    let fn_src = r#"
        fn f<F: Field>(public a: F) -> F { a + a }
    "#;
    let fn_gs = parse_and_build(fn_src);
    assert!(fn_gs[0].find_check().is_none(), "Function should not have a check node");
}

// ============================================================================
// Group D: Graph Transformation Tests
// ============================================================================

/// erase_ann strips annotations from a DAG.
#[test]
fn pin_erase_ann() {
    let src = r#"
        fn f<F: Field>(public a: F, public b: F) -> F { a + b }
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
        fn f<F: Field>(public a: F) -> F { a + a }
        fn g<F: Field>(public b: F) -> F { b + b }
    "#;
    let gs = parse_and_build(src);
    let dag_f = &gs[0];
    let dag_g = &gs[1];

    let combined = dag_f.combine_dag(dag_g);

    // Combined should have sum of nodes and edges
    assert_eq!(combined.node_count(), dag_f.node_count() + dag_g.node_count());
    assert_eq!(combined.edge_count(), dag_f.edge_count() + dag_g.edge_count());
}

/// map_annotations transforms annotations on a DAG.
#[test]
fn pin_map_annotations_dag() {
    let src = r#"
        fn f<F: Field>(public a: F, public b: F) -> F { a + b }
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
        fn double<F: Field>(public x: F) -> F { x + x }
        proto foo<F: Field>(private s: F) where s == s {
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
    assert!(protos[0].find_check().is_some());
    // Function should not
    assert!(funcs[0].find_check().is_none());
}

/// get_proto finds a protocol by name.
#[test]
fn pin_dags_get_proto() {
    let src = r#"
        fn helper<F: Field>(public x: F) -> F { x }
        proto bar<F: Field>(private s: F) where s == s {
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
        fn f<F: Field>(public a: F) -> Uni<F, 2> { fun x => x ^ 2 }
    "#;
    let result = try_parse_and_build(src);
    match result {
        Err(GraphError::NonPolynomialFun(_)) => {},
        Err(e) => panic!("Expected NonPolynomialFun, got: {}", e),
        Ok(_) => panic!("Expected error but got Ok"),
    }
}

/// Unbound variable in Fun body triggers an error.
#[test]
fn pin_error_fun_unbound_var() {
    let src = r#"
        fn f<F: Field>(public a: F) -> Uni<F, 1> { fun x => y }
    "#;
    // This may fail at parse/typecheck (unwrap in try_parse_and_build) or at graph building
    let result = std::panic::catch_unwind(|| try_parse_and_build(src));
    // Either it panics or returns Err — either way it should not succeed
    match result {
        Ok(Ok(_)) => panic!("Unbound variable in Fun should fail"),
        _ => {}, // Error or panic — both acceptable
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
        fn f<F: Field>(public x: F, public y: F) -> F {
            let a = x + y;
            let b = a + x;
            let c = b + y;
            c
        }
    "#;
    let gs = parse_and_build(src);

    let mut expected = UDag::<B>::new();
    let s = ATyp::scalar();
    let inp = expected.add_node(Node::inp(
        Vid::new("f"),
        vec![pub_scalar_pref("x"), pub_scalar_pref("y")],
    ));
    let var_x = GOp::<B>::var(&Vid::new("x"), inp, s.clone());
    let var_y = GOp::<B>::var(&Vid::new("y"), inp, s.clone());

    // a = x + y
    let add_a = expected.add_node(Node::bin(BinOp::Add, &var_x, &var_y, &s));
    expected.add_edges(DepType::Data, add_a, var_x.clone());
    expected.add_edges(DepType::Data, add_a, var_y.clone());

    // b = a + x
    let ref_a = GOp::<B>::var(&Vid::new("a"), add_a, s.clone());
    let add_b = expected.add_node(Node::bin(BinOp::Add, &ref_a, &var_x, &s));
    expected.add_edges(DepType::Data, add_b, ref_a);
    expected.add_edges(DepType::Data, add_b, var_x);

    // c = b + y
    let ref_b = GOp::<B>::var(&Vid::new("b"), add_b, s.clone());
    let add_c = expected.add_node(Node::bin(BinOp::Add, &ref_b, &var_y, &s));
    expected.add_edges(DepType::Data, add_c, ref_b);
    expected.add_edges(DepType::Data, add_c, var_y);

    // `c` resolves to Ref::Var("c", add_c) → triggers ret node
    let ref_c = GOp::<B>::var(&Vid::new("c"), add_c, s.clone());
    let ret = expected.add_node(Node::ret(&ref_c));
    expected.add_edges(DepType::Data, ret, ref_c);

    assert!(gs[0] == expected);
}

/// Protocol with 3 transcript interactions verifies edge chain ordering.
/// Tests: multiple transcript edges in sequence.
#[test]
fn pin_multi_transcript() {
    let src = r#"
        proto foo<F: Field>(private s: F) where s == s {
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
    assert!(dag.transcript_edge(tnodes[1], Direction::Incoming).is_some(),
        "Second transcript should have incoming edge");
    assert!(dag.transcript_edge(tnodes[2], Direction::Incoming).is_some(),
        "Third transcript should have incoming edge");
}

/// Multilinear Fun: `fun x, y => x + y` creates DenseMle.
/// Tests: CExp::Fun with multiple variables (multilinear path).
#[test]
fn pin_fun_multilinear() {
    use ark_ff::{Zero, One};
    use ark_poly::evaluations::multivariate::multilinear::DenseMultilinearExtension;
    use backend::{Value, PolyVariant, VirtualPolynomial};
    type F = <B as backend::ArkConfig>::F;

    let src = r#"
        fn f<F: Field>() -> Mle<F, 2> { fun x, y => x + y }
    "#;
    let gs = parse_and_build(src);

    let mut expected = UDag::<B>::new();
    let _inp = expected.add_node(Node::inp(Vid::new("f"), vec![]));

    // fun x, y => x + y
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
        fn f<F: Field>(public a: [F; 2]) -> [F; 2] { [x * x + x for x in a] }
    "#;
    let gs = parse_and_build(src);

    let mut expected = UDag::<B>::new();
    let a = Vid::new("a");
    let vs2 = ATyp::vec_scalar(2);
    let s = ATyp::scalar();
    let pref_a = PRef::from_var(a.clone(), NodeIndex::new(0), vs2.clone(), 0, Qualifier::Public, Distribution::Nonuniform);
    let inp = expected.add_node(Node::inp(Vid::new("f"), vec![pref_a]));
    let var_a = GOp::<B>::var(&a, inp, vs2);

    // Iteration 0: x = Ram(a, 0); x*x → mul0; mul0 + x → add0
    let ram0 = GOp::<B>::ram(var_a.clone(), GOp::<B>::index(0));
    let mul0 = expected.add_node(Node::bin(BinOp::Mul, &ram0, &ram0, &s));
    expected.add_edges(DepType::Data, mul0, ram0.clone());
    expected.add_edges(DepType::Data, mul0, ram0.clone());
    let ref_mul0 = GOp::<B>::underscore(mul0, s.clone());
    let add0 = expected.add_node(Node::bin(BinOp::Add, &ref_mul0, &ram0, &s));
    expected.add_edges(DepType::Data, add0, ref_mul0);
    expected.add_edges(DepType::Data, add0, ram0);

    // Iteration 1: x = Ram(a, 1); x*x → mul1; mul1 + x → add1
    let ram1 = GOp::<B>::ram(var_a.clone(), GOp::<B>::index(1));
    let mul1 = expected.add_node(Node::bin(BinOp::Mul, &ram1, &ram1, &s));
    expected.add_edges(DepType::Data, mul1, ram1.clone());
    expected.add_edges(DepType::Data, mul1, ram1.clone());
    let ref_mul1 = GOp::<B>::underscore(mul1, s.clone());
    let add1 = expected.add_node(Node::bin(BinOp::Add, &ref_mul1, &ram1, &s));
    expected.add_edges(DepType::Data, add1, ref_mul1);
    expected.add_edges(DepType::Data, add1, ram1);

    // Result: Vec([ref_add0, ref_add1]) → ret node
    let ref_add0 = GOp::<B>::underscore(add0, s.clone());
    let ref_add1 = GOp::<B>::underscore(add1, s.clone());
    let vec_op = GOp::<B>::vec(vec![ref_add0, ref_add1]);
    let ret = expected.add_node(Node::ret(&vec_op));
    expected.add_edges(DepType::Data, ret, vec_op);

    assert!(gs[0] == expected);
}

/// Diamond DAG: `let c = a + b; c * c` — same node feeds both operands.
/// Tests: Ref sharing across operands of a binary op.
#[test]
fn pin_diamond_dag() {
    let src = r#"
        fn f<F: Field>(public a: F, public b: F) -> F {
            let c = a + b;
            c * c
        }
    "#;
    let gs = parse_and_build(src);

    let mut expected = UDag::<B>::new();
    let s = ATyp::scalar();
    let inp = expected.add_node(Node::inp(
        Vid::new("f"),
        vec![pub_scalar_pref("a"), pub_scalar_pref("b")],
    ));
    let var_a = GOp::<B>::var(&Vid::new("a"), inp, s.clone());
    let var_b = GOp::<B>::var(&Vid::new("b"), inp, s.clone());

    // c = a + b
    let add = expected.add_node(Node::bin(BinOp::Add, &var_a, &var_b, &s));
    expected.add_edges(DepType::Data, add, var_a);
    expected.add_edges(DepType::Data, add, var_b);

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
        fn add1<F: Field>(public x: F) -> F { x + 1 }
        fn double<F: Field>(public x: F) -> F { x + x }
        fn composed<F: Field>(public a: F) -> F { double(add1(a)) }
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
        fn f<F: Field>(public p: Mle<F, 2>, public x: F) -> Mle<F, 1> { p(x) }
    "#;
    let gs = parse_and_build(src);

    let dag = &gs[0];
    // MLE application desugars to: mle_l + (mle_r - mle_l) * x
    // where mle_l = p[0..1], mle_r = p[1..2]
    // This should produce several nodes for the arithmetic
    assert!(dag.node_count() > 2, "MLE app should produce multiple nodes");
    // Verify it's a function (no check node)
    assert!(dag.find_check().is_none());
}

// ── Stress tests (verify no stack overflow with iterative builder) ──

// ── Reduce operation tests ──

/// Reduce with addition: `reduce(+, [a, b, c])` creates a single Reduce node.
#[test]
fn pin_reduce_add() {
    let src = r#"
        fn f<F: Field>(public v: [F; 3]) -> F {
            reduce(+, v)
        }
    "#;
    let gs = parse_and_build(src);
    let dag = &gs[0];

    let mut expected = UDag::<B>::new();
    let inp = expected.add_node(Node::inp(
        Vid::new("f"),
        vec![pub_pref("v", ATyp::vec_scalar(3))],
    ));
    let var_v = GOp::<B>::var(&Vid::new("v"), inp, ATyp::vec_scalar(3));

    let reduce = expected.add_node(Node::ret(
        &GOp::reduce(BinOp::Add, var_v.clone()),
    ));
    expected.add_edges(DepType::Data, reduce, var_v);

    assert!(gs[0] == expected);
}

/// Reduce with multiplication: `reduce(*, [a, b, c])`.
#[test]
fn pin_reduce_mul() {
    let src = r#"
        fn f<F: Field>(public v: [F; 4]) -> F {
            reduce(*, v)
        }
    "#;
    let gs = parse_and_build(src);
    let dag = &gs[0];

    let mut expected = UDag::<B>::new();
    let inp = expected.add_node(Node::inp(
        Vid::new("f"),
        vec![pub_pref("v", ATyp::vec_scalar(4))],
    ));
    let var_v = GOp::<B>::var(&Vid::new("v"), inp, ATyp::vec_scalar(4));

    let reduce = expected.add_node(Node::ret(
        &GOp::reduce(BinOp::Mul, var_v.clone()),
    ));
    expected.add_edges(DepType::Data, reduce, var_v);

    assert!(gs[0] == expected);
}

/// Reduce with subtraction (non-commutative): `reduce(-, [a, b, c])`.
#[test]
fn pin_reduce_sub() {
    let src = r#"
        fn f<F: Field>(public v: [F; 3]) -> F {
            reduce(-, v)
        }
    "#;
    let gs = parse_and_build(src);
    let dag = &gs[0];

    let mut expected = UDag::<B>::new();
    let inp = expected.add_node(Node::inp(
        Vid::new("f"),
        vec![pub_pref("v", ATyp::vec_scalar(3))],
    ));
    let var_v = GOp::<B>::var(&Vid::new("v"), inp, ATyp::vec_scalar(3));

    let reduce = expected.add_node(Node::ret(
        &GOp::reduce(BinOp::Sub, var_v.clone()),
    ));
    expected.add_edges(DepType::Data, reduce, var_v);

    assert!(gs[0] == expected);
}

