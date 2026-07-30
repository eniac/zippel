use backend::ArkBls12_381;
use egg::EGraph;

use crate::conv::{Counter, convert_cexp};
use crate::extraction::extract_zir;
use crate::lang::{ZAnalysis, ZIR};

#[test]
fn test_basic_conversion() {
    // Simple: let x = 5 in x + 3
    use lang::ast::{CExp, Exp};
    let exp = CExp::Let(
        Some(lang::id::Vid::from("x")),
        Box::new(Exp::Lit(5)),
        Box::new(Exp::Bin(
            lang::ast::BinOp::Add,
            Box::new(Exp::Var(lang::id::Vid::from("x"))),
            Box::new(Exp::Lit(3)),
        )),
    );

    let mut egraph: EGraph<ZIR<ArkBls12_381>, ZAnalysis<ArkBls12_381>> = EGraph::default();
    let mut counter = Counter::new();
    let root = convert_cexp(&exp, &mut egraph, &mut counter);

    // Should produce a valid e-graph
    assert!(egraph.total_size() > 0);
    let _ = egraph.find(root);

    // Extraction should produce a valid RecExpr
    let recexpr = extract_zir(&egraph, root);
    assert!(!recexpr.as_ref().is_empty());
}

#[test]
fn test_seq_wrap_let_binding() {
    // let x = 5 in x → Seq([Constant(5), Constant(5)]) after inlining
    use lang::ast::{CExp, Exp};
    let exp = CExp::Let(
        Some(lang::id::Vid::from("x")),
        Box::new(Exp::Lit(5)),
        Box::new(Exp::Var(lang::id::Vid::from("x"))),
    );

    let mut egraph: EGraph<ZIR<ArkBls12_381>, ZAnalysis<ArkBls12_381>> = EGraph::default();
    let mut counter = Counter::new();
    let root = convert_cexp(&exp, &mut egraph, &mut counter);

    // The root should be a Seq (from the Seq-wrap of let-binding)
    let class = &egraph[egraph.find(root)];
    let has_seq = class.nodes.iter().any(|n| matches!(n, ZIR::Seq(_)));
    assert!(has_seq, "let-binding should be Seq-wrapped");
}

#[test]
fn test_map_binder() {
    // [x for x in 0..10] → Map(tag, [domain, Var(tag)])
    use lang::ast::{CExp, Exp};
    use lang::typ::range::CRange;
    let exp = CExp::Map(
        Box::new(Exp::Range(CRange::new(0, 10))),
        lang::id::Vid::from("x"),
        Box::new(Exp::Var(lang::id::Vid::from("x"))),
    );

    let mut egraph: EGraph<ZIR<ArkBls12_381>, ZAnalysis<ArkBls12_381>> = EGraph::default();
    let mut counter = Counter::new();
    let root = convert_cexp(&exp, &mut egraph, &mut counter);

    // Should contain a Map node
    let class = &egraph[egraph.find(root)];
    let has_map = class.nodes.iter().any(|n| matches!(n, ZIR::Map(_, _)));
    assert!(has_map, "should contain a Map node");
}

#[test]
fn test_log_inlining() {
    // p <- interpolate(v) in body
    // Log(binder, val, body) → Seq([Log(tag, [val_id]), body_id])
    use lang::ast::{CExp, Exp};
    let exp = CExp::Log(
        lang::id::Vid::from("p"),
        Box::new(Exp::Lit(42)),
        Box::new(Exp::Var(lang::id::Vid::from("p"))),
    );

    let mut egraph: EGraph<ZIR<ArkBls12_381>, ZAnalysis<ArkBls12_381>> = EGraph::default();
    let mut counter = Counter::new();
    let root = convert_cexp(&exp, &mut egraph, &mut counter);

    // Root should be a Seq (from Log + Seq continuation)
    let class = &egraph[egraph.find(root)];
    let has_seq = class.nodes.iter().any(|n| matches!(n, ZIR::Seq(_)));
    assert!(has_seq, "Log should be Seq-continued");

    // Should contain a Log node (barrier)
    let has_log = egraph
        .classes()
        .flat_map(|c| c.nodes.iter())
        .any(|n| matches!(n, ZIR::Log(_, _)));
    assert!(has_log, "should contain a Log node");
}

#[test]
fn test_record_fields_sorted() {
    // Record with unsorted fields should be sorted after conversion
    use lang::ast::{CExp, Exp};
    use share::Ctx;
    let mut fields = Ctx::new();
    fields.insert(&"z".to_string(), &Exp::Lit(1));
    fields.insert(&"a".to_string(), &Exp::Lit(2));
    fields.insert(&"m".to_string(), &Exp::Lit(3));

    let exp = CExp::Record(fields);

    let mut egraph: EGraph<ZIR<ArkBls12_381>, ZAnalysis<ArkBls12_381>> = EGraph::default();
    let mut counter = Counter::new();
    let _root = convert_cexp(&exp, &mut egraph, &mut counter);

    // Find the Record node and check field names are sorted
    for class in egraph.classes() {
        for node in &class.nodes {
            if let ZIR::Record(names, _) = node {
                let mut sorted = names.to_vec();
                sorted.sort();
                assert_eq!(names.to_vec(), sorted, "Record field names must be sorted");
            }
        }
    }
}

#[test]
fn test_side_effect_flags() {
    // Challenge should set has_visible_side_effect = true
    // Random should set has_side_effect = true but NOT has_visible_side_effect
    use lang::ast::CExp;
    use lang::id::Tid;

    let exp = CExp::Random(Tid::from("F"), false);

    let mut egraph: EGraph<ZIR<ArkBls12_381>, ZAnalysis<ArkBls12_381>> = EGraph::default();
    let mut counter = Counter::new();
    let root = convert_cexp(&exp, &mut egraph, &mut counter);

    let class = &egraph[egraph.find(root)];
    assert!(
        class.data.has_side_effect,
        "Random should set has_side_effect"
    );
    assert!(
        !class.data.has_visible_side_effect,
        "Random should NOT set has_visible_side_effect"
    );

    // Challenge
    let exp = CExp::Challenge(Tid::from("F"), false);
    let mut egraph: EGraph<ZIR<ArkBls12_381>, ZAnalysis<ArkBls12_381>> = EGraph::default();
    let mut counter = Counter::new();
    let root = convert_cexp(&exp, &mut egraph, &mut counter);

    let class = &egraph[egraph.find(root)];
    assert!(
        class.data.has_visible_side_effect,
        "Challenge should set has_visible_side_effect"
    );
    assert!(
        class.data.has_side_effect,
        "Challenge should set has_side_effect"
    );
}

#[test]
fn test_zir_rir_conversion() {
    use crate::convert::convert_zir_to_rir;
    use crate::lang::{RAnalysis, RIR};
    use lang::ast::{CExp, Exp};

    let exp = CExp::Bin(
        lang::ast::BinOp::Add,
        Box::new(Exp::Lit(1)),
        Box::new(Exp::Lit(2)),
    );

    let mut zir_egraph: EGraph<ZIR<ArkBls12_381>, ZAnalysis<ArkBls12_381>> = EGraph::default();
    let mut counter = Counter::new();
    let zir_root = convert_cexp(&exp, &mut zir_egraph, &mut counter);

    let mut rir_egraph: EGraph<RIR<ArkBls12_381>, RAnalysis<ArkBls12_381>> = EGraph::default();
    let rir_root = convert_zir_to_rir(&zir_egraph, zir_root, &mut rir_egraph);

    // The RIR e-graph should have an Add node at the root
    let class = &rir_egraph[rir_egraph.find(rir_root)];
    let has_add = class.nodes.iter().any(|n| matches!(n, RIR::Add(_)));
    assert!(has_add, "RIR should contain an Add node");
}

#[test]
fn test_extraction_valid_recexpr() {
    use lang::ast::{CExp, Exp};

    let exp = CExp::Bin(
        lang::ast::BinOp::Mul,
        Box::new(Exp::Lit(3)),
        Box::new(Exp::Lit(7)),
    );

    let mut egraph: EGraph<ZIR<ArkBls12_381>, ZAnalysis<ArkBls12_381>> = EGraph::default();
    let mut counter = Counter::new();
    let root = convert_cexp(&exp, &mut egraph, &mut counter);

    let recexpr = extract_zir(&egraph, root);
    assert!(recexpr.as_ref().len() >= 3); // Mul + 2 constants
}

#[test]
fn test_no_duplicate_tags() {
    // Two Random nodes should have different tags
    use lang::ast::CExp;
    use lang::id::Tid;
    use std::collections::HashSet;

    let exp = CExp::Bin(
        lang::ast::BinOp::Add,
        Box::new(CExp::Random(Tid::from("F"), false)),
        Box::new(CExp::Random(Tid::from("F"), false)),
    );

    let mut egraph: EGraph<ZIR<ArkBls12_381>, ZAnalysis<ArkBls12_381>> = EGraph::default();
    let mut counter = Counter::new();
    let _root = convert_cexp(&exp, &mut egraph, &mut counter);

    // Collect all Random tags
    let mut tags: HashSet<egg::Symbol> = HashSet::new();
    let mut count = 0;
    for class in egraph.classes() {
        for node in &class.nodes {
            if let ZIR::Random(tag, _) = node {
                tags.insert(*tag);
                count += 1;
            }
        }
    }
    assert_eq!(tags.len(), count, "each Random should have a unique tag");
}
