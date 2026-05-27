use backend::op::{GOp, mk};
use backend::{ATyp, ArkBls12_381};
use compiler::compile_prover;
use graph::{ArgKind, Dag, Node};
use lang::id::Vid;
use lang::typ::{CRange, Distribution, Nothing, Qualifier};

#[test]
fn prover_lowers_vector_transcript_output() {
    let mut dag: Dag<ArkBls12_381, Nothing> = Dag::new();
    let a = dag.add_node(Node::Arg(
        Vid::new("a"),
        ATyp::scalar(),
        Qualifier::Public,
        Distribution::Nonuniform,
        ArgKind::Input,
    ));
    let b = dag.add_node(Node::Arg(
        Vid::new("b"),
        ATyp::scalar(),
        Qualifier::Public,
        Distribution::Nonuniform,
        ArgKind::Input,
    ));
    dag.add_node(Node::Transcr(
        mk(GOp::<ArkBls12_381>::vec(vec![
            GOp::underscore(a, ATyp::scalar()),
            GOp::underscore(b, ATyp::scalar()),
        ])),
        Nothing,
    ));

    let mut out = Vec::new();
    compile_prover(&dag, &mut out).expect("vector output should be supported");
    let source = String::from_utf8(out).unwrap();

    assert!(
        source.contains("vec![a.clone(), b.clone()]"),
        "generated prover should construct the vector output\n---\n{source}\n---"
    );
}

#[test]
fn prover_lowers_record_transcript_output_as_tuple() {
    let mut dag: Dag<ArkBls12_381, Nothing> = Dag::new();
    let a = dag.add_node(Node::Arg(
        Vid::new("a"),
        ATyp::scalar(),
        Qualifier::Public,
        Distribution::Nonuniform,
        ArgKind::Input,
    ));
    let b = dag.add_node(Node::Arg(
        Vid::new("b"),
        ATyp::scalar(),
        Qualifier::Public,
        Distribution::Nonuniform,
        ArgKind::Input,
    ));
    let mut fields = share::Ctx::new();
    fields.insert(
        &"left".to_string(),
        &mk(GOp::<ArkBls12_381>::underscore(a, ATyp::scalar())),
    );
    fields.insert(
        &"right".to_string(),
        &mk(GOp::<ArkBls12_381>::underscore(b, ATyp::scalar())),
    );
    dag.add_node(Node::Transcr(mk(backend::op::Op::Record(fields)), Nothing));

    let mut out = Vec::new();
    compile_prover(&dag, &mut out).expect("record output should be supported");
    let source = String::from_utf8(out).unwrap();

    assert!(
        source.contains("let n2 = (a.clone(), b.clone());"),
        "generated prover should construct the record tuple in sorted field order\n---\n{source}\n---"
    );
}

#[test]
fn prover_lowers_record_projection_by_field_name() {
    let mut dag: Dag<ArkBls12_381, Nothing> = Dag::new();
    let a = dag.add_node(Node::Arg(
        Vid::new("a"),
        ATyp::scalar(),
        Qualifier::Public,
        Distribution::Nonuniform,
        ArgKind::Input,
    ));
    let b = dag.add_node(Node::Arg(
        Vid::new("b"),
        ATyp::scalar(),
        Qualifier::Public,
        Distribution::Nonuniform,
        ArgKind::Input,
    ));

    let mut fields = share::Ctx::new();
    fields.insert(
        &"left".to_string(),
        &mk(GOp::<ArkBls12_381>::underscore(a, ATyp::scalar())),
    );
    fields.insert(
        &"right".to_string(),
        &mk(GOp::<ArkBls12_381>::underscore(b, ATyp::scalar())),
    );
    let record = dag.add_node(Node::Op(mk(backend::op::Op::Record(fields)), Nothing));

    let mut record_types = share::Ctx::new();
    record_types.insert(&"left".to_string(), &ATyp::scalar());
    record_types.insert(&"right".to_string(), &ATyp::scalar());
    dag.add_node(Node::Transcr(
        mk(GOp::<ArkBls12_381>::proj(
            GOp::underscore(record, ATyp::Record(record_types)),
            "right".to_string(),
            ATyp::scalar(),
        )),
        Nothing,
    ));

    let mut out = Vec::new();
    compile_prover(&dag, &mut out).expect("record projection should be supported");
    let source = String::from_utf8(out).unwrap();

    assert!(
        source.contains("let n3 = ((a.clone(), b.clone())).1.clone();"),
        "generated prover should project the right field by tuple index\n---\n{source}\n---"
    );
}

#[test]
fn prover_lowers_vector_ram_by_index() {
    let mut dag: Dag<ArkBls12_381, Nothing> = Dag::new();
    let values = dag.add_node(Node::Arg(
        Vid::new("values"),
        ATyp::vec_scalar(2),
        Qualifier::Public,
        Distribution::Nonuniform,
        ArgKind::Input,
    ));
    let index = dag.add_node(Node::Arg(
        Vid::new("index"),
        ATyp::fin(CRange::new(0, 2)),
        Qualifier::Public,
        Distribution::Nonuniform,
        ArgKind::Input,
    ));
    dag.add_node(Node::Transcr(
        mk(GOp::<ArkBls12_381>::ram(
            GOp::underscore(values, ATyp::vec_scalar(2)),
            GOp::underscore(index, ATyp::fin(CRange::new(0, 2))),
        )),
        Nothing,
    ));

    let mut out = Vec::new();
    compile_prover(&dag, &mut out).expect("vector RAM should be supported");
    let source = String::from_utf8(out).unwrap();

    assert!(
        source.contains("let n2 = values[index].clone();"),
        "generated prover should index the vector with the usize argument\n---\n{source}\n---"
    );
}

#[test]
fn prover_lowers_bool_value_transcript_output() {
    let mut dag: Dag<ArkBls12_381, Nothing> = Dag::new();
    dag.add_node(Node::Transcr(
        mk(backend::op::Op::Value(
            backend::Value::<ArkBls12_381>::Bool(true),
        )),
        Nothing,
    ));

    let mut out = Vec::new();
    compile_prover(&dag, &mut out).expect("bool Value should be supported");
    let source = String::from_utf8(out).unwrap();

    assert!(
        source.contains("let n0 = true;"),
        "generated prover should render bool literals\n---\n{source}\n---"
    );
}

#[test]
fn prover_lowers_scalar_value_transcript_output_from_compressed_bytes() {
    let mut dag: Dag<ArkBls12_381, Nothing> = Dag::new();
    dag.add_node(Node::Transcr(
        mk(backend::op::Op::Value(
            backend::Value::<ArkBls12_381>::Scalar(ark_bls12_381::Fr::from(7u64)),
        )),
        Nothing,
    ));

    let mut out = Vec::new();
    compile_prover(&dag, &mut out).expect("scalar Value should be supported");
    let source = String::from_utf8(out).unwrap();

    assert!(
        source.contains("let n0 = scalar_from_compressed_bytes(&["),
        "generated prover should render scalar literals via canonical bytes\n---\n{source}\n---"
    );
}

#[test]
fn prover_lowers_pairing_transcript_output() {
    let mut dag: Dag<ArkBls12_381, Nothing> = Dag::new();
    let g1 = dag.add_node(Node::Arg(
        Vid::new("g1"),
        ATyp::g1(),
        Qualifier::Public,
        Distribution::Nonuniform,
        ArgKind::Input,
    ));
    let g2 = dag.add_node(Node::Arg(
        Vid::new("g2"),
        ATyp::g2(),
        Qualifier::Public,
        Distribution::Nonuniform,
        ArgKind::Input,
    ));
    dag.add_node(Node::Transcr(
        mk(backend::op::Op::Pair(
            mk(GOp::<ArkBls12_381>::underscore(g1, ATyp::g1())),
            mk(GOp::<ArkBls12_381>::underscore(g2, ATyp::g2())),
            ATyp::gt(),
        )),
        Nothing,
    ));

    let mut out = Vec::new();
    compile_prover(&dag, &mut out).expect("pairing should be supported");
    let source = String::from_utf8(out).unwrap();

    assert!(
        source.contains("let n2 = pair(&g1, &g2);"),
        "generated prover should call the typed pairing helper\n---\n{source}\n---"
    );
}
