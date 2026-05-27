use ark_bls12_381::Fr;
use ark_serialize::CanonicalSerialize;
use ark_std::rand::RngCore;
use backend::op::GOp;
use backend::{ATyp, ArkBls12_381, Value};
use graph::eval::eval_op;
use lang::ast::BinOp;
use std::collections::HashMap;
use std::fs;
use std::path::Path;
use std::process::Command;

#[test]
fn scalar_add_generated_program_matches_eval_op_for_random_cases() {
    let mut rng = ark_std::test_rng();
    let cases = (0..4)
        .map(|_| ScalarAddCase {
            lhs: rng.next_u64() % 1_000,
            rhs: rng.next_u64() % 1_000,
        })
        .collect::<Vec<_>>();

    let expected = cases.iter().map(eval_scalar_add_case).collect::<Vec<_>>();
    let actual = run_generated_scalar_add_program(&cases);

    assert_eq!(actual, expected);
}

#[derive(Clone, Debug)]
struct ScalarAddCase {
    lhs: u64,
    rhs: u64,
}

fn eval_scalar_add_case(case: &ScalarAddCase) -> String {
    let op = GOp::<ArkBls12_381>::bin(
        BinOp::Add,
        GOp::value(&Value::Scalar(Fr::from(case.lhs))),
        GOp::value(&Value::Scalar(Fr::from(case.rhs))),
        ATyp::scalar(),
    );
    let mut rng = ark_std::test_rng();
    let value = eval_op(&op, &HashMap::new(), &mut rng).expect("scalar add eval_op succeeds");
    encode_scalar_value(&value)
}

fn encode_scalar_value(value: &Value<ArkBls12_381>) -> String {
    let Value::Scalar(value) = value else {
        panic!("expected scalar result, got {value:?}");
    };
    let mut bytes = Vec::new();
    value
        .serialize_compressed(&mut bytes)
        .expect("scalar serialization succeeds");
    to_hex(&bytes)
}

fn run_generated_scalar_add_program(cases: &[ScalarAddCase]) -> Vec<String> {
    let source = scalar_add_program_source(cases);
    run_generated_program(&source)
}

fn run_generated_program(source: &str) -> Vec<String> {
    let temp = tempfile::tempdir().expect("tempdir should be created");
    let package_dir = temp.path();
    write_generated_package(package_dir, source);

    let output = Command::new(std::env::var_os("CARGO").unwrap_or_else(|| "cargo".into()))
        .args([
            "run",
            "--quiet",
            "--manifest-path",
            package_dir.join("Cargo.toml").to_str().unwrap(),
        ])
        .env("CARGO_TARGET_DIR", shared_target_dir())
        .output()
        .expect("cargo run should start");

    assert!(
        output.status.success(),
        "generated package failed\nstatus: {}\nstdout:\n{}\nstderr:\n{}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    String::from_utf8(output.stdout)
        .expect("generated output should be UTF-8")
        .lines()
        .map(str::to_owned)
        .collect()
}

fn scalar_add_program_source(cases: &[ScalarAddCase]) -> String {
    let cases_source = cases
        .iter()
        .map(|case| format!("({}, {})", case.lhs, case.rhs))
        .collect::<Vec<_>>()
        .join(", ");
    format!(
        r#"use ark_bls12_381::Fr;
use ark_serialize::CanonicalSerialize;

fn main() {{
    let cases: &[(u64, u64)] = &[{cases_source}];
    for (lhs, rhs) in cases {{
        let out = Fr::from(*lhs) + Fr::from(*rhs);
        println!("{{}}", encode_fr(&out));
    }}
}}

fn encode_fr(value: &Fr) -> String {{
    let mut bytes = Vec::new();
    value.serialize_compressed(&mut bytes).unwrap();
    to_hex(&bytes)
}}

fn to_hex(bytes: &[u8]) -> String {{
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(bytes.len() * 2);
    for byte in bytes {{
        out.push(HEX[(byte >> 4) as usize] as char);
        out.push(HEX[(byte & 0x0f) as usize] as char);
    }}
    out
}}
"#
    )
}

fn write_generated_package(package_dir: &Path, source: &str) {
    fs::create_dir_all(package_dir.join("src")).expect("generated src dir should be created");

    fs::write(
        package_dir.join("Cargo.toml"),
        r#"[package]
name = "op-codegen-pbt"
version = "0.1.0"
edition = "2024"

[dependencies]
ark-bls12-381 = { git = "https://github.com/arkworks-rs/algebra.git" }
ark-serialize = { git = "https://github.com/arkworks-rs/algebra.git" }
"#,
    )
    .expect("Cargo.toml should be written");

    assert!(
        !source.contains("Value")
            && !source.contains("eval_op")
            && !source.contains("MutexGraph")
            && !source.contains("runtime::")
            && !source.contains("graph::")
            && !source.contains("backend::"),
        "operation harness generated a forbidden Zippel dependency"
    );
    fs::write(package_dir.join("src/main.rs"), source).expect("main.rs should be written");
}

fn shared_target_dir() -> std::path::PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("compiler crate should have workspace parent")
        .join("target")
        .join("op-codegen-pbt")
}

fn to_hex(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        out.push(HEX[(byte >> 4) as usize] as char);
        out.push(HEX[(byte & 0x0f) as usize] as char);
    }
    out
}
