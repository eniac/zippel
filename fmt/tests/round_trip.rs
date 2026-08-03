use fmt::format_source;

fn round_trip(src: &str) -> String {
    format_source(src).unwrap_or_else(|e| panic!("parse error: {:?}", e))
}

#[test]
fn smoke_schnorr() {
    let src = include_str!("../../examples/schnorr/schnorr.zippel");
    let out = round_trip(src);
    println!("--- schnorr formatted ---\n{}", out);
    // Round-trip: parse the output again, format it, should be identical.
    let out2 = round_trip(&out);
    assert_eq!(out, out2, "idempotency failed");
}

#[test]
fn smoke_hadamard() {
    let src = include_str!("../../examples/hadamard/hadamard.zippel");
    let out = round_trip(src);
    println!("--- hadamard formatted ---\n{}", out);
    let out2 = round_trip(&out);
    assert_eq!(out, out2, "idempotency failed");
}

#[test]
fn smoke_cp() {
    let src = include_str!("../../examples/cp/cp.zippel");
    let out = round_trip(src);
    println!("--- cp formatted ---\n{}", out);
    let out2 = round_trip(&out);
    assert_eq!(out, out2, "idempotency failed");
}
