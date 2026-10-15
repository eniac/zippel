# Using Zippel as a library

This shows how to depend on Zippel from an external crate: write a
protocol, compile it, run the prover and verifier, and check
completeness.

If you're instead adding a protocol to this repository's own
`examples/`, see
[`CONTRIBUTING.md`](../CONTRIBUTING.md#creating-a-new-protocol-with-zippel).

## 1. Add the dependency

Zippel is not published on crates.io, so you need to depend on it
directly from git.

For this example, we will also use `ark-std` and `rand`:

```toml
[dependencies]
zippel = { git = "https://github.com/eniac/zippel" }
ark-std = "0.6"
rand = { version = "0.8", features = ["std"] }
```

`ark-std` and `rand` must be pinned to the versions Zippel uses
internally (`ark-std = "0.6"`, `rand = "0.8"`).

Zippel also requires nightly Rust; pin the same toolchain Zippel does
(see [`rust-toolchain.toml`](../rust-toolchain.toml)) in your own crate.

## 2. Write the protocol

`schnorr.zippel`:

```
proto schnorr<G: Group, F: Scalar<G>>(witness x: F, instance g: G, instance h: G) where h == g * x {
    let r = random<F>;
    u <- g * r;
    c <- challenge<F>;
    z <- r + x * c;
    verify(g * z == u + h * c)
}
```

A `proto` takes generic curve/field parameters (`G: Group`, `F:
Scalar<G>`), then its parameters tagged `witness` (secret, known only
to the prover) or `instance` (public), and an optional `where` clause
stating the relation being proven. The body samples randomness
(`random<F>`), draws challenges (`challenge<F>`), computes messages
with `<-`, and ends in a `verify(...)` check.

## 3. Write the harness

The harness is the Rust code that compiles the protocol against a
concrete curve, supplies witness and instance values, and runs the
prover and verifier.

`src/main.rs`:

```rust
use ark_std::UniformRand;
use zippel::backend::{ArkBls12_381, ArkConfig, ArkGroupOps, Value};
use zippel::share::Ctx;
use zippel::analyses::GbBackendKind;
use zippel::{Analysis, CompileOptions, ParsedModule, proof_size_bytes};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let module = ParsedModule::load("schnorr.zippel")?;
    let protocol = module.compile::<ArkBls12_381>(&Ctx::new(), CompileOptions::default())?;

    let prover = protocol.project_prover();
    let verifier = protocol.project_verifier()?;

    let inputs = make_inputs();
    let proof = prover.prove(inputs.clone())?;
    println!(
        "Proof size: {} bytes ({} elements)",
        proof_size_bytes::<ArkBls12_381>(&proof),
        proof.len()
    );

    let passed = verifier.verify(proof, inputs)?;
    println!(
        "Verification: {}",
        if passed {
            "PASSED"
        } else {
            "FAILED"
        }
    );

    let analysis = protocol.prepare_analysis()?;
    match analysis.run(Analysis::Completeness, GbBackendKind::ArkGb) {
        Ok(()) => println!("Completeness: PASSED"),
        Err(e) => println!("Completeness: FAILED ({e})"),
    }
    Ok(())
}

fn make_inputs() -> Vec<(&'static str, Value<ArkBls12_381>)> {
    let mut rng = rand::rngs::OsRng;
    let x = <ArkBls12_381 as ArkConfig>::F::rand(&mut rng);
    let g = <ArkBls12_381 as ArkConfig>::G1::rand(&mut rng);
    let h = <ArkBls12_381 as ArkConfig>::G1Ops::vec_mul(&g, &[x])
        .into_iter()
        .next()
        .unwrap();
    vec![
        ("x", Value::Scalar(x)),
        ("g", Value::g1(g)),
        ("h", Value::g1_affine(h)),
    ]
}
```

`ParsedModule::load` reads and parses the source. Calling
`compile::<ArkBls12_381>` chooses the curve and returns a joint
`CompiledProtocol`. The first argument supplies concrete size parameters:
Schnorr has none, so this example uses an empty `Ctx`.
`CompileOptions::default()` selects the first protocol in the file.

`project_prover` builds a `CompiledProver`; `project_verifier` builds a
`CompiledVerifier`, reporting source diagnostics if a verifier check depends on
private inputs or randomness. Each owns its projected graph and transcript
identity and can be reused after the joint protocol is dropped. `prove` belongs
to the prover; `verify` belongs to the verifier.

`make_inputs` supplies a witness `x` and public values `g` and `h` satisfying
`h = g * x`. Input names must match the source parameters exactly. `prove` takes
these inputs and returns a proof. We clone the inputs so we can reuse them for
verification; cloning a `Value` shares its data.

`verify` takes the proof and inputs, reading only the public instance arguments.
It returns `Ok(true)` if every verification check passes, `Ok(false)` if any
check fails, and `Err` for an execution error.

`prepare_analysis` returns a `PreparedAnalysis` for running static checks. Here,
`run(Analysis::Completeness, GbBackendKind::ArkGb)` checks completeness using
the ark-gb backend.

Loading, compilation, verifier projection, execution and analysis preparation
return `Result`; the example uses `?` to propagate errors. The analysis result
is handled separately so the example can print whether the completeness check
passed.

## 4. Compile and run

```bash
cargo run
```

```
Proof size: 80 bytes (2 elements)
Verification: PASSED
Completeness: PASSED
```