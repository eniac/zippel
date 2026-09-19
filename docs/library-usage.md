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
    c <- challenge<F*>;
    z <- r + x * c;
    verify(g * z == u + h * c)
}
```

A `proto` takes generic curve/field parameters (`G: Group`, `F:
Scalar<G>`), then its parameters tagged `witness` (secret, known only
to the prover) or `instance` (public), and an optional `where` clause
stating the relation being proven. The body samples randomness
(`random<F>`), draws challenges (`challenge<F*>`), computes messages
with `<-`, and ends in a `verify(...)` check.

## 3. Write the harness

The harness is the Rust code that compiles the protocol against a
concrete curve, supplies witness and instance values, and runs the
prover and verifier.

`src/main.rs`:

```rust
use ark_std::UniformRand;
use std::path::PathBuf;
use zippel::backend::{ArkBls12_381, ArkConfig, ArkGroupOps, Value};
use zippel::lang::id::Vid;
use zippel::share::Ctx;
use zippel::{check_verification, proof_size_bytes, ZippelArgs, ZippelHandler};

fn main() {
    let args = ZippelArgs::new(PathBuf::from("schnorr.zippel"));
    let mut handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
    handler.compile(&Ctx::new());

    let inputs = prover_create_inputs();
    let proof = handler.run_prover(&inputs).expect("run_prover failed");
    println!(
        "Proof size: {} bytes ({} elements)",
        proof_size_bytes::<ArkBls12_381>(&proof),
        proof.len()
    );

    let verifier_result = handler
        .run_verifier(&proof, &inputs)
        .expect("run_verifier failed");
    println!(
        "Verification: {}",
        if check_verification(&verifier_result) {
            "PASSED"
        } else {
            "FAILED"
        }
    );

    match handler.analyze_completeness() {
        Ok(()) => println!("Completeness: PASSED"),
        Err(e) => println!("Completeness: FAILED ({e})"),
    }
}

fn prover_create_inputs() -> Ctx<Vid, Value<ArkBls12_381>> {
    let mut rng = rand::rngs::OsRng;
    let x = <ArkBls12_381 as ArkConfig>::F::rand(&mut rng);
    let g = <ArkBls12_381 as ArkConfig>::G1::rand(&mut rng);
    let h = <ArkBls12_381 as ArkConfig>::G1Ops::vec_mul(&g, &[x])
        .into_iter()
        .next()
        .unwrap();
    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("x".to_string()), Value::Scalar(x)),
        (Vid("g".to_string()), Value::G1(g)),
        (Vid("h".to_string()), Value::G1Affine(h)),
    ])
}
```

- `ZippelHandler<C>` drives compiling, running, and analyzing a
  protocol for one concrete curve `C`.
- `ZippelArgs` points a handler at a `.zippel` file.
- `Ctx<Vid, Value<C>>` maps each protocol parameter name to a value;
  its keys must match the `.zippel` file's parameter names exactly
  (`x`, `g`, `h` above).
- `analyze_completeness()` returns `Result<(),
  analyses::AnalysisError<C>>`; `Ok(())` means the protocol is
  complete.

## 4. Compile and run

```bash
cargo run
```

```
Proof size: 80 bytes (2 elements)
Verification: PASSED
Completeness: PASSED
```