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

For this example, we will also use `rand`:

```toml
[dependencies]
zippel = { git = "https://github.com/eniac/zippel" }
rand = { version = "0.8", features = ["std"] }
```

`rand` must be pinned to the version Zippel uses internally
(`rand = "0.8"`).

Zippel patches arkworks with a fork whose multi-scalar multiplication
(MSM) runs in the caller's thread pool; see the `[patch.crates-io]`
section of Zippel's `Cargo.toml`. Cargo does not apply a dependency's
patches to your crate, so copy that section into your own workspace's
`Cargo.toml` to get the same performance. Without it, Cargo uses the
arkworks release from crates.io.

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
use zippel::backend::{ArkBls12_381, Backend, Field, Group, Value};
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
    let x = <ArkBls12_381 as Backend>::F::rand(&mut rng);
    let g = <ArkBls12_381 as Backend>::G1::rand(&mut rng);
    let h = (g * x).normalize();
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

`make_inputs` supplies a witness `x` and public values `g` and `h`
satisfying `h = g * x`, built with Zippel's `Field` and `Group` traits from
`zippel::backend`. The shipped backends' elements are arkworks types, so
arkworks APIs work on them too. Input names must match the source parameters
exactly. `prove` takes these inputs and returns a proof. We clone the inputs
so we can reuse them for verification; cloning a `Value` shares its data.

`verify` takes the proof and inputs, reading only the public instance arguments.
It returns `Ok(true)` if every verification check passes, `Ok(false)` if any
check fails, and `Err` for an execution error.

`prepare_analysis` returns a `PreparedAnalysis` for running static checks. Here,
`run(Analysis::Completeness, GbBackendKind::ArkGb)` checks completeness using
the ark-gb backend. The analyses need the backend's scalar field to be an
arkworks prime field (`analyses::AnalysisBackend`). They depend only on that
field, so to analyze a protocol that runs on another backend, compile it for
the arkworks backend with the same scalar field.

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

## 5. Writing a backend

A protocol runs over a *backend*: a type implementing
`zippel::backend::Backend`, which names a scalar field, two source groups
and a pairing. Zippel ships arkworks backends (`ArkBls12_381`, `ArkBn254`,
`ArkCurve25519`, ...) and two built on the zkcrypto `ff`/`group` 0.14
crates (`DalekRistretto`, `PastaPallas`). You can write a backend for any
other library too.

### From `ff`/`group` 0.14

If your curve's types implement `ff::PrimeField` and
`group::Group + group::GroupEncoding`, a marker type is all you need:

```rust
use zippel::backend::ff_group::{FfPoint, FfScalar};
use zippel::backend::{Backend, NoPairing};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct MyCurve;

impl std::fmt::Display for MyCurve {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "my curve")
    }
}

impl Backend for MyCurve {
    type F = FfScalar<my_curve::Scalar>;
    type G1 = FfPoint<my_curve::Point>;
    type G2 = Self::G1;
    type P = NoPairing<Self::G1>;
    const HAS_PAIRING: bool = false;
}
```

`FfPoint<G>` uses a generic Pippenger MSM. To use the curve's own MSM
instead, implement
`zippel::backend::ff_group::Msm<my_curve::Point>`
on a marker type in your crate and use `FfPoint<my_curve::Point, MyMsm>`;
`DalekMsm` is an example.

### From any other library

Implement Zippel's traits from `zippel::backend::algebra`.
`backend/src/ark.rs` and `backend/src/ff_group.rs` are complete examples.

- `Field`: the standard operators, plus `zero`, `one`, `is_zero`,
  `inverse`, `rand`, `from_le_bytes_mod_order`, `write_bytes`,
  `cmp_canonical` and `two_adic_root`, and the constants `MODULUS_BITS`
  and `TWO_ADICITY`. `pow`, `fft` and `ifft` have default implementations
  (a radix-2 FFT over `two_adic_root`).
- `Group`: the standard operators and scalar multiplication, plus `zero`,
  `generator`, `is_zero`, `rand`, `add_affine`, `normalize`,
  `normalize_batch`, `batch_mul`, `msm`, `write_bytes` and
  `write_affine_bytes`. `Affine` is the form an MSM takes; for a group with
  a single form, set it to `Self`.
- `Pairing`: `pairing`, `multi_pairing`, `multi_pairing_prepared` and
  `prepare_g2`. A backend without a pairing uses `NoPairing` and sets
  `HAS_PAIRING = false`.

Rust's orphan rule means you need a newtype around any type your crate
does not own, as `FfScalar` and `FfPoint` are.

Three properties matter for correctness:

- `write_bytes` is the transcript encoding. It must be canonical (equal
  elements give equal bytes), and a group element must encode the same in
  both forms.
- `cmp_canonical` is a total order consistent with equality, and `Hash`
  agrees with equality.
- `two_adic_root(k)` is a primitive `2^k`-th root of unity for every
  `k <= TWO_ADICITY`.

To check them, call the conformance test from a test in your crate:

```rust
#[test]
fn my_curve_conforms() {
    let mut rng = rand::thread_rng();
    zippel::backend::conformance::check_backend::<MyCurve, _>(&mut rng);
}
```

Compilation rejects a protocol that needs something the backend lacks (a
pairing, or an FFT larger than `2^TWO_ADICITY`), with a diagnostic at the
operation; for the shipped backends, `cargo zcheck --backend NAME` reports
the same. Static analysis needs an arkworks scalar field, so analyze a protocol
on the arkworks backend with the same scalar field (`ArkCurve25519` for
Ristretto, `ArkPallas` for Pallas).
