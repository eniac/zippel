# Contributing to Zippel

## Code layout

| Crate / directory | Description |
|---|---|
| [`lang`](lang) | Zippel language: parser, type checker, size concretization |
| [`graph`](graph) | Graph IR construction and prover/verifier projection |
| [`backend`](backend) | Concrete curve and field types backed by `arkworks` |
| [`analyses`](analyses) | Completeness and special-soundness analyses over Gröbner bases |
| [`runtime`](runtime) | Executes projected prover/verifier graphs on a work-stealing scheduler |
| [`share`](share) | Utilities shared across the workspace |
| [`fmt`](fmt) | `zippel-fmt`, the source formatter |
| [`check`](check) | `zippel-check`, which runs every compile-time check on `.zippel` files without a harness or inputs |
| [`benchmarks`](benchmarks) | Zippel vs. hand-optimized native baselines |
| [`examples`](examples) | Protocol implementations and their Rust harnesses |
| [`artifact`](artifact) | Docker image and scripts to reproduce our evaluation results |

## Development setup

Building the default workspace members only requires the nightly Rust
toolchain (see [README.md](README.md#quick-start)). Building or testing
everything, including the `benchmarks` crate (`cargo test-all`, or
anything under `cargo build --workspace`), also requires:

- `gcc`, `m4`, and `pkg-config` (the `arkworks`/GMP dependency chain)
- [Singular](https://www.singular.uni-kl.de/), the Gröbner-basis backend
  used by `analyses`' regression tests. Tests that need it are skipped
  with a warning if it is not on `PATH`.

## Before opening a pull request

CI runs four checks on every push and pull request:

```bash
cargo fmt --all -- --check                # Rust formatting
cargo clippy --workspace --all-targets    # lints
cargo zfmt --check examples/*/*.zippel    # Zippel formatting
cargo test --workspace                    # tests
```

Run these locally before submitting. To reformat in place instead of
only checking, drop `--check` from `cargo fmt`, or pass `--write`
instead of `--check` to `cargo zfmt`.

`cargo zfmt`, `cargo zcheck`, `cargo zrun`, and `cargo zrunr` are
aliases defined in [`.cargo/config.toml`](.cargo/config.toml) for
`zippel-fmt`, `zippel-check`, and the example runner (debug and
release).

`cargo test` also runs `zippel-check` over every example
(`check/tests/examples.rs`). Examples that only pass at sizes
larger than the defaults are listed with their sizes in
`EXAMPLE_SIZES` there; add yours if it needs specific sizes.

CI also fails if any path component (a directory or file name, ignoring
extension, case-insensitively) is a reserved Windows device name (`con`,
`prn`, `aux`, `nul`, `clock$`, `com1`-`com9`, `lpt1`-`lpt9`), since these
cannot be checked out on Windows.

## Creating a new protocol with Zippel

This walks through adding a new protocol end to end. As a running
example, we build `schnorr4`, a copy of [`examples/schnorr`](examples/schnorr)
under a new name.

### 1. Create the example directory

```bash
mkdir examples/schnorr4
```

Every example lives in its own `examples/<name>/` directory holding a
`<name>.zippel` protocol file and a `main.rs` harness.

### 2. Wire it into `examples/main.rs`

Add a `#[path]` module declaration and an `EXAMPLES` row:

```rust
#[path = "schnorr4/main.rs"]
mod schnorr4;
```

```rust
("schnorr4", schnorr4::run),
```

`EXAMPLES` maps a name to that module's `run(&[String])`; `main()` looks
up `argv[1]` in it and forwards `argv[2..]`.

### 3. Define the protocol

`examples/schnorr4/schnorr4.zippel`:

```
proto schnorr4<G: Group, F: Scalar<G>>(witness x: F, instance g: G, instance h: G) where h == g * x {
    let r = random<F>;
    u <- g * r;
    c <- challenge<F*>;
    z <- r + x * c;
    verify(g * z == u + h * c)
}
```

A `proto` takes generic curve/field parameters (`G: Group`, `F:
Scalar<G>`), then its parameters tagged `witness` (secret, known only to
the prover) or `instance` (public), and an optional `where` clause
stating the relation being proven. The body samples randomness
(`random<F>`), draws challenges (`challenge<F*>`), computes messages
with `<-`, and ends in a `verify(...)` check.

### 4. Check it

```bash
cargo zcheck examples/schnorr4/schnorr4.zippel
```

`zippel-check` runs everything `compile` does, with no harness or
inputs needed: parsing, the semantic checks, type checking, and
splitting the protocol into prover and verifier programs. The last step
rejects a `verify` that depends on a `witness`, an `extra` argument, or
a `random` value, since the verifier never sees those. Checking
happens at concrete sizes: set a `Size` parameter with
`--size NAME=VALUE` (repeatable). Parameters you leave unset default
to the smallest values (by sum, each at most 16) that keep every range
non-empty; if none exist, `zippel-check` reports an error asking for
`--size`. Defaults may be too small for some protocols (for example, one that indexes `v[1]`
needs `N >= 2`). A pass only covers the sizes printed on the status
line.

### 5. Define the harness

The harness compiles the protocol against a concrete curve, generates
witness/instance values, and runs the prover and verifier.
`examples/schnorr4/main.rs`:

```rust
use ark_std::UniformRand;
use backend::{ArkBls12_381, ArkConfig, ArkGroupOps, Value};
use lang::id::Vid;
use share::Ctx;
use std::path::PathBuf;
use zippel::*;

use crate::common;

pub fn run(_args: &[String]) {
    println!("=== Schnorr4 (ArkBls12_381) ===");
    let args = ZippelArgs::new(PathBuf::from("examples/schnorr4/schnorr4.zippel"));
    let mut handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
    handler.compile(&Ctx::new());

    let inputs = prover_create_inputs();
    common::run_prover_and_verify(&mut handler, &inputs);

    // Static analysis (completeness, ZK, and soundness)
    println!("\n--- Static Analysis ---");

    common::time_analysis!("Completeness", handler.analyze_completeness());
    common::time_analysis!("ZK", handler.analyze_knowledge());
    common::time_analysis!(
        "Soundness",
        handler.analyze_special_soundness(vec![2])
    );
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

- `ZippelHandler<ArkBls12_381>` fixes the concrete curve.
- `Ctx<Vid, Value<...>>` maps each `.zippel` parameter name to a
  value; its keys must match the protocol's parameter names exactly
  (`x`, `g`, `h` above).
- `common::run_prover_and_verify`/`common::time_analysis!` are shared
  by every example; reuse them in your own harness.
- `analyze_completeness()` and `analyze_knowledge()` (the
  zero-knowledge check) take no arguments.
- `analyze_special_soundness(l_vec)` takes one `l` per round, the
  number of accepting transcripts needed to extract a witness under
  `l`-special soundness (schnorr4 is 2-special-sound, hence
  `vec![2]`).

### 6. Compile and run

```bash
cargo zrun schnorr4
```