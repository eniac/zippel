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
| [`experiments`](experiments) | Zippel vs. hand-optimized native baselines |
| [`examples`](examples) | Protocol implementations and their Rust harnesses |
| [`artifact`](artifact) | Docker image and scripts to reproduce our evaluation results |

## Development setup

Building the default workspace members only requires the nightly Rust toolchain
(see [README.md](README.md#quick-start)). Building or testing everything,
including the `experiments` crate (`cargo test-all`, or anything under `cargo
build --workspace`), also requires:

- `gcc`, `m4`, and `pkg-config` (the `arkworks`/GMP dependency chain)
- [Singular](https://www.singular.uni-kl.de/), the Gröbner-basis backend used by
  `analyses`' regression tests. Tests that need it are skipped with a warning if
  it is not on `PATH`.

## Before opening a pull request

CI runs these checks on every push to `main` and every pull request:

```bash
cargo fmt --all -- --check                # Rust formatting
cargo clippy --workspace --all-targets    # lints
cargo clippy -p experiments --all-targets --features dhat  # heap-profiling code
cargo zfmt --check examples/*/*.zippel    # Zippel formatting
cargo test --workspace                    # tests (CI splits them across jobs)
cargo zrunr run <name> --size NAME=VALUE  # supply every declared size
```

Run them locally before submitting. CI builds the tests optimized
(`CARGO_PROFILE_TEST_OPT_LEVEL=3`, debug assertions still on) and passes
`--locked`, so commit `Cargo.lock` changes. To reformat in place instead of only
checking, drop `--check` from `cargo fmt`, or pass `--write` instead of
`--check` to `cargo zfmt`.

`cargo zfmt`, `cargo zcheck`, `cargo zrun`, and `cargo zrunr` are aliases
defined in [`.cargo/config.toml`](.cargo/config.toml) for `zippel-fmt`,
`zippel-check`, and the example runner (debug and release).

`cargo test` also runs `zippel-check` over every example
(`check/tests/examples.rs`) using automatic defaults. The checker searches for
small sizes that satisfy size/operator constraints and cover overloads in
function groups reachable from protocols. Unused helpers are still typechecked.
Pass `--size` to check specific sizes.

CI also fails if any path component (a directory or file name, ignoring
extension, case-insensitively) is a reserved Windows device name (`con`, `prn`,
`aux`, `nul`, `clock$`, `com1`-`com9`, `lpt1`-`lpt9`), since these cannot be
checked out on Windows.

## PR benchmarks

Maintainers with repository write permission can request a comparison on an open
PR:

```text
/bench run
/bench analyze
/bench run pst13 kzg
/bench analyze schnorr hyperplonk_zerocheck
/bench run kzg --base abc1234 --head def5678
/bench analyze --base main --head pr
/bench run sumcheck --size NUM_VARS_CONST=4 --size MAX_DEGREE_CONST=2
```

Omitting names selects PST13, KZG and IPA. An explicit space-separated list
replaces that selection. Any example registered in `examples/registry.rs` can be
selected in either mode. The [CI catalog](.github/scripts/bench/suite.json)
provides vetted defaults: PST13 and KZG runtime workloads have 2^14 elements,
IPA has 2^10, and analyses use separate small sizes. Other explicit examples use their registered
sizes. Analysis chooses the configured pass, or completeness when registered,
otherwise the first registered pass. Unsupported or failing analyses are
reported as failures.

Repeat `--size NAME=VALUE` (or `-s NAME=VALUE`) to override sizes, just as with
`cargo zrun`. Explicit sizes replace the entire default set and must cover every
declared size. With multiple examples, the same sizes apply to each; each
validates its names and constraints. Reports show the actual resolved sizes,
curve, and analysis parameters from each revision. Changed configurations
suppress percentage comparisons.

`--base` and `--head` accept full or abbreviated commit SHAs (at least seven hex
characters), `main` for the repository's default-branch tip, or `pr` for this
PR's current head. Commit selections must belong to the history of that default
branch, this PR, or its base branch. Both sides can select from any of those
histories, including fork PRs. Omitting a flag uses the PR's base/head tip for
that side. Selections are resolved to full SHAs before the run starts.
Explicitly selected historical comparisons remain reportable after later pushes;
if an automatic tip changes, the report says so instead of showing numbers.

An accepted command gets an 👀 reaction; a rejected one gets a reply saying why
(or a 👎 when the commenter lacks write access). A newer command for the same
PR and mode cancels the older run. The workflow compares the accepted base/head
commits on one runner and updates one report per mode. Each phase has three
native timing samples and three instruction profiles, each sample with fresh
example inputs; a change inside both sides' sample ranges is marked noise.
Timing is advisory. Failures and timeouts remain visible. One budget,
`budget_seconds` in the [CI catalog](.github/scripts/bench/suite.json), bounds
builds and measurement together; cases that do not fit are reported as budget.

Only request benchmarks on PR code you trust. The CI harness reuses existing
example specifications and public APIs; normal examples and `experiments` have
no profiling hooks. Workflows must be deployed on the default branch before
comment commands work. The benchmark job holds only a read-only token, but it
runs in the default branch's context, so the code it builds could still write
the repository's Actions caches. The coordinator supplies the same CI harness to
both revisions, including commits that predate the benchmark workflow, provided
their example and public library APIs are compatible.

For local checks:

```sh
python3 -m unittest discover -s .github/scripts/bench/tests -p 'test_*.py'
cargo clippy --locked -p zippel --bench ci -- -D warnings
```

Full verification needs Valgrind and Singular on PATH, along with the pinned
Rust toolchain. Use a fresh output directory:

```sh
python3 .github/scripts/bench/verification/verify.py \
  --directory /tmp/zippel-bench-verification-NEW
```

This runs real native/profiling checks and writes JSON results, raw profiles,
and Markdown reports. Unit tests live under `bench/tests/`; the real workload
verification driver and worker-counter probe live under `bench/verification/`.

## Creating a new protocol with Zippel

This walks through adding a new protocol end to end. As a running example, we
build `schnorr4`, a copy of [`examples/schnorr`](examples/schnorr) under a new
name.

### 1. Create the example directory

```bash
mkdir examples/schnorr4
```

Every example lives in its own `examples/<name>/` directory holding a
`<name>.zippel` protocol file and a `main.rs` harness.

### 2. Wire it into `examples/registry.rs`

Add a `#[path]` module declaration and an entry in the `with_examples!` list:

```rust
#[path = "schnorr4/main.rs"]
pub mod schnorr4;
```

```rust
macro_rules! with_examples {
    ($callback:ident) => {
        $callback! {
            // ...
            schnorr4,
            // ...
        }
    };
}
```

The shared registry registers each module's `spec()` under both `run` and
`analyze` for the normal CLI and CI harness. Keep the list alphabetical.
Examples supply input construction and metadata; the common harness handles
arguments, compilation, timing and results.

### 3. Define the protocol

`examples/schnorr4/schnorr4.zippel`:

```
proto schnorr4<G: Group, F: Scalar<G>>(witness x: F, instance g: G, instance h: G) where h == g * x {
    let r = random<F>;
    u <- g * r;
    c <- challenge<F>;
    z <- r + x * c;
    verify(g * z == u + h * c)
}
```

A `proto` takes generic curve/field parameters (`G: Group`, `F: Scalar<G>`),
then its parameters tagged `witness` (secret, known only to the prover) or
`instance` (public), and an optional `where` clause stating the relation being
proven. The body samples randomness (`random<F>`), draws challenges
(`challenge<F>`), computes messages with `<-`, and ends in a `verify(...)`
check.

### 4. Check it

```bash
cargo zcheck examples/schnorr4/schnorr4.zippel
```

`zippel-check` runs everything `compile` does, with no harness or inputs needed:
parsing, the semantic checks, type checking, and splitting the protocol into
prover and verifier programs. The last step rejects a `verify` that depends on a
`witness`, an `extra` argument, or a `random` value, since the verifier never
sees those. Checking happens at concrete sizes: set a `Size` parameter with
`--size NAME=VALUE` (repeatable). For parameters you leave unset, `zippel-check`
chooses small defaults where possible. If checking fails, try supplying sizes
appropriate for your protocol. A pass only covers the sizes printed on the
status line.

### 5. Write the example's Rust module

Create `examples/schnorr4/main.rs`. You need two functions: one that builds
valid inputs for your protocol, and a public `spec()` that tells the shared
harness how to run it.

For the Schnorr protocol above, sample a secret `x` and a generator `g`, then
compute `h = g * x` so the inputs satisfy the protocol's relation:

```rust
use ark_std::UniformRand;
use backend::{ArkBls12_381, ArkConfig, Value};
use lang::id::{Tid, Vid};
use share::Ctx;

use crate::common;

fn make_inputs(_sizes: &Ctx<Tid, usize>) -> Ctx<Vid, Value<ArkBls12_381>> {
    let mut rng = rand::rngs::OsRng;
    let x = <ArkBls12_381 as ArkConfig>::F::rand(&mut rng);
    let g = <ArkBls12_381 as ArkConfig>::G1::rand(&mut rng);
    let h = g * x;

    Ctx::from_iter([
        (Vid::new("x"), Value::Scalar(x)),
        (Vid::new("g"), Value::g1(g)),
        (Vid::new("h"), Value::g1(h)),
    ])
}

pub fn spec() -> common::ExampleSpec<ArkBls12_381> {
    common::ExampleSpec {
        source: "examples/schnorr4/schnorr4.zippel",
        defaults: &[],
        validate: None,
        make_inputs,
        analyses: &[
            common::Analysis::Completeness,
            common::Analysis::Zk,
            common::Analysis::Soundness(&[2]),
        ],
    }
}
```

Adapt this module to your protocol:

- Choose the concrete curve in `ExampleSpec<...>` and use the same curve for the
  input values.
- Set `source` to your `.zippel` file's path from the repository root.
- In `make_inputs`, return a value for every `witness`, `instance`, and `extra`
  argument. The keys must be the exact argument names in the source. Compute
  public claims from the generated witness, as `h` is computed from `x` above,
  so the resulting instance satisfies your relation.
- List the analyses you want the harness to run in `analyses`. Soundness needs
  the protocol's transcript count for each challenge round: Schnorr has one
  round and uses `Soundness(&[2])`. Omit soundness if you have not established
  those parameters.

If your protocol declares sizes, put a small runnable value for each one in
`defaults`, for example `&[("N", 4)]`. In `make_inputs`, read that value with
`let n = common::size(sizes, "N");` and use it for input lengths and any
size-dependent calculations. Choose defaults that exercise both recursive and
base cases. See [the IPA module](examples/ipa/main.rs) for a sized example.
Schnorr has no size parameters, so it uses `defaults: &[]` and ignores `_sizes`.

Start with `validate: None`. If your input generator needs additional size
constraints, supply a callback that returns `Err` with an explanation for
unsupported sizes; see [Spartan](examples/spartan/main.rs) for an example. The
shared harness calls it before generating inputs.

The harness handles compilation, command-line arguments, timing and result
printing. Your module only supplies the inputs and the specification above.

### 6. Compile and run

```bash
cargo zrun run schnorr4
cargo zrun analyze schnorr4
cargo zrun analyze schnorr4 soundness --backend singular
cargo zrun run schnorr4 --help
# For an example with sizes:
cargo zrun run ipa --size S=4
cargo zrun analyze ipa completeness --size S=2
```

Use `run` to check that your generated inputs produce a proof the verifier
accepts. Use `analyze` to run a registered analysis, or omit the pass name to
run all analyses you registered. Analyses use `ark-gb` by default; to use
`--backend singular`, install Singular and make it available on `PATH`.

Try your example at its defaults and at other supported sizes. Supply sizes with
repeated `--size NAME=VALUE` flags. If you supply any, include every `Size`
parameter: explicit sizes replace the entire default set. Use your example's
`--help` to see its defaults and registered analyses.
