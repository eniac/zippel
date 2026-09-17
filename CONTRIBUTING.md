# Contributing to Zippel

## Development setup

Building the default workspace members only requires the nightly Rust
toolchain (see [README.md](README.md#installation)). Building or testing
everything, including the `benchmarks` crate (`cargo test-all`, or
anything under `cargo build --workspace`), also requires:

- `gcc`, `m4`, and `pkg-config` (the `arkworks`/GMP dependency chain)
- [Singular](https://www.singular.uni-kl.de/), the Gröbner-basis backend
  used by `analyses`' regression tests. Tests that need it are skipped
  with a warning if it is not on `PATH`.

## Before opening a pull request

CI runs four checks on every push and pull request:

```bash
cargo fmt --all -- --check                                         # Rust formatting
cargo clippy --workspace --all-targets                             # lints
cargo run -p fmt --bin zippel-fmt -- --check examples/*/*.zippel   # Zippel formatting
cargo test --workspace                                             # tests
```

Run these locally before submitting. Drop `--check` from either
formatting command to reformat in place instead of only checking.

CI also fails if any path component (a directory or file name, ignoring
extension, case-insensitively) is a reserved Windows device name (`con`,
`prn`, `aux`, `nul`, `clock$`, `com1`-`com9`, `lpt1`-`lpt9`), since these
cannot be checked out on Windows.

## Adding a new protocol example

Create `examples/<name>/<name>.zippel` and `examples/<name>/main.rs`
exposing `pub fn run(_args: &[String])`, then add a `#[path] mod` line
and an `EXAMPLES` row in `examples/main.rs`. No `Cargo.toml` change is
needed.