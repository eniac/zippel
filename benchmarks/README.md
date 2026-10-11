# benchmarks

Wall-clock comparison between **zippel-compiled protocols** and **native Rust
baselines** for thirteen SNARK / commitment / signature / range-proof schemes. Each system runs
both sides on the same machine, same curve, same input size, inside the same
rayon thread pool — only the implementation differs.

Systems benched: `schnorr`, `sumcheck`, `ipa`, `kzg`, `pari`, `groth16`,
`pst13`, `hyrax`, `spartan`, `dekart`, `kzh`, `dory`, `hyperplonk`.

For every (system, log_size, threads) point the bench measures, for the
zippel side and the native baseline:

- prover and verifier wall-clock
- prover and verifier peak heap (see *Peak memory* below)
- non-comment source lines of each side
- zippel compile time (source → executable graph) and graph sizes

Every wall-clock, peak heap and compile time is taken `BENCH_SAMPLES` times
(default 10) and every sample is kept: one CSV row per sample, so means,
variances and intervals are computed afterwards. Times are in milliseconds
and memory in MiB.

## Quick start

From the repository root:

```sh
benchmarks/run_all.sh
```

Default: every system, threads ∈ {1, 2, 4, 8, 16}, full-size grid, output to
`bench_results.csv`. Takes a long time at log_size=18-20 single-thread —
expect tens of minutes per system per thread count.

For iteration, narrow the sweep with environment variables:

```sh
SYSTEMS=hyrax THREADS=1,4,8 OUT=hyrax.csv BENCH_SAMPLES=3 benchmarks/run_all.sh
```

On Linux, when `RAYON_NUM_THREADS=T` is set (as `run_all.sh` does), `bench_all` pins
every timed thread (both rayon pools and the main thread) to the first T
physical cores, one SMT sibling each, and prints the core list in its header. Both sides therefore
get exactly T cores. The setup pool stays unpinned. Set `BENCH_NO_PIN=1` to
disable pinning, e.g. to pin externally:

```sh
SYSTEMS=hyrax THREADS=1,2,4,8 OUT=hyrax.csv BENCH_NO_PIN=1 numactl --cpunodebind=0 --membind=0 benchmarks/run_all.sh
```

On macOS and other non-Linux platforms, `bench_all` automatically runs
without CPU pinning and reports that pinning is unsupported in its header.
`RAYON_NUM_THREADS=T` still bounds both sides to T compute threads: Zippel's
runtime runs every node inside its rayon pool, and the patched arkworks (see
the workspace `Cargo.toml`) keeps MSMs inside the caller's pool. Without
pinning, though, threads may share a physical core and timings vary more. To
use the same unpinned execution policy on Linux, set `BENCH_NO_PIN=1` there
too.

## Folder layout

```
benchmarks/
├── Cargo.toml             excluded from the workspace — see Cargo.toml notes
├── run_all.sh             orchestrator: sweeps threads × systems → one CSV
├── run_sweep.sh           older orchestrator (mostly superseded by run_all.sh)
├── run_sweep_safe.sh      older orchestrator with crash-recovery
├── README.md              this file
├── src/
│   ├── lib.rs             public surface: re-exports each system + Timing + SAMPLES
│   ├── cache.rs           on-disk SRS cache (artifacts/*.bin); skips long keygens on re-run
│   │
│   ├── schnorr.rs         each *.rs file holds two pub mods:
│   ├── sumcheck.rs           - zippel_side::Setup     compiles .zippel, holds inputs
│   ├── ipa.rs                - native_side::Setup     calls the upstream crate / vendored copy
│   ├── kzg.rs              both expose `Setup::new(...)` + `Setup::time_protocol(...) -> Timing`
│   ├── pari.rs
│   ├── groth16.rs
│   ├── pst13.rs
│   ├── hyrax.rs
│   ├── spartan.rs
│   ├── dekart.rs
│   ├── kzh.rs
│   ├── dory.rs
│   ├── hyperplonk.rs
│   │
│   ├── pari_upstream/     vendored garuda-pari (was outside arkworks-0.6 / fixes for fair compare)
│   ├── pst13_upstream/    vendored ark-poly-commit::multilinear_pc with two open() fixes
│   ├── hyrax_upstream/    vendored ark-poly-commit::hyrax with flat-matrix row_mul rewrite
│   ├── sumcheck_upstream/ vendored hyperplonk sumcheck (ported to ark 0.6)
│   ├── dekart_upstream/   vendored aptos-dkg dekart_univariate_v2 (ported to ark 0.6)
│   ├── kzh_upstream/      vendored irondict KZH-k, dense non-zk path (ported to ark 0.6)
│   ├── dory_upstream/     vendored a16z dory-pcs, transparent path, concrete BLS12-381
│   ├── hyperplonk_upstream/ vendored Espresso HyperPlonk SNARK over multilinear KZG (ported to ark 0.6)
│   │
│   └── bin/
│       ├── bench_all.rs           main entry point used by run_all.sh
│       ├── schnorr.rs, sumcheck.rs, …   single-system one-shot runners (legacy / debug)
│       ├── groth16_profile.rs     groth16 profiling harness
│       ├── spartan_bench.rs       libspartan-only timing
│       ├── dekart.rs              dekart zippel vs native side-by-side (--sweep, --ell)
│       ├── dekart_profile.rs      dekart prover-only timing of truncated protos
│       └── spartan_compare.rs     spartan zippel vs native side-by-side
│
├── benches/               criterion benches for a couple of systems (rarely used now)
├── artifacts/             auto-created at runtime — on-disk SRS cache (see cache.rs)
└── *.csv                  sample / saved bench outputs
```

`*_upstream/` modules exist where the original upstream code had a bug,
performance issue, or used an older arkworks version. The vendored copy is
the actual baseline the bench measures against (so the comparison is "zippel
vs a well-implemented native PST13", not "zippel vs ark-poly-commit-0.6's
known-buggy MSM scheduler"). Each `*_upstream/mod.rs` documents what was
changed and why at the top of the file.

## Driver: `run_all.sh`

Wrapper around the `bench_all` binary that sweeps `RAYON_NUM_THREADS`. In-
process pool reconfiguration via `rayon::ThreadPool::install` hangs on
arkworks' parallel paths, so the script re-invokes the binary once per
thread count and appends each iteration's rows to the same CSV. Ctrl-C
between iterations preserves rows that completed.

Environment variables:

| var | default | meaning |
|-----|---------|---------|
| `THREADS` | `1,2,4,8,16` | comma-separated thread counts to sweep |
| `OUT` | `bench_results.csv` | output CSV path |
| `SYSTEMS` | (all) | comma-separated subset, e.g. `hyrax,pst13` |
| `QUICK` | `0` | set `1` for a smaller log_size grid (iteration mode) |
| `BENCH_SAMPLES` | `10` | samples per measurement, each kept as its own CSV row |

Each measurement runs the prover `BENCH_SAMPLES` times back-to-back under
the timer, then `BENCH_SAMPLES` more times with the heap counter on; the
verifier and the zippel compile are sampled the same way.

## Driver internals: `bench_all` binary

`run_all.sh` builds and invokes `<workspace root>/target/release/bench_all`. Its flags map
mostly to the script's env vars but can be used directly for one-off runs:

```sh
cargo run --release --manifest-path benchmarks/Cargo.toml --bin bench_all -- \
    --systems hyrax,pst13 \
    --sizes 16,18 \
    --out custom.csv \
    --threads-label 8
```

Flags:

- `--out PATH` — output CSV path (default `bench_results.csv`)
- `--systems S1,S2,...` — restrict to a subset of systems
- `--sizes N1,N2,...` — override the per-system log_size grid
- `--quick` — small grid for fast iteration
- `--threads-label N` — overrides the `threads` CSV column (the script uses
  this so `RAYON_NUM_THREADS=N`'s value shows up consistently even when
  rayon's pool reports something else)
- `--no-header --append` — used by `run_all.sh` to concatenate
  multi-thread-count runs into one CSV

Single-system entry points in `src/bin/` (e.g. `cargo run --release --bin
hyrax`) exist for debugging one system in isolation without spinning up
others — they're independent of `bench_all` and don't share CSV output.

## CSV format

```
system,baseline,threads,log_size,sample,zippel_prover_ms,zippel_verifier_ms,zippel_ncloc,baseline_prover_ms,baseline_verifier_ms,baseline_ncloc,compile_ms,prover_nodes,verifier_nodes,zippel_prover_peak_mib,zippel_verifier_peak_mib,baseline_prover_peak_mib,baseline_verifier_peak_mib
```

One row per sample: `sample` runs from 0 to `BENCH_SAMPLES − 1` in run
order. The `*_ms` columns and the `*_peak_mib` columns of one row come from
different runs (timed runs never count memory), so treat each column as its
own list of samples rather than pairing them by row. The zippel columns
repeat across a system's baselines (Spartan has two). `*_ncloc` and
`*_nodes` are constants repeated on every row.

`log_size` is log₂ of each system's natural complexity parameter (so points
plot linearly on a log-size x-axis):

- `schnorr` — `0` (fixed protocol, no size knob)
- `sumcheck` — `num_vars` (hypercube has 2^nv points)
- `ipa` — `S` (vector length N = 2^S)
- `kzg` — log₂(N) where N = coefficient count
- `pari` — `M` (K = 2^M constraints)
- `groth16` — log₂(num_constraints)
- `pst13` — `N` (polynomial has 2^N coefficients)
- `hyrax` — `N` (multilinear poly has 2^N evaluations; N must be even)
- `spartan` — `M` (num_cons = 2^M)
- `dekart` — `L` (n = 2^L − 1 values, each in [0, 2^16); ell is fixed at 16
  in `bench_all`, use `--ell` on the standalone `dekart` bin to vary it)
- `kzh` — `N` (KZH-2: 2^N evaluations, split into ⌈N/2⌉ row and ⌊N/2⌋
  column variables as irondict does)
- `dory` — `N` (2^N evaluations as a square 2^(N/2) × 2^(N/2) matrix; N must
  be even). "prove" is commit + evaluation proof on both sides
- `hyperplonk` — `N` (vanilla-Plonk circuit of 2^N gates, the end-to-end
  SNARK: PIOP plus multilinear-KZG batch opening). "prove" starts from the
  witness and includes the witness commitments; preprocessing is untimed

`compiler` is the zippel compile time alone: source parse + concretization
+ graph construction + prover/verifier projection. It excludes the Rust
compiler (which builds the bench binary once, outside any measurement) and
excludes runtime scheduling and the prove/verify execution.

`zippel_ncloc` is line count of the proto (or its rendered instance, for
systems where the proto is template-generated). `native_ncloc` is the line
count of the native module file or vendored upstream copy. Both are
non-comment, non-blank lines.

## Peak memory

`bench_all` installs a counting global allocator (`benchmarks::mem`). The
`*_peak_mib` columns are the most heap live at any moment during a prover
(or verifier) call, counted from zero at the call's start: every buffer the
call allocates counts, even one freed before it returns, while memory that
was already live (the proving key, SRS, witness and other inputs both sides
hold) does not. For zippel this includes every intermediate value it keeps
during the run.

Both sides keep their inputs. The native provers and verifiers borrow
theirs. zippel's `run_prover`/`run_verifier` take each input either given (a
`Value`, which the run frees after its last reader) or lent (an `Arc<Value>`
the caller keeps a clone of, which the run never frees). The harness owns
every input as an `Arc` (`benchmarks::harness_inputs`) and lends all of them,
and the proof, to every run (`benchmarks::lend`), so the run frees nothing
that was live before it started, whatever kind of value an input is. Only
values computed inside the measured call (below) are given. (A deployment
that gives its witness to the prover lowers the process's high-water mark by
the witness size; that is a property of the API, not of the runtime, and is
not measured.)

The rules every measurement follows, on both sides:

- A measured call frees nothing that was live before it started (checked by
  tracking the counter's minimum, which is 0 for every run).
- Whatever a call consumes or needs is made inside it: transcripts and
  sponges, and copies of inputs a call consumes (libspartan's `prove` takes
  its witness by value). Native IPA folds its first round straight from the
  borrowed inputs instead of copying them.
- Both sides do the same work inside the call. Where the zippel protocol
  takes a derived witness as input that the native prover computes itself,
  the harness computes it inside zippel's measured call: Groth16's
  `h_coeffs`, PARI's four sparse matrix-vector products, Spartan's
  `Az`/`Bz`/`Cz`, DeKART's bit decomposition. Nothing is subtracted
  afterwards.

The counter is off during the timed samples; each measurement adds
`BENCH_SAMPLES` untimed prover runs and as many untimed verifier runs with
counting on, after the timed ones, and records each run's peak. At one
thread the peak is essentially deterministic; with more threads it varies
with how the scheduler interleaves allocations. Stack memory is not
counted.

## Heap profiling

The peak columns say how much heap a run used; to see *what* used it, build
with the `dhat` feature. Every measurement's first counted run is then
profiled by [dhat](https://docs.rs/dhat), and the profile is written to
`$DHAT_DIR` (default `dhat/`) as `<n>-<file>_<line>.json`, where
`<file>_<line>` is the `sample`/`sample_with` call site that took it (e.g.
`hyperplonk_203` is HyperPlonk's zippel prover). Profile one thread, so the
peak is deterministic, and keep line tables so frames carry `file:line`:

```sh
CARGO_PROFILE_RELEASE_DEBUG=line-tables-only \
  cargo build --release -p benchmarks --bin bench_all --features dhat
RAYON_NUM_THREADS=1 BENCH_SAMPLES=1 DHAT_FRAMES=64 \
  target/release/bench_all --systems hyperplonk --sizes 16 --threads-label 1 --out /tmp/x.csv
benchmarks/dhat_top.py dhat/00-hyperplonk_203.json        # what is live at the peak
benchmarks/dhat_top.py -n 30 -d 3 dhat/00-*.json          # more sites, more context
```

`dhat_top.py` groups the bytes live at the peak (dhat's *t-gmax*) by the
innermost frame in our own code, so an arkworks buffer allocated from
`backend/src/values.rs` is charged to that line. The JSON also opens in
dhat's viewer (`dh_view.html`) for full stacks. `DHAT_FRAMES` (default 32)
caps backtrace depth; rayon stacks are deep, so raise it if many sites come
out unattributed.

dhat's own bookkeeping goes through the counting allocator, so the profiled
sample's `*_peak_mib` is slightly high and its wall-time much higher: don't
take timings from a `dhat` build.

## Output caching

Setup-phase artifacts (SRS, universal params, large preprocessed data) are
cached in `artifacts/` keyed by `(system, log_size)`. First run at a given
size builds + saves (cache miss), subsequent runs deserialize from disk
(cache hit). Cache messages are printed to stderr during the bench.

Override the cache directory with `BENCH_ARTIFACTS_DIR=/path/to/dir`. The
cache is always populated outside any timed region (callers wrap setup in
`setup_pool().install(...)`), so cache I/O never enters a measured number.

Delete `artifacts/` to force a clean rebuild — useful after curve or
serialization-format changes.

## Tips

- **Bench runs are long.** At log_size=20 single-thread some systems take
  10+ minutes per iteration. Use `QUICK=1` or `--sizes` for development.
- **Don't compare across machines.** Apple Silicon and Xeon have different
  per-core characteristics and different rayon overheads; absolute numbers
  vary 5-10× between architectures.
- **Look at the spread, not just the mean.** Timings at one thread on a
  loaded server jitter 20-50%. The first sample of each measurement runs
  with cold caches; check whether it is an outlier before averaging it in.
- **Pinning is on by default on Linux when `RAYON_NUM_THREADS` is set.**
  Without it the scheduler scatters threads
  across sockets and SMT siblings, which adds NUMA crossbar costs and lets
  either side borrow extra cores. Keep the machine otherwise idle during a
  sweep: other load on the pinned cores skews both sides.
