# experiments

Zippel against existing implementations of the same protocols: the paper's
Figure 7, which is the artifact's Experiment 1. The artifact's Experiments 2
and 3 (completeness and special-soundness analyses) run from
`benches/analysis/`; `benches/` also holds the Criterion benchmarks of Zippel
alone.

Wall-clock comparison between **zippel-compiled protocols** and **native Rust
baselines** for thirteen SNARK / commitment / signature / range-proof schemes.
Each system runs both sides on the same machine, same curve, same input size,
inside the same rayon thread pool — only the implementation differs.

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
experiments/run_all.sh
```

Default: every system, threads ∈ {1, 2, 4, 8, 16}, full-size grid, output to
`bench_results.csv`. Takes a long time at log_size=18-20 single-thread —
expect tens of minutes per system per thread count.

For iteration, narrow the sweep with environment variables:

```sh
SYSTEMS=hyrax THREADS=1,4,8 OUT=hyrax.csv BENCH_SAMPLES=3 experiments/run_all.sh
```

On Linux, when `RAYON_NUM_THREADS=T` is set (as `run_all.sh` does), `bench_all`
pins every timed thread (both rayon pools and the main thread) to the first T
physical cores, one SMT sibling each, and prints the core list in its header.
Both sides therefore get exactly T cores. The setup pool stays unpinned. Set
`BENCH_NO_PIN=1` to disable pinning, e.g. to pin externally:

```sh
SYSTEMS=hyrax THREADS=1,2,4,8 OUT=hyrax.csv BENCH_NO_PIN=1 numactl --cpunodebind=0 --membind=0 experiments/run_all.sh
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

```text
experiments/
├── Cargo.toml             workspace member; select with -p experiments
├── build.rs               locate external baseline sources for NCLOC
├── run_all.sh             thread/system sweep using bench_all
├── dhat_top.py            heap-profile summaries
├── README.md
├── src/
│   ├── lib.rs             timing, heap measurement and module exports
│   ├── cache.rs           on-disk SRS cache
│   ├── cross.rs           fixed-challenge cross-verification helpers (test-only)
│   ├── ncloc.rs           protocol and native baseline source counts
│   ├── spartan.rs         protocol harness + inline cross_tests
│   ├── sumcheck.rs
│   ├── …                  other protocol harnesses
│   ├── upstream/
│   │   ├── mod.rs
│   │   ├── ark_spartan/
│   │   ├── dekart/
│   │   ├── dory/
│   │   ├── hyperplonk/
│   │   ├── hyrax/
│   │   ├── kzh/
│   │   ├── libspartan/    test-only conformance/cross-verification copy
│   │   ├── pari/
│   │   ├── pst13/
│   │   └── sumcheck/
│   └── bin/
│       ├── bench_all.rs           canonical comparison and CSV driver
│       ├── dalek_msm.rs           dalek 4/5 backend comparison
│       ├── msm_micro.rs           native/backend/runtime MSM comparison
│       ├── *_profile.rs          protocol-stage diagnostics
│       ├── spartan_bench.rs       native NIZK/SNARK diagnostic
│       └── …                     per-protocol CLIs with additional controls
├── tests/mem.rs            transient-heap counter regression
└── artifacts/              generated SRS cache (ignored by Git)
```

Protocol files own their Zippel/native harnesses and inline cross-tests. Native
implementations are imported through `experiments::upstream::<name>`. Each
`upstream/<name>/mod.rs` records provenance and local changes. The libspartan
copy is test-only; production libspartan measurements use the pinned dependency.

Historical CSVs and analysis outputs live in
[`../artifact/results/`](../artifact/results/). The paper's pinned measurements
retain their original contents and filenames.
Use `bench_all --systems schnorr` for the former Schnorr one-shot command and
`bench_all --systems spartan --sizes 18` for the former Spartan comparison.
The legacy sweep scripts and four duplicate Criterion wrappers are removed;
`run_all.sh` owns thread sweeps. The workspace-root `benches/` remains separate.

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

`run_all.sh` builds and invokes `<workspace root>/target/release/bench_all`. Its
flags map mostly to the script's env vars but can be used directly for one-off
runs:

```sh
cargo run --release --manifest-path experiments/Cargo.toml --bin bench_all -- \
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

`bench_all` installs a counting global allocator (`experiments::mem`). The
`*_peak_mib` columns are the most heap live at any moment during a prover
(or verifier) call, counted from zero at the call's start: every buffer the
call allocates counts, even one freed before it returns, while memory that
was already live (the proving key, SRS, witness and other inputs both sides
hold) does not. For zippel this includes every intermediate value it keeps
during the run.

Both sides keep their inputs. The native provers and verifiers borrow
theirs. zippel's `run_prover`/`run_verifier` own the values they are passed,
and a `Value` is a cheap handle: cloning one shares its heap data and copies
none (a backend test, `cloning_a_value_shares_its_heap_payload`, checks every
variant). The harness owns every input (`experiments::harness_inputs`) and
lends all of them, and the proof, to every run by passing clones
(`experiments::lend`), so the run frees nothing that was live before it
started. Values computed inside the measured call (below) are passed without
keeping a clone. (A deployment
that gives its witness to the prover lowers the process's high-water mark by
the witness size; that is a property of the API, not of the runtime, and is
not measured.)

The rules every measurement follows, on both sides:

- A measured call frees nothing its caller owns: native calls borrow their
  inputs, and zippel's are lent as clones, which share their data (see
  above). One source of noise remains on both sides: rayon frees resized
  work-queue buffers lazily (through crossbeam-epoch), sometimes during a
  later measured call, which can lower that call's peak by a few KB.
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
  cargo build --release -p experiments --bin bench_all --features dhat
RAYON_NUM_THREADS=1 BENCH_SAMPLES=1 DHAT_FRAMES=64 \
  target/release/bench_all --systems hyperplonk --sizes 16 --threads-label 1 --out /tmp/x.csv
experiments/dhat_top.py dhat/00-hyperplonk_203.json        # what is live at the peak
experiments/dhat_top.py -n 30 -d 3 dhat/00-*.json          # more sites, more context
experiments/dhat_top.py --total dhat/00-hyperplonk_203.json  # what allocates most overall
experiments/dhat_top.py --diff before/00-*.json after/00-*.json  # what a change moved
```

`dhat_top.py` groups the bytes live at the peak (dhat's *t-gmax*) by the
innermost frame in our own code, so an arkworks buffer allocated from
`backend/src/values.rs` is charged to that line. The JSON also opens in
dhat's viewer (`dh_view.html`) for full stacks. `DHAT_FRAMES` (default 32)
caps backtrace depth; rayon stacks are deep, so raise it if many sites come
out unattributed.

`--total` ranks sites by the bytes and blocks they allocate over the whole
run instead: allocation churn that never shows at the peak (e.g. per-element
values in a comprehension). `--diff BEFORE AFTER` compares two profiles of
the same measurement site by site at their peaks, largest increases first;
profile a build before and after a change (into two `DHAT_DIR`s) to see what
it moved. Small profiles are shown in KiB.

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
