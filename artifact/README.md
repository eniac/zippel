# Zippel: IEEE S&P 2027 Artifact

Zippel is a language/compiler/runtime for cryptographic proof systems,
with static analyses (Gröbner-basis based) that check completeness and
special soundness directly from a protocol's source. This package builds
the whole system in Docker and runs the three experiments behind the
paper's evaluation section.

**Note on scope.** This artifact reproduces the submitted paper's Figure 7
(page 13) and the completeness/special-soundness claims in Section 9.3.
It also produces two supplementary tables the submitted paper doesn't
include at all (a per-protocol Graph IR node-count table, and a
30-protocol inline/no-inline completeness breakdown). These are being
added to the paper in response to reviewer feedback, so the submitted
paper has no table to check them against yet. Each experiment below says
which one it is.

## Repo layout

| Path | What it is |
|---|---|
| `lang/` | Zippel language: parser, type checker, size concretization |
| `graph/` | Graph IR construction and prover/verifier projection |
| `backend/` | arkworks-backed concrete curve/field types |
| `analyses/` | Completeness and special-soundness analyses (Gröbner bases) |
| `runtime/` | Executes the projected prover/verifier graphs |
| `share/` | Shared utilities (`Ctx`, `Set`, etc.) used across crates |
| `fmt/` | `zippel-fmt` formatter, keeps `examples/*.zippel` in the canonical style the paper's LoC counts use |
| `examples/` | 30+ `.zippel` protocol implementations + Rust harnesses |
| `benches/inline/` | Inline vs. no-inline completeness sweep (Experiment 3) |
| `benchmarks/` | Zippel vs. native performance comparison (Experiment 1) |
| `analyses/tests/gb_snapshots/` | Completeness/soundness regression suite (Experiment 2) |
| `artifact/` | This package: `Dockerfile` + `scripts/` |

## Setup

Build the image from the repo root (not from `artifact/`):

```sh
docker build -f artifact/Dockerfile -t zippel-ae .
```

This installs the nightly Rust toolchain pinned by `rust-toolchain.toml`,
plus `gcc`/`m4`/`pkg-config`/Singular via apt, and prebuilds the workspace
in release mode. Takes about 10 minutes and 25GB of disk. Needs network
access to pull the base image and fetch crates.

Verify the environment:

```sh
docker run --rm zippel-ae bash artifact/scripts/smoke_test.sh
```

This builds and runs 3 example protocols, runs one completeness trial
through Singular, and runs one `inline`-bench check. It's not a real
experiment, just a check that the toolchain and Singular integration
work. It should finish in well under a minute and end with:

```
Smoke test passed.
```

If it sits on `Compiling ...` for a few minutes on first run, that's
expected (see "Note on recompiles" below), not a hang.

## Experiments

| # | Script | Produces | Paper reference |
|---|---|---|---|
| 1 | `run_benchmark.sh` + `process_benchmark.py` | Zippel-vs-native speedup table; Graph IR node-count table | Figure 7 (p.13); node-count table is supplementary, not in the paper |
| 2 | `run_correctness.sh` | Pass/fail/ignored counts for completeness + special-soundness | §9.3 prose (partial coverage, see below) |
| 3 | `run_inline.sh` + `process_inline.py` | 30-protocol inline/no-inline completeness table | §9.3 prose; the table itself is supplementary, not in the paper |

All three write to `artifact/output/` on the host if you bind-mount it (shown
below). If you don't mount anything, everything stays inside the
ephemeral container and is lost when it exits. Each also pays a short
extra compile the first time it runs in a given container, even though
the image is prebuilt (see "Note on recompiles" at the end).

---

### Experiment 1: performance benchmark + graph sizes

```sh
mkdir -p artifact/output
docker run --rm -v "$(pwd)/artifact/output:/zippel/artifact/output" zippel-ae \
  bash -c "artifact/scripts/run_benchmark.sh && python3 artifact/scripts/process_benchmark.py"
```

Runs all 9 systems the paper benchmarks (Schnorr, Sumcheck, Bulletproofs
IPA, KZG, Pari, Groth16, PST13, Hyrax, Spartan) at each system's
paper-reported size (`2^18`, fixed for Schnorr) across threads
`{1,2,4,8}`, then renders two markdown tables from the resulting CSV.
Narrow it for a quick check instead of the full sweep:

```sh
docker run --rm -v "$(pwd)/artifact/output:/zippel/artifact/output" -e SYSTEMS=schnorr,kzg -e THREADS=1,2 zippel-ae \
  bash -c "artifact/scripts/run_benchmark.sh && python3 artifact/scripts/process_benchmark.py"
```

**What to expect:**

- **Performance table** (Figure 7, page 13): non-comment line counts for
  the Zippel protocol and its native baseline, ratio of native baseline
  time to Zippel time per thread count, plus a single-thread verifier
  ratio. Values are wall-clock and will not match the paper exactly:
  they're hardware-dependent, and single-sample timings for very fast
  protocols (Schnorr) can be noisy (see `benchmarks/README.md`'s
  `PROVER_SAMPLES` for averaging). Expect the same qualitative story:
  parity or moderate speedup on most systems, Spartan closest to parity
  but sometimes slower (roughly 0.85 to 1.5x depending on thread count)
  because its zippel encoding uses generic curve infrastructure where the
  native baseline is hand-specialized for one curve.
- **Graph-size table** (supplementary, the paper has no table for this):
  Prover/verifier Graph IR node counts. Until this artifact, the counting
  logic (`ZippelHandler::prover_graph()/verifier_graph()`) was wired up
  for only one of the nine systems (Hyrax), in a standalone debug binary,
  not the main benchmark driver. We added it for the other eight while
  building this artifact, so treat these numbers as new rather than a
  reproduction of anything already published.

Runtime: single-threaded Groth16 alone took about 137s end to end on our
hardware (about 77s of that is Zippel's own compile step: unrolling
KZG's SRS-evaluation loops at `2^18` size is the dominant cost, not
proving). Hyrax, PST13, and Spartan are comparable or heavier at `2^18`.
We have not timed the full 9-system by 4-thread sweep end to end. Budget
on the order of an hour, more on slower hardware.

**LoC for all 30 protocols (Figure 6).** The performance table above only
covers the 9 systems with a native baseline to compare against. Figure 6
lists all 30 protocols in the paper by line count alone, with no build or
Docker needed to check it:

```sh
python3 artifact/scripts/report_loc.py
```

These numbers will not match the submitted paper's Figure 6 for most
protocols. Two things changed since submission: `zippel-fmt` (see the
repo layout table above) did not exist yet, so the example files were not
written in its canonical style, and reformatting them afterward moved
line counts on its own; and several protocols' `where`-clause constraints
were revised afterward (see the completeness-count accounting under
Experiment 3).

This doesn't undercut the paper's conciseness claim. The native baseline
side of the comparison is untouched (vendored, external code we don't
format or edit), so all the movement above is on the Zippel side, and
Zippel is still substantially shorter than its native baseline for every
one of the 9 benchmarked systems:

| System | LoC Zippel (submitted to now) | LoC Native | Native/Zippel (submitted to now) |
|---|---|---|---|
| Schnorr | 7 to 7 | 186 | 26.6x to 26.6x |
| Sumcheck | 58 to 90 | 1544 | 26.6x to 17.2x |
| Bulletproofs | 79 to 77 | 166 | 2.1x to 2.1x |
| KZG | 14 to 24 | 527 | 37.6x to 22.0x |
| Pari | 79 to 101 | 1141 | 14.4x to 11.3x |
| Groth16 | 36 to 88 | 458 | 12.7x to 5.2x |
| PST13 | 54 to 82 | 250 | 4.6x to 3.0x |
| Hyrax | 47 to 49 | 277 | 5.9x to 5.7x |
| Spartan | 461 to 419 | 1867 | 4.0x to 4.5x |

Groth16 moved the most, but it is still 5.2x shorter than its native baseline.
Everything else moved by less. Bulletproofs and Hyrax barely moved at
all, close to a pure reformatting effect with no real code change. Spartan
actually got shorter.

---

### Experiment 2: completeness/soundness correctness suite

```sh
docker run --rm zippel-ae bash artifact/scripts/run_correctness.sh
```

Runs `analyses/tests/gb_snapshots`: asserts the completeness and
special-soundness analyses actually pass (not just "compiles"), and
snapshots the computed Gröbner basis for regression detection. No output
file, read the printed summary. Finishes in about 15s.

To run just one trial (e.g. while debugging): `run_correctness.sh
'completeness::schnorr'` (substring match).

**What to expect:**

```
running 83 tests
...
test result: ok. 28 passed; 0 failed; 55 ignored; ...

== Summary by trial group ==
completeness  pass=24  ignored=13  failed=0
soundness     pass=4   ignored=5   failed=0
knowledge     pass=0   ignored=37  failed=0
```

`0 failed` is the thing to check, that's a pass. The `ignored` counts are
expected, not artifact bugs:

- **completeness** (13 ignored): protocols whose Gröbner basis computation
  is too slow to include in a fast regression suite (includes `spartan`,
  the heaviest protocol in the codebase, and the whole HyperPlonk family;
  see Experiment 3 for their actual outcome under a real timeout).
- **soundness** (5 ignored): `okamoto` fails because Pedersen commitments
  aren't perfectly binding, so the witness isn't unique. The submitted
  paper gives this exact reason as an illustrative limitation, not a bug.
  `cds`/`coin_proof` are marked ignored because the paper reports they
  aren't special-sound either. `commitment_equality`/`pedersen_eq` are
  two newer protocols, not in the paper at all, that currently lack a
  valid extractor.
- **knowledge** (37 ignored, unconditionally): unrelated to this paper,
  an internal trial for a separate zero-knowledge-leak analysis. Safe to
  ignore.

This suite covers a superset of the paper's protocols for both
properties: for completeness, all 30 from the paper plus 7 extra
pedagogical ones; for special-soundness, all 6 of the paper's candidates
(Schnorr, Multi-Schnorr, Chaum-Pedersen, Okamoto, CDS Disjunction, E-Cash
Coin) plus 3 more not in the paper (`okamoto_elgamal`,
`commitment_equality`, `pedersen_eq`). Its 24 completeness passes are not
the paper's "N of 30" number, that comes from Experiment 3. Its
special-soundness split does match the paper's exact result on the 6
protocols the paper actually discusses: the first 3 pass, the other 3
are marked ignored.

---

### Experiment 3: inline vs. no-inline completeness sweep

```sh
mkdir -p artifact/output
docker run --rm -v "$(pwd)/artifact/output:/zippel/artifact/output" zippel-ae \
  bash -c "artifact/scripts/run_inline.sh && python3 artifact/scripts/process_inline.py"
```

Runs all 30 of the paper's protocols, with and without the inlining pass,
through the completeness analysis (20-minute timeout, 16GiB memory limit
per run, both overridable via `--timeout`/`--memory-limit-mb`, see the
comments at the top of `run_inline.sh`). For a quick check on a few
protocols instead of all 60 runs:

```sh
docker run --rm -v "$(pwd)/artifact/output:/zippel/artifact/output" zippel-ae \
  bash -c "artifact/scripts/run_inline.sh --timeout 90 --protocols schnorr,groth16,ipa,hyperplonk && python3 artifact/scripts/process_inline.py"
```

**What to expect, and why it differs from the paper.** The submitted
paper's §9.3 says: "All 30 protocols are perfectly complete... Zippel can
automatically verify 20 of them (66.7%)." Since submission we found and
fixed real bugs in our protocol encodings. The corrected count is **18 of
30**, not 20:

- **Minus 5** (previously reported complete, actually weren't): the whole
  HyperPlonk family plus Dekart were false positives from a bug that has
  since been fixed. They now correctly show `timeout`/`oom`/`crashed`
  instead of `ok`.
- **Plus 3** (previously reported incomplete, actually were complete):
  Groth16, KZH, and Bulletproofs (`ipa`) each had a `where`-clause missing
  real constraints, making the relation too weak to check. Fixed, and all
  three now show `ok`.
- Net: 20 minus 5 plus 3 equals **18**. We intend to correct the "20" in
  the next revision of the paper.

So a full run of this experiment will not match the submitted paper's "20
of 30." It should match 18. If your run's `ok` count differs from 18,
that's worth investigating; a difference from 20 is expected and correct.

Sample row from a validation run:

```
| Protocol | Nodes | P/V/D Inline | P/V/D No-inline | Time Inline | Time No-inline |
| groth16  | 150   | 50/70/5      | 210/230/2        | 15.4s        | timeout        |
```

Status meanings: `ok` means the analysis ran and confirmed completeness.
`timeout` means it exceeded the 20-minute limit. `oom` means it hit the
memory limit (a real, traced grand-product blowup in HyperPlonk's
permutation check: the 6-way product of independent challenge-variable
factors hits the mathematical maximum term count with nothing to cancel,
not a bug in the limiter itself). `crashed`/`incomplete` mean a caught
panic, or a completeness check that ran to completion and genuinely
failed.

**Runtime**: a full 30x2 sweep took about 5.4 hours (sum of per-run wall
time) in a prior measurement. Treat that as a rough estimate, not a
guarantee, but it comfortably fits a one-day budget either way. Consider
starting it and doing something else while it runs rather than waiting on
it interactively.

## Note on recompiles

The Docker image prebuilds the whole workspace, but each of
`run_correctness.sh`, `run_benchmark.sh`, and `run_inline.sh` still
triggers its own partial recompile (tens of seconds to a couple of
minutes) the first time that specific command runs. This is normal, not
a broken image.

Because `docker run --rm` containers are ephemeral, this cost repeats on
every separate `docker run` invocation, not just once overall: a fresh
container has no memory of a recompile from a previous one. If you're
running these scripts repeatedly (e.g. iterating on a size or protocol
subset), avoid re-paying it by also mounting a persistent volume at
`/zippel/target`:

```sh
docker volume create zippel-ae-target
docker run --rm \
  -v zippel-ae-target:/zippel/target \
  -v "$(pwd)/artifact/output:/zippel/artifact/output" \
  zippel-ae bash -c "..."
```

Subsequent runs against the same volume reuse whatever got compiled
before. Don't bind-mount the whole repo over `/zippel` for this purpose:
that replaces the image's prebuilt `target/` with whatever's on the host
(likely nothing), discarding the prebuild entirely.