# PR benchmark scripts

`bench.yml` runs `/bench` (see CONTRIBUTING.md) in three jobs, one script each:

| Job | Script | Does |
|---|---|---|
| request | `command.py` | Parses and authorizes the comment; freezes the commits to compare |
| compare | `run.py` | Builds both revisions' harnesses; measures within `suite.json`'s budget |
| report | `report.py` | Validates `results.json` against the request; updates the PR comment |

They share:

- `untrusted.py`: strict, bounded JSON reading for data that PR code produced.
- `model.py`: the `results.json` schema as dataclasses, written by `run.py` and
  validated by `report.py`.
- `harness.py`: the CI harness protocol below.
- `callgrind.py` and `singular_wrapper.py`: instruction counts, including the
  Singular processes an analysis launches.
- `process.py`: running revision code with a time limit and output bound.
- `github.py`: the `gh api` client and step outputs.

Run `python3 -m unittest discover -s .github/scripts/bench/tests` after changes.

## Output formats

The PR benchmark and CI read these outputs directly; none of their scripts
parses help text or Rust source. Each revision's harness is the authority on its
example names, sizes, analyses and phases: the scripts pass them through, bound
their size, and escape them as inline code in the report.

`cargo zrun list` prints every registered example name, one per line, in
registry order. CI's Examples job runs each one.

The CI harness (`benches/ci/main.rs`) is built with
`cargo build --release --bench ci`, and `run.py` runs the executable directly.
It prints exactly one JSON document on stdout:

- `list`: every registered example and the analyses it registers, as
  `[{"name": "kzg", "analyses": ["completeness"]}, ...]`.
- `run EXAMPLE` or `analyze EXAMPLE`, with optional `-s NAME=VALUE` (repeatable)
  and `--samples K` (1 to 3): on success, exit 0 and
  `{"status": "ok", "config": {...}, "phases": [...], "ms": {PHASE: [K samples]}}`.
  `phases` lists the measured phases in order (today `compile`, `prove`,
  `verify` for `run`, and `compile`, `prepare` and each analysis for
  `analyze`), and `ms` has exactly those keys. `config` holds the resolved
  `sizes`, the protocol `source` (relative to the checkout; its directory and
  the shared example and harness code make up the `workload` hash), the
  `curve`, the `analysis` names (`null` for `run`) and the soundness `rounds`.
  On failure, exit 1 and `{"status": "failed", "error": "..."}`.

Malformed arguments are usage errors: clap prints them to stderr and exits 2,
with nothing on stdout.

`run.py` writes `results.json`, which `bench.yml` uploads as `bench-results` and
`report.py` validates and renders. It holds the request's `mode`, `examples`,
`base_sha` and `head_sha`, `measurement_seconds`, `build_seconds` per side, the
runner's `environment`, and one row per example with a `base` and a `head` case.
Each case has a `status` (`ok`, `failed`, `timeout`, `budget` when the time
budget ran out, or `unsupported` when that revision's `list` lacks the example,
or lists no analyses for `analyze`), the harness's `phases`, `ms` and `config`,
a `workload` hash of the sources measured, and `instructions` per phase
(`parent` and Singular `children` counts per sample) with an
`instruction_status` (`ok`, `timeout` or `unavailable`).

The `analysis` bench prints JSON lines, documented in
`benches/analysis/output.rs`.
