#!/usr/bin/env bash
# Run the groebner Criterion benches with a reproducible build configuration
# and save the results under a named baseline.
#
# Usage:
#   ./bench-baseline.sh <baseline-name> [extra cargo bench args...]
#
# Examples:
#   ./bench-baseline.sh before-i1
#   ./bench-baseline.sh before-i2 --quick                   # criterion args
#   ./bench-baseline.sh before-i2 --warm-up-time 1          # criterion args
#
# All extra args go to criterion (after `--save-baseline <name>`), NOT to cargo.
# To pass cargo flags (e.g. `--features ...`), set CARGO_BENCH_ARGS:
#   CARGO_BENCH_ARGS="--features linked_list_poly" ./bench-baseline.sh after-i5
#
# Notes:
#   - Forces `target-cpu=native` so the AVX2 sev-sweep path is compiled in.
#     Without this flag, src/simd.rs silently falls through to the scalar path.
#   - Captures rustc + CPU info next to the baseline for repro provenance.

set -euo pipefail

if [[ $# -lt 1 ]]; then
    echo "usage: $0 <baseline-name> [cargo bench args...]" >&2
    exit 1
fi

BASELINE="$1"
shift

REPO="$(cd "$(dirname "$0")" && pwd)"
MANIFEST_DIR="$REPO/target/criterion/.baselines"
mkdir -p "$MANIFEST_DIR"

echo "== ark-gb bench baseline '$BASELINE' =="
echo "rustc: $(rustc -V)"
echo "cpu:   $(uname -m) $(grep -m1 -oE 'model name.*' /proc/cpuinfo | sed 's/^model name\s*:\s*//')"

# Provenance manifest sits next to criterion's baselines dir for forensics.
{
    echo "baseline: $BASELINE"
    echo "date: $(date -u +%FT%TZ)"
    echo "rustc: $(rustc -V)"
    echo "host: $(uname -srm)"
    echo "cpu_flags: $(grep -m1 -oE 'flags\s*:.*' /proc/cpuinfo | tr ' ' '\n' | grep -E '^(avx2|bmi2|sse4_2|avx512f)$' | tr '\n' ' ')"
    echo "git_head: $(git -C "$REPO" rev-parse HEAD)"
    echo "git_dirty: $(git -C "$REPO" status --porcelain | wc -l)"
} > "$MANIFEST_DIR/$BASELINE.txt"

export RUSTFLAGS="${RUSTFLAGS:-} -C target-cpu=native"
echo "RUSTFLAGS: $RUSTFLAGS"

cd "$REPO"
# shellcheck disable=SC2086
cargo bench --bench groebner ${CARGO_BENCH_ARGS:-} -- --save-baseline "$BASELINE" "$@"
