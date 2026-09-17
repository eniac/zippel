#!/usr/bin/env bash
# Experiment 2: completeness/soundness correctness suite
# (analyses/tests/gb_snapshots, Singular backend).
#
# This validates that the completeness/special-soundness analyses
# themselves have not regressed against their committed Groebner-basis
# snapshots. It does not by itself reproduce a specific paper figure --
# the paper's "N of 30 protocols provably complete" headline number comes
# from run_inline.sh instead. See ../README.md for the full mapping.
#
# Usage:
#   artifact/scripts/run_correctness.sh [FILTER]
#
# FILTER (optional) is forwarded as libtest-mimic's substring test-name
# filter, e.g. `completeness::schnorr` or `soundness::` -- useful for
# smoke-testing this script itself without paying for the full suite.
# With no FILTER, runs everything (fast: ~15s on the full suite).

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(dirname "${SCRIPT_DIR}")/.."
cd "${ROOT}"

FILTER="${1:-}"

LOG="$(mktemp)"
trap 'rm -f "${LOG}"' EXIT

echo "== Completeness/soundness correctness suite (analyses/tests/gb_snapshots) =="
set +e
if [ -n "${FILTER}" ]; then
    cargo test -p analyses --test gb_snapshots --release -- "${FILTER}" 2>&1 | tee "${LOG}"
else
    cargo test -p analyses --test gb_snapshots --release 2>&1 | tee "${LOG}"
fi
STATUS="${PIPESTATUS[0]}"
set -e

echo
echo "== Summary by trial group =="
for group in completeness soundness knowledge; do
    pass=$(grep -c "^test ${group}::.* \.\.\. ok$" "${LOG}" || true)
    ignored=$(grep -c "^test ${group}::.* \.\.\. ignored$" "${LOG}" || true)
    failed=$(grep -c "^test ${group}::.* \.\.\. FAILED$" "${LOG}" || true)
    printf "%-13s pass=%-3s ignored=%-3s failed=%-3s\n" "${group}" "${pass}" "${ignored}" "${failed}"
done

exit "${STATUS}"
