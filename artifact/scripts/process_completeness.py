#!/usr/bin/env python3
"""Render run_completeness.sh's JSON output into a markdown table
(supplementary, not present in the submitted paper, which only has
prose in Section 9.3). See ../README.md for the completeness-count
accounting this table's Pass column substantiates.

Columns:
    Protocol | Pass | Time

Rows are the paper's Figure 6 protocols (paper.py) present in the run,
in Figure 6 order; Dory IPA ("~" in Figure 6) runs at the smaller
instance the paper confirms it at. Pass is a check mark when the analysis verified completeness ("~" for
Dory IPA, verified only at the smaller instance), a cross otherwise. Time is total_ms (build+gb+run) formatted as ms/s when
status is "ok", else the status string itself (timeout/crashed/failed/oom).

Below the table: how many verified, and the minimum, maximum and median
time over the verified runs. Exit nonzero if any protocol's outcome
differs from its Figure 6 Comp. mark.

Usage:
    artifact/scripts/process_completeness.py [JSON_PATH]

JSON_PATH defaults to artifact/output/completeness_results.json.
"""

import json
import statistics
import sys

from paper import NO, PARTIAL, rows

DEFAULT_JSON = "artifact/output/completeness_results.json"

PASS_MARK = "✓"  # ✓
FAIL_MARK = "✗"  # ✗


def total_ms(r):
    parts = [r.get("build_ms"), r.get("gb_ms"), r.get("run_ms")]
    if any(p is None for p in parts):
        return None
    return sum(parts)


def fmt_ms(ms):
    return f"{ms:.1f}ms" if ms < 1000 else f"{ms / 1000:.1f}s"


def timing_summary(verified):
    """One line with the min, max and median of `verified`, a list of
    (total_ms, label) pairs."""
    times = sorted(verified)
    median = statistics.median(ms for ms, _ in times)
    return (f"Analysis time over verified runs: min {fmt_ms(times[0][0])} ({times[0][1]}), "
            f"max {fmt_ms(times[-1][0])} ({times[-1][1]}), median {fmt_ms(median)}.")


def fmt_pass(r, mark):
    if r.get("status") != "ok":
        return FAIL_MARK
    return PARTIAL if mark == PARTIAL else PASS_MARK


def fmt_time(r):
    if r.get("status") != "ok":
        return r.get("status", "?")
    ms = total_ms(r)
    if ms is None:
        return "?"
    return fmt_ms(ms)


def main():
    json_path = sys.argv[1] if len(sys.argv) > 1 else DEFAULT_JSON
    with open(json_path) as f:
        data = json.load(f)

    results = {r["protocol"]: r for r in data["results"]}
    paper = rows("completeness")
    present = [(label, results[protocol], mark) for label, protocol, mark in paper
               if protocol in results]

    print(f"Source: {json_path} ({len(results)} rows, timeout={data.get('timeout_s')}s, "
          f"memory_limit_mb={data.get('memory_limit_mb')})")
    print()

    print("| Protocol | Pass | Time |")
    print("|---|---|---|")
    unexpected = []
    for label, r, mark in present:
        print(f"| {label} | {fmt_pass(r, mark)} | {fmt_time(r)} |")
        if (r.get("status") == "ok") == (mark == NO):
            unexpected.append(f"{label}: Figure 6 has {mark}, the analysis returned {r.get('status')}")
    for protocol in results.keys() - {protocol for _, protocol, _ in paper}:
        unexpected.append(f"{protocol}: not one of the Figure 6 protocols in paper.py")

    verified = [(total_ms(r), label) for label, r, _ in present
                if r.get("status") == "ok" and total_ms(r) is not None]
    print()
    print(f"Automatically verified complete: {len(verified)} of {len(present)} "
          f"Figure 6 protocols present in this run.")
    if verified:
        print(timing_summary(verified))
    print(f"Unexpected outcomes: {len(unexpected)}")
    if unexpected:
        print()
        for message in unexpected:
            print(message)
        sys.exit(1)


if __name__ == "__main__":
    main()
