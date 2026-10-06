#!/usr/bin/env python3
"""Render run_soundness.sh's JSON into a markdown table of per-protocol
results (supplementary; the submitted paper's special-soundness claim in
Section 9.3 is prose-only).

Columns:
    Protocol | Pass | Time | Status | Reason

Rows are the paper's Figure 6 soundness candidates (paper.py) present in
the run. Pass indicates whether the analysis established special
soundness; Figure 6's Sound. column gives the expected mark. A cross
expects the analysis to fail or time out (E-Cash Coin may time out under
the configured budget); crashes and out-of-memory results are always
unexpected. Time is total_ms (build+gb+run), as in process_completeness.py,
or "-" when the analysis stopped before reporting it. Below the table:
the minimum, maximum and median time over the verified runs.
Exit nonzero if any protocol has an unexpected outcome.

Usage:
    artifact/scripts/process_soundness.py [JSON_PATH]

JSON_PATH defaults to artifact/output/soundness_results.json.
"""

import json
import sys

from paper import OK, rows
from process_completeness import fmt_ms, timing_summary, total_ms

DEFAULT_JSON = "artifact/output/soundness_results.json"

PASS_MARK = "✓"  # ✓
FAIL_MARK = "✗"  # ✗

# Expected coverage, not a claim that the unsuccessful candidates are
# unsound. These are limitations of the current analysis (see ../README.md).
EXPECTED = {
    protocol: ("ok",) if mark == OK else ("failed", "timeout")
    for _, protocol, mark in rows("soundness")
}
LABELS = {protocol: label for label, protocol, _ in rows("soundness")}


def markdown_cell(value):
    return " ".join(str(value).splitlines()).replace("|", "\\|")


def fmt_time(result):
    ms = total_ms(result)
    return "-" if ms is None else fmt_ms(ms)


def main():
    json_path = sys.argv[1] if len(sys.argv) > 1 else DEFAULT_JSON
    with open(json_path) as f:
        data = json.load(f)
    if data.get("analysis") != "soundness":
        sys.exit(f"expected soundness results in {json_path}")
    results = data["results"]
    if not results:
        sys.exit(f"no soundness results found in {json_path}")

    print(f"Source: {json_path} ({len(results)} rows, timeout={data.get('timeout_s')}s, "
          f"memory_limit_mb={data.get('memory_limit_mb')})")
    print()
    print("| Protocol | Pass | Time | Status | Reason |")
    print("|---|---|---|---|---|")
    unexpected = []
    seen = set()
    for result in results:
        name = result["protocol"]
        status = result.get("status", "?")
        mark = PASS_MARK if status == "ok" else FAIL_MARK
        reason = markdown_cell(result.get("error") or "")
        print(f"| {markdown_cell(LABELS.get(name, name))} | {mark} | {fmt_time(result)} | "
              f"{markdown_cell(status)} | {reason} |")
        expected = EXPECTED.get(name)
        if expected is None:
            unexpected.append(f"{name}: not a soundness candidate in the paper's Figure 6")
        elif status not in expected:
            unexpected.append(f"{name}: expected {' or '.join(expected)}, got {status}")
        if name in seen:
            unexpected.append(f"{name}: duplicate result")
        seen.add(name)

    pass_count = sum(1 for r in results if r.get("status") == "ok")
    failed_count = sum(1 for r in results if r.get("status") == "failed")
    timeout_count = sum(1 for r in results if r.get("status") == "timeout")
    print()
    print(f"soundness pass={pass_count} failed={failed_count} timeout={timeout_count} "
          f"unexpected={len(unexpected)}")
    verified = [(total_ms(r), LABELS.get(r["protocol"], r["protocol"])) for r in results
                if r.get("status") == "ok" and total_ms(r) is not None]
    if verified:
        print(timing_summary(verified))
    if unexpected:
        print()
        for message in unexpected:
            print(message)
        sys.exit(1)


if __name__ == "__main__":
    main()
