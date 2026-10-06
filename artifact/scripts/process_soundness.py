#!/usr/bin/env python3
"""Render run_soundness.sh's JSON into a markdown table of per-protocol
results (supplementary; the submitted paper's special-soundness claim in
Section 9.3 is prose-only).

Columns:
    Protocol | Pass | Time | Status | Reason

Pass indicates whether the analysis established special soundness; a
cross is expected for five candidates. Time is the benchmark's wall_s,
including protocol loading. Exit nonzero if any reported protocol has
an unexpected outcome. E-Cash Coin may time out under the configured
budget; other timeouts, crashes and out-of-memory results are unexpected.

Usage:
    artifact/scripts/process_soundness.py [JSON_PATH]

JSON_PATH defaults to artifact/output/soundness_results.json.
"""

import json
import sys

DEFAULT_JSON = "artifact/output/soundness_results.json"

PASS_MARK = "✓"  # ✓
FAIL_MARK = "✗"  # ✗

# Expected coverage, not a claim that the unsuccessful candidates are
# unsound. These are limitations of the current analysis (see ../README.md).
EXPECTED_STATUSES = {
    "schnorr": ("ok",),
    "schnorr_3round": ("ok",),
    "cp": ("ok",),
    "okamoto": ("failed",),
    "cds": ("failed",),
    "coin_proof": ("failed", "timeout"),
    "okamoto_elgamal": ("ok",),
    "commitment_equality": ("failed",),
    "pedersen_eq": ("failed",),
}


def markdown_cell(value):
    return " ".join(str(value).splitlines()).replace("|", "\\|")


def fmt_time(result):
    seconds = result.get("wall_s")
    if seconds is None:
        return "?"
    return f"{seconds * 1000:.1f}ms" if seconds < 1 else f"{seconds:.1f}s"


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
        print(f"| {markdown_cell(name)} | {mark} | {fmt_time(result)} | "
              f"{markdown_cell(status)} | {reason} |")
        expected = EXPECTED_STATUSES.get(name)
        if expected is None:
            unexpected.append(f"{name}: no expected outcome registered")
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
    if unexpected:
        print()
        for message in unexpected:
            print(message)
        sys.exit(1)


if __name__ == "__main__":
    main()
