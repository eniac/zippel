#!/usr/bin/env python3
"""Render run_soundness.sh's test log into a markdown table of per-trial
results (supplementary; the submitted paper's special-soundness claim in
Section 9.3 is prose-only).

Columns:
    Trial | Pass

Pass is a check mark for a passing trial, a cross for a failing one, or
"ignored" for a trial marked `#[ignore]` (expected -- see ../README.md
for which trials these are and why).

Usage:
    artifact/scripts/process_soundness.py [LOG_PATH]

LOG_PATH defaults to artifact/output/soundness_results.log.
"""

import re
import sys

DEFAULT_LOG = "artifact/output/soundness_results.log"

PASS_MARK = "✓"  # ✓
FAIL_MARK = "✗"  # ✗

LINE_RE = re.compile(r"^test (soundness::\S+)\s+\.\.\.\s+(ok|ignored|FAILED)$")


def parse_log(path):
    trials = []
    with open(path) as f:
        for line in f:
            m = LINE_RE.match(line.strip())
            if m:
                trials.append((m.group(1), m.group(2)))
    return trials


def fmt_result(status):
    if status == "ok":
        return PASS_MARK
    if status == "FAILED":
        return FAIL_MARK
    return "ignored"


def main():
    log_path = sys.argv[1] if len(sys.argv) > 1 else DEFAULT_LOG
    trials = parse_log(log_path)
    if not trials:
        sys.exit(f"no soundness trials found in {log_path}")

    print(f"Source: {log_path} ({len(trials)} trials)")
    print()
    print("| Trial | Pass |")
    print("|---|---|")
    for name, status in trials:
        print(f"| {name} | {fmt_result(status)} |")

    pass_count = sum(1 for _, s in trials if s == "ok")
    ignored_count = sum(1 for _, s in trials if s == "ignored")
    failed_count = sum(1 for _, s in trials if s == "FAILED")
    print()
    print(f"soundness pass={pass_count} ignored={ignored_count} failed={failed_count}")


if __name__ == "__main__":
    main()
