#!/usr/bin/env python3
"""run_examples.py - build and run every registered Zippel example.

Reports completeness / soundness / verification pass-or-fail for each example.
Each example exits non-zero on verification failure, so the exit status of
``cargo run --example <name>`` is the pass/fail signal. Examples are launched
through cargo (never the raw target .exe) so the RUST_MIN_STACK value in
.cargo/config.toml applies. Slow Groebner-analysis examples (e.g. r1cs_sigma)
are bounded by a per-example timeout.

Usage:
  python run_examples.py [-t SECS] [-n] [-l] [--skip a,b] [PATTERN ...]

  -t/--timeout SECS  per-example timeout in seconds (default 300; 0 disables)
  -n/--no-build      skip the initial `cargo build --examples`
  -l/--list          list example names and exit
  --skip a,b         comma/space-separated example names to skip (also $SKIP)
  PATTERN            optional glob(s); only matching example names are run

Exit status: 0 if every example that ran passed; 1 if any failed or timed out.
"""
from __future__ import annotations

import argparse
import fnmatch
import os
import re
import subprocess
import sys
import time

REPO = os.path.dirname(os.path.abspath(__file__))
CARGO_TOML = os.path.join(REPO, "Cargo.toml")


def example_names() -> list[str]:
    """Names of the explicit [[example]] targets (autoexamples = false).

    The ``name = "..."`` line always immediately follows the [[example]]
    header. Text mode + universal newlines makes this robust to CRLF endings
    (the reason the equivalent sed/grep one-liner mis-parsed on Windows).
    """
    names: list[str] = []
    in_example = False
    with open(CARGO_TOML, "r", encoding="utf-8") as fh:
        for raw in fh:
            line = raw.strip()
            if line == "[[example]]":
                in_example = True
            elif in_example:
                m = re.match(r'name\s*=\s*"([^"]+)"', line)
                if m:
                    names.append(m.group(1))
                    in_example = False
                elif line.startswith("["):
                    in_example = False
    return names


def kill_tree(pid: int) -> None:
    """Kill a process and all its descendants.

    ``cargo run`` spawns the example as a grandchild, so killing only the
    direct child leaves the native example .exe running and burning CPU. On
    Windows the whole tree is reaped with ``taskkill /T``; elsewhere via the
    process group created with ``start_new_session=True``.
    """
    if sys.platform == "win32":
        subprocess.run(
            ["taskkill", "/F", "/T", "/PID", str(pid)],
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )
    else:
        import signal

        try:
            os.killpg(os.getpgid(pid), signal.SIGKILL)
        except OSError:
            try:
                os.kill(pid, signal.SIGKILL)
            except OSError:
                pass


def run_one(name: str, timeout: float) -> tuple[str, int | None, float]:
    """Run one example. Returns (status, returncode, elapsed_seconds)."""
    popen_kwargs: dict = {"cwd": REPO}
    if sys.platform != "win32":
        popen_kwargs["start_new_session"] = True  # own group for killpg
    start = time.monotonic()
    try:
        proc = subprocess.Popen(
            ["cargo", "run", "-q", "--example", name], **popen_kwargs
        )
    except FileNotFoundError:
        print("run_examples.py: `cargo` not found on PATH", file=sys.stderr)
        sys.exit(2)
    try:
        rc = proc.wait(timeout=timeout if timeout > 0 else None)
    except subprocess.TimeoutExpired:
        kill_tree(proc.pid)
        try:
            proc.wait(timeout=15)
        except subprocess.TimeoutExpired:
            pass
        return "timeout", None, time.monotonic() - start
    return ("ok" if rc == 0 else "fail"), rc, time.monotonic() - start


def parse_skip(arg: str | None) -> set[str]:
    raw: list[str] = []
    if arg:
        raw += re.split(r"[,\s]+", arg)
    raw += re.split(r"[,\s]+", os.environ.get("SKIP", ""))
    return {x for x in raw if x}


def main() -> int:
    try:
        sys.stdout.reconfigure(line_buffering=True)  # keep ordering vs children
    except Exception:
        pass

    ap = argparse.ArgumentParser(
        prog="run_examples.py",
        description="Build and run every registered Zippel example.",
    )
    ap.add_argument(
        "-t", "--timeout", type=float, default=300,
        help="per-example timeout in seconds (default 300; 0 disables)",
    )
    ap.add_argument(
        "-n", "--no-build", action="store_true",
        help="skip the initial `cargo build --examples`",
    )
    ap.add_argument(
        "-l", "--list", action="store_true",
        help="list example names and exit",
    )
    ap.add_argument(
        "--skip", default=None,
        help="comma/space-separated example names to skip (also $SKIP)",
    )
    ap.add_argument(
        "patterns", nargs="*", metavar="PATTERN",
        help="glob(s); only matching example names are run",
    )
    args = ap.parse_args()

    names = example_names()
    if args.list:
        print("\n".join(names))
        return 0

    skip = parse_skip(args.skip)
    selected = [
        n for n in names
        if not args.patterns or any(fnmatch.fnmatch(n, p) for p in args.patterns)
    ]

    flt = f", filter={args.patterns}" if args.patterns else ""
    skp = f", skip={sorted(skip)}" if skip else ""
    print(
        f"run_examples.py: {len(names)} registered examples, "
        f"timeout={args.timeout:g}s{skp}{flt}"
    )

    if not args.no_build:
        print("==> cargo build --examples")
        if subprocess.run(["cargo", "build", "--examples"], cwd=REPO).returncode != 0:
            print("run_examples.py: build failed", file=sys.stderr)
            return 1

    passed: list[str] = []
    failed: list[str] = []
    timedout: list[str] = []
    skipped: list[str] = []

    for name in selected:
        if name in skip:
            print(f"=== SKIP    {name}")
            skipped.append(name)
            continue
        print(f"=== RUN     {name}")
        status, rc, elapsed = run_one(name, args.timeout)
        if status == "ok":
            print(f"--- OK      {name}  ({elapsed:.1f}s)")
            passed.append(name)
        elif status == "timeout":
            print(f"--- TIMEOUT {name}  (after {args.timeout:g}s)")
            timedout.append(name)
        else:
            print(f"--- FAIL    {name}  (exit {rc}, {elapsed:.1f}s)")
            failed.append(name)

    ran = len(passed) + len(failed) + len(timedout)
    print("\n==================== SUMMARY ====================")
    print(f"passed:   {len(passed)} / {ran} run")
    if failed:
        print(f"failed:   {len(failed)}  -> {' '.join(failed)}")
    if timedout:
        print(f"timedout: {len(timedout)}  -> {' '.join(timedout)}")
    if skipped:
        print(f"skipped:  {len(skipped)}  -> {' '.join(skipped)}")

    return 0 if not failed and not timedout else 1


if __name__ == "__main__":
    sys.exit(main())
