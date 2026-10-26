"""Instructions (Ir) per measured phase sample under Callgrind, including the
Singular processes an analysis launches.

The harness labels each sample `<phase>.<index>` (benches/ci/profile.rs): it
dumps the parent's counts under that label and writes it to a `phase` file, which
singular_wrapper.py reads to name each child's profile.
"""

import os
from pathlib import Path
import shlex
import shutil
import sys

from model import Counts
from process import environment
from untrusted import require

WRAPPER = Path(__file__).with_name("singular_wrapper.py")
CLIENT_REQUEST = "desc: Trigger: Client Request: "


def profile(harness, mode, example, sizes, samples, phases, directory, timeout):
    """Run one example under Callgrind; per phase, the counts of each sample."""
    valgrind = _which("valgrind")
    directory = directory.resolve()
    env = environment(ZIPPEL_BENCH_PROFILE_DIR=str(directory))
    if mode == "analyze":
        # Analyses launch Singular; a stand-in first on PATH profiles each launch.
        bin_directory = directory / "bin"
        bin_directory.mkdir()
        stand_in = bin_directory / "Singular"
        stand_in.write_text(f'#!/bin/sh\nexec {shlex.quote(sys.executable)} {shlex.quote(str(WRAPPER))} "$@"\n')
        stand_in.chmod(0o755)
        env.update(PATH=f"{bin_directory}{os.pathsep}{env['PATH']}",
                   ZIPPEL_BENCH_VALGRIND=valgrind, ZIPPEL_BENCH_SINGULAR=_which("Singular"))
    prefix = [valgrind, "--tool=callgrind", "--instr-atstart=no", "--separate-threads=no",
              f"--callgrind-out-file={directory}/parent.%p", f"--log-file={directory}/parent.log"]
    harness.measure(mode, example, sizes, samples, directory / "profile.json", timeout, prefix, env)
    return collect(directory, phases, samples)


def collect(directory, phases, samples):
    """Per phase, the parent and children counts of each sample, in sample order."""
    parent = {}
    children = {(phase, index): 0 for phase in phases for index in range(samples)}
    for path in directory.glob("parent.*"):
        if path.suffix == ".log":
            continue
        content = path.read_text()
        key = dump_label(content)
        if key is None:
            continue
        require(key in children, "unexpected parent profile sample")
        require(key not in parent, "duplicate parent profile sample")
        parent[key] = instruction_total(content)
    for path in directory.glob("child.*.out"):
        key = _child_label(path.name)
        require(key in children, "unattributed Singular child profile")
        children[key] += instruction_total(path.read_text())
    require(set(parent) == set(children), "missing parent profile samples")
    launched = directory / "children"
    if launched.exists():
        require(len(launched.read_text().splitlines()) == len(list(directory.glob("child.*.out"))),
                "missing Singular child profile")
    return {phase: Counts([parent[phase, index] for index in range(samples)],
                          [children[phase, index] for index in range(samples)]) for phase in phases}


def dump_label(content):
    """The `(phase, sample)` of a client-request dump; None for other dumps, such as
    the one at exit. Phases may contain dots, so the sample is split from the right."""
    line = next((line for line in content.splitlines() if line.startswith(CLIENT_REQUEST)), None)
    if line is None:
        return None
    phase, _, index = line.removeprefix(CLIENT_REQUEST).rpartition(".")
    return (phase, int(index)) if index.isdigit() else None


def _child_label(name):
    """`child.<phase>.<sample>.<pid>.out`, as singular_wrapper.py names it."""
    parts = name.removeprefix("child.").removesuffix(".out").rsplit(".", 2)
    return (parts[0], int(parts[1])) if len(parts) == 3 and parts[1].isdigit() else None


def instruction_total(content):
    """The Ir total of one Callgrind dump."""
    events = next((line.split()[1:] for line in content.splitlines() if line.startswith("events:")), [])
    # Client-request dumps can have a zero summary placeholder. The final
    # totals line is the completed, non-inclusive event count for this part.
    values = next((line.split()[1:] for line in content.splitlines() if line.startswith("totals:")), [])
    require("Ir" in events and len(events) == len(values), "incomplete Callgrind summary")
    value = int(values[events.index("Ir")])
    require(value > 0, "empty instruction profile")
    return value


def _which(program):
    path = shutil.which(program)
    if path is None:
        raise FileNotFoundError(f"{program} is not installed")
    return path
