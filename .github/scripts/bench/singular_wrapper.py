"""Stands in for Singular while callgrind.py profiles an analysis: runs the real
Singular under Callgrind, naming its profile after the phase sample the harness
is measuring."""

import os
from pathlib import Path
import sys

root = Path(os.environ["ZIPPEL_BENCH_PROFILE_DIR"])
phase = (root / "phase").read_text()
name, _, index = phase.rpartition(".")
if not name or not index.isdigit():
    sys.exit("Singular launched outside a measured phase")
with (root / "children").open("a") as stream:
    stream.write(phase + "\n")
valgrind = os.environ["ZIPPEL_BENCH_VALGRIND"]
os.execv(valgrind, [valgrind, "--tool=callgrind", "--instr-atstart=yes",
                    f"--callgrind-out-file={root}/child.{phase}.%p.out", f"--log-file={root}/child.%p.log",
                    os.environ["ZIPPEL_BENCH_SINGULAR"], *sys.argv[1:]])
