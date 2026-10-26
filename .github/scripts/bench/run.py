"""Compare job: build each revision's CI harness and measure the requested
examples on both within one time budget, writing results.json (model.py)."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import shutil
import subprocess
import sys
import time

from callgrind import profile
from harness import Harness
from model import SAMPLES, SIDES, Case, Results, Row
from process import environment, execute
from untrusted import dump, load

SUITE = json.loads(Path(__file__).with_name("suite.json").read_bytes())


def build(tree, directory, target_directory, timeout):
    """Build the revision's own CI harness, which matches its library API."""
    directory.mkdir(parents=True, exist_ok=True)
    start = time.monotonic()
    log = directory / "build.jsonl"
    try:
        execute(["cargo", "build", "--locked", "--release", "--message-format=json", "-p", "zippel", "--bench", "ci"],
                tree, environment(CARGO_TARGET_DIR=str(target_directory)), timeout, log)
    except ValueError:
        _log_build_errors(tree, log)
        raise
    messages = [json.loads(line) for line in log.read_text().splitlines()]
    executables = {message["executable"] for message in messages
                   if message.get("reason") == "compiler-artifact"
                   and message.get("target", {}).get("name") == "ci" and message.get("executable")}
    if len(executables) != 1:
        raise ValueError("Cargo did not identify one benchmark executable")
    # Both revisions share the target directory, so keep this one's copy.
    binary = directory / "ci"
    shutil.copy2(executables.pop(), binary)
    return Harness(str(binary), tree), time.monotonic() - start


def _log_build_errors(tree, log):
    # The build logs are not uploaded; put Cargo's errors in the job log.
    print(f"{tree.name} build failed:", file=sys.stderr)
    for line in log.read_text().splitlines() if log.exists() else []:
        message = json.loads(line)
        if message.get("reason") == "compiler-message" and message["message"]["level"] == "error":
            print(message["message"]["rendered"], file=sys.stderr)
    errors = log.with_suffix(".stderr")
    if errors.exists():
        print("\n".join(errors.read_text().splitlines()[-20:]), file=sys.stderr)


def workload(tree, source):
    """What a case measures besides the library: the directory holding the
    example's protocol (its code and inputs), shared example code and the CI
    harness. Directories a revision lacks contribute nothing."""
    tree = tree.resolve()
    example = (tree / source).resolve().parent
    if not example.is_relative_to(tree):
        raise ValueError("protocol source outside the checkout")
    files = sorted({path for directory in (example, tree / "examples/common", tree / "benches/ci")
                    if directory.is_dir() for path in directory.rglob("*") if path.is_file()})
    return hashlib.sha256(b"".join(path.relative_to(tree).as_posix().encode() + path.read_bytes()
                                   for path in files)).hexdigest()


class Comparison:
    """Measures each requested example on both revisions until the deadline."""

    def __init__(self, request, harnesses, directory, deadline):
        self.mode = request["mode"]
        self.sizes = request.get("sizes")
        self.request = request
        self.harnesses = harnesses
        self.directory = directory
        self.deadline = deadline

    def remaining(self):
        return self.deadline - time.monotonic()

    def run(self):
        started = time.monotonic()
        registered = {side: self.harnesses[side].examples(self.directory / f"{side}-list.json", self.remaining())
                      for side in SIDES}
        rows = [Row(name, *(Case() if self.supports(registered[side], name) else Case("unsupported")
                            for side in SIDES))
                for name in self.request["examples"]]
        for index, row in enumerate(rows):
            # Alternate which side goes first, so drift during the run favours neither.
            for side in SIDES if index % 2 == 0 else SIDES[::-1]:
                self.time(row.side(side), side, row.example, self.directory / f"{index}-{side}-native")
            for side in SIDES:
                self.count(row.side(side), side, row.example, self.directory / f"{index}-{side}-instructions")
        return Results(self.mode, self.request["examples"], self.request["base_sha"], self.request["head_sha"], rows,
                       measurement_seconds=time.monotonic() - started, environment=runner())

    def supports(self, registered, name):
        """Whether a revision registers the example, with analyses to run for `analyze`."""
        analyses = registered.get(name)
        return analyses is not None and (self.mode == "run" or bool(analyses))

    def time(self, case, side, name, stage):
        """Native wall times. A case not reached before the deadline stays `budget`."""
        if case.status != "budget" or self.remaining() <= 0:
            return
        stage.mkdir()
        harness = self.harnesses[side]
        try:
            case.measurement = harness.measure(self.mode, name, self.sizes, SAMPLES, stage / "native.json",
                                               self.remaining())
            case.workload = workload(harness.tree, case.measurement.config.source)
            case.status = "ok"
        except subprocess.TimeoutExpired:
            case.status = "timeout"
        except (ValueError, OSError) as error:
            print(f"{name} {side} native: {error!r}", file=sys.stderr)
            case.status, case.measurement = "failed", None

    def count(self, case, side, name, stage):
        """Instruction counts, for a case whose wall times were measured."""
        if case.status != "ok" or self.remaining() <= 0:
            return
        stage.mkdir()
        try:
            case.instructions = profile(self.harnesses[side], self.mode, name, self.sizes, SAMPLES,
                                        case.measurement.phases, stage, self.remaining())
            case.instruction_status = "ok"
        except subprocess.TimeoutExpired:
            case.instruction_status = "timeout"
        except (ValueError, OSError) as error:
            print(f"{name} {side} profile: {error!r}", file=sys.stderr)


def runner():
    """The machine and tool versions, for whoever reads the raw results."""
    versions = {}
    for name, args in (("rust", ["rustc", "--version"]), ("valgrind", ["valgrind", "--version"]),
                       ("singular", ["Singular", "--version"])):
        try:
            output = subprocess.check_output(args, text=True, stderr=subprocess.STDOUT, timeout=5)
            versions[name] = output.splitlines()[0][:200]
        except (OSError, subprocess.SubprocessError, IndexError):
            versions[name] = "unavailable"
    cpu = platform.machine()
    cpuinfo = Path("/proc/cpuinfo")
    if cpuinfo.exists():
        cpu = next((line.partition(":")[2].strip() for line in cpuinfo.read_text().splitlines()
                    if line.startswith("model name")), cpu)
    return {"platform": platform.platform(), "cpu": cpu, "threads": 1, **versions}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--base-dir", type=Path, required=True)
    parser.add_argument("--head-dir", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    # Binaries live under the output's siblings and run from each checkout,
    # so every derived path must be absolute.
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    # The trusted request job's output, passed through the environment.
    request = load(os.environ["REQUEST"].encode())
    (output / "request.json").write_bytes(dump(request))
    trees = {"base": args.base_dir.resolve(), "head": args.head_dir.resolve()}
    for side, tree in trees.items():
        actual = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=tree, text=True).strip()
        if actual != request[f"{side}_sha"]:
            raise ValueError("checkout does not match the frozen request")
    # The one budget covers builds and measurement; bench.yml's job
    # timeout only adds runner setup and uploads on top.
    deadline = time.monotonic() + SUITE["budget_seconds"]
    harnesses, build_seconds = {}, {}
    for side, tree in trees.items():
        harnesses[side], build_seconds[side] = build(tree, output.parent / f"{output.name}-build-{side}",
                                                     output.parent / f"{output.name}-target",
                                                     deadline - time.monotonic())
    results = Comparison(request, harnesses, output, deadline).run()
    results.build_seconds = build_seconds
    (output / "results.json").write_bytes(results.to_json())


if __name__ == "__main__":
    main()
