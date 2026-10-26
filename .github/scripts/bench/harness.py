"""One revision's CI harness (benches/ci). Every command prints one JSON document
(README.md). A failure's message comes from PR code, so it goes to the job log,
never to the report."""

from dataclasses import dataclass
from pathlib import Path
import sys

from model import Measurement
from process import environment, execute
from untrusted import list_of, load, record, require, text


@dataclass(frozen=True)
class Harness:
    binary: str
    tree: Path

    def examples(self, log, timeout):
        """Each example this revision registers, with the analyses it registers."""
        listed = list_of(self._run(["list"], log, timeout), lambda example: record(example, {"name", "analyses"}), 1024)
        result = {}
        for example in listed:
            # Names are only matched against the request, never shown.
            name = example["name"]
            require(isinstance(name, str) and name not in result, "invalid example list")
            result[name] = list_of(example["analyses"], lambda analysis: text(analysis, 64), 64)
        return result

    @staticmethod
    def arguments(mode, example, sizes, samples):
        """Without sizes, the harness uses the example's own defaults for the mode."""
        sizes = [argument for name, value in (sizes or {}).items() for argument in ("--size", f"{name}={value}")]
        return [mode, example, *sizes, "--samples", str(samples)]

    def measure(self, mode, example, sizes, samples, log, timeout, prefix=(), env=None):
        """Measure one example. `prefix` runs the harness under another program
        (Callgrind) with `env`."""
        document = self._run(self.arguments(mode, example, sizes, samples), log, timeout, prefix, env)
        require(type(document) is dict and document.get("status") == "ok", "benchmark did not report status ok")
        return Measurement.from_json(document, samples)

    def _run(self, args, log, timeout, prefix=(), env=None):
        try:
            execute([*prefix, self.binary, *args], self.tree, env or environment(), timeout, log)
        except ValueError:
            _log_failure(log)
            raise
        return load(log.read_bytes())


def _log_failure(log):
    try:
        error = load(log.read_bytes())["error"]
    except (OSError, ValueError, KeyError, TypeError):
        return
    print(f"harness error: {str(error)[:500]!r}", file=sys.stderr)
