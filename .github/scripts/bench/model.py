"""The results of one comparison: what run.py writes to results.json and
report.py reads back. README.md documents the JSON; this module defines it.

results.json is produced in the job that runs PR code, so every `from_json`
validates; `to_json` writes the same shape back.
"""

from dataclasses import asdict, dataclass, field
import re

from untrusted import distinct, dump, list_of, load, machine_int, number, record, require, text

# Native timings and instruction profiles each take this many samples per phase.
SAMPLES = 3
SIDES = ("base", "head")
STATUSES = ("ok", "failed", "timeout", "budget", "unsupported")
INSTRUCTION_STATUSES = ("ok", "timeout", "unavailable")


def _short(value):
    return text(value, 64)


@dataclass(frozen=True)
class Config:
    """How a revision's harness resolved an example. The meaning of each field is
    the harness's; this only bounds what the report shows."""

    sizes: dict
    source: str
    curve: str
    analysis: list | None
    rounds: list

    @classmethod
    def from_json(cls, value):
        # A harness may describe more than the report shows.
        value = record(value, {"sizes", "source", "curve", "analysis", "rounds"}, extra=True)
        sizes = value["sizes"]
        require(type(sizes) is dict and len(sizes) <= 64, "expected bounded sizes")
        analysis = value["analysis"]
        return cls(sizes={_short(name): machine_int(size) for name, size in sizes.items()},
                   source=text(value["source"], 512), curve=text(value["curve"], 128),
                   analysis=None if analysis is None else list_of(analysis, _short, 64),
                   rounds=list_of(value["rounds"], machine_int, 64))


@dataclass(frozen=True)
class Measurement:
    """One harness run: its configuration and the wall time (ms) of each sample
    per phase, phases in the order measured."""

    config: Config
    phases: list
    ms: dict

    @classmethod
    def from_json(cls, value, samples=SAMPLES):
        """Reads the `config`, `phases` and `ms` fields of a harness document or
        of a results case."""
        phases = distinct(list_of(value.get("phases"), _short, 64))
        require(phases, "expected phases")
        ms = value.get("ms")
        require(type(ms) is dict and set(ms) == set(phases), "expected samples for exactly the phases")
        return cls(Config.from_json(value.get("config")), phases,
                   {phase: list_of(ms[phase], number, samples, length=samples) for phase in phases})

    def to_json(self):
        return {"config": asdict(self.config), "phases": self.phases, "ms": self.ms}


@dataclass(frozen=True)
class Counts:
    """Instructions (Ir) of each sample: the harness process and the Singular
    processes it launched."""

    parent: list
    children: list

    def totals(self):
        return [parent + children for parent, children in zip(self.parent, self.children)]

    @classmethod
    def from_json(cls, value, samples=SAMPLES):
        value = record(value, {"parent", "children"})
        return cls(*(list_of(value[key], machine_int, samples, length=samples) for key in ("parent", "children")))


@dataclass
class Case:
    """One example on one side. It starts as `budget` (not reached before the
    deadline) and is filled in as it is measured."""

    status: str = "budget"
    measurement: Measurement | None = None
    workload: str | None = None
    instruction_status: str = "unavailable"
    instructions: dict | None = None

    def to_json(self):
        data = {"status": self.status, "ms": {}, "instruction_status": self.instruction_status,
                "instructions": None if self.instructions is None
                else {phase: asdict(counts) for phase, counts in self.instructions.items()}}
        if self.measurement is not None:
            data.update(self.measurement.to_json())
        if self.workload is not None:
            data["workload"] = self.workload
        return data

    @classmethod
    def from_json(cls, value):
        value = record(value, {"status", "ms", "instruction_status", "instructions"},
                       {"config", "phases", "workload"})
        case = cls(status=value["status"], instruction_status=value["instruction_status"])
        require(case.status in STATUSES, "unknown case status")
        require(case.instruction_status in INSTRUCTION_STATUSES, "unknown instruction status")
        if case.status == "ok":
            case.measurement = Measurement.from_json(value)
            case.workload = value.get("workload")
            require(isinstance(case.workload, str) and re.fullmatch(r"[0-9a-f]{64}", case.workload),
                    "expected a workload hash")
        else:
            require(value["ms"] == {}, "an unmeasured case cannot have samples")
        if case.instruction_status == "ok":
            counts = value["instructions"]
            require(case.measurement is not None and type(counts) is dict
                    and set(counts) == set(case.measurement.phases), "expected counts for exactly the phases")
            case.instructions = {phase: Counts.from_json(counts[phase]) for phase in case.measurement.phases}
        else:
            require(value["instructions"] is None, "an unprofiled case cannot have counts")
        return case


@dataclass
class Row:
    example: str
    base: Case = field(default_factory=Case)
    head: Case = field(default_factory=Case)

    def side(self, name):
        return self.base if name == "base" else self.head


@dataclass
class Results:
    mode: str
    examples: list
    base_sha: str
    head_sha: str
    rows: list
    measurement_seconds: float | None = None
    build_seconds: dict | None = None
    # The runner and tool versions, for whoever reads the raw artifact.
    environment: dict = field(default_factory=dict)

    def to_json(self):
        data = {"mode": self.mode, "examples": self.examples, "base_sha": self.base_sha,
                "head_sha": self.head_sha, "environment": self.environment,
                "rows": [{"example": row.example, "base": row.base.to_json(), "head": row.head.to_json()}
                         for row in self.rows]}
        if self.measurement_seconds is not None:
            data["measurement_seconds"] = self.measurement_seconds
        if self.build_seconds is not None:
            data["build_seconds"] = self.build_seconds
        return dump(data)

    @classmethod
    def from_json(cls, data, request):
        """Results checked against the trusted request they claim to answer."""
        value = record(load(data), {"mode", "examples", "base_sha", "head_sha", "rows"},
                       {"measurement_seconds", "build_seconds", "environment"})
        require(all(value[key] == request[key] for key in ("mode", "examples", "base_sha", "head_sha")),
                "result identity differs from the trusted request")
        rows = value["rows"]
        require(isinstance(rows, list) and len(rows) == len(request["examples"]),
                "result does not contain the exact requested example list")
        parsed = []
        for row, name in zip(rows, request["examples"]):
            row = record(row, {"example", "base", "head"})
            require(row["example"] == name, "result does not contain the exact requested example list")
            parsed.append(Row(name, Case.from_json(row["base"]), Case.from_json(row["head"])))
        sizes = request.get("sizes")
        require(sizes is None or all(case.measurement.config.sizes == sizes for row in parsed
                                     for case in (row.base, row.head) if case.measurement),
                "resolved sizes differ from the requested sizes")
        builds = value.get("build_seconds")
        if builds is not None:
            builds = record(builds, set(SIDES))
            builds = {side: number(builds[side]) for side in SIDES}
        measurement = value.get("measurement_seconds")
        return cls(value["mode"], value["examples"], value["base_sha"], value["head_sha"], parsed,
                   measurement_seconds=None if measurement is None else number(measurement),
                   build_seconds=builds)
