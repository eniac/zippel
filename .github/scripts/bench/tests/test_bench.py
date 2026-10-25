"""Behavioral checks for the command, measurement and reporting boundaries."""

import copy
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from common import CATALOG, Command, GitHub, canonical, parse_command, read_json
from command import Unauthorized, prepare, reply, select_revisions
from report import change, publish, render, validate_results
from run import arguments, build, execute, workload, instruction_total, native, parse_profiles, phases

RUN_URL = "https://github.com/eniac/zippel/actions/runs/500"


def request(mode="run", names=None):
    names = names or ["pst13", "ipa"]
    return {"repository": "eniac/zippel", "pr": 42, "comment_id": 55,
            "mode": mode, "examples": names, "sizes": None, "selectors": {"base": None, "head": None},
            "base_sha": "b" * 40, "head_sha": "c" * 40,
            "base_repository": "eniac/zippel", "head_repository": "contributor/zippel",
            "observed_base_sha": "b" * 40, "observed_head_sha": "c" * 40}


def results(req, analyses=("completeness",)):
    rows = []
    for name in req["examples"]:
        analysis = list(analyses) if req["mode"] == "analyze" else None
        config = {"source": f"examples/{name}/{name}.zippel", "curve": "TestCurve",
                  "sizes": req.get("sizes") if req.get("sizes") is not None else {"N": 2},
                  "analysis": analysis, "rounds": [2] if analysis and "soundness" in analysis else []}
        names = phases(req["mode"], config)
        side = {"status": "ok", "ms": {p: [1.0, 2.0, 3.0] for p in names},
                "workload": "d" * 64, "instruction_status": "ok", "config": config,
                "instructions": {p: {"parent": [100, 101, 102], "children": [20, 20, 20]} for p in names}}
        rows.append({"example": name, "base": copy.deepcopy(side), "head": copy.deepcopy(side)})
    return {"mode": req["mode"], "examples": req["examples"],
            "base_sha": req["base_sha"], "head_sha": req["head_sha"], "rows": rows}


class API:
    repository = "eniac/zippel"

    def __init__(self):
        self.pr = {"state": "open", "number": 42, "head": {"sha": "c" * 40, "repo": {"full_name": "contributor/zippel"}},
                   "base": {"sha": "b" * 40}}
        self.comments = []
        self.writes = []
        self.allowed = True

    def repo_path(self, suffix):
        return f"repos/{self.repository}/{suffix}"

    def permission(self, _):
        return self.allowed

    def comment(self, pr, body):
        self.api(self.repo_path(f"issues/{pr}/comments"), "POST", {"body": body})

    def api(self, path, method="GET", data=None, select=None):
        if method != "GET":
            self.writes.append((path, method, data))
            return {}
        if "/commits/" in path:
            selector = path.rsplit("/", 1)[1]
            if selector == "main":
                return {"sha": "b" * 40}
            matches = [letter * 40 for letter in "bcdef" if (letter * 40).startswith(selector)]
            if len(matches) == 1:
                return {"sha": matches[0]}
            raise subprocess.CalledProcessError(1, ["gh", "api"])
        if "/compare/" in path:
            candidate, tip = path.rsplit("/", 1)[1].split("...")
            if candidate == tip:
                return {"status": "identical"}
            ancestors = {"b" * 40: {"d" * 40}, "c" * 40: {"d" * 40, "e" * 40}}
            return {"status": "ahead" if candidate in ancestors.get(tip, set()) else "diverged"}
        if path.endswith("pulls/42"):
            return self.pr
        raise AssertionError(path)

    def pages(self, path):
        return iter(self.comments)


def event(body):
    return {"issue": {"number": 42, "pull_request": {"url": "PR"}},
            "comment": {"id": 55, "body": body, "user": {"type": "User", "login": "maintainer", "id": 9}},
            "repository": {"id": 7, "default_branch": "main"}}


class Commands(unittest.TestCase):
    def test_defaults_and_explicit_names(self):
        self.assertEqual(parse_command(" /bench run "), Command("run", CATALOG["defaults"]))
        self.assertEqual(parse_command("/bench analyze ipa kzg ipa"), Command("analyze", ["ipa", "kzg"]))
        self.assertIsNone(parse_command("ordinary discussion"))
        self.assertIsNone(parse_command("/benchmark results look good"))

    def test_any_registered_example_and_repeatable_sizes(self):
        command = parse_command("/bench run sumcheck --size NUM_VARS_CONST=4 -s MAX_DEGREE_CONST=2")
        self.assertEqual(command, Command("run", ["sumcheck"], sizes={"NUM_VARS_CONST": 4, "MAX_DEGREE_CONST": 2}))
        self.assertEqual(parse_command("/bench analyze okamoto").examples, ["okamoto"])
        self.assertEqual(parse_command("/bench run hyperplonk_zerocheck").examples, ["hyperplonk_zerocheck"])
        for text in ("/bench run kzg --size", "/bench run kzg --size N=-1", "/bench run ipa -s S=1 --size S=2",
                     "/bench run kzg --size N=word", "/bench run kzg --size =2",
                     "/bench run kzg --size 1N=2", "/bench run kzg --size N=18446744073709551616"):
            with self.subTest(text=text), self.assertRaises(ValueError):
                parse_command(text)

    def test_size_flags_replace_catalog_defaults(self):
        self.assertEqual(arguments("ci", "run", "kzg", {"N": 8}),
                         ["ci", "run", "kzg", "--size", "N=8"])
        self.assertEqual(arguments("ci", "run", "sumcheck"), ["ci", "run", "sumcheck"])
        self.assertEqual(arguments("ci", "analyze", "okamoto"), ["ci", "analyze", "okamoto"])

    def test_explicit_commits_can_surround_example_names(self):
        self.assertEqual(parse_command("/bench run --head eeeeeee kzg --base main pst13 kzg"),
                         Command("run", ["kzg", "pst13"], "main", "eeeeeee"))
        self.assertEqual(parse_command("/bench analyze --base DDDDDDD --head pr"),
                         Command("analyze", CATALOG["defaults"], "ddddddd", "pr"))
        for text in ("/bench run --base", "/bench run --head main --head pr",
                     "/bench run --base refs/heads/other", "/bench run --base abc",
                     "/bench run --base $(id)", "/bench run --unknown main"):
            with self.subTest(text=text), self.assertRaises(ValueError):
                parse_command(text)

    def test_invalid_names_and_shell_text_reject_whole_request(self):
        for body in ("/bench", "/bench runtime", "/bench run pst13 missing", "/bench run ../ipa",
                     "/bench analyze schnorr --rounds 2", "/bench analyze spartan", "/bench run ipa;echo", "/bench run $(id)",
                     "/bench run ipa\n/bench run kzg"):
            with self.subTest(body=body), self.assertRaises(ValueError):
                parse_command(body)

    def test_selects_history_on_main_and_fork_pr(self):
        api = API()
        base, head = select_revisions(api, Command("run", ["kzg"], "ddddddd", "eeeeeee"), api.pr, "main")
        self.assertEqual(base, ("d" * 40, "eniac/zippel"))
        self.assertEqual(head, ("e" * 40, "contributor/zippel"))
        base, head = select_revisions(api, Command("analyze", ["kzg"], "pr", "main"), api.pr, "main")
        self.assertEqual(base, ("c" * 40, "contributor/zippel"))
        self.assertEqual(head, ("b" * 40, "eniac/zippel"))
        for selector in ("fffffff", "0123456"):
            with self.subTest(selector=selector), self.assertRaises(ValueError):
                select_revisions(api, Command("run", ["kzg"], selector, "pr"), api.pr, "main")

    def test_fork_only_commit_lookup_and_checkout_repository(self):
        api = API()
        original = api.api
        def fork_only(path, method="GET", data=None, select=None):
            if path == "repos/eniac/zippel/commits/eeeeeee":
                raise subprocess.CalledProcessError(1, ["gh", "api"])
            return original(path, method, data, select=select)
        with patch.object(api, "api", side_effect=fork_only):
            base, _ = select_revisions(api, Command("run", ["kzg"], "eeeeeee", "main"), api.pr, "main")
        self.assertEqual(base, ("e" * 40, "contributor/zippel"))

    def test_authorization_freezes_selected_and_observed_commits(self):
        api = API()
        frozen = prepare(api, event("/bench analyze --base ddddddd kzg --head eeeeeee --size N=8"))
        self.assertEqual((frozen["base_sha"], frozen["head_sha"]), ("d" * 40, "e" * 40))
        self.assertEqual((frozen["observed_base_sha"], frozen["observed_head_sha"]), ("b" * 40, "c" * 40))
        self.assertEqual(frozen["selectors"], {"base": "ddddddd", "head": "eeeeeee"})
        self.assertEqual(frozen["sizes"], {"N": 8})
        self.assertEqual(frozen["head_repository"], "contributor/zippel")
        self.assertEqual(frozen["examples"], ["kzg"])
        self.assertIsNone(prepare(api, event("/benchmark please")))
        self.assertEqual(api.writes, [])

    def test_non_writers_are_rejected_before_parsing(self):
        api = API()
        api.allowed = False
        for body in ("/bench run kzg", "/bench nonsense"):
            with self.subTest(body=body), self.assertRaises(Unauthorized):
                prepare(api, event(body))

    def test_rejection_reply_keeps_quoted_text_inert(self):
        api = API()
        reply(api, 42, "unsupported run examples: ```@everyone`")
        path, method, data = api.writes[0]
        self.assertEqual((path, method), ("repos/eniac/zippel/issues/42/comments", "POST"))
        self.assertEqual(data["body"].count("```"), 2)
        self.assertIn("@everyone'", data["body"])


class Reports(unittest.TestCase):
    def test_failure_is_reported(self):
        api = API()
        self.assertTrue(publish(api, request(), RUN_URL, failure="build failed"))
        self.assertEqual(api.writes[0][0], "repos/eniac/zippel/issues/42/comments")
        self.assertIn("No comparison: build failed", api.writes[0][2]["body"])

    def test_closed_pr_does_not_write(self):
        api = API()
        api.pr["state"] = "closed"
        self.assertFalse(publish(api, request(), RUN_URL, results(request())))
        self.assertEqual(api.writes, [])

    def test_moved_tip_reports_why_instead_of_numbers(self):
        for field in ("head", "base"):
            api = API()
            api.pr[field]["sha"] = "e" * 40
            self.assertTrue(publish(api, request(), RUN_URL, results(request())))
            body = api.writes[0][2]["body"]
            self.assertIn("moved after the request", body)
            self.assertNotIn("| Example / phase |", body)

    def test_explicit_revisions_remain_reportable_after_branch_advances(self):
        api = API()
        req = request()
        req.update(selectors={"base": "ddddddd", "head": "eeeeeee"}, base_sha="d" * 40, head_sha="e" * 40)
        api.pr["base"]["sha"] = api.pr["head"]["sha"] = "f" * 40
        self.assertTrue(publish(api, req, RUN_URL, results(req)))
        self.assertIn("| Example / phase |", api.writes[-1][2]["body"])

    def test_only_bot_report_is_updated(self):
        api = API()
        req = request()
        marker = "<!-- zippel-benchmark-report:run -->\n"
        api.comments = [{"id": 1, "body": marker, "user": {"login": "attacker", "type": "User"}},
                        {"id": 2, "body": render(req, RUN_URL, results(req)), "user": {"login": "github-actions[bot]", "type": "Bot"}}]
        self.assertTrue(publish(api, req, RUN_URL, results(req)))
        self.assertTrue(publish(api, req, RUN_URL, results(req)))
        self.assertTrue(all(w[0].endswith("issues/comments/2") and w[1] == "PATCH" for w in api.writes))

    def test_valid_result_and_changed_workload(self):
        req = request()
        data = results(req)
        body = render(req, RUN_URL, validate_results(canonical(data), req))
        self.assertIn("| +0.0% (noise) |", body)
        self.assertNotIn("**+", body)
        data["rows"][0]["head"]["workload"] = "e" * 64
        body = render(req, RUN_URL, validate_results(canonical(data), req))
        line = next(line for line in body.splitlines() if "pst13 / prove" in line)
        self.assertIn("(workload changed)", line)
        self.assertIn("+0.0% (noise)", line)

    def test_resolved_defaults_are_reported_and_config_changes_are_labelled(self):
        req = request("run", ["sumcheck"])
        data = results(req)
        data["rows"][0]["base"]["config"]["sizes"] = {"NUM_VARS_CONST": 3, "MAX_DEGREE_CONST": 2}
        data["rows"][0]["head"]["config"]["sizes"] = {"NUM_VARS_CONST": 4, "MAX_DEGREE_CONST": 2}
        body = render(req, RUN_URL, validate_results(canonical(data), req))
        self.assertIn("NUM_VARS_CONST=4", body)
        line = next(line for line in body.splitlines() if "sumcheck / prove" in line)
        self.assertIn("(workload changed)", line)
        self.assertIn("+0.0% (noise)", line)
        req["sizes"] = {"NUM_VARS_CONST": 5, "MAX_DEGREE_CONST": 2}
        with self.assertRaises(ValueError):
            validate_results(canonical(data), req)

    def test_forged_targets_units_missing_rows_and_samples(self):
        req = request()
        changes = [lambda r: r.update(measurement_seconds=True),
                   lambda r: r.update(build_seconds={"base": 1, "head": "text"}),
                   lambda r: r.update(head_sha="e" * 40), lambda r: r.update(examples=["kzg"]),
                   lambda r: r["rows"].pop(), lambda r: r["rows"].append(r["rows"][0]),
                   lambda r: r["rows"][0]["base"]["ms"]["prove"].pop(),
                   lambda r: r["rows"][0]["base"]["ms"]["prove"].__setitem__(0, True),
                   lambda r: r["rows"][0]["base"]["instructions"]["prove"].update(parent=[1.5, 2, 3]),
                   lambda r: r["rows"][0]["base"]["instructions"]["prove"].update(parent=[1, 2]),
                   lambda r: r["rows"][0]["base"].update(instruction_status="unavailable"),
                   lambda r: r["rows"][0]["base"].update(workload="<script>"),
                   lambda r: r["rows"][0]["base"]["config"].update(source="../../secret"),
                   lambda r: r["rows"][0]["base"]["config"].update(curve="`injected`"),
                   lambda r: r["rows"][0]["base"]["config"].update(sizes={"N": True}),
                   lambda r: r["rows"][0]["base"]["config"].update(rounds=["2"])]
        for change_result in changes:
            data = results(req)
            change_result(data)
            with self.subTest(change=change_result), self.assertRaises(ValueError):
                validate_results(canonical(data), req)

    def test_analyze_reports_every_registered_analysis(self):
        req = request("analyze", ["schnorr"])
        body = render(req, RUN_URL, validate_results(canonical(results(req, ("completeness", "soundness"))), req))
        rows = [line.split(" | ")[0] for line in body.splitlines() if line.startswith("| schnorr")]
        self.assertEqual(rows, ["| schnorr / compile", "| schnorr / prepare",
                                "| schnorr / completeness", "| schnorr / soundness"])

    def test_analysis_added_by_head_has_no_base_numbers(self):
        req = request("analyze", ["pst13"])
        data = results(req, ("completeness", "soundness"))
        base = data["rows"][0]["base"]
        base["config"].update(analysis=["completeness"], rounds=[])
        for field in ("ms", "instructions"):
            del base[field]["soundness"]
        body = render(req, RUN_URL, validate_results(canonical(data), req))
        line = next(line for line in body.splitlines() if "pst13 / soundness" in line)
        self.assertIn("(workload changed) | — | 121 | — | — | 2.00 | — |", line)

    def test_incomplete_profile_preserves_native_time_with_no_instruction_delta(self):
        req = request("analyze", ["kzg"])
        data = results(req)
        data["rows"][0]["head"].update(instructions=None, instruction_status="timeout")
        body = render(req, RUN_URL, validate_results(canonical(data), req))
        self.assertIn("| timeout | — |", body)
        self.assertIn("| 2.00 | 2.00 |", body)

    def test_only_changes_outside_both_sample_ranges_are_bold(self):
        self.assertEqual(change([100, 101, 102], [101, 102, 103]), "+1.0% (noise)")
        self.assertEqual(change([100, 101, 102], [110, 111, 112]), "**+9.9%**")
        self.assertEqual(change([0, 0, 0], [1, 1, 1]), "—")

    def test_untrusted_json_limits(self):
        for data in (b'{"x":NaN}', b'{"x":Infinity}', b'{"x":1,"x":2}', b" " * (1024 * 1024 + 1)):
            with self.subTest(data=data[:20]), self.assertRaises(ValueError):
                read_json(data)
        metadata = canonical({"body": "x" * (1024 * 1024 + 1)})
        completed = subprocess.CompletedProcess([], 0, stdout=metadata)
        with patch("common.subprocess.run", return_value=completed):
            self.assertEqual(len(GitHub("eniac/zippel").api("repos/eniac/zippel")["body"]), 1024 * 1024 + 1)


class Measurements(unittest.TestCase):
    def test_each_revision_builds_its_own_harness_into_its_own_binary(self):
        with tempfile.TemporaryDirectory() as root:
            directory = Path(root)
            shared = directory / "target"
            shared.mkdir()
            executable = shared / "ci"
            calls = []
            def compile_revision(args, cwd, env, timeout, log):
                calls.append((cwd.name, args[-2:]))
                executable.write_text(cwd.name)
                log.write_text(json.dumps({"reason": "compiler-artifact", "target": {"name": "ci"},
                                           "executable": str(executable)}))
            with patch("run.execute", side_effect=compile_revision):
                base, _ = build(directory / "base", directory / "base-build", shared, 10)
                head, _ = build(directory / "head", directory / "head-build", shared, 10)
            # The shared target directory is rebuilt per side; each keeps its copy.
            self.assertEqual(Path(base).read_text(), "base")
            self.assertEqual(Path(head).read_text(), "head")
            self.assertEqual(calls, [("base", ["--bench", "ci"]), ("head", ["--bench", "ci"])])

    def test_workload_hashes_the_revisions_own_harness(self):
        with tempfile.TemporaryDirectory() as root:
            directory = Path(root)
            for side, harness in (("base", "// one\n"), ("head", "// two\n")):
                tree = directory / side
                (tree / "examples/common").mkdir(parents=True)
                (tree / "examples/kzg").mkdir()
                (tree / "examples/kzg/main.rs").write_text("")
                (tree / "examples/kzg/kzg.zippel").write_text("")
                (tree / "benches/ci").mkdir(parents=True)
                (tree / "benches/ci/main.rs").write_text(harness)
                (tree / "benches/ci/profile.rs").write_text("")
            hashes = {side: workload(directory / side, "kzg", "examples/kzg/kzg.zippel") for side in ("base", "head")}
            self.assertNotEqual(hashes["base"], hashes["head"])

    def test_native_batch_requires_three_samples_per_public_phase(self):
        with tempfile.TemporaryDirectory() as root:
            directory = Path(root)
            expected = {phase: [1.0, 2.0, 3.0] for phase in phases("run", None)}
            def emit(args, cwd, env, timeout, log):
                self.assertEqual(args[-2:], ["--samples", "3"])
                log.write_text(json.dumps({"status": "ok", "ms": expected,
                                           "config": results(request("run", ["kzg"]))["rows"][0]["base"]["config"]}))
            with patch("run.execute", side_effect=emit):
                self.assertEqual(native("binary", directory, "run", "kzg", directory, 10)["ms"], expected)
                expected["prove"].pop()
                with self.assertRaises(ValueError):
                    native("binary", directory, "run", "kzg", directory, 10)

    def test_callgrind_event_column_and_missing_child(self):
        self.assertEqual(instruction_total("events: Dr Ir\nsummary: 0 0\ntotals: 50 123\n"), 123)
        with self.assertRaises(ValueError):
            instruction_total("events: Ir\nsummary: 123\n")
        with self.assertRaises(ValueError):
            instruction_total("events: Ir\nsummary: 0\ntotals: 0\n")
        with tempfile.TemporaryDirectory() as root:
            directory = Path(root)
            for phase in ("compile", "prepare", "analysis"):
                (directory / f"parent.{phase}").write_text(f"desc: Trigger: Client Request: {phase}.0\nevents: Ir\nsummary: 0\ntotals: 100\n")
            (directory / "children").write_text("analysis.0\n")
            with self.assertRaises(ValueError):
                parse_profiles(directory, ("compile", "prepare", "analysis"), samples=1)

    def test_profile_samples_keep_order_and_child_attribution(self):
        with tempfile.TemporaryDirectory() as root:
            directory = Path(root)
            for index, total in enumerate((300, 100, 200)):
                (directory / f"parent.1.{index}").write_text(
                    f"desc: Trigger: Client Request: analysis.{index}\nevents: Ir\nsummary: 0\ntotals: {total}\n")
            (directory / "child.analysis.1.77.out").write_text("events: Ir\ntotals: 5\n")
            (directory / "child.analysis.1.78.out").write_text("events: Ir\ntotals: 7\n")
            (directory / "children").write_text("analysis.1\nanalysis.1\n")
            self.assertEqual(parse_profiles(directory, ("analysis",)),
                             {"analysis": {"parent": [300, 100, 200], "children": [0, 12, 0]}})
            (directory / "parent.1.3").write_text("desc: Trigger: Client Request: analysis.0\nevents: Ir\ntotals: 1\n")
            with self.assertRaises(ValueError):
                parse_profiles(directory, ("analysis",))

    def test_timeout_kills_the_process_group(self):
        with tempfile.TemporaryDirectory() as root:
            directory = Path(root)
            script = "import subprocess,time; p=subprocess.Popen(['sleep','30']); print(p.pid,flush=True); time.sleep(30)"
            with self.assertRaises(subprocess.TimeoutExpired):
                execute([sys.executable, "-c", script], directory, os.environ.copy(), 0.2, directory / "probe")
            pid = (directory / "probe").read_text().strip()
            state = Path(f"/proc/{pid}/stat")
            if state.exists():
                self.assertIn(state.read_text().split()[2], ("Z", "X"))


if __name__ == "__main__":
    unittest.main()
