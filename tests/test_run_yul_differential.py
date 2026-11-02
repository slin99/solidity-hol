#!/usr/bin/env python3

import contextlib
import io
import json
from pathlib import Path
import sys
import tempfile
import textwrap
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))

import run_differential as core  # noqa: E402
import run_yul_differential as driver  # noqa: E402

SOURCE = "testdata/differential/a.sol"
CORPUS_ARTIFACT = "testdata/differential/expected/a.json"
CONTRACT = "A"
DEPLOYED = "60016000"


def corpus(cases=None):
    return {
        "format": core.CORPUS_FORMAT,
        "fuel": 1000,
        "suites": [{
            "name": "a",
            "source": SOURCE,
            "contract": CONTRACT,
            "artifact": CORPUS_ARTIFACT,
            "cases": cases if cases is not None else [
                {"name": "f_returns", "function": "f", "args": [1],
                 "expect": {"return": [2]}},
            ],
        }],
    }


class FakeRoot:
    """A repository root with one suite, its artifacts, and a fake compiler."""

    def __init__(self, directory: Path, deployed: str = DEPLOYED,
                 unstaged: str | None = None) -> None:
        self.root = directory
        self.write(core.CORPUS.as_posix(), json.dumps(corpus()))
        self.write(SOURCE, "contract A {}\n")
        pin = (ROOT / "SOLIDITY_PIN").read_text(encoding="ascii").strip()
        self.write(CORPUS_ARTIFACT, json.dumps({
            "format": core.ARTIFACT_FORMAT,
            "compiler": {"pin": pin, "reportedVersion": f"Version: 0.8.37+commit.{pin[:8]}"},
            "output": {"contracts": {SOURCE: {CONTRACT: {
                "evm": {"deployedBytecode": {"object": DEPLOYED}}}}}},
        }))
        self.deployed = deployed
        artifacts = [f"../{driver.YUL_ROOT.as_posix()}/{name}.{tag}.json"
                     for name in ("a",) for tag, _ in driver.ARTIFACT_STAGES]
        artifacts.append(f"../{core.CORPUS.as_posix()}")
        if unstaged is not None:
            artifacts.remove(unstaged)
        self.write(driver.CORPUS_SCRIPT.as_posix(), "\n".join(
            ["fun holbuild_extra_deps (_ : string list) = ()",
             "val () = holbuild_extra_deps ["] +
            [f'  "{path}"' + ("," if i < len(artifacts) - 1 else "")
             for i, path in enumerate(artifacts)] + ["]"]))

    def write(self, name: str, text: str) -> None:
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")

    def fake_solc(self) -> Path:
        """A compiler that answers --version with the pin, and compiles."""
        pin = (ROOT / "SOLIDITY_PIN").read_text(encoding="ascii").strip()
        output = {"contracts": {SOURCE: {CONTRACT: {
            "irAst": {"nodeType": "YulObject"},
            "evm": {"deployedBytecode": {"object": self.deployed}}}}}}
        path = self.root / "solc"
        path.write_text(textwrap.dedent(f"""\
            #!{sys.executable}
            import json
            import sys
            if "--version" in sys.argv:
                print("Version: 0.8.37+commit.{pin[:8]}.Linux.g++")
            else:
                json.load(sys.stdin)
                json.dump({output!r}, sys.stdout)
            """), encoding="utf-8")
        path.chmod(0o755)
        return path

    def holbuild(self, results: list[dict], status: int) -> Path:
        """A holbuild that writes the given result lines to its child log."""
        log = self.root / "build.log"
        lines = "".join(driver.RESULT_PREFIX + json.dumps(r) + "\n" for r in results)
        path = self.root / "holbuild"
        path.write_text(textwrap.dedent(f"""\
            #!{sys.executable}
            import sys
            open({str(log)!r}, "w").write({lines!r})
            print("child log: {log}")
            sys.exit({status})
            """), encoding="utf-8")
        path.chmod(0o755)
        return path

    def run(self, results: list[dict], status: int = 0) -> tuple[int, dict]:
        report_dir = self.root / "report"
        with contextlib.redirect_stdout(io.StringIO()):
            exit_status = driver.main(
                ["--solc", str(self.fake_solc()), "--holbuild", str(self.holbuild(results, status)),
                 "--report-dir", str(report_dir)],
                root=self.root)
        report = json.loads((report_dir / "yul-differential.json").read_text(encoding="utf-8"))
        return exit_status, report


def suite_result(name: str, stages: list[str], status: str = "ok", **rest) -> dict:
    """The suite's own line, which is also the evidence for which stages were
    admitted: the theory writes one when it gets through the suite's stages."""
    return {"kind": "suite", "suite": name, "status": status, "stages": stages, **rest}


def rejection(suite: str, name: str, status: str = "import-rejected", **rest) -> dict:
    """The line the importer's refusal of one stage produces; nothing else
    emits a stage line."""
    return {"kind": "stage", "suite": suite, "stage": name, "status": status, **rest}


def case(suite: str, name: str, stage_name: str, status: str = "agree", **rest) -> dict:
    return {"kind": "case", "suite": suite, "case": name, "stage": stage_name,
            "status": status, **rest}


RETURNED = {"returned": "0x" + "00" * 31 + "02"}


def all_agree() -> list[dict]:
    results = [suite_result("a", list(driver.STAGES))]
    results += [case("a", "f_returns", name, outcome=RETURNED) for name in driver.STAGES]
    return results


class DriverTests(unittest.TestCase):
    def test_agreement_passes(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            status, report = FakeRoot(Path(temporary)).run(all_agree())
        self.assertEqual(status, 0)
        self.assertEqual(report["failures"], [])
        self.assertEqual(report["totals"], {"stages_admitted": 3, "stages_expected": 3,
                                            "cases_run": 3, "cases_expected": 3,
                                            "agreements": 3, "case_statuses": {}})
        self.assertEqual([w["theorem"] for w in report["kernel_checked"]],
                         ["yul_a_f_returns_ir", "yul_a_f_returns_ir_optimized",
                          "yul_a_f_returns_optimized"])

    def test_a_stage_that_is_not_admitted_is_counted_separately(self) -> None:
        """Its cases are not run there, so they are an admission, not a
        disagreement, and not a missing result."""
        results = [suite_result("a", [driver.IR, driver.IR_OPTIMIZED]),
                   rejection("a", driver.OPTIMIZED, message="no nodeType")]
        results += [case("a", "f_returns", name, outcome=RETURNED)
                    for name in (driver.IR, driver.IR_OPTIMIZED)]
        with tempfile.TemporaryDirectory() as temporary:
            status, report = FakeRoot(Path(temporary)).run(results)
        self.assertEqual(status, 1)
        self.assertEqual(report["totals"]["stages_admitted"], 2)
        self.assertEqual(report["totals"]["agreements"], 2)
        self.assertEqual([(f["kind"], f["status"]) for f in report["failures"]],
                         [("admission", "import-rejected")])

    def test_a_disagreement_is_reported_with_its_status(self) -> None:
        results = all_agree()
        results[-1] = case("a", "f_returns", driver.OPTIMIZED, "mismatch",
                           bytecode=RETURNED, yul={"reverted": "0x"})
        with tempfile.TemporaryDirectory() as temporary:
            status, report = FakeRoot(Path(temporary)).run(results, status=1)
        self.assertEqual(status, 1)
        self.assertEqual([(f["kind"], f["status"]) for f in report["failures"]],
                         [("case", "mismatch")])
        self.assertEqual(report["failures"][0]["theorem"], "yul_a_f_returns_optimized")
        self.assertEqual(report["totals"]["case_statuses"], {"mismatch": 1})

    def test_the_totals_classify_the_cases_that_are_not_agreements(self) -> None:
        """An inconclusive is a diagnostic on one side, not a disagreement, and
        the totals have to say which there are rather than call both a
        failure."""
        results = all_agree()
        results[1] = case("a", "f_returns", driver.IR, "inconclusive",
                          yul={"diagnostic": "InvalidCompletion"})
        results[2] = case("a", "f_returns", driver.IR_OPTIMIZED, "inconclusive",
                          yul={"diagnostic": "InvalidCompletion"})
        results[3] = case("a", "f_returns", driver.OPTIMIZED, "mismatch",
                          bytecode=RETURNED, yul={"reverted": "0x"})
        with tempfile.TemporaryDirectory() as temporary:
            status, report = FakeRoot(Path(temporary)).run(results, status=1)
        self.assertEqual(status, 1)
        self.assertEqual(report["totals"]["case_statuses"],
                         {"inconclusive": 2, "mismatch": 1})
        self.assertEqual(report["totals"]["agreements"], 0)

    def test_a_missing_result_fails(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            status, report = FakeRoot(Path(temporary)).run(
                [suite_result("a", list(driver.STAGES))], status=0)
        self.assertEqual(status, 1)
        self.assertEqual([f["status"] for f in report["failures"]], ["missing"] * 3)

    def test_a_suite_with_no_result_admits_nothing(self) -> None:
        """A build that stopped before a suite reports it admits no stage of it:
        silence is not evidence."""
        with tempfile.TemporaryDirectory() as temporary:
            status, report = FakeRoot(Path(temporary)).run([], status=0)
        self.assertEqual(status, 1)
        self.assertEqual(report["totals"]["stages_admitted"], 0)
        self.assertEqual([a["admitted"] for a in report["admissions"]], [False] * 3)
        self.assertEqual([(f["kind"], f["status"]) for f in report["failures"]],
                         [("suite", "missing")])

    def test_a_failed_suite_is_reported_with_its_message(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            status, report = FakeRoot(Path(temporary)).run(
                [suite_result("a", [], "prepare-failed", message="the artifact is stale")])
        self.assertEqual(status, 1)
        self.assertEqual([(f["kind"], f["status"]) for f in report["failures"]],
                         [("suite", "prepare-failed")])
        self.assertEqual(report["totals"]["stages_admitted"], 0)

    def test_the_yul_must_be_the_same_program_as_the_bytecode(self) -> None:
        """The optimizer-off compile's bytecode is what the corpus validates,
        so a different one means the Yul is not that program."""
        with tempfile.TemporaryDirectory() as temporary:
            status, report = FakeRoot(Path(temporary), deployed="deadbeef").run(all_agree())
        self.assertEqual(status, 1)
        failed = [f for f in report["failures"] if f["kind"] == "external-check"]
        self.assertEqual([f["check"] for f in failed], ["yul-artifact-is-the-same-program"])

    def test_a_generated_artifact_that_is_not_staged_fails(self) -> None:
        missing = f"../{driver.YUL_ROOT.as_posix()}/a.optimized.json"
        with tempfile.TemporaryDirectory() as temporary:
            status, report = FakeRoot(Path(temporary), unstaged=missing).run(all_agree())
        self.assertEqual(status, 1)
        failed = [f for f in report["failures"] if f["kind"] == "external-check"]
        self.assertEqual([f["check"] for f in failed], ["yul-artifacts-staged"])
        self.assertIn("a.optimized.json", failed[0]["detail"])


class CommittedTests(unittest.TestCase):
    def test_a_run_without_hol_reports_no_stage_results(self) -> None:
        """--no-hol still writes a report: the compiler-side checks, and every
        stage counted as neither admitted nor run."""
        with tempfile.TemporaryDirectory() as temporary:
            root = FakeRoot(Path(temporary))
            report_dir = root.root / "report"
            with contextlib.redirect_stdout(io.StringIO()):
                status = driver.main(["--solc", str(root.fake_solc()), "--no-hol",
                                      "--report-dir", str(report_dir)], root=root.root)
            report = json.loads(
                (report_dir / "yul-differential.json").read_text(encoding="utf-8"))
            summary = (report_dir / "yul-differential.md").read_text(encoding="utf-8")
        self.assertEqual(status, 0)
        self.assertIsNone(report["hol"])
        self.assertEqual(report["totals"]["stages_admitted"], 0)
        self.assertEqual(sorted(report["per_stage"]), sorted(driver.STAGES))
        self.assertIn("The HOL corpus was not run", summary)

    def test_the_committed_corpus_theory_stages_every_artifact(self) -> None:
        loaded = core.load_corpus(ROOT / core.CORPUS)
        written = [f"{driver.YUL_ROOT.as_posix()}/{suite['name']}.{tag}.json"
                   for suite in loaded["suites"] for tag, _ in driver.ARTIFACT_STAGES]
        self.assertEqual(driver.check_staging(ROOT, written)["status"], "pass")


if __name__ == "__main__":
    unittest.main()
