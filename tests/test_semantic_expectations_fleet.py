from pathlib import Path
import json
import subprocess
import sys
import tempfile
from typing import Any, Callable
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))

import run_semantic_expectations as runner

CONFIGURED = {"HOLBUILD_REMOTE_CACHE_URL": "https://cache.invalid"}
DONE = f"solidity-hol:{runner.CONTEXT} " + "a" * 64 + " done\n"


def record(test: str, **fields: Any) -> str:
    return runner.PREFIX + json.dumps({"test": test, **fields}) + "\n"


class FleetExpectationTests(unittest.TestCase):
    def setUp(self) -> None:
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.work = Path(temporary.name)
        self.commands: list[list[str]] = []

    def make_tests(self, count: int) -> list[dict[str, Any]]:
        tests = []
        for i in range(count):
            artifact = self.work / f"artifact-{i}.json"
            artifact.write_text(json.dumps({"artifact": i}))
            tests.append({"test": f"t{i}.sol", "artifact": str(artifact), "source": "s",
                          "contract": "C", "calls": [], "verify_bytecode": False})
        return tests

    def fleet(self, write: Callable[[Path, dict[str, Any]], str] | None = None,
              status: int = 0) -> Callable[..., subprocess.CompletedProcess[str]]:
        """A holbuild whose run-action completes every test of the staged batch."""
        def run(command: list[str], **kwargs: Any) -> subprocess.CompletedProcess[str]:
            self.commands.append(command)
            if "--help" in command:
                return subprocess.CompletedProcess(command, 0, stdout="build run run-action")
            if "build" in command:
                return subprocess.CompletedProcess(command, 0)
            self.assertIn("run-action", command)
            script = Path(command[command.index("--script") + 1])
            batch = json.loads((script.parent / "batch.json").read_text())
            outputs = Path(command[command.index("--outputs-dir") + 1]) / "solidity-hol" / runner.CONTEXT
            outputs.mkdir(parents=True)
            text = (write or (lambda d, b: DONE))(outputs, batch)
            kwargs["stdout"].write(text)
            return subprocess.CompletedProcess(command, 75 if runner.NO_COORDINATOR in text else status)
        return run

    def run_batches(self, run: Callable[..., Any], tests: list[dict[str, Any]],
                    environment: dict[str, str] | None = None) -> None:
        with patch.dict(runner.os.environ, environment or {}, clear=True), \
                patch.object(runner.subprocess, "run", side_effect=run):
            runner.run_batches("holbuild", self.work, tests)

    def complete(self, outputs: Path, batch: dict[str, Any]) -> str:
        (outputs / "results.jsonl").write_text(
            "HOL noise\n" + "".join(record(t["test"], kind="complete") for t in batch["tests"]))
        return DONE

    def test_batches_are_staged_portably_and_run_against_the_differential_theory(self) -> None:
        tests = self.make_tests(2)
        self.run_batches(self.fleet(self.complete), tests)
        [action] = [c for c in self.commands if "run-action" in c]
        self.assertNotIn("run", [c[2] for c in self.commands if len(c) > 2])
        for flag in ("--remote-only", "--skip-checkpoints", "--skip-proof-steps"):
            self.assertIn(flag, action)
        self.assertEqual(action[action.index("--load") + 1], "solidityDifferentialLib")
        self.assertEqual(action[action.index("--output") + 1], "results.jsonl")
        self.assertEqual(action[-1], "solidityDifferentialTheory")
        script = Path(action[action.index("--script") + 1])
        self.assertEqual(script.read_text(), runner.HOL_SCRIPT.read_text())
        supports = {Path(action[i + 1]).relative_to(script.parent).as_posix()
                    for i, arg in enumerate(action) if arg == "--support"}
        self.assertEqual(supports, {"batch.json", "0.json", "1.json", "SOLIDITY_PIN",
                                    "profiles/solc-0.8.37-via-ir-osaka.json",
                                    "profiles/solc-0.8.37-via-ir-osaka-optimized.json"})
        staged = json.loads((script.parent / "batch.json").read_text())["tests"]
        for i, test in enumerate(staged):
            self.assertEqual(test["artifact"], f"{i}.json")
            self.assertEqual({**test, "artifact": tests[i]["artifact"]}, tests[i])
            self.assertEqual(json.loads((script.parent / test["artifact"]).read_text()), {"artifact": i})
        self.assertEqual(runner.completed_tests(self.work), {"t0.sol", "t1.sol"})

    def test_batches_are_bounded_and_run_in_order(self) -> None:
        tests = self.make_tests(2 * runner.BATCH_SIZE + 1)
        self.run_batches(self.fleet(self.complete), tests)
        batches = [json.loads((Path(c[c.index("--script") + 1]).parent / "batch.json").read_text())
                   for c in self.commands if "run-action" in c]
        self.assertEqual([len(b["tests"]) for b in batches], [16, 16, 1])
        self.assertEqual([t["test"] for b in batches for t in b["tests"]], [t["test"] for t in tests])
        self.assertEqual(runner.completed_tests(self.work), {t["test"] for t in tests})

    def test_resume_skips_completed_tests_and_continues_numbering(self) -> None:
        # A local batch interrupted after one test, and a fleet batch that failed.
        partial = self.work / "batch-0000"
        partial.mkdir()
        (partial / "results.jsonl").write_text(
            record("t0.sol", kind="complete") + record("t1.sol", index=0, status="executed"))
        (self.work / "batch-0001").mkdir()
        self.assertEqual(runner.completed_tests(self.work), {"t0.sol"})
        tests = self.make_tests(3)
        self.run_batches(self.fleet(self.complete),
                         [t for t in tests if t["test"] not in runner.completed_tests(self.work)])
        [action] = [c for c in self.commands if "run-action" in c]
        self.assertEqual(Path(action[action.index("--script") + 1]).parent.name, "batch-0002")
        self.assertEqual(runner.completed_tests(self.work), {"t0.sol", "t1.sol", "t2.sol"})

    def test_failed_fleet_runs_never_fall_back_or_count(self) -> None:
        def failed(outputs: Path, batch: dict[str, Any]) -> str:
            (outputs / "LOG").write_text("exception")
            return DONE.replace(" done", " failed script")

        def missing(outputs: Path, batch: dict[str, Any]) -> str:
            return DONE

        def unavailable(outputs: Path, batch: dict[str, Any]) -> str:
            return "coordinator unavailable\n"

        for name, run in (("failed", self.fleet(failed)), ("missing", self.fleet(missing)),
                          ("unavailable", self.fleet(unavailable, status=75)),
                          ("status", self.fleet(self.complete, status=1))):
            with self.subTest(name), tempfile.TemporaryDirectory() as temporary:
                self.work = Path(temporary)
                with self.assertRaisesRegex(SystemExit, "fleet action failed"):
                    self.run_batches(run, self.make_tests(1))
                self.assertEqual(runner.completed_tests(self.work), set())

    def no_coordinator(self, outputs: Path, batch: dict[str, Any]) -> str:
        return runner.NO_COORDINATOR + "\n"

    def test_remote_configuration_without_a_coordinator_fails_closed(self) -> None:
        with self.assertRaisesRegex(SystemExit, "remote configuration exists"):
            self.run_batches(self.fleet(self.no_coordinator), self.make_tests(1), CONFIGURED)
        self.assertFalse(any(c[2:3] == ["run"] for c in self.commands))

    def test_older_holbuild_with_remote_configuration_requires_upgrade(self) -> None:
        def old(command: list[str], **kwargs: Any) -> subprocess.CompletedProcess[str]:
            self.commands.append(command)
            return subprocess.CompletedProcess(command, 0, stdout="build run")
        with self.assertRaisesRegex(SystemExit, "upgrade holbuild"):
            self.run_batches(old, self.make_tests(1), CONFIGURED)
        self.assertFalse(any(c[2:3] == ["run"] for c in self.commands))

    def test_coordinator_disappearing_after_the_first_batch_is_fatal(self) -> None:
        def first_only(outputs: Path, batch: dict[str, Any]) -> str:
            if batch["tests"][0]["test"] != "t0.sol":
                return self.no_coordinator(outputs, batch)
            return self.complete(outputs, batch)

        with self.assertRaisesRegex(SystemExit, "coordinator disappeared"):
            self.run_batches(self.fleet(first_only), self.make_tests(runner.BATCH_SIZE + 1))

    def test_only_unconfigured_setups_run_locally(self) -> None:
        def run(command: list[str], **kwargs: Any) -> subprocess.CompletedProcess[str]:
            if command[2:3] != ["run"]:
                return self.fleet(self.no_coordinator)(command, **kwargs)
            self.commands.append(command)
            manifest = Path(kwargs["env"]["SEMANTIC_EXPECTATIONS_MANIFEST"])
            batch = json.loads(manifest.read_text())["tests"]
            self.assertTrue(all(Path(t["artifact"]).is_absolute() for t in batch))
            kwargs["stdout"].write("".join(record(t["test"], kind="complete") for t in batch))
            return subprocess.CompletedProcess(command, 0)
        tests = self.make_tests(runner.BATCH_SIZE + 1)
        self.run_batches(run, tests)
        self.assertEqual(len([c for c in self.commands if "run-action" in c]), 1)
        self.assertEqual(len([c for c in self.commands if c[2:3] == ["run"]]), 2)
        self.assertEqual(runner.completed_tests(self.work), {t["test"] for t in tests})


if __name__ == "__main__":
    unittest.main()
