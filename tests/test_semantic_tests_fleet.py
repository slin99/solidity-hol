from pathlib import Path
import json
import subprocess
import sys
import tempfile
import threading
from typing import Any
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))

import semantic_tests_coverage as coverage


class FleetCoverageTests(unittest.TestCase):
    def run_coverage(self, mode: str) -> dict:
        with tempfile.TemporaryDirectory() as temporary:
            work = Path(temporary)
            artifact = work / "compiled.json"
            artifact.write_text('{"artifact": true}')
            expected = {"test": "test.sol", "status": "admitted"}
            line = coverage.RESULT_PREFIX + json.dumps(expected) + "\n"

            def run(command: list[str], **kwargs: Any) -> subprocess.CompletedProcess[str]:
                if "--help" in command:
                    return subprocess.CompletedProcess(command, 0, stdout=(
                        "build run" if mode.startswith("old") else "build run run-action"))
                if "build" in command:
                    return subprocess.CompletedProcess(command, 0)
                if "run" in command:
                    self.assertIn(mode, {"old", "unconfigured"})
                    manifest = Path(kwargs["env"]["SEMANTIC_TESTS_MANIFEST"])
                    self.assertEqual(manifest.read_text(), f"test.sol\t{artifact}\n")
                    kwargs["stdout"].write(line)
                    return subprocess.CompletedProcess(command, 0)

                self.assertIn("run-action", command)
                script = Path(command[command.index("--script") + 1])
                supports = [Path(command[i + 1]) for i, arg in enumerate(command)
                            if arg == "--support"]
                staged = {path.relative_to(script.parent).as_posix() for path in supports}
                self.assertEqual(staged, {"manifest.txt", "0.json", "SOLIDITY_PIN",
                                         "profiles/solc-0.8.37-via-ir-osaka.json"})
                name, path = (script.parent / "manifest.txt").read_text().strip().split("\t")
                self.assertEqual(name, "test.sol")
                self.assertFalse(Path(path).is_absolute())
                self.assertEqual(json.loads((script.parent / path).read_text()), {"artifact": True})
                if mode in {"unconfigured", "configured-no-coordinator"}:
                    kwargs["stdout"].write("run-action --remote-only: no coordinator to run on; "
                                           "pass --remote-exec URL\n")
                    return subprocess.CompletedProcess(command, 75)
                if mode == "unavailable":
                    kwargs["stdout"].write("coordinator unavailable\n")
                    return subprocess.CompletedProcess(command, 75)
                state = "done" if mode == "missing" else mode
                kwargs["stdout"].write("solidity-hol:solidityElaborateTheory " + "a" * 64
                                       + f" {state}\n")
                output = Path(command[command.index("--outputs-dir") + 1])
                result = output / "solidity-hol/solidityElaborateTheory/results.jsonl"
                result.parent.mkdir(parents=True)
                # A failed action must be refused even if an older output exists.
                result.write_text(line if mode != "missing" else "")
                return subprocess.CompletedProcess(command, 0)

            environment = ({"HOLBUILD_REMOTE_CACHE_URL": "https://cache.invalid"}
                           if mode in {"old-configured", "configured-no-coordinator"} else {})
            with patch.dict(coverage.os.environ, environment, clear=True), \
                    patch.object(coverage.subprocess, "run", side_effect=run):
                return coverage.run_hol("holbuild", work, [("test.sol", artifact)])

    def test_remote_results_are_fetched_from_portable_inputs(self) -> None:
        for state in ("done", "cached"):
            with self.subTest(state=state):
                self.assertEqual(self.run_coverage(state), {
                    "test.sol": {"test": "test.sol", "status": "admitted"}})

    def test_only_unconfigured_or_older_tools_fall_back(self) -> None:
        for mode in ("old", "unconfigured"):
            with self.subTest(mode=mode):
                self.assertEqual(self.run_coverage(mode)["test.sol"]["status"], "admitted")

    def test_configured_fleet_failures_never_fall_back(self) -> None:
        for mode in ("failed", "unavailable", "missing", "configured-no-coordinator"):
            with self.subTest(mode=mode), self.assertRaisesRegex(SystemExit, "HOL .*failed"):
                self.run_coverage(mode)

    def test_older_tool_with_remote_configuration_requires_upgrade(self) -> None:
        with self.assertRaisesRegex(SystemExit, "upgrade holbuild"):
            self.run_coverage("old-configured")

    def test_project_remote_configuration_prevents_fallback(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            config = root / ".holconfig.toml"
            with patch.object(coverage, "ROOT", root), \
                    patch.dict(coverage.os.environ, {}, clear=True):
                self.assertFalse(coverage.remote_configured())
                config.write_text('[build]\njobs = 2\n')
                self.assertFalse(coverage.remote_configured())
                config.write_text('[remote_cache]\nurl = "https://cache.invalid"\n')
                self.assertTrue(coverage.remote_configured())

    def test_bounded_shards_merge_every_result_and_later_failures_are_fatal(self) -> None:
        for disappear in (False, True):
            with self.subTest(disappear=disappear), tempfile.TemporaryDirectory() as temporary:
                work = Path(temporary)
                artifact = work / "compiled.json"
                artifact.write_text("{}")
                units = [(f"test-{i}.sol", artifact) for i in range(128 * 6 + 1)]
                batches = []
                lock = threading.Lock()

                def run(command: list[str], **kwargs: Any) -> subprocess.CompletedProcess[str]:
                    if "--help" in command:
                        return subprocess.CompletedProcess(command, 0, stdout="run-action")
                    if "build" in command:
                        return subprocess.CompletedProcess(command, 0)
                    self.assertIn("run-action", command)
                    script = Path(command[command.index("--script") + 1])
                    rows = (script.parent / "manifest.txt").read_text().splitlines()
                    with lock:
                        batches.append(rows)
                    if disappear and script.parent.name == "0001":
                        kwargs["stdout"].write("run-action --remote-only: no coordinator to run on; "
                                               "pass --remote-exec URL\n")
                        return subprocess.CompletedProcess(command, 75)
                    output = Path(command[command.index("--outputs-dir") + 1])
                    result = output / "solidity-hol/solidityElaborateTheory/results.jsonl"
                    result.parent.mkdir(parents=True)
                    result.write_text("".join(coverage.RESULT_PREFIX + json.dumps({
                        "test": row.split("\t")[0], "status": "admitted"}) + "\n" for row in rows))
                    kwargs["stdout"].write("solidity-hol:solidityElaborateTheory " + "a" * 64
                                           + " done\n")
                    return subprocess.CompletedProcess(command, 0)

                with patch.dict(coverage.os.environ, {}, clear=True), \
                        patch.object(coverage.subprocess, "run", side_effect=run):
                    if disappear:
                        with self.assertRaisesRegex(SystemExit, "coordinator disappeared"):
                            coverage.run_hol("holbuild", work, units)
                    else:
                        results = coverage.run_hol("holbuild", work, units)
                        self.assertEqual(list(results), [name for name, _ in units])
                        self.assertEqual(len(batches), 7)
                        self.assertTrue(all(len(batch) <= 128 for batch in batches))
