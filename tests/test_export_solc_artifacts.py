#!/usr/bin/env python3

import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import textwrap
import unittest
from unittest.mock import patch
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
EXPORTER = ROOT / "tools" / "export_solc_artifacts.py"
SOURCE = ROOT / "testdata" / "frontend" / "types.sol"
sys.path.insert(0, str(ROOT / "tools"))
import export_solc_artifacts as exporter

sys.path.insert(0, str(ROOT / "tools"))

import export_solc_artifacts as exporter  # noqa: E402


class ExporterTests(unittest.TestCase):
    def test_remappings_reach_compiler_and_artifact(self) -> None:
        remappings = ("a/=b/", "c/=b/")
        with patch.object(exporter, "compiler_identity", return_value="test"), \
             patch.object(exporter, "compile_standard_json", return_value={}) as compile_json:
            artifact = exporter.build_artifact_from_sources(
                Path("solc"), {"b/C.sol": "contract C {}"},
                exporter.DEFAULT_PROFILE, remappings=remappings,
            )
        compiler_input = compile_json.call_args.args[1]
        self.assertEqual(compiler_input["settings"]["remappings"], list(remappings))
        self.assertEqual(artifact["input"], compiler_input)
        self.assertNotIn("remappings", artifact["profile"]["settings"])

    def test_empty_remappings_preserve_profile_settings(self) -> None:
        with patch.object(exporter, "compiler_identity", return_value="test"), \
             patch.object(exporter, "compile_standard_json", return_value={}):
            artifact = exporter.build_artifact_from_sources(
                Path("solc"), {}, exporter.DEFAULT_PROFILE,
            )
        self.assertEqual(artifact["input"]["settings"], {
            **artifact["profile"]["settings"],
            "outputSelection": exporter.OUTPUT_SELECTION,
        })

    def fake_solc(self, directory: Path, version: str, output: dict) -> Path:
        path = directory / "solc"
        path.write_text(
            textwrap.dedent(
                f"""\
                #!{sys.executable}
                import json
                import sys
                if "--version" in sys.argv:
                    print({version!r})
                else:
                    json.load(sys.stdin)
                    json.dump({output!r}, sys.stdout)
                """
            ),
            encoding="utf-8",
        )
        path.chmod(0o755)
        return path

    def run_exporter(self, solc: Path, output: Path) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            [
                sys.executable,
                str(EXPORTER),
                "--solc",
                str(solc),
                "--output",
                str(output),
                str(SOURCE),
            ],
            cwd=ROOT,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )

    def test_rejects_wrong_compiler_commit(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            solc = self.fake_solc(
                directory,
                "Version: 0.8.37+commit.00000000.Linux.g++",
                {},
            )
            result = self.run_exporter(solc, directory / "artifact.json")
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("compiler commit mismatch", result.stderr)

    def test_rejects_compiler_errors(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            solc = self.fake_solc(
                directory,
                "Version: 0.8.37+commit.f401782d.Linux.g++",
                {
                    "errors": [
                        {
                            "severity": "error",
                            "formattedMessage": "synthetic compiler error",
                        }
                    ]
                },
            )
            result = self.run_exporter(solc, directory / "artifact.json")
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("synthetic compiler error", result.stderr)

    def test_output_is_deterministic(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            solc = self.fake_solc(
                directory,
                "Version: 0.8.37+commit.f401782d.Linux.g++",
                {"contracts": {}, "sources": {}},
            )
            first = directory / "first.json"
            second = directory / "second.json"
            self.assertEqual(self.run_exporter(solc, first).returncode, 0)
            self.assertEqual(self.run_exporter(solc, second).returncode, 0)
            self.assertEqual(first.read_bytes(), second.read_bytes())

    def test_stack_depth_fallback_retains_profile_errors_sources_and_remappings(self) -> None:
        fixture = exporter.read_json(ROOT / "testdata/frontend/expected/stack_depth.json")
        failures = fixture["unoptimizedFailure"]["errors"]
        inputs = []

        def compile_input(solc: Path, compiler_input: dict) -> dict:
            inputs.append(copy.deepcopy(compiler_input))
            if not compiler_input["settings"]["optimizer"]["enabled"]:
                raise exporter.CompilationError(failures)
            return fixture["output"]

        sources = {"alias/stack.sol": "contract StackDepth {}"}
        with patch.object(exporter, "compiler_identity", return_value="pinned"), \
             patch.object(exporter, "compile_standard_json", side_effect=compile_input):
            artifact = exporter.build_artifact_from_sources(
                Path("solc"), sources, exporter.DEFAULT_PROFILE, remappings=["alias/=src/"])
        self.assertEqual(len(inputs), 2)
        self.assertFalse(inputs[0]["settings"]["optimizer"]["enabled"])
        self.assertTrue(inputs[1]["settings"]["optimizer"]["enabled"])
        self.assertEqual(inputs[0]["sources"], inputs[1]["sources"])
        self.assertEqual(inputs[1]["settings"]["remappings"], ["alias/=src/"])
        self.assertEqual(artifact["profile"], exporter.read_json(exporter.OPTIMIZED_PROFILE))
        self.assertEqual(artifact["input"], inputs[1])
        self.assertEqual(artifact["unoptimizedFailure"], fixture["unoptimizedFailure"])

    def test_unrelated_or_mixed_errors_do_not_retry(self) -> None:
        stack = {"severity": "error", "type": "YulException",
                 "message": "variable is too deep in the stack"}
        parser = {"severity": "error", "type": "ParserError",
                  "message": "Stack too deep"}
        for failures in ([parser], [stack, parser],
                         [{**stack, "message": "unrelated compiler failure"}]):
            with self.subTest(errors=failures), \
                 patch.object(exporter, "compiler_identity", return_value="pinned"), \
                 patch.object(exporter, "compile_standard_json",
                              side_effect=exporter.CompilationError(failures)) as compile_json:
                with self.assertRaises(exporter.CompilationError):
                    exporter.build_artifact_from_sources(
                        Path("solc"), {"a.sol": "contract A {}"}, exporter.DEFAULT_PROFILE)
                self.assertEqual(compile_json.call_count, 1)

    def test_direct_optimized_profile_is_rejected(self) -> None:
        with self.assertRaisesRegex(SystemExit, "must start with.*unoptimized"):
            exporter.build_artifact_from_sources(
                Path("solc"), {"a.sol": "contract A {}"}, exporter.OPTIMIZED_PROFILE)

    def test_normally_compiled_artifact_has_no_fallback(self) -> None:
        with patch.object(exporter, "compiler_identity", return_value="pinned"), \
             patch.object(exporter, "compile_standard_json", return_value={}) as compile_json:
            artifact = exporter.build_artifact_from_sources(
                Path("solc"), {"a.sol": "contract A {}"}, exporter.DEFAULT_PROFILE)
        self.assertEqual(compile_json.call_count, 1)
        self.assertEqual(artifact["profile"], exporter.read_json(exporter.DEFAULT_PROFILE))
        self.assertNotIn("unoptimizedFailure", artifact)


if __name__ == "__main__":
    unittest.main()
