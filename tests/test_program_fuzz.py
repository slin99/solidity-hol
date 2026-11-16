from collections import Counter
import json
import os
from pathlib import Path
import re
import sys
import tempfile
from typing import Any
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))

import export_solc_artifacts as exporter
import generate_solidity_programs as generator
import run_differential_fuzz as fuzz
import run_program_fuzz as programs

SEEDS = range(60)


class GeneratorTests(unittest.TestCase):
    def test_a_seed_gives_the_same_program_every_time(self) -> None:
        self.assertEqual(generator.generate(7), generator.generate(7))
        self.assertNotEqual(generator.generate(7), generator.generate(8))

    def test_every_targeted_interaction_is_generated(self) -> None:
        seen: Counter[str] = Counter()
        for seed in SEEDS:
            seen.update(generator.Program(seed).features)
        for feature in ("evaluation-order", "aliasing", "copies", "dispatch", "try", "abi",
                        "checked", "unchecked"):
            # Each in a good share of the programs, not just once.
            self.assertGreater(seen[feature], len(SEEDS) // 4, feature)

    def test_one_contract_deploys_and_the_interface_matches_its_functions(self) -> None:
        for seed in SEEDS:
            text = generator.generate(seed)
            self.assertEqual(re.findall(r"^contract (\w+)", text, re.M), ["Gen"])
            declared = re.findall(r"function (f\d+)\(([^)]*)\) external returns \((\w+)\);", text)
            defined = re.findall(r"function (f\d+)\(([^)]*)\) public[^{]*returns \((\w+)\)", text)
            self.assertEqual(
                declared, [(name, ", ".join(p.split()[0] for p in params.split(", ")), ret)
                           for name, params, ret in defined])

    def test_try_calls_only_reach_earlier_functions(self) -> None:
        """No recursion through try: a function only calls those before it."""
        for seed in SEEDS:
            text = generator.generate(seed)
            for body in re.split(r"\n    function ", text):
                caller = re.match(r"(f\d+)\(", body)
                if caller is None:
                    continue
                for callee in re.findall(r"IGen\(address\(this\)\)\.(f\d+)\(", body):
                    self.assertLess(int(callee[1:]), int(caller.group(1)[1:]), (seed, callee))

    def test_integer_literals_fit_their_types(self) -> None:
        for seed in SEEDS:
            for t, value in re.findall(r"\b(u?int\d+)\((-?\d+)\)", generator.generate(seed)):
                bits = int(t.lstrip("uint"))
                low, high = ((-(1 << (bits - 1)), (1 << (bits - 1)) - 1) if t.startswith("int")
                             else (0, (1 << bits) - 1))
                self.assertTrue(low <= int(value) <= high, (seed, t, value))

    @unittest.skipUnless(os.environ.get("SOLC"), "set SOLC to the pinned solc to compile")
    def test_generated_programs_compile(self) -> None:
        for seed in SEEDS:
            exporter.build_artifact_from_sources(
                Path(os.environ["SOLC"]), {"gen.sol": generator.generate(seed)},
                exporter.DEFAULT_PROFILE)


def hol_result(status: str, **fields: Any) -> dict[str, Any]:
    return {"status": status, **fields}


class DriverTests(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory()
        self.output = Path(self.tmp.name)
        self.programs = [programs.Program(seed, self.output / "programs") for seed in range(3)]

    def tearDown(self) -> None:
        self.tmp.cleanup()

    def compile_all(self, failing: set[int] = frozenset()) -> dict[str, str]:
        def build(solc: Path, sources: dict[str, str], profile: Path) -> dict[str, Any]:
            [name] = sources
            if any(name == f"gen_{seed:06d}.sol" for seed in failing):
                raise exporter.CompilationError([{"formattedMessage": "TypeError: bad"}])
            return {"sources": sources}

        with patch.object(exporter, "build_artifact_from_sources", side_effect=build):
            return programs.compile_programs(Path("solc"), self.programs)

    def test_compile_failures_are_reported_and_the_others_written(self) -> None:
        failures = self.compile_all(failing={1})
        self.assertEqual(list(failures), ["gen_000001"])
        self.assertIn("TypeError: bad", failures["gen_000001"])
        self.assertTrue(self.programs[0].artifact.is_file())
        self.assertFalse(self.programs[1].artifact.is_file())
        self.assertEqual(self.programs[1].source.read_text(), generator.generate(1))

    def test_only_fully_admitted_programs_are_kept(self) -> None:
        failures = self.compile_all(failing={2})
        hol = {"gen_000000": hol_result("admitted", functions=4),
               "gen_000001": hol_result("partially-admitted", functions=4,
                                        unsupported=["f3: unsupported member"])}
        with patch.object(programs.coverage, "run_hol", return_value=hol) as run_hol:
            admission = programs.admit("holbuild", self.output, self.programs, failures)
        # Only compiled programs go to HOL.
        self.assertEqual([name for name, _ in run_hol.call_args.args[2]],
                         ["gen_000000", "gen_000001"])
        self.assertEqual(admission.admitted, ["gen_000000"])
        self.assertEqual(admission.rejected["gen_000001"]["blockers"], ["f3: unsupported member"])
        self.assertEqual(admission.rejected["gen_000002"]["category"], "compile-failure")
        self.assertEqual(admission.counts(), {"admitted": 1, "compile-failure": 1,
                                              "partially-admitted": 1})
        # Prepared once: a resumed run reads it back.
        with patch.object(programs.coverage, "run_hol", side_effect=AssertionError):
            self.assertEqual(programs.admit("holbuild", self.output, self.programs, failures),
                             admission)

    def test_targets_name_the_artifact_from_the_root(self) -> None:
        target = self.programs[0].target()
        self.assertEqual(target["contract"], "Gen")
        self.assertEqual(target["source"], "gen_000000.sol")
        self.assertEqual((fuzz.ROOT / target["artifact"]).resolve(),
                         self.programs[0].artifact.resolve())

    def test_the_report_gives_the_admission_rate_and_the_dropped_programs(self) -> None:
        admission = programs.Admission(["gen_000000"], {"gen_000001": {
            "category": "elaboration-rejected", "blockers": ["12: unsupported\nmore"]}})
        text = programs.markdown(range(2), admission, None)
        self.assertIn("1 of 2 programs admitted (50.0%)", text)
        self.assertIn("- `gen_000001` (elaboration-rejected): 12: unsupported", text)
        self.assertNotIn("more", text)

    def test_an_admission_only_run_writes_its_report(self) -> None:
        hol = {p.name: hol_result("admitted") for p in self.programs}

        def build(solc: Path, sources: dict[str, str], profile: Path) -> dict[str, Any]:
            return {"sources": sources}

        with patch.object(exporter, "build_artifact_from_sources", side_effect=build), \
                patch.object(programs.coverage, "run_hol", return_value=hol), \
                patch("builtins.print"):
            status = programs.main(["--seeds", "0:3", "--solc", "solc", "--admission-only",
                                    "--output", str(self.output)])
        self.assertEqual(status, 0)
        report = json.loads((self.output / "report.json").read_text())
        self.assertEqual(report["counts"], {"admitted": 3})
        self.assertIsNone(report["fuzz"])


if __name__ == "__main__":
    unittest.main()
