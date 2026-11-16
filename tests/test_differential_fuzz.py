from collections import Counter
from dataclasses import replace
from pathlib import Path
import json
import subprocess
import sys
import tempfile
from types import SimpleNamespace
from typing import Any
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))

import run_differential_fuzz as fuzz

SUITE = "storage_structs"


def target(name: str = SUITE) -> fuzz.Target:
    [t] = fuzz.suite_targets([name])
    return t


def call(**fields: Any) -> fuzz.Call:
    return replace(fuzz.Call(function="f", mode="typed", calldata=b"\x01\x02\x03\x04",
                             sender=fuzz.SENDER, value=0, storage={}, immutables={}), **fields)


class EncodingTests(unittest.TestCase):
    def test_keccak_matches_known_digests(self) -> None:
        self.assertEqual(fuzz.keccak256(b"").hex(),
                         "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470")
        self.assertEqual(fuzz.keccak256(b"abc").hex(),
                         "4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45")
        # Two blocks: the rate is 136 bytes.
        self.assertEqual(fuzz.keccak256(b"a" * 200).hex(),
                         "96ea54061def936c4be90b518992fdc6f12f535068a256229aca54267b4d084d")

    def test_selectors_agree_with_the_compiler(self) -> None:
        for t in fuzz.suite_targets([]):
            for sig, selector in t.selectors.items():
                self.assertEqual(fuzz.keccak256(sig.encode())[:4], selector, f"{t.name}: {sig}")

    def test_dynamic_values_are_encoded_after_the_heads(self) -> None:
        types = [{"type": "uint256"}, {"type": "bytes"}, {"type": "uint256[]"}]
        encoded = fuzz.encode_tuple(types, [1, b"ab", [2]])
        words = [encoded[i:i + 32] for i in range(0, len(encoded), 32)]
        self.assertEqual([int.from_bytes(w, "big") for w in words[:3]], [1, 0x60, 0xA0])
        self.assertEqual(int.from_bytes(words[3], "big"), 2)
        self.assertEqual(words[4], b"ab".ljust(32, b"\0"))
        self.assertEqual([int.from_bytes(w, "big") for w in words[5:]], [1, 2])

    def test_static_tuples_and_arrays_are_inline(self) -> None:
        t = {"type": "tuple[2]", "components": [{"type": "bool"}, {"type": "int8"}]}
        self.assertFalse(fuzz.is_dynamic(t))
        self.assertEqual(fuzz.head_size(t), 128)
        encoded = fuzz.encode_tuple([t], [[[True, -1], [False, 2]]])
        self.assertEqual(encoded[32:64], b"\xff" * 32)
        self.assertEqual(fuzz.canonical(t), "(bool,int8)[2]")

    def test_external_function_values_are_address_and_selector(self) -> None:
        t = {"type": "tuple", "components": [{"type": "function"}, {"type": "function[]"}]}
        value = fuzz.random_value(fuzz.random.Random(1), t)
        self.assertEqual(len(value[0]), 24)
        self.assertIn(int.from_bytes(value[0][:20], "big"), fuzz.ADDRESSES)
        encoded = fuzz.encode_tuple([{"type": "function"}], [value[0]])
        self.assertEqual(encoded, value[0] + bytes(8))


class GenerationTests(unittest.TestCase):
    def test_generation_is_deterministic_per_seed(self) -> None:
        t = target()
        self.assertEqual(fuzz.generate_calls(3, t, 20), fuzz.generate_calls(3, t, 20))
        self.assertNotEqual(fuzz.generate_calls(3, t, 20), fuzz.generate_calls(4, t, 20))

    def test_calldata_is_70_percent_typed_20_mutated_10_raw(self) -> None:
        calls = fuzz.generate_calls(0, target(), 2000)
        modes = Counter(c.mode for c in calls)
        for mode, share in (("typed", 0.7), ("mutated", 0.2), ("raw", 0.1)):
            self.assertAlmostEqual(modes[mode] / len(calls), share, delta=0.02)
        selectors = set(target().selectors.values())
        self.assertTrue(all(c.calldata[:4] in selectors for c in calls if c.mode == "typed"))


class StorageTests(unittest.TestCase):
    LAYOUT = {
        "storage": [
            {"label": "balances", "slot": "0", "offset": 0, "type": "t_mapping"},
            {"label": "values", "slot": "1", "offset": 0, "type": "t_array"},
            {"label": "small", "slot": "2", "offset": 0, "type": "t_uint8"},
            {"label": "flag", "slot": "2", "offset": 1, "type": "t_bool"},
            {"label": "name", "slot": "3", "offset": 0, "type": "t_string"},
        ],
        "types": {
            "t_mapping": {"encoding": "mapping", "key": "t_address", "value": "t_uint256",
                          "label": "mapping(address => uint256)", "numberOfBytes": "32"},
            "t_array": {"encoding": "dynamic_array", "base": "t_uint256",
                        "label": "uint256[]", "numberOfBytes": "32"},
            "t_address": {"encoding": "inplace", "label": "address", "numberOfBytes": "20"},
            "t_uint256": {"encoding": "inplace", "label": "uint256", "numberOfBytes": "32"},
            "t_uint8": {"encoding": "inplace", "label": "uint8", "numberOfBytes": "1"},
            "t_bool": {"encoding": "inplace", "label": "bool", "numberOfBytes": "1"},
            "t_string": {"encoding": "bytes", "label": "string", "numberOfBytes": "32"},
        },
    }

    def test_seeded_slots_follow_the_layout(self) -> None:
        stub = SimpleNamespace(layout=self.LAYOUT, enum_sizes={})
        mapping_slots = {fuzz.hash_word(fuzz.word(a) + fuzz.word(0)) for a in fuzz.ADDRESSES}
        element = fuzz.hash_word(fuzz.word(1))
        for seed in range(50):
            storage = fuzz.initial_storage(fuzz.random.Random(seed), stub)  # type: ignore[arg-type]
            length = storage.get(1, 0)
            self.assertLessEqual(length, fuzz.MAX_ELEMENTS)
            allowed = {0, 1, 2, 3} | mapping_slots | {element + i for i in range(length)}
            self.assertLessEqual(set(storage), allowed | {fuzz.hash_word(fuzz.word(3)) + i
                                                          for i in range(2)})
            packed = storage.get(2, 0)
            self.assertLess(packed, 1 << 16)
            self.assertIn(packed >> 8, (0, 1))
            name = storage.get(3, 0)
            if name and name & 1 == 0:  # short: length * 2 in the low byte
                self.assertLess((name & 0xFF) // 2, 32)

    def test_real_layouts_seed_without_errors(self) -> None:
        for t in fuzz.suite_targets([]):
            fuzz.initial_storage(fuzz.random.Random(0), t)


class StratifyTests(unittest.TestCase):
    def recording(self, data: str) -> fuzz.Recording:
        return fuzz.Recording({"revert": data}, {}, [])

    def test_functions_alternate_and_rare_shapes_come_first(self) -> None:
        common = [(call(function="a", value=i), self.recording("0x01")) for i in range(10)]
        rare = [(call(function="a", value=99), self.recording("0x02"))]
        other = [(call(function="b", value=i), self.recording("0x01")) for i in range(5)]
        chosen = fuzz.stratify(0, "t", common + rare + other, 4)
        self.assertEqual([c.function for c, _ in chosen], ["a", "b", "a", "b"])
        self.assertIn(99, [c.value for c, _ in chosen])

    def test_every_twentieth_case_is_confirmed(self) -> None:
        screened = [(call(value=i), self.recording("0x")) for i in range(41)]
        cases = fuzz.make_cases(screened)
        self.assertEqual([c.name for c in cases if c.confirm], ["fuzz_0000", "fuzz_0020", "fuzz_0040"])


class ShrinkTests(unittest.TestCase):
    def test_shrinking_keeps_only_what_the_failure_needs(self) -> None:
        # Fails while the first argument word is nonzero.
        def still_fails(proposals: dict[str, list[fuzz.Call]]) -> dict[str, list[bool]]:
            return {k: [any(c.calldata[4:36]) for c in calls] for k, calls in proposals.items()}

        data = b"\xaa\xbb\xcc\xdd" + fuzz.word(5) + fuzz.word(6) + fuzz.word(7)
        failing = call(calldata=data, storage={1: 2, 3: 4, 5: 6}, value=10, sender=0xC0FFEE,
                       immutables={"owner": 1})
        [(key, minimal)] = fuzz.shrink({"c/fuzz_0000": failing}, still_fails, 20).items()
        self.assertEqual(key, "c/fuzz_0000")
        self.assertEqual(minimal, call(calldata=b"\xaa\xbb\xcc\xdd" + fuzz.word(5)))

    def test_a_case_no_variant_reproduces_is_left_alone(self) -> None:
        failing = call(storage={1: 2})
        never = lambda proposals: {k: [False] * len(v) for k, v in proposals.items()}
        self.assertEqual(fuzz.shrink({"c/x": failing}, never, 5), {"c/x": failing})


class FuzzerTests(unittest.TestCase):
    """The driver with pyrevm and HOL replaced: screening records every call
    as returning nothing; HOL reports the first case of each contract, and
    every variant of it, as disagreeing."""

    def setUp(self) -> None:
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.output = Path(temporary.name)
        self.evaluated: list[list[str]] = []
        self.screened = 0

    def screen(self, t: fuzz.Target, c: fuzz.Call) -> fuzz.Recording:
        self.screened += 1
        return fuzz.Recording({"returned": "0x"}, {}, [])

    def evaluate(self, work: Path, entries: list[dict[str, Any]]) -> list[dict[str, Any]]:
        self.evaluated.append([e["name"] for e in entries])
        lines = []
        for entry in entries:
            lines.append({"kind": "contract", "contract": entry["name"], "status": "ok",
                          "unsupported": []})
            for case in entry["cases"]:
                bad = case["name"].startswith("fuzz_0000")
                lines.append({"kind": "case", "contract": entry["name"], "case": case["name"],
                              "status": "disagree" if bad else "agree", "screen": "Agree",
                              "confirmed": bad or bool(case.get("confirm"))})
        batch = work / f"batch-{len(list(work.glob('batch-*'))):04d}"
        batch.mkdir(parents=True)
        (batch / "results.jsonl").write_text(
            "".join(fuzz.PREFIX + json.dumps(line) + "\n" for line in lines))
        return fuzz.batch_records(work)

    def fuzzer(self) -> fuzz.Fuzzer:
        return fuzz.Fuzzer(self.output, seed=0, candidates=5, k=4,
                           evaluate=self.evaluate, screen=self.screen)

    def test_a_run_reports_minimizes_and_resumes(self) -> None:
        targets = fuzz.suite_targets([SUITE, "qualified_events"])
        summary = self.fuzzer().run(targets, max_batches=None, shrink_rounds=5)
        self.assertEqual(summary["totals"], {"agree": 6, "disagree": 2})
        self.assertEqual(summary["confirmed"], 2)
        self.assertEqual(summary["missing"], [])
        self.assertEqual({r["contract"] for r in summary["disagree"]}, {SUITE, "qualified_events"})
        minimized = json.loads((self.output / "minimized" / f"{SUITE}.json").read_text())
        [case] = minimized["cases"]
        self.assertEqual(case["name"], "fuzz_0000")
        self.assertNotIn("fuzz", case)
        self.assertNotIn("confirm", case)
        self.assertEqual(case["storage"], {})
        self.assertEqual(minimized["name"], f"fuzz_{SUITE}")
        self.assertEqual(minimized["peer"], fuzz.ECHO_PEER)  # what the recording ran with
        self.assertEqual(minimized["fuel"], targets[0].entry["fuel"])
        self.assertTrue(fuzz.failed(summary))

        screened, evaluated = self.screened, len(self.evaluated)
        again = self.fuzzer().run(targets, max_batches=None, shrink_rounds=0)
        self.assertEqual(again["totals"], summary["totals"])
        self.assertEqual(len(self.evaluated), evaluated)  # nothing left to evaluate
        self.assertEqual(self.screened, screened + 2)  # only the minimized recordings
        self.assertTrue((self.output / "report.md").is_file())

    def test_a_contract_that_fails_to_prepare_fails_the_run(self) -> None:
        manifests = {"c": {"screening": {}, "cases": [
            {"name": "a", "fuzz": {"function": "f", "mode": "typed"}}]}}
        results = [{"kind": "contract", "contract": "c", "status": "error", "message": "boom"}]
        summary = fuzz.report(manifests, results)
        self.assertEqual(summary["missing"], [])
        self.assertTrue(fuzz.failed(summary))

    def test_a_contract_whose_candidates_all_halt_fails_the_run(self) -> None:
        def halting(t: fuzz.Target, c: fuzz.Call) -> fuzz.Recording:
            raise fuzz.Halt("OutOfGas")

        fuzzer = fuzz.Fuzzer(self.output, seed=0, candidates=5, k=4,
                             evaluate=self.evaluate, screen=halting)
        summary = fuzzer.run(fuzz.suite_targets([SUITE]), max_batches=None, shrink_rounds=0)
        self.assertEqual(summary["no_cases"], [SUITE])
        self.assertGreater(summary["screening"][SUITE]["halted"]["OutOfGas"], 0)
        self.assertTrue(fuzz.failed(summary))
        self.assertIn(SUITE, fuzz.markdown(summary))

    def test_a_case_error_is_reported_and_fails_the_run(self) -> None:
        manifests = {"c": {"screening": {}, "cases": [
            {"name": "a", "fuzz": {"function": "f", "mode": "typed"}}]}}
        results = [{"kind": "contract", "contract": "c", "status": "ok", "unsupported": []},
                   {"kind": "case", "contract": "c", "case": "a", "status": "error",
                    "message": "boom"}]
        summary = fuzz.report(manifests, results)
        self.assertEqual([r["case"] for r in summary["error"]], ["a"])
        self.assertTrue(fuzz.failed(summary))

    def test_a_partially_evaluated_contract_reports_its_missing_cases(self) -> None:
        targets = fuzz.suite_targets([SUITE])
        fuzzer = self.fuzzer()

        def partial(work: Path, entries: list[dict[str, Any]]) -> list[dict[str, Any]]:
            entry = entries[0]
            lines = [{"kind": "contract", "contract": entry["name"], "status": "ok",
                      "unsupported": []},
                     {"kind": "case", "contract": entry["name"], "case": "fuzz_0001",
                      "status": "disagree", "screen": "Mismatch", "confirmed": True}]
            batch = work / "batch-0000"
            batch.mkdir(parents=True)
            (batch / "results.jsonl").write_text(
                "".join(fuzz.PREFIX + json.dumps(line) + "\n" for line in lines))
            return fuzz.batch_records(work)

        fuzzer.evaluate = partial
        summary = fuzzer.run(targets, max_batches=None, shrink_rounds=0)
        self.assertEqual([r["case"] for r in summary["disagree"]], ["fuzz_0001"])
        self.assertEqual(len(summary["missing"]), 3)
        self.assertTrue(fuzz.failed(summary))

    def test_resume_is_refused_when_inputs_change(self) -> None:
        inputs = fuzz.run_inputs([target()], 0, 5, 4)
        fuzz.check_inputs(self.output, inputs, resume=False)
        fuzz.check_inputs(self.output, inputs, resume=True)
        with self.assertRaisesRegex(SystemExit, "not empty"):
            fuzz.check_inputs(self.output, inputs, resume=False)
        for changed in ({**inputs, "seed": 1}, fuzz.run_inputs([target()], 0, 5, 8),
                        {**inputs, "source_hash": "0"}):
            with self.assertRaisesRegex(SystemExit, "cannot resume"):
                fuzz.check_inputs(self.output, changed, resume=True)

    def test_a_contract_sent_to_hol_without_a_result_fails_the_run(self) -> None:
        targets = fuzz.suite_targets([])[:2]
        evaluate = self.evaluate
        self.evaluate = lambda work, entries: evaluate(work, entries[:1])  # type: ignore[method-assign]
        summary = self.fuzzer().run(targets, max_batches=None, shrink_rounds=0)
        self.assertEqual(summary["unreported"], [targets[1].name])
        self.assertTrue(fuzz.failed(summary))
        self.assertIn(targets[1].name, (self.output / "report.md").read_text())

    def test_a_relative_output_is_made_absolute(self) -> None:
        with patch.object(fuzz, "check_inputs", side_effect=SystemExit("stop")) as check, \
                self.assertRaises(SystemExit):
            fuzz.main(["--output", "out", "--suite", SUITE])
        self.assertEqual(check.call_args.args[0], Path.cwd() / "out")

    def test_max_batches_bounds_the_contracts_evaluated(self) -> None:
        targets = fuzz.suite_targets([])[:3]
        summary = self.fuzzer().run(targets, max_batches=2, shrink_rounds=0)
        self.assertEqual(len(self.evaluated[0]), 2)
        self.assertEqual(summary["contracts"], 2)
        self.assertEqual(summary["unevaluated"], [targets[-1].name])

    def test_inconclusives_are_grouped_and_invalid_completion_functions_flagged(self) -> None:
        manifests = {"c": {"screening": {}, "cases": [
            {"name": "a", "fuzz": {"function": "f", "mode": "typed"}},
            {"name": "b", "fuzz": {"function": "f", "mode": "mutated"}},
            {"name": "d", "fuzz": {"function": "g", "mode": "typed"}}]}}
        results = [
            {"kind": "case", "contract": "c", "case": "a", "status": "inconclusive",
             "reason": "InvalidCompletion", "confirmed": False},
            {"kind": "case", "contract": "c", "case": "b", "status": "agree", "confirmed": False},
            {"kind": "case", "contract": "c", "case": "d", "status": "inconclusive",
             "reason": "OutOfFuel", "confirmed": False}]
        summary = fuzz.report(manifests, results)
        self.assertEqual(summary["inconclusive"], [
            {"contract": "c", "function": "f", "reason": "InvalidCompletion", "cases": 1},
            {"contract": "c", "function": "g", "reason": "OutOfFuel", "cases": 1}])
        self.assertEqual(summary["invalid_completion_functions"], [{"contract": "c", "function": "f"}])


class TargetTests(unittest.TestCase):
    def test_a_targets_manifest_names_contracts_outside_the_suites(self) -> None:
        suite = json.loads((fuzz.SUITES / f"{SUITE}.json").read_text())
        entry = {k: suite[k] for k in ("source", "contract")}
        with tempfile.TemporaryDirectory() as temporary:
            manifest = Path(temporary) / "targets.json"
            manifest.write_text(json.dumps({"targets": [
                {**entry, "name": "outside", "artifact": str(ROOT / suite["artifact"]),
                 "fuel": 7}]}))
            [t] = fuzz.manifest_targets(manifest)
        self.assertEqual((t.name, t.entry["fuel"], t.entry["peer"]), ("outside", 7, fuzz.ECHO_PEER))
        self.assertEqual(t.selectors, target().selectors)

    def test_target_artifact_paths_are_kept_relative_to_the_root(self) -> None:
        suite = json.loads((fuzz.SUITES / f"{SUITE}.json").read_text())
        peer = fuzz.ECHO_PEER
        with tempfile.TemporaryDirectory() as temporary:
            manifest = Path(temporary) / "targets.json"
            manifest.write_text(json.dumps({"targets": [
                {**{k: suite[k] for k in ("name", "source", "contract")},
                 "artifact": str(ROOT / suite["artifact"]),
                 "peer": {**peer, "artifact": str(ROOT / peer["artifact"])}}]}))
            [t] = fuzz.manifest_targets(manifest)
        self.assertEqual(t.entry["artifact"], suite["artifact"])
        self.assertEqual(t.entry["peer"], peer)


class FleetTests(unittest.TestCase):
    def test_each_contract_gets_an_action_and_a_failed_one_fails_only_itself(self) -> None:
        names = ["first", "second"]
        entries = [{**target().entry, "name": n, "cases": [], "screening": {}} for n in names]
        actions = []

        def run(command: list[str], **kwargs: Any) -> subprocess.CompletedProcess[str]:
            if "--help" in command:
                return subprocess.CompletedProcess(command, 0, stdout="run-action")
            if "build" in command:
                return subprocess.CompletedProcess(command, 0)
            script = Path(command[command.index("--script") + 1])
            [staged] = json.loads((script.parent / "batch.json").read_text())["contracts"]
            actions.append(staged["name"])
            outputs = Path(command[command.index("--outputs-dir") + 1]) / "solidity-hol" / \
                fuzz.fleet.CONTEXT
            outputs.mkdir(parents=True)
            if staged["name"] == "first":
                kwargs["stdout"].write(f"solidity-hol:{fuzz.fleet.CONTEXT} {'a' * 64} failed memory\n")
                return subprocess.CompletedProcess(command, 1)
            (outputs / "results.jsonl").write_text(fuzz.PREFIX + json.dumps(
                {"kind": "contract", "contract": "second", "status": "ok", "unsupported": []}) + "\n")
            kwargs["stdout"].write(f"solidity-hol:{fuzz.fleet.CONTEXT} {'a' * 64} done\n")
            return subprocess.CompletedProcess(command, 0)

        with tempfile.TemporaryDirectory() as temporary, \
                patch.dict(fuzz.fleet.os.environ, {}, clear=True), \
                patch.object(fuzz.fleet.subprocess, "run", side_effect=run):
            results = fuzz.run_fleet("holbuild", Path(temporary) / "work", entries)
        self.assertEqual(actions, names)
        self.assertEqual([(r["contract"], r["status"], r.get("message")) for r in results],
                         [("first", "action-failed", "memory"), ("second", "ok", None)])
        summary = fuzz.report({e["name"]: e for e in entries}, results)
        self.assertEqual(list(summary["contract_failures"]), ["first"])

    def test_contracts_run_through_the_fuzz_script_with_their_peer(self) -> None:
        entry = {**target().entry, "cases": []}
        commands = []

        def run(command: list[str], **kwargs: Any) -> subprocess.CompletedProcess[str]:
            commands.append(command)
            if "--help" in command:
                return subprocess.CompletedProcess(command, 0, stdout="run-action")
            if "build" in command:
                return subprocess.CompletedProcess(command, 0)
            outputs = Path(command[command.index("--outputs-dir") + 1]) / "solidity-hol" / \
                fuzz.fleet.CONTEXT
            outputs.mkdir(parents=True)
            (outputs / "results.jsonl").write_text(fuzz.PREFIX + json.dumps(
                {"kind": "contract", "contract": SUITE, "status": "ok", "unsupported": []}) + "\n")
            kwargs["stdout"].write(f"solidity-hol:{fuzz.fleet.CONTEXT} {'a' * 64} done\n")
            return subprocess.CompletedProcess(command, 0)

        with tempfile.TemporaryDirectory() as temporary, \
                patch.dict(fuzz.fleet.os.environ, {}, clear=True), \
                patch.object(fuzz.fleet.subprocess, "run", side_effect=run):
            results = fuzz.run_fleet("holbuild", Path(temporary) / "work", [entry])
            [action] = [c for c in commands if "run-action" in c]
            script = Path(action[action.index("--script") + 1])
            self.assertEqual(script.read_text(), fuzz.SCRIPT.path.read_text())
            [staged] = json.loads((script.parent / "batch.json").read_text())["contracts"]
            self.assertEqual(staged["peer"]["artifact"], "0.peer.json")
            self.assertTrue((script.parent / "0.peer.json").is_file())
        self.assertEqual([r["contract"] for r in results], [SUITE])


@unittest.skipUnless(sys.version_info[:2] == (3, 11), "pyrevm runs on Python 3.11")
class ScreeningTests(unittest.TestCase):
    def setUp(self) -> None:
        try:
            import pyrevm  # type: ignore[import-not-found]
        except ImportError:
            self.skipTest("pyrevm is not installed")
        self.pyrevm = pyrevm

    def test_recordings_cover_returns_reverts_and_storage_writes(self) -> None:
        t = target()
        recordings = [fuzz.screen(self.pyrevm, t, c) for c in fuzz.generate_calls(0, t, 30)]
        kinds = Counter(next(iter(r.expect)) for r in recordings)
        self.assertGreater(kinds["returned"], 0)
        self.assertGreater(kinds["revert"], 0)
        self.assertTrue(any(r.final_storage for r in recordings))

    def test_calls_over_the_gas_budget_are_dropped(self) -> None:
        t = target()
        c = fuzz.generate_calls(0, t, 1)[0]
        fuzz.screen(self.pyrevm, t, c)
        with patch.object(fuzz, "GAS_BUDGET", 0), self.assertRaisesRegex(fuzz.Halt, "OverGasBudget"):
            fuzz.screen(self.pyrevm, t, c)

    def test_logs_are_recorded(self) -> None:
        t = target("qualified_events")
        recordings = [fuzz.screen(self.pyrevm, t, c) for c in fuzz.generate_calls(0, t, 30)]
        logged = [log for r in recordings for log in r.logs]
        self.assertTrue(logged)
        self.assertTrue(all(log["logger"] == fuzz.address(fuzz.CONTRACT) for log in logged))


if __name__ == "__main__":
    unittest.main()
