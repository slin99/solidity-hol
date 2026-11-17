#!/usr/bin/env python3

import contextlib
import io
import json
from pathlib import Path
import shutil
import sys
import tempfile
import textwrap
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))

import run_differential as driver  # noqa: E402

SOURCE = "testdata/differential/a.sol"
ARTIFACT = "testdata/differential/expected/a.json"


def corpus(cases=None):
    return {
        "format": driver.CORPUS_FORMAT,
        "fuel": 1000,
        "suites": [{
            "name": "a",
            "source": SOURCE,
            "contract": "A",
            "artifact": ARTIFACT,
            "cases": cases if cases is not None else [
                {"name": "f_returns", "function": "f", "args": [1, True, "0x00ff"],
                 "expect": {"return": [2]}},
            ],
        }],
    }


class FakeRoot:
    """A repository root with one suite, its artifact and a fake holbuild."""

    def __init__(self, directory: Path, source: str = "contract A {}\n") -> None:
        self.root = directory
        shutil.copyfile(ROOT / "SOLIDITY_PIN", directory / "SOLIDITY_PIN")
        (directory / "profiles").mkdir()
        profile = driver.exporter.DEFAULT_PROFILE
        shutil.copyfile(profile, directory / "profiles" / profile.name)
        optimized = driver.exporter.OPTIMIZED_PROFILE
        shutil.copyfile(optimized, directory / "profiles" / optimized.name)
        self.write_corpus(corpus())
        self.write(SOURCE, source)
        pin = (ROOT / "SOLIDITY_PIN").read_text(encoding="ascii").strip()
        self.write(ARTIFACT, json.dumps({
            "format": driver.ARTIFACT_FORMAT,
            "compiler": {"pin": pin, "reportedVersion": f"Version: 0.8.37+commit.{pin[:8]}"},
            "profile": json.loads(profile.read_text(encoding="utf-8")),
            "input": {
                "settings": {**json.loads(profile.read_text(encoding="utf-8"))["settings"],
                             "outputSelection": driver.exporter.OUTPUT_SELECTION},
                "sources": {SOURCE: {"content": "contract A {}\n"}},
            },
            "output": {"contracts": {SOURCE: {"A": {"evm": {"deployedBytecode": {"object": "00"}}}}}},
        }))
        self.wrappers()

    def write_corpus(self, data: dict) -> None:
        manifest = {key: value for key, value in data.items() if key != "suites"}
        manifest["suite_directory"] = "suites"
        self.write(driver.CORPUS.as_posix(), json.dumps(manifest))
        for suite in data["suites"]:
            self.write(f"testdata/differential/suites/{suite['name']}.json", json.dumps(suite))

    def wrappers(self) -> None:
        data = driver.load_corpus(self.root / driver.CORPUS)
        driver.theories.write_wrappers(
            self.root, driver.theories.wrappers(self.root, driver.CORPUS, data))

    def write(self, name: str, text: str) -> None:
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")

    def holbuild(self, results: list[dict], status: int, *, cached: bool = False) -> Path:
        """Write declared verdict outputs on success and diagnostic logs on failure."""
        path = self.root / "holbuild"
        path.write_text(textwrap.dedent(f"""\
            #!{sys.executable}
            import json
            from pathlib import Path
            import sys
            results = {results!r}
            for target in sys.argv[1:]:
                if not target.startswith('solidityDifferentialCorpus_'):
                    continue
                suite = target.removeprefix('solidityDifferentialCorpus_').removesuffix('Theory')
                log = Path('.holbuild/logs/current/solidity-hol') / target / 'build.log'
                log.parent.mkdir(parents=True, exist_ok=True)
                log.write_text(''.join({driver.RESULT_PREFIX!r} + json.dumps(r) + '\\n'
                                      for r in results if r.get('suite') == suite))
                if {status} == 0:
                    output = Path('tests/corpus') / (target.removesuffix('Theory') + '.results.jsonl')
                    output.write_text(log.read_text())
                if {cached!r}:
                    log.unlink()
                    print(target + ' restored from cache')
                else:
                    print('child log: ' + str(log.resolve()))
            sys.exit({status})
            """), encoding="utf-8")
        path.chmod(0o755)
        return path

    def run(self, holbuild: Path) -> tuple[int, dict]:
        report_dir = self.root / "report"
        with contextlib.redirect_stdout(io.StringIO()):
            status = driver.main(["--holbuild", str(holbuild), "--report-dir", str(report_dir)],
                                 root=self.root)
        report = json.loads((report_dir / "report.json").read_text(encoding="utf-8"))
        return status, report


SUITE_OK = {"kind": "suite", "suite": "a", "status": "ok"}
RETURNED = {"returned": "0x" + "00" * 31 + "02"}


class CorpusTests(unittest.TestCase):
    def test_discovers_new_suite_files_without_editing_shared_lists(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fake = FakeRoot(Path(temporary))
            data = corpus()
            suite = data.pop("suites")[0]
            data["suite_directory"] = "suites"
            fake.write(driver.CORPUS.as_posix(), json.dumps(data))
            (fake.root / "testdata/differential/suites/a.json").unlink()
            fake.write("testdata/differential/suites/z.json", json.dumps(suite))
            other = {**suite, "name": "another"}
            fake.write("testdata/differential/suites/a.json", json.dumps(other))
            loaded = driver.load_corpus(fake.root / driver.CORPUS)
            self.assertEqual([s["name"] for s in loaded["suites"]], ["another", "a"])
            fake.wrappers()
            self.assertEqual(driver.check_staging(fake.root, driver.CORPUS, loaded)["status"],
                             "pass")
            fake.write("testdata/differential/suites/duplicate.json", json.dumps(other))
            with self.assertRaisesRegex(driver.CorpusError, "duplicate suite another"):
                driver.load_corpus(fake.root / driver.CORPUS)

    def test_suite_files_must_be_valid_and_staged(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fake = FakeRoot(Path(temporary))
            data = corpus()
            suite = data.pop("suites")[0]
            data["suite_directory"] = "suites"
            fake.write(driver.CORPUS.as_posix(), json.dumps(data))
            path = "testdata/differential/suites/a.json"
            fake.write(path, json.dumps(suite))
            loaded = driver.load_corpus(fake.root / driver.CORPUS)
            (fake.root / "tests/corpus/solidityBytecodeCorpus_aScript.sml").unlink()
            check = driver.check_staging(fake.root, driver.CORPUS, loaded)
            self.assertEqual(check["status"], "fail")
            self.assertIn("solidityBytecodeCorpus_aScript.sml", check["detail"])
            fake.write(path, "{")
            with self.assertRaises(driver.CorpusError):
                driver.load_corpus(fake.root / driver.CORPUS)

    def test_committed_corpus_is_consistent(self) -> None:
        loaded = driver.load_corpus(ROOT / driver.CORPUS)
        checks = driver.check_artifacts(ROOT, loaded)
        checks.append(driver.check_staging(ROOT, driver.CORPUS, loaded))
        self.assertEqual([c for c in checks if c["status"] != "pass"], [])
        rollup = (ROOT / "tests/solidityDifferentialCorpusScript.sml").read_text(
            encoding="utf-8")
        self.assertEqual(rollup, driver.theories.rollup(loaded))

    def test_rejects_duplicate_cases(self) -> None:
        case = {"name": "f", "function": "f", "args": [], "expect": {"panic": 17}}
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "corpus.json"
            path.write_text(json.dumps(corpus([case, case])), encoding="utf-8")
            with self.assertRaisesRegex(driver.CorpusError, "duplicate case"):
                driver.load_corpus(path)

    def test_rejects_malformed_expectation(self) -> None:
        case = {"name": "f", "function": "f", "args": [], "expect": {"return": [1], "panic": 1}}
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "corpus.json"
            path.write_text(json.dumps(corpus([case])), encoding="utf-8")
            with self.assertRaisesRegex(driver.CorpusError, "exactly one"):
                driver.load_corpus(path)

    def test_raw_return_expectation(self) -> None:
        driver.check_expectation({"returned": "0x00ff"}, "expect")
        with self.assertRaisesRegex(driver.CorpusError, "returned must be"):
            driver.check_expectation({"returned": [0, 255]}, "expect")

    def test_rejects_malformed_storage(self) -> None:
        for storage, message in [([1], "object from slot"),
                                 ({"0x1": 1}, "slot '0x1'"),
                                 ({"0": -1}, r"\[0\] is not a 256-bit word"),
                                 ({"0": "0x01" + "00" * 32}, r"\[0\] is not a 256-bit word")]:
            case = {"name": "f", "function": "f", "args": [], "storage": storage,
                    "expect": {"return": []}}
            with self.subTest(storage=storage), tempfile.TemporaryDirectory() as temporary:
                path = Path(temporary) / "corpus.json"
                path.write_text(json.dumps(corpus([case])), encoding="utf-8")
                with self.assertRaisesRegex(driver.CorpusError, message):
                    driver.load_corpus(path)

    def test_accepts_transaction_cases(self) -> None:
        cases = [{"name": "raw", "calldata": "0x", "sender": "0x3000", "value": 5,
                  "expect": {"return": []},
                  "logs": [{"topics": ["0x" + "11" * 32, 2], "data": "0x"},
                           {"logger": "0x5000", "topics": [], "data": "0x"}]},
                 {"name": "named", "function": "f", "args": [], "value": "7",
                  "expect": {"revert": "0x"}, "logs": []},
                 {"name": "deploy", "deploy": True, "args": [1],
                  "expect": {"return": []}},
                 {"name": "deploy_raw", "deploy": True, "calldata": "0x01",
                  "expect": {"revert": "0x"}}]
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "corpus.json"
            path.write_text(json.dumps(corpus(cases)), encoding="utf-8")
            driver.load_corpus(path)

    def test_rejects_malformed_transaction_cases(self) -> None:
        base = {"name": "f", "expect": {"return": []}}
        for fields, message in [
                ({"calldata": "0x", "function": "f"}, "calldata excludes"),
                ({"calldata": "0x", "deploy": True, "args": []}, "calldata excludes"),
                ({"deploy": False, "args": []}, "deploy must be true"),
                ({"deploy": True, "function": "f", "args": []}, "deploy must be true"),
                ({"deploy": True, "args": [], "storage": {"0": 1}}, "deploy must be true"),
                ({"calldata": "00"}, "calldata must be"),
                ({}, "function must be"),
                ({"calldata": "0x", "sender": 2**160}, "sender must be a 160-bit word"),
                ({"calldata": "0x", "sender": "0x1000"}, "not be the contract or peer"),
                ({"calldata": "0x", "sender": "0x5000"}, "not be the contract or peer"),
                ({"calldata": "0x", "peer_storage": {}}, "peer_storage without a peer"),
                ({"calldata": "0x", "value": -1}, "value must be a 127-bit word"),
                ({"calldata": "0x", "value": 2**127}, "value must be a 127-bit word"),
                ({"calldata": "0x12g4"}, "calldata must be"),
                ({"calldata": "0x", "logs": [{"topics": [1] * 5, "data": "0x"}]},
                 "at most 4"),
                ({"calldata": "0x", "logs": [{"topics": [2**256], "data": "0x"}]},
                 r"topics\[0\] must be a 256-bit word"),
                ({"calldata": "0x", "logs": [{"topics": [], "data": "ab"}]},
                 "data must be 0x-prefixed hex"),
                ({"calldata": "0x", "logs": [{"topics": []}]}, "must have topics, data"),
                ({"calldata": "0x", "logs": [{"topics": [], "data": "0x", "logger": 2**160}]},
                 r"logger must be a 160-bit word")]:
            case = {**base, **fields}
            with self.subTest(fields=fields), tempfile.TemporaryDirectory() as temporary:
                path = Path(temporary) / "corpus.json"
                path.write_text(json.dumps(corpus([case])), encoding="utf-8")
                with self.assertRaisesRegex(driver.CorpusError, message):
                    driver.load_corpus(path)

    def test_peer_suites(self) -> None:
        peer = {"source": "p.sol", "contract": "P", "artifact": "p.json"}
        case = {"name": "f", "calldata": "0x", "peer_storage": {"0": 1},
                "expect": {"return": []}}
        for suite_peer, message in [(peer, None),
                                    ({**peer, "extra": "x"}, "peer must have exactly"),
                                    ({**peer, "contract": ""}, "peer must have exactly")]:
            data = corpus([case])
            data["suites"][0]["peer"] = suite_peer
            with self.subTest(peer=suite_peer), tempfile.TemporaryDirectory() as temporary:
                path = Path(temporary) / "corpus.json"
                path.write_text(json.dumps(data), encoding="utf-8")
                if message is None:
                    driver.load_corpus(path)
                else:
                    with self.assertRaisesRegex(driver.CorpusError, message):
                        driver.load_corpus(path)

    def test_detects_unstaged_peer_artifact(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fake = FakeRoot(Path(temporary))
            data = corpus()
            data["suites"][0]["peer"] = {"source": SOURCE, "contract": "A",
                                         "artifact": "testdata/peer.json"}
            fake.write("testdata/peer.json", (fake.root / ARTIFACT).read_text())
            fake.write_corpus(data)
            loaded = driver.load_corpus(fake.root / driver.CORPUS)
            check = driver.check_staging(fake.root, driver.CORPUS, loaded)
            self.assertEqual(check["status"], "fail")
            fake.wrappers()
            text = (fake.root / "tests/corpus/solidityBytecodeCorpus_aScript.sml").read_text()
            self.assertEqual(driver.unstaged_files(text, {"../../testdata/peer.json"}), [])

    def test_detects_stale_artifact(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fake = FakeRoot(Path(temporary), source="contract A { }\n")
            checks = driver.check_artifacts(fake.root, corpus())
            failed = [c["check"] for c in checks if c["status"] != "pass"]
            self.assertEqual(failed, ["source-fresh"])

    def test_detects_stale_imported_source(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fake = FakeRoot(Path(temporary))
            artifact = json.loads((fake.root / ARTIFACT).read_text(encoding="utf-8"))
            artifact["input"]["sources"]["testdata/base.sol"] = {"content": "contract B {}\n"}
            fake.write(ARTIFACT, json.dumps(artifact))
            fake.write("testdata/base.sol", "contract B { }\n")
            checks = driver.check_artifacts(fake.root, corpus())
            failed = [(c["check"], c["subject"]) for c in checks if c["status"] != "pass"]
            self.assertEqual(failed, [("source-fresh", f"{ARTIFACT}:testdata/base.sol")])

    def test_detects_unstaged_artifact(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fake = FakeRoot(Path(temporary))
            fake.write("tests/corpus/solidityBytecodeCorpus_aScript.sml", "val () = ()\n")
            loaded = driver.load_corpus(fake.root / driver.CORPUS)
            self.assertEqual(driver.check_staging(fake.root, driver.CORPUS, loaded)["status"],
                             "fail")

    def test_detects_compiler_identity_inconsistent_with_pin_and_profile(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fake = FakeRoot(Path(temporary))
            path = fake.root / ARTIFACT
            artifact = json.loads(path.read_text(encoding="utf-8"))
            commit = artifact["compiler"]["pin"][:8]
            for version in (f"Version: 0.8.20+commit.{commit}",
                            "Version: 0.8.37+commit.00000000",
                            f"Version: 0.8.37+commit.{commit[:4]}",
                            "Version: 0.8.37", None):
                with self.subTest(version=version):
                    artifact["compiler"]["reportedVersion"] = version
                    fake.write(ARTIFACT, json.dumps(artifact))
                    checks = driver.check_artifacts(fake.root, corpus())
                    self.assertEqual([c["check"] for c in checks if c["status"] != "pass"],
                                     ["artifact-compiler-version"])

    def test_reproduces_artifacts_with_recorded_remappings(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fake = FakeRoot(Path(temporary))
            artifact = json.loads((fake.root / ARTIFACT).read_text(encoding="utf-8"))
            artifact["input"]["language"] = "Solidity"
            artifact["input"]["settings"]["remappings"] = ["a/=b/"]
            fake.write(ARTIFACT, driver.exporter.json_text(artifact))
            with patch.object(driver.exporter, "ROOT", fake.root), \
                 patch.object(driver.exporter, "compiler_identity",
                              return_value=artifact["compiler"]["reportedVersion"]), \
                 patch.object(driver.exporter, "compile_standard_json",
                              return_value=artifact["output"]) as compile_json:
                checks = driver.reproduce_artifacts(fake.root, corpus(), Path("solc"), False)
            self.assertEqual([c for c in checks if c["status"] != "pass"], [])
            self.assertEqual(compile_json.call_args.args[1], artifact["input"])

    def test_reproduction_rejects_malformed_remappings_before_compiling(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fake = FakeRoot(Path(temporary))
            artifact = json.loads((fake.root / ARTIFACT).read_text(encoding="utf-8"))
            for settings in (None, [], {"remappings": "a/=b/"},
                             {"remappings": [1]}, {"remappings": ["a/b/"]}):
                with self.subTest(settings=settings):
                    artifact["input"]["settings"] = settings
                    fake.write(ARTIFACT, driver.exporter.json_text(artifact))
                    with patch.object(driver.exporter, "build_artifact_from_sources") as build:
                        checks = driver.reproduce_artifacts(
                            fake.root, corpus(), Path("solc"), False)
                    build.assert_not_called()
                    self.assertEqual([c["status"] for c in checks], ["fail"])
                    self.assertIn("input", checks[0]["detail"])

    def test_checks_optional_remappings(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fake = FakeRoot(Path(temporary))
            artifact = json.loads((fake.root / ARTIFACT).read_text(encoding="utf-8"))
            for remappings, accepted in (([], True), (["a/=b/"], True),
                                          ("a/=b/", False), ([1], False),
                                          (["a/b/"], False), (None, False)):
                with self.subTest(remappings=remappings):
                    artifact["input"]["settings"]["remappings"] = remappings
                    fake.write(ARTIFACT, json.dumps(artifact))
                    checks = driver.check_artifacts(fake.root, corpus())
                    self.assertEqual([c["check"] for c in checks if c["status"] != "pass"],
                                     [] if accepted else ["artifact-settings"])

    def test_detects_input_settings_inconsistent_with_profile(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fake = FakeRoot(Path(temporary))
            original = json.loads((fake.root / ARTIFACT).read_text(encoding="utf-8"))
            for key, value in (("viaIR", False), ("evmVersion", "paris"),
                               ("outputSelection", {})):
                with self.subTest(setting=key):
                    artifact = json.loads(json.dumps(original))
                    artifact["input"]["settings"]["remappings"] = ["a/=b/"]
                    artifact["input"]["settings"][key] = value
                    fake.write(ARTIFACT, json.dumps(artifact))
                    checks = driver.check_artifacts(fake.root, corpus())
                    self.assertEqual([c["check"] for c in checks if c["status"] != "pass"],
                                     ["artifact-settings"])

    def test_optimized_profile_requires_stack_depth_fallback(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fake = FakeRoot(Path(temporary))
            artifact = json.loads((fake.root / ARTIFACT).read_text())
            default = artifact["profile"]
            optimized = driver.exporter.read_json(driver.exporter.OPTIMIZED_PROFILE)
            artifact["profile"] = optimized
            artifact["input"]["settings"].update(optimized["settings"])
            stack = {"severity": "error", "type": "YulException",
                     "message": "variable too deep in the stack"}
            for failure, accepted in (
                (None, False), ({"profile": default, "errors": []}, False),
                ({"profile": default, "errors": [stack]}, True),
                ({"profile": optimized, "errors": [stack]}, False),
                ({"profile": default, "errors": [{**stack, "type": "ParserError"}]}, False),
            ):
                with self.subTest(failure=failure):
                    if failure is None:
                        artifact.pop("unoptimizedFailure", None)
                    else:
                        artifact["unoptimizedFailure"] = failure
                    fake.write(ARTIFACT, json.dumps(artifact))
                    checks = driver.check_artifacts(fake.root, corpus())
                    self.assertEqual([c["check"] for c in checks if c["status"] != "pass"],
                                     [] if accepted else ["artifact-profile"])
            fake.wrappers()
            wrapper = fake.root / "tests/corpus/solidityDifferentialCorpus_aScript.sml"
            self.assertIn(driver.exporter.OPTIMIZED_PROFILE.name, wrapper.read_text())

    def test_default_profile_rejects_fallback_metadata(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fake = FakeRoot(Path(temporary))
            artifact = json.loads((fake.root / ARTIFACT).read_text())
            artifact["unoptimizedFailure"] = None
            fake.write(ARTIFACT, json.dumps(artifact))
            checks = driver.check_artifacts(fake.root, corpus())
            self.assertEqual([c["check"] for c in checks if c["status"] != "pass"],
                             ["artifact-profile"])


class DriverTests(unittest.TestCase):
    def test_cache_is_default_and_force_is_explicit(self) -> None:
        self.assertFalse(driver.parse_args([]).force)
        self.assertFalse(driver.parse_args(["--allow-cached"]).force)
        self.assertTrue(driver.parse_args(["--force"]).force)

    def test_shards_are_stable_disjoint_and_complete(self) -> None:
        suites = [{**corpus()["suites"][0], "name": name}
                  for name in ("echo", "alpha", "delta", "bravo", "charlie")]
        data = {**corpus(), "suites": suites}
        shards = [driver.select_shard(data, 3, index)["suites"] for index in range(3)]
        names = [[suite["name"] for suite in shard] for shard in shards]
        self.assertEqual(names, [["charlie"], ["bravo", "delta"], ["alpha", "echo"]])
        self.assertEqual(sorted(name for shard in names for name in shard),
                         sorted(suite["name"] for suite in suites))

        expanded = {**data, "suites": suites + [
            {**corpus()["suites"][0], "name": "aardvark"},
        ]}
        assignments = {name: index for index, shard in enumerate(names) for name in shard}
        expanded_assignments = {
            suite["name"]: index
            for index in range(3)
            for suite in driver.select_shard(expanded, 3, index)["suites"]
        }
        self.assertEqual({name: expanded_assignments[name] for name in assignments},
                         assignments)

    def test_rejects_invalid_or_empty_shards(self) -> None:
        for argv in (["--shard-count", "0"],
                     ["--shard-count", "2", "--shard-index", "2"],
                     ["--shard-index", "-1"]):
            with self.subTest(argv=argv), self.assertRaises(SystemExit):
                driver.parse_args(argv)
        with self.assertRaisesRegex(driver.CorpusError, "contains no suites"):
            driver.select_shard(corpus(), 2, 1)

    def test_agreement_passes(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fake = FakeRoot(Path(temporary))
            status, report = fake.run(fake.holbuild([
                SUITE_OK,
                {"kind": "case", "suite": "a", "case": "f_returns", "status": "agree",
                 "theorem": "a_f_returns", "outcome": RETURNED},
            ], 0))
            self.assertEqual(status, 0)
            self.assertNotIn("--force=theory", report["hol"]["command"])
            self.assertEqual(report["failures"], [])
            self.assertIn({"theorem": "a_f_returns", "suite": "a", "case": "f_returns",
                           "status": "proved", "outcome": RETURNED}, report["kernel_checked"])

    def test_missing_artifact_is_reported_without_a_traceback(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fake = FakeRoot(Path(temporary))
            (fake.root / ARTIFACT).unlink()
            status, report = fake.run(fake.holbuild([], 1))
        self.assertEqual(status, 1)
        self.assertIn("artifact-readable", [failure.get("check")
                                           for failure in report["failures"]])
        self.assertIn("corpus-staged", [failure.get("check")
                                       for failure in report["failures"]])

    def test_altered_expectation_fails_with_reproduction(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fake = FakeRoot(Path(temporary))
            unexpected = {"kind": "case", "suite": "a", "case": "f_returns",
                          "status": "unexpected", "bytecode": RETURNED, "source": RETURNED,
                          "expected": {"returned": "0x" + "00" * 31 + "03"}}
            status, report = fake.run(fake.holbuild([SUITE_OK, unexpected], 1))
            self.assertEqual(status, 1)
            self.assertEqual([f["status"] for f in report["failures"]], ["unexpected"])
            directory = fake.root / "report" / "failures" / "a" / "f_returns"
            for name in ("inputs.json", "outcomes.json", "compiler.json", "artifact.json",
                         "sources/" + SOURCE):
                self.assertTrue((directory / name).is_file(), name)
            outcomes = json.loads((directory / "outcomes.json").read_text(encoding="utf-8"))
            self.assertEqual(outcomes["bytecode"], RETURNED)

    def test_suite_rejection_fails(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fake = FakeRoot(Path(temporary))
            rejected = {"kind": "suite", "suite": "a", "status": "import-rejected",
                        "message": "unsupported nodeType"}
            status, report = fake.run(fake.holbuild([rejected], 1))
            self.assertEqual(status, 1)
            self.assertEqual([f["status"] for f in report["failures"]], ["import-rejected"])
            self.assertEqual(report["kernel_checked"], [])

    def test_missing_result_fails(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fake = FakeRoot(Path(temporary))
            status, report = fake.run(fake.holbuild([SUITE_OK], 0))
            self.assertEqual(status, 1)
            self.assertEqual([f["status"] for f in report["failures"]], ["missing"])

    def test_missing_suite_result_fails_without_claiming_witnesses(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fake = FakeRoot(Path(temporary))
            status, report = fake.run(fake.holbuild([], 0))
            self.assertEqual(status, 1)
            self.assertEqual([f["status"] for f in report["failures"]], ["missing"])
            self.assertEqual(report["kernel_checked"], [])
            self.assertTrue((fake.root / "report/failures/a/inputs.json").is_file())

    def test_missing_suite_result_does_not_discard_other_suites(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fake = FakeRoot(Path(temporary))
            data = corpus()
            second = {**data["suites"][0], "name": "b"}
            data["suites"].append(second)
            fake.write_corpus(data)
            fake.wrappers()
            status, report = fake.run(fake.holbuild([
                SUITE_OK,
                {"kind": "case", "suite": "a", "case": "f_returns", "status": "agree",
                 "theorem": "a_f_returns", "outcome": RETURNED},
            ], 0))
            self.assertEqual(status, 1)
            self.assertEqual([(f["suite"], f["status"]) for f in report["failures"]],
                             [("b", "missing")])
            self.assertEqual(len(report["kernel_checked"]), 3)
            self.assertTrue(all(w["suite"] == "a" for w in report["kernel_checked"]))

    def test_cached_build_keeps_witnesses_without_result_log(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fake = FakeRoot(Path(temporary))
            status, report = fake.run(fake.holbuild([
                SUITE_OK,
                {"kind": "case", "suite": "a", "case": "f_returns", "status": "agree",
                 "outcome": RETURNED},
            ], 0, cached=True))
            self.assertEqual(status, 0)
            self.assertEqual(len(report["kernel_checked"]), 3)
            self.assertTrue(all(w["status"] == "proved (cached)"
                                for w in report["kernel_checked"]))
            self.assertEqual(report["kernel_checked"][-1]["outcome"], RETURNED)

    def test_cached_build_without_verdict_file_fails(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fake = FakeRoot(Path(temporary))
            fake.write("holbuild", f"#!{sys.executable}\nprint('restored from cache')\n")
            command = fake.root / "holbuild"
            command.chmod(0o755)
            status, report = fake.run(command)
        self.assertEqual(status, 1)
        self.assertEqual(report["kernel_checked"], [])
        self.assertEqual([f["status"] for f in report["failures"]], ["missing"])

    def test_failed_build_ignores_stale_success_file(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fake = FakeRoot(Path(temporary))
            fake.write(driver.theories.results_path("solidityDifferentialCorpus_aTheory").as_posix(),
                       driver.RESULT_PREFIX + json.dumps(SUITE_OK) + "\n" +
                       driver.RESULT_PREFIX + json.dumps({"kind": "case", "suite": "a",
                           "case": "f_returns", "status": "agree", "outcome": RETURNED}))
            status, report = fake.run(fake.holbuild([], 1))
        self.assertEqual(status, 1)
        self.assertEqual(report["kernel_checked"], [])
        self.assertEqual([f["kind"] for f in report["failures"]], ["hol-build"])

    def test_cached_partial_verdict_file_fails(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fake = FakeRoot(Path(temporary))
            status, report = fake.run(fake.holbuild([SUITE_OK], 0, cached=True))
        self.assertEqual(status, 1)
        self.assertFalse(any("case" in w for w in report["kernel_checked"]))
        self.assertEqual([f["status"] for f in report["failures"]], ["missing"])

    def test_bytecode_failure_never_claims_source_witnesses(self) -> None:
        rows = [
            {"kind": "case", "suite": "a", "case": "f_returns",
             "side": "bytecode", "status": "agree"},
            {"kind": "case", "suite": "a", "case": "later",
             "side": "bytecode", "status": "error", "message": "mismatch"},
        ]
        with tempfile.TemporaryDirectory() as temporary:
            fake = FakeRoot(Path(temporary))
            status, report = fake.run(fake.holbuild(rows, 1))
        self.assertEqual(status, 1)
        self.assertEqual(report["kernel_checked"], [])

    def test_mixed_cached_and_executed_suites_do_not_read_stale_logs(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fake = FakeRoot(Path(temporary))
            data = corpus()
            data["suites"].append({**data["suites"][0], "name": "b"})
            fake.write_corpus(data)
            fake.wrappers()
            targets = {driver.theories.theory_name(name, "source") + "Theory": name
                       for name in ("a", "b")}
            for target in targets:
                fake.write(f".holbuild/logs/current/solidity-hol/{target}/build.log",
                           driver.RESULT_PREFIX + json.dumps(SUITE_OK) + "\n")
            for target, suite in targets.items():
                rows = [{**SUITE_OK, "suite": suite}]
                if suite == "b":
                    rows.append({"kind": "case", "suite": suite, "case": "f_returns",
                                 "status": "agree", "outcome": RETURNED})
                fake.write(driver.theories.results_path(target).as_posix(),
                           "".join(driver.RESULT_PREFIX + json.dumps(row) + "\n" for row in rows))
            fake.write("holbuild", f"#!{sys.executable}\n" +
                       f"print('{next(iter(targets))} built')\n")
            command = fake.root / "holbuild"
            command.chmod(0o755)
            status, report = fake.run(command)
        self.assertEqual(status, 1)
        self.assertEqual([(f["suite"], f["status"]) for f in report["failures"]],
                         [("a", "missing")])
        witnesses = [w for w in report["kernel_checked"] if w["suite"] == "b"]
        self.assertEqual(len(witnesses), 3)
        self.assertTrue(all(w["status"] == "proved (cached)" for w in witnesses))

    def test_one_suite_keeps_its_own_log_when_a_dependency_also_fails(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fake = FakeRoot(Path(temporary))
            target = "solidityDifferentialCorpus_aTheory"
            logs = []
            for theory, case in ((target, "source_failure"),
                                 ("solidityBytecodeCorpus_aTheory", "bytecode_failure")):
                path = f".holbuild/logs/current/solidity-hol/{theory}/build.log"
                fake.write(path, driver.RESULT_PREFIX + json.dumps(
                    {"kind": "case", "suite": "a", "case": case, "status": "error"}))
                logs.append(str(fake.root / path))
            fake.write("holbuild", f"#!{sys.executable}\nimport sys\n" +
                       "\n".join(f"print({prefix + log!r})" for prefix, log in
                                 zip(("child log: ", "instrumented log: "), logs)) +
                       "\nsys.exit(1)\n")
            command = fake.root / "holbuild"
            command.chmod(0o755)
            with contextlib.redirect_stdout(io.StringIO()):
                result = driver.run_hol(fake.root, str(command), 1, False, [],
                                        suite_targets={target: "a"})
        self.assertEqual(result["status"], 1)
        self.assertEqual([row["case"] for row in result["results"]],
                         ["source_failure", "bytecode_failure"])

    def test_build_failure_without_results_fails(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fake = FakeRoot(Path(temporary))
            status, report = fake.run(fake.holbuild([], 1))
            self.assertEqual(status, 1)
            self.assertEqual([f["kind"] for f in report["failures"]], ["hol-build"])


if __name__ == "__main__":
    unittest.main()
