#!/usr/bin/env python3

from pathlib import Path
import sys
import tempfile
import textwrap
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))

import semantic_tests_coverage as coverage  # noqa: E402

PROFILE = {"settings": {"evmVersion": "osaka", "debug": {"revertStrings": "default"}}}


class ReadTestTests(unittest.TestCase):
    def read(self, text: str) -> coverage.SemanticTest:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            path = root / "dir" / "t.sol"
            path.parent.mkdir()
            path.write_text(textwrap.dedent(text), encoding="utf-8")
            return coverage.read_test(root, path)

    def test_splits_sources_and_reads_settings(self) -> None:
        test = self.read("""\
            ==== Source: a.sol ====
            contract A {}
            ==== Source: b.sol ====
            import "a.sol";
            // ====
            // EVMVersion: >=cancun
            // compileViaYul: true
            // ----
            // f() -> 1
            """)
        self.assertEqual(test.name, "dir/t.sol")
        self.assertEqual(list(test.sources), ["a.sol", "b.sol"])
        self.assertEqual(test.sources["a.sol"], "contract A {}\n")
        self.assertEqual(test.sources["b.sol"], 'import "a.sol";\n')
        self.assertEqual(test.settings, {"EVMVersion": ">=cancun", "compileViaYul": "true"})
        self.assertIsNone(coverage.skip_reason(test, PROFILE))

    def test_skips_by_own_settings(self) -> None:
        def reason(settings: str) -> str | None:
            return coverage.skip_reason(
                self.read(f"contract C {{}}\n// ====\n{settings}// ----\n"), PROFILE)

        self.assertIn("legacy", reason("// compileViaYul: false\n"))
        self.assertIn("EVMVersion: <osaka", reason("// EVMVersion: <osaka\n"))
        self.assertIsNone(reason("// EVMVersion: >=osaka\n"))
        self.assertIn("revertStrings: debug", reason("// revertStrings: debug\n"))


class CompileTests(unittest.TestCase):
    def test_compilation_retains_artifact_contract_for_preparation(self) -> None:
        metadata = {"storageLayout": {"storage": [{"astId": 3, "slot": "0"}]},
                    "evm": {"deployedBytecode": {"object": "00"}}}
        output = {"sources": {"t.sol": {"ast": {"nodeType": "SourceUnit", "id": 1, "nodes": []}}},
                  "contracts": {"t.sol": {"C": metadata}}}
        artifact = {"format": "solidity-hol-solc-artifact-v1", "compiler": {"pin": "pinned"},
                    "profile": PROFILE, "input": {"settings": PROFILE["settings"]},
                    "output": output}
        with patch.object(coverage.exporter, "build_artifact_from_sources",
                          return_value=artifact):
            result = coverage.compile_test(Path("solc"), coverage.SemanticTest("t.sol", {}, {}),
                                           Path("profile"))
        self.assertEqual(result, artifact)


class FeatureTests(unittest.TestCase):
    def test_reasons_drop_node_ids(self) -> None:
        self.assertEqual(coverage.reason("IndexRangeAccess 12: unsupported expression IndexRangeAccess"),
                         "IndexRangeAccess: unsupported expression IndexRangeAccess")
        self.assertEqual(coverage.reason("InlineAssembly 5: YulFunctionCall 7: call to balance"),
                         "InlineAssembly: YulFunctionCall: call to balance")
        self.assertEqual(coverage.reason("42: unsupported member access"), "unsupported member access")

    def test_lines_are_labelled_by_the_first_matching_pattern(self) -> None:
        self.assertEqual(coverage.feature("TryStatement 3: typed catch clauses are not supported"), "try/catch")
        self.assertEqual(coverage.feature("FunctionDefinition 9: unsupported source unit member "
                                          "FunctionDefinition"), "free functions")

    def test_an_unlabelled_line_is_its_own_feature(self) -> None:
        self.assertEqual(coverage.feature("42: unsupported member access"), "unsupported member access")


class ReportTests(unittest.TestCase):
    def test_classification_keeps_every_blocker(self) -> None:
        result = coverage.classify("t.sol", {"status": "import-rejected", "blockers": [
            "IndexRangeAccess 4: unsupported expression IndexRangeAccess",
            "7: unsupported member access"]})
        self.assertEqual(result.category, coverage.IMPORT_REJECTED)
        self.assertEqual(result.features(), {"array slices", "unsupported member access"})

    def test_unknown_statuses_are_errors(self) -> None:
        with self.assertRaises(ValueError):
            coverage.classify("t.sol", {"status": "skipped"})

    def test_ranking_counts_only_blockers(self) -> None:
        def rejected(name: str, blockers: list[str]) -> coverage.Classification:
            return coverage.classify(name, {"status": "elaboration-rejected", "blockers": blockers})

        slice_ = "IndexRangeAccess 4: unsupported expression IndexRangeAccess"
        report = coverage.Report("pin", "profile", [
            rejected("a.sol", [slice_]),
            rejected("b.sol", [slice_, "InlineAssembly 20: YulFunctionCall: call to balance"]),
        ])
        ranking = {f["feature"]: f for f in report.feature_ranking()}
        self.assertEqual(ranking["array slices"], {"feature": "array slices", "tests": 2, "only_blocker": 1})
        self.assertEqual(ranking["inline assembly"]["only_blocker"], 0)
        self.assertEqual(report.greedy_order(5), [("array slices", 1), ("inline assembly", 2)])

    def test_function_reasons_count_each_reason_once_per_function(self) -> None:
        admitted = coverage.classify("t.sol", {
            "status": "partially-admitted", "functions": 3,
            "unsupported": ["IndexRangeAccess 4: unsupported expression IndexRangeAccess\n"
                            "8: unsupported member access\n9: unsupported member access",
                            "calls an unsupported function"]})
        report = coverage.Report("pin", "profile", [admitted])
        self.assertEqual(report.function_reasons(), {
            "IndexRangeAccess: unsupported expression IndexRangeAccess": 1,
            "unsupported member access": 1, "calls an unsupported function": 1})
        self.assertIn("| unsupported member access | 1 |", report.markdown())


if __name__ == "__main__":
    unittest.main()
