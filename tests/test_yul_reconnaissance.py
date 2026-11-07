#!/usr/bin/env python3

from pathlib import Path
import json
import re
import subprocess
import sys
import tempfile
import textwrap
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))

import yul_reconnaissance as recon  # noqa: E402

ARTIFACT = ROOT / "testdata" / "yul" / "reconnaissance.json"
REPORT = ROOT / "testdata" / "yul" / "reconnaissance.md"


class ParserTests(unittest.TestCase):
    def test_reads_an_object_with_a_nested_deployed_object(self) -> None:
        text = textwrap.dedent(
            """\
            /// @use-src 0:"a.sol"
            object "A_1" {
                code {
                    let x := add(1, 2)
                    mstore(64, memoryguard(128))
                }
                object "A_1_deployed" {
                    code { return(0, 0) }
                }
                data "metadata" hex"aabb"
            }
            """
        )
        objects = recon.parse_object_file(text)
        self.assertEqual([obj["name"] for obj in objects], ["A_1"])
        self.assertEqual([obj["name"] for obj in objects[0]["objects"]], ["A_1_deployed"])
        self.assertEqual(objects[0]["data"], [
            {"kind": "data", "name": "metadata", "value": 'hex"aabb"'}
        ])

    def test_statement_and_expression_kinds(self) -> None:
        text = textwrap.dedent(
            """\
            object "A" {
                code {
                    let a, b := f(1)
                    a, b := g(2, 3)
                    if iszero(a) { leave }
                    for { let i := 0 } lt(i, 10) { i := add(i, 1) } {
                        switch i
                        case 1 { break }
                        case 0x02 { continue }
                        default { }
                    }
                    g()
                }
            }
            """
        )
        code = recon.parse_object_file(text)[0]["code"]
        kinds = [statement["kind"] for statement in code["statements"]]
        self.assertEqual(
            kinds,
            ["variableDeclaration", "assignment", "if", "for", "expressionStatement"],
        )
        loop = code["statements"][3]
        self.assertEqual([case["kind"] for case in loop["body"]["statements"][0]["cases"]],
                         ["case", "case"])
        self.assertEqual(loop["body"]["statements"][0]["default"]["kind"], "default")
        first_case = loop["body"]["statements"][0]["cases"][0]
        self.assertEqual(first_case["value"]["literalKind"], "number")
        self.assertEqual(loop["init"]["statements"][0]["names"], ["i"])

    def test_literals(self) -> None:
        text = 'object "A" { code { let a := true let b := "x" let c := 0xff '
        text += 'let d := 0b1010 let e := hex"00ff" } }'
        names = [statement["value"]["literalKind"]
                 for statement in recon.parse_object_file(text)[0]["code"]["statements"]]
        self.assertEqual(names, ["bool", "string", "number", "number", "hexString"])

    def test_rejects_what_it_does_not_understand(self) -> None:
        with self.assertRaises(recon.YulSyntaxError):
            recon.parse_object_file('object "A" { code { let a := !b } }')
        with self.assertRaises(recon.YulSyntaxError):
            recon.parse_object_file('object "A" { code { } nope }')
        with self.assertRaises(recon.YulSyntaxError):
            recon.parse_object_file('function f() {}')

    def test_doc_comments_are_skipped(self) -> None:
        text = textwrap.dedent(
            """\
            object "A" {
                code {
                    /// @src 0:1:2  "contract A {..."
                    /* a block comment
                       over two lines */
                    stop()
                }
            }
            """
        )
        statements = recon.parse_object_file(text)[0]["code"]["statements"]
        self.assertEqual(len(statements), 1)


class AnalysisTests(unittest.TestCase):
    def facts(self, text: str) -> dict:
        return {fact["name"]: fact for fact in recon.analyse_artifact(text)}

    def test_separates_builtins_from_defined_functions(self) -> None:
        text = textwrap.dedent(
            """\
            object "A_1" {
                code {
                    mstore(0, datasize("A_1_deployed"))
                }
                object "A_1_deployed" {
                    code {
                        helper(mload(0))
                        function helper(x) { sstore(x, calldataload(4)) }
                    }
                }
            }
            """
        )
        facts = self.facts(text)
        self.assertEqual(facts["A_1"]["role"], "creation")
        self.assertEqual(facts["A_1_deployed"]["role"], "runtime")
        self.assertEqual(sorted(facts["A_1"]["builtins"]), ["datasize", "mstore"])
        self.assertEqual(sorted(facts["A_1_deployed"]["builtins"]),
                         ["calldataload", "mload", "sstore"])

    def test_counts_node_kinds_and_literal_kinds(self) -> None:
        text = 'object "A" { code { let x := 1 mstore(x, "s") } }'
        facts = recon.analyse_artifact(text)[0]
        self.assertEqual(facts["nodeKinds"]["variableDeclaration"], 1)
        self.assertEqual(facts["nodeKinds"]["literal:number"], 1)
        self.assertEqual(facts["nodeKinds"]["literal:string"], 1)
        self.assertEqual(facts["nodeKinds"]["functionCall"], 1)

    def test_object_level_forms_are_reported_present_or_absent(self) -> None:
        text = textwrap.dedent(
            """\
            object "A_1" {
                code { codecopy(0, dataoffset("A_1_deployed"), datasize("A_1_deployed")) }
                object "A_1_deployed" { code { stop() } }
                data "metadata" hex"00"
            }
            """
        )
        fixture = {
            "source": "testdata/x.sol",
            "contracts": [{"contract": "A", "objects": recon.analyse_artifact(text)}],
        }
        forms = recon.object_level_forms([fixture])
        self.assertEqual(sorted(forms), sorted(recon.OBJECT_LEVEL_FORMS))
        self.assertEqual(forms["datasize"]["creation"], 1)
        self.assertEqual(forms["dataoffset"]["creation"], 1)
        self.assertEqual(forms["datacopy"]["creation"], 0)
        self.assertEqual(forms["verbatim"]["creation"], 0)
        self.assertEqual(forms["subobject"]["creation"], 1)
        self.assertEqual(forms["data"]["creation"], 1)
        self.assertEqual(forms["datasize"]["fixtures"], ["testdata/x.sol"])

    def test_verbatim_is_recognised(self) -> None:
        text = 'object "A" { code { let x := verbatim_1i_1o(0x01, 1) } }'
        facts = recon.analyse_artifact(text)[0]
        self.assertEqual(sorted(facts["builtins"]), ["verbatim_1i_1o"])
        fixture = {
            "source": "testdata/x.sol",
            "contracts": [{"contract": "A", "objects": recon.analyse_artifact(text)}],
        }
        self.assertEqual(recon.object_level_forms([fixture])["verbatim"]["creation"], 1)


class GeneratedArtifactTests(unittest.TestCase):
    """The committed artifact is the one the script produces."""

    def setUp(self) -> None:
        if not ARTIFACT.exists():
            self.skipTest("no committed reconnaissance artifact")

    def test_format_and_roles(self) -> None:
        artifact = json.loads(ARTIFACT.read_text(encoding="utf-8"))
        self.assertEqual(artifact["format"], "solidity-hol-yul-reconnaissance-v2")
        self.assertEqual(
            [stage["id"] for stage in artifact["stages"]],
            [stage.id for stage in recon.STAGES],
        )
        for stage in artifact["stages"]:
            summary = artifact["summary"][stage["id"]]
            self.assertEqual(summary["unknownBuiltins"], {})
            roles = {
                obj["role"]
                for fixture in artifact["fixtures"]
                for contract in fixture["contracts"]
                for obj in contract["objects"]
                if obj["stage"] == stage["id"]
            }
            self.assertEqual(roles, {"creation", "runtime"})
            for entry in summary["builtins"].values():
                self.assertTrue(entry["fixtures"])
            for entry in summary["nodeKinds"].values():
                self.assertTrue(entry["fixtures"])

    def test_the_report_is_the_markdown_the_artifact_renders_to(self) -> None:
        artifact = json.loads(ARTIFACT.read_text(encoding="utf-8"))
        self.assertEqual(recon.render_markdown(artifact),
                         REPORT.read_text(encoding="utf-8"))

    def test_records_the_pin_profile_and_selection_it_was_made_with(self) -> None:
        artifact = json.loads(ARTIFACT.read_text(encoding="utf-8"))
        pin = (ROOT / "SOLIDITY_PIN").read_text(encoding="ascii").strip()
        profile = json.loads(
            (ROOT / recon.DEFAULT_PROFILE).read_text(encoding="utf-8")
        )
        version = profile["compilerVersion"]
        self.assertEqual(artifact["compiler"]["pin"], pin)
        self.assertIn(f"Version: {version}+commit.{pin[:8]}.",
                      artifact["compiler"]["reportedVersion"])
        self.assertEqual(artifact["profile"], profile)
        self.assertEqual(artifact["outputSelection"], recon.OUTPUT_SELECTION)

    def test_stages_are_the_two_artifacts_and_both_optimizer_settings(self) -> None:
        artifact = json.loads(ARTIFACT.read_text(encoding="utf-8"))
        runs = artifact["profile"]["settings"]["optimizer"]["runs"]
        self.assertEqual(
            [
                (stage["artifact"], stage["optimizer"]["enabled"])
                for stage in artifact["stages"]
            ],
            [("ir", False), ("irOptimized", False), ("irOptimized", True)],
        )
        enabled = artifact["stages"][-1]["optimizer"]
        self.assertEqual(enabled["runs"], runs)

    @staticmethod
    def dialect_builtin_names() -> set[str]:
        """The builtin spellings the HOL dialect defines."""
        text = (ROOT / "semantics" / "yulDialectScript.sml").read_text(
            encoding="utf-8"
        )
        names = set(re.findall(r'builtin_name\s+Y\w+\s*=\s*"([^"]+)"', text))
        if not names:
            raise AssertionError("no builtin_name equations found")
        return names

    @staticmethod
    def builtin_of_name_spellings() -> set[str]:
        """The spellings HOL's builtin_of_name accepts."""
        text = (ROOT / "semantics" / "yulDialectScript.sml").read_text(
            encoding="utf-8"
        )
        _, _, rest = text.partition("Definition builtin_of_name_def:")
        body, _, _ = rest.partition("\nEnd\n")
        names = set(re.findall(r'name = "([^"]+)"', body))
        if not names:
            raise AssertionError("no builtin_of_name equations found")
        return names

    def test_dialect_defines_only_evm_dialect_builtins(self) -> None:
        self.assertLessEqual(self.dialect_builtin_names(), recon.EVM_DIALECT_BUILTINS)

    def test_dialect_spells_and_looks_up_the_same_builtins(self) -> None:
        self.assertEqual(self.builtin_of_name_spellings(),
                         self.dialect_builtin_names())

    def test_dialect_covers_every_builtin_the_pinned_solc_emits(self) -> None:
        artifact = json.loads(ARTIFACT.read_text(encoding="utf-8"))
        emitted = {
            name
            for summary in artifact["summary"].values()
            for name in summary["builtins"]
        }
        self.assertGreater(len(emitted), 0)
        self.assertLessEqual(emitted, self.dialect_builtin_names())

    def test_builtins_are_in_the_evm_dialect(self) -> None:
        artifact = json.loads(ARTIFACT.read_text(encoding="utf-8"))
        for summary in artifact["summary"].values():
            for name in summary["builtins"]:
                self.assertTrue(
                    name in recon.EVM_DIALECT_BUILTINS
                    or recon.VERBATIM_RE.fullmatch(name) is not None,
                    f"{name} is not an EVM dialect builtin",
                )


class DriverTests(unittest.TestCase):
    def fake_solc(self, directory: Path, ir: str) -> Path:
        """A solc that answers with `ir`, and with `irOptimized` that differs
        from it only when the request turns the optimizer on."""
        path = directory / "solc"
        version = "Version: 0.8.37+commit.f401782d.Linux.g++"
        path.write_text(
            textwrap.dedent(
                f"""\
                #!{sys.executable}
                import json
                import sys
                if "--version" in sys.argv:
                    print({version!r})
                else:
                    request = json.load(sys.stdin)
                    name = next(iter(request["sources"]))
                    ir = {ir!r}
                    optimized = ir
                    if request["settings"]["optimizer"]["enabled"]:
                        optimized = ir.replace("stop()", "pop(0)")
                    json.dump({{"contracts": {{name: {{"A": {{"ir": ir,
                                                          "irOptimized": optimized}}}}}}}}, sys.stdout)
                """
            ),
            encoding="utf-8",
        )
        path.chmod(0o755)
        return path

    def test_builds_the_report_from_the_compiler(self) -> None:
        ir = 'object "A_1" { code { mstore(0, 1) } object "A_1_deployed" { code { stop() } } }'
        with tempfile.TemporaryDirectory() as temporary:
            solc = self.fake_solc(Path(temporary), ir)
            original = recon.fixture_sources
            recon.fixture_sources = lambda: [ROOT / "testdata" / "frontend" / "types.sol"]
            try:
                artifact = recon.build_artifact(solc, recon.DEFAULT_PROFILE)
            finally:
                recon.fixture_sources = original
        self.assertEqual(artifact["compiler"]["pin"], (ROOT / "SOLIDITY_PIN").read_text().strip())
        for stage in ("ir", "ir-optimized-off"):
            summary = artifact["summary"][stage]
            self.assertEqual(summary["builtins"]["mstore"]["runtime"], 0)
            self.assertEqual(summary["builtins"]["mstore"]["creation"], 1)
            self.assertEqual(summary["builtins"]["stop"]["runtime"], 1)
            self.assertEqual(sorted(summary["builtins"]), ["mstore", "stop"])
        # only the optimizer-on stage sees what the optimizer introduced: the
        # `stop()` of the unoptimized runtime object becomes a `pop(0)`
        self.assertEqual(sorted(artifact["summary"]["ir-optimized-on"]["builtins"]),
                         ["mstore", "pop"])
        report = recon.render_markdown(artifact)
        self.assertIn("| `mstore` | 1 | 0 | 0 | 1 |", report)
        self.assertIn("`ir-optimized-on`: the `irOptimized` artifact, optimizer on, `runs: 200`",
                      report)


class CliTests(unittest.TestCase):
    def test_help_mentions_the_required_arguments(self) -> None:
        proc = subprocess.run(
            [sys.executable, str(ROOT / "tools" / "yul_reconnaissance.py"), "--help"],
            cwd=ROOT,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        self.assertEqual(proc.returncode, 0, proc.stderr)
        self.assertIn("--solc", proc.stdout)


if __name__ == "__main__":
    unittest.main()
