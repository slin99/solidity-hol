#!/usr/bin/env python3

import json
from pathlib import Path
import sys
import tempfile
import textwrap
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))

import export_solc_yul as yul_exporter  # noqa: E402

SOURCE = "testdata/differential/shadowed_builtins.sol"
OPTIMIZER_OFF = ROOT / "profiles" / "solc-0.8.37-via-ir-osaka.json"
OPTIMIZER_ON = ROOT / "profiles" / "solc-0.8.37-via-ir-osaka-optimized.json"


class ExportTests(unittest.TestCase):
    def fake_solc(self, directory: Path, output: dict) -> Path:
        path = directory / "solc"
        path.write_text(
            textwrap.dedent(
                f"""\
                #!{sys.executable}
                import json
                import sys
                if "--version" in sys.argv:
                    print("Version: 0.8.37+commit."
                          "{Path(ROOT / 'SOLIDITY_PIN').read_text().strip()[:8]}"
                          ".Linux.g++")
                else:
                    json.load(sys.stdin)
                    json.dump({output!r}, sys.stdout)
                """
            ),
            encoding="utf-8",
        )
        path.chmod(0o755)
        return path

    def build(self, directory: Path, profile: Path) -> dict:
        solc = self.fake_solc(directory, {"contracts": {}, "sources": {}})
        return yul_exporter.build_yul_artifact(
            solc,
            {SOURCE: (ROOT / SOURCE).read_text(encoding="utf-8")},
            profile,
        )

    def test_requests_the_ast_outputs(self) -> None:
        """The ASTs are what is imported, so the artifact must carry them."""
        with tempfile.TemporaryDirectory() as temporary:
            artifact = self.build(Path(temporary), OPTIMIZER_OFF)
        settings = artifact["input"]["settings"]
        self.assertIs(settings["experimental"], True)
        self.assertEqual(
            settings["outputSelection"],
            {"*": {"*": ["irAst", "irOptimizedAst", "evm.deployedBytecode.object"]}},
        )

    def test_the_profile_is_the_only_other_setting(self) -> None:
        """The exporter adds the experimental flag and nothing else, so the
        artifact records the profile it was given."""
        with tempfile.TemporaryDirectory() as temporary:
            artifact = self.build(Path(temporary), OPTIMIZER_OFF)
        profile = json.loads(OPTIMIZER_OFF.read_text(encoding="utf-8"))
        self.assertEqual(artifact["profile"], profile)
        self.assertEqual(
            {key: value for key, value in artifact["input"]["settings"].items()
             if key != "outputSelection"},
            {**profile["settings"], "experimental": True},
        )


class ProfileTests(unittest.TestCase):
    def test_the_two_stages_differ_only_in_the_optimizer(self) -> None:
        """The harness compares ir-optimized with the production build, so the
        only difference between the compiles may be the optimizer."""
        off = json.loads(OPTIMIZER_OFF.read_text(encoding="utf-8"))
        on = json.loads(OPTIMIZER_ON.read_text(encoding="utf-8"))
        self.assertEqual(off["compilerVersion"], on["compilerVersion"])
        self.assertEqual(off["settings"]["optimizer"], {"enabled": False, "runs": 200})
        self.assertEqual(on["settings"]["optimizer"], {"enabled": True, "runs": 200})
        self.assertEqual(
            {k: v for k, v in off["settings"].items() if k != "optimizer"},
            {k: v for k, v in on["settings"].items() if k != "optimizer"},
        )


if __name__ == "__main__":
    unittest.main()
