#!/usr/bin/env python3
"""Export deterministic solc Standard JSON Yul AST artifacts.

The Yul differential harness (tools/run_yul_differential.py) imports the Yul
the pinned compiler itself generated, as a JSON AST rather than as text: solc
emits irAst (the code generator's output) and irOptimizedAst (after the Yul
transformations) into the Standard JSON output, both of which are the tree the
compiler's own converter walks. The ASTs need settings.experimental, which
this exporter sets; it adds no other setting, so the profile it is given is
the profile the artifact records.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
from typing import Any

import export_solc_artifacts as exporter

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_PROFILE = ROOT / "profiles" / "solc-0.8.37-via-ir-osaka.json"

OUTPUT_SELECTION: dict[str, dict[str, list[str]]] = {
    "*": {"*": ["irAst", "irOptimizedAst", "evm.deployedBytecode.object"]}
}

# The AST outputs are gated behind this option, which changes no codegen.
EXPERIMENTAL = True


def build_yul_artifact(
    solc: Path, sources: dict[str, str], profile_path: Path
) -> dict[str, Any]:
    """The Yul AST artifact of sources given by Standard JSON name and content."""
    pin = exporter.PIN_FILE.read_text(encoding="ascii").strip()
    profile = exporter.read_json(profile_path)
    expected_version = profile.get("compilerVersion")
    settings = profile.get("settings")
    if not isinstance(expected_version, str) or not isinstance(settings, dict):
        raise SystemExit("profile must contain compilerVersion and settings")
    identity = exporter.compiler_identity(solc, expected_version, pin)

    compiler_input = {
        "language": "Solidity",
        "sources": {name: {"content": sources[name]} for name in sorted(sources)},
        "settings": {
            **settings,
            "experimental": EXPERIMENTAL,
            "outputSelection": OUTPUT_SELECTION,
        },
    }
    compiler_output = exporter.compile_standard_json(solc, compiler_input)
    return {
        "format": "solidity-hol-solc-artifact-v1",
        "compiler": {"pin": pin, "reportedVersion": identity},
        "profile": profile,
        "input": compiler_input,
        "output": compiler_output,
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("sources", nargs="+", type=Path)
    parser.add_argument("--solc", required=True, type=Path)
    parser.add_argument("--profile", type=Path, default=DEFAULT_PROFILE)
    parser.add_argument("--output", required=True, type=Path)
    return parser.parse_args()


def build_artifact(solc: Path, source_paths: list[Path], profile_path: Path) -> dict[str, Any]:
    sources: dict[str, str] = {}
    for path in source_paths:
        name = exporter.source_name(path)
        if name in sources:
            raise SystemExit(f"duplicate source name: {name}")
        sources[name] = path.read_text(encoding="utf-8")
    return build_yul_artifact(solc, sources, profile_path)


def main() -> None:
    args = parse_args()
    exporter.write_json_atomic(
        args.output, build_artifact(args.solc, args.sources, args.profile)
    )


if __name__ == "__main__":
    sys.exit(main())
