#!/usr/bin/env python3
"""Export deterministic solc Standard JSON artifacts for frontend study."""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_PROFILE = ROOT / "profiles" / "solc-0.8.37-via-ir-osaka.json"
PIN_FILE = ROOT / "SOLIDITY_PIN"
VERSION_RE = re.compile(r"Version:\s*(\d+\.\d+\.\d+)\+commit\.([0-9a-fA-F]+)")

OUTPUT_SELECTION: dict[str, dict[str, list[str]]] = {
    "*": {
        "": ["ast"],
        "*": [
            "abi",
            "storageLayout",
            "transientStorageLayout",
            "evm.bytecode.object",
            "evm.deployedBytecode.object",
            "evm.deployedBytecode.immutableReferences",
            "evm.methodIdentifiers",
        ],
    }
}


def read_json(path: Path) -> Any:
    with path.open(encoding="utf-8") as stream:
        return json.load(stream)


def compiler_identity(solc: Path, expected_version: str, pin: str) -> str:
    try:
        proc = subprocess.run(
            [str(solc), "--version"],
            check=True,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
    except (OSError, subprocess.CalledProcessError) as error:
        raise SystemExit(f"could not run {solc}: {error}") from error

    text = proc.stdout + proc.stderr
    match = VERSION_RE.search(text)
    if match is None:
        raise SystemExit(f"could not parse compiler identity from {solc} --version:\n{text}")
    version, reported_commit = match.groups()
    if version != expected_version:
        raise SystemExit(
            f"compiler version mismatch: expected {expected_version}, reported {version}"
        )
    if not pin.lower().startswith(reported_commit.lower()) or len(reported_commit) < 8:
        raise SystemExit(
            f"compiler commit mismatch: pin is {pin}, compiler reports {reported_commit}"
        )
    return text.strip()


def source_name(path: Path) -> str:
    resolved = path.resolve()
    try:
        return resolved.relative_to(ROOT).as_posix()
    except ValueError as error:
        raise SystemExit(f"source is outside the repository: {path}") from error


def compile_standard_json(solc: Path, compiler_input: dict[str, Any]) -> dict[str, Any]:
    proc = subprocess.run(
        [str(solc), "--standard-json"],
        input=json.dumps(compiler_input, sort_keys=True, separators=(",", ":")),
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if proc.returncode != 0:
        raise SystemExit(f"solc exited with status {proc.returncode}:\n{proc.stderr}")
    try:
        output = json.loads(proc.stdout)
    except json.JSONDecodeError as error:
        raise SystemExit(f"solc did not produce JSON:\n{proc.stdout}\n{proc.stderr}") from error

    errors = [
        diagnostic
        for diagnostic in output.get("errors", [])
        if diagnostic.get("severity") == "error"
    ]
    if errors:
        messages = "\n\n".join(
            diagnostic.get("formattedMessage", json.dumps(diagnostic, sort_keys=True))
            for diagnostic in errors
        )
        raise SystemExit(f"solc reported compilation errors:\n{messages}")
    return output


def json_text(value: Any) -> str:
    return json.dumps(value, indent=2, sort_keys=True) + "\n"


def write_json_atomic(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, temporary_name = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as stream:
            stream.write(json_text(value))
        os.replace(temporary_name, path)
    except BaseException:
        try:
            os.unlink(temporary_name)
        except FileNotFoundError:
            pass
        raise


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
        name = source_name(path)
        if name in sources:
            raise SystemExit(f"duplicate source name: {name}")
        sources[name] = path.read_text(encoding="utf-8")
    return build_artifact_from_sources(solc, sources, profile_path)


def build_artifact_from_sources(
    solc: Path, sources: dict[str, str], profile_path: Path
) -> dict[str, Any]:
    """The artifact of sources given by Standard JSON name and content."""
    pin = PIN_FILE.read_text(encoding="ascii").strip()
    if re.fullmatch(r"[0-9a-f]{40}", pin) is None:
        raise SystemExit(f"{PIN_FILE} must contain one lowercase 40-character SHA")

    profile = read_json(profile_path)
    expected_version = profile.get("compilerVersion")
    settings = profile.get("settings")
    if not isinstance(expected_version, str) or not isinstance(settings, dict):
        raise SystemExit("profile must contain compilerVersion and settings")
    identity = compiler_identity(solc, expected_version, pin)

    compiler_input = {
        "language": "Solidity",
        "sources": {name: {"content": sources[name]} for name in sorted(sources)},
        "settings": {**settings, "outputSelection": OUTPUT_SELECTION},
    }
    compiler_output = compile_standard_json(solc, compiler_input)
    return {
        "format": "solidity-hol-solc-artifact-v1",
        "compiler": {
            "pin": pin,
            "reportedVersion": identity,
        },
        "profile": profile,
        "input": compiler_input,
        "output": compiler_output,
    }


def main() -> None:
    args = parse_args()
    write_json_atomic(args.output, build_artifact(args.solc, args.sources, args.profile))


if __name__ == "__main__":
    main()
