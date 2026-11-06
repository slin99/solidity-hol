#!/usr/bin/env python3
"""Execute admitted upstream semanticTests outside the per-PR CI sweep."""

from __future__ import annotations

import argparse
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from dataclasses import asdict, dataclass, field
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
from typing import Any

import export_solc_artifacts as exporter
import semantic_tests_coverage as coverage

ROOT = Path(__file__).resolve().parents[1]
PREFIX = "expectation-result: "
ACCOUNT = 0x1212121212121212121212121212120000000012


class UnsupportedExpectation(ValueError):
    """An expectation cannot be represented by this runner."""


def tokens(text: str) -> list[str]:
    """Split comma-separated expectation bytes, preserving quoted commas."""
    return [m.group().strip() for m in re.finditer(
        r'(?:hex)?"(?:[^"\\]|\\.)*"|(?:left|right)\([^)]*\)|[^,\s][^,]*', text)]


def encode_token(token: str) -> bytes:
    """The isoltest language encodes bytes directly, without ABI type inference."""
    alignment = re.fullmatch(r"(left|right)\((.*)\)", token)
    side = "right"
    if alignment:
        side, token = alignment.groups()
    if token.startswith('hex"') and token.endswith('"'):
        try:
            return bytes.fromhex(token[4:-1])
        except ValueError as error:
            raise UnsupportedExpectation(f"invalid hex bytes: {token}") from error
    if token.startswith('"'):
        try:
            raw = json.loads(token).encode("utf-8")
        except (json.JSONDecodeError, AttributeError) as error:
            raise UnsupportedExpectation(f"unsupported string: {token}") from error
        if len(raw) > 32:
            raise UnsupportedExpectation("string token exceeds one ABI word")
        return raw.ljust(32, b"\0")
    if token in ("true", "false"):
        number = int(token == "true")
    elif re.fullmatch(r"-?(?:0x[0-9a-fA-F]+|[0-9]+)", token):
        number = int(token, 16 if "0x" in token else 10)
    else:
        raise UnsupportedExpectation(f"unsupported byte token: {token}")
    if not -(1 << 255) <= number < 1 << 256:
        raise UnsupportedExpectation(f"integer token outside 256 bits: {token}")
    number %= 1 << 256
    size = max(1, (number.bit_length() + 7) // 8) if alignment else 32
    raw = number.to_bytes(size, "big")
    return raw.ljust(32, b"\0") if side == "left" else raw.rjust(32, b"\0")


def encode_bytes(text: str) -> str:
    """Concatenate isoltest tokens as 0x-prefixed raw bytes."""
    return "0x" + b"".join(encode_token(t) for t in tokens(text)).hex()


@dataclass
class Call:
    """A transaction, or an explicitly unsupported directive in sequence."""

    index: int
    text: str
    deploy: bool = False
    value: int = 0
    sender: str = str(ACCOUNT)
    calldata: str | None = None
    expected: dict[str, str] | None = None
    reason: str | None = None
    observations: list[str] = field(default_factory=list)
    implicit: bool = False

    def manifest(self) -> dict[str, Any]:
        return {k: v for k, v in asdict(self).items() if v is not None}


def expectation_lines(text: str) -> list[str]:
    """Join multiline calls and retain gas/event observations with their call."""
    if "// ----" not in text:
        return []
    lines: list[str] = []
    for raw in text.split("// ----", 1)[1].splitlines():
        if not raw.strip():
            continue
        if not raw.lstrip().startswith("//"):
            raise UnsupportedExpectation("non-comment line after expectation separator")
        line = raw.lstrip()[2:].strip()
        if not line.startswith("~ emit "):
            line = re.sub(r"#.*?#", "", line).strip()
        if not line:
            continue
        if line.startswith(("gas ", "~ emit ")):
            lines.append(line)
        elif re.match(r"(?:[A-Za-z_$][\w$]*|)\(", line) or re.match(r"\w+:\s", line):
            lines.append(line)
        elif lines and not lines[-1].startswith(("gas ", "~ emit ")):
            lines[-1] += " " + line
        else:
            lines.append(line)
    return lines


def parse_calls(text: str, methods: dict[str, str]) -> list[Call]:
    """Parse call arguments/results; unsupported transactions stop later replay."""
    calls: list[Call] = []
    sender = ACCOUNT
    for line in expectation_lines(text):
        if line.startswith(("gas ", "~ emit ")) and calls:
            calls[-1].observations.append(line)
            continue
        call = Call(len(calls), line, sender=str(sender))
        calls.append(call)
        account = re.fullmatch(r"account:\s*(\d+)\s*->\s*(.*)", line)
        if account:
            sender = ACCOUNT + int(account[1]) * 4096
            call.expected = {"returned": encode_bytes(account[2])}
            call.reason = "builtin account directive"
            continue
        match = re.fullmatch(r"(\w*\(.*?\))(?:,\s*(\d+)\s*(wei|ether))?\s*(?::\s*(.*?))?\s*(?:->\s*(.*))?", line)
        if not match:
            call.reason = "unsupported expectation syntax or builtin directive"
            continue
        signature, value, unit, arguments, expected = match.groups()
        call.deploy = signature == "constructor()"
        call.value = int(value or "0") * (10**18 if unit == "ether" else 1)
        try:
            encoded = encode_bytes(arguments or "")[2:]
            signature = signature.replace(" ", "")
            if call.deploy or signature == "()":
                call.calldata = "0x" + encoded
            elif signature in methods:
                call.calldata = "0x" + methods[signature] + encoded
            else:
                raise UnsupportedExpectation(f"unknown signature or builtin: {signature}")
            expected_tokens = tokens(expected or "")
            reverted = bool(expected_tokens and expected_tokens[0] == "FAILURE")
            if reverted:
                expected_tokens = expected_tokens[1:]
            call.expected = {"reverted" if reverted else "returned":
                             "0x" + b"".join(encode_token(t) for t in expected_tokens).hex()}
        except UnsupportedExpectation as error:
            call.reason = str(error)
    if not calls or not calls[0].deploy:
        calls.insert(0, Call(-1, "constructor() [implicit]", deploy=True,
                             calldata="0x", expected={"returned": "0x"}, implicit=True))
    return calls


def classify(calls: list[Call], executed: dict[int, dict[str, Any]]) -> list[dict[str, Any]]:
    """Combine parsing and execution evidence; diagnostics never agree."""
    results: list[dict[str, Any]] = []
    for call in calls:
        result = call.manifest()
        actual = executed.get(call.index)
        if actual is None:
            result.update(status="not-runnable", reason="no evaluator result")
        else:
            result.update(actual)
            if actual["status"] == "executed":
                if call.reason:
                    result.update(status="not-runnable", reason=call.reason)
                elif actual["actual"] == call.expected:
                    result["status"] = "agree"
                else:
                    result["status"] = "disagree"
        if not call.implicit:
            results.append(result)
        elif result["status"] != "agree":
            # An implicit deployment failure must remain visible even in an empty test.
            results.append(result)
    return results


def test_status(calls: list[dict[str, Any]]) -> str:
    """Disagreements take precedence over incomplete replay."""
    statuses = {c["status"] for c in calls}
    if "disagree" in statuses:
        return "disagree"
    if not statuses or "not-runnable" in statuses:
        return "not-runnable"
    return "agree"


def markdown(report: dict[str, Any]) -> str:
    """Render the regenerable summary and per-call evidence."""
    lines = ["# Upstream semanticTests call expectations", "",
             "Generated by `tools/run_semantic_expectations.py`; run separately from per-PR CI.", "",
             f"Solidity pin: `{report['solidity_pin']}`. Core revision: `{report['core_revision']}`.", "",
             "| outcome | tests | calls |", "| --- | ---: | ---: |"]
    for status in ("agree", "disagree", "not-runnable"):
        lines.append(f"| {status} | {report['test_counts'].get(status, 0)} | {report['call_counts'].get(status, 0)} |")
    lines += ["", "Calls execute after deployment in order, sharing storage, balances and immutables. "
              "A skipped transaction makes subsequent calls not runnable. A diagnostic is never agreement. "
              "Test categories prioritize disagreement, then not runnable; fully agreeing tests have every call agreeing.", "",
              "Gas and event observations are recorded separately as untested; agreement here covers return/revert bytes only.", "",
              "## Per-test results", "", "| test | outcome | agree / disagree / not runnable |", "| --- | --- | --- |"]
    for test in report["tests"]:
        counts = Counter(c["status"] for c in test["calls"])
        lines.append(f"| `{test['test']}` | {test['status']} | " + " / ".join(str(counts[s]) for s in ("agree", "disagree", "not-runnable")) + " |")
    lines += ["", "## Calls requiring attention", ""]
    for test in report["tests"]:
        bad = [c for c in test["calls"] if c["status"] != "agree"]
        if not bad:
            continue
        lines += [f"### `{test['test']}`", ""]
        for call in bad:
            lines += [f"- Call {call['index']}: `{call['text']}` — {call['status']}."]
            if call.get("reason"):
                lines.append(f"  {call['reason']}")
            if call["status"] == "disagree":
                lines.append(f"  Expected `{json.dumps(call['expected'])}`; got `{json.dumps(call['actual'])}`.")
        lines.append("")
    return "\n".join(lines) + "\n"


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("solidity", type=Path)
    parser.add_argument("--solc", type=Path, required=True)
    parser.add_argument("--coverage", type=Path, default=ROOT / "docs/semantic-tests-coverage.json")
    parser.add_argument("--output", type=Path, default=ROOT / "docs/semantic-expectations")
    parser.add_argument("--work-dir", type=Path, required=True, help="retain manifests, compiler artifacts and HOL log")
    parser.add_argument("--match", default="", help="run only test names containing this string")
    parser.add_argument("--holbuild", default="holbuild")
    parser.add_argument("-j", type=int, default=4)
    args = parser.parse_args(argv)
    pin = exporter.PIN_FILE.read_text().strip()
    profile = exporter.read_json(exporter.DEFAULT_PROFILE)
    exporter.compiler_identity(args.solc, profile["compilerVersion"], pin)
    report = exporter.read_json(args.coverage)
    if report["solidity_pin"] != pin or report["profile"] != exporter.DEFAULT_PROFILE.stem:
        raise SystemExit("coverage report compiler pin/profile differs from this checkout")
    corpus_pin = subprocess.check_output(["git", "-C", str(args.solidity), "rev-parse", "HEAD"], text=True).strip()
    if corpus_pin != pin:
        raise SystemExit(f"test corpus revision {corpus_pin} differs from pin {pin}")
    work = args.work_dir.resolve()
    work.mkdir(parents=True, exist_ok=True)
    tests_root = args.solidity / coverage.TESTS_DIR
    selected = [t["test"] for t in report["tests"] if t["category"] == coverage.ADMITTED and args.match in t["test"]]

    def compile_one(name: str) -> dict[str, Any]:
        test = coverage.read_test(tests_root, tests_root / name)
        artifact = coverage.compile_test(args.solc, test, exporter.DEFAULT_PROFILE)
        path = work / (hashlib.sha256(name.encode()).hexdigest()[:16] + ".json")
        exporter.write_json_atomic(path, artifact)
        sources = artifact["output"]["sources"]
        source_names = [m[2] for line in (tests_root / name).read_text().splitlines()
                        if (m := coverage.SOURCE_MARKER.match(line)) and m[1] == "Source"]
        source = source_names[-1] if source_names else name
        candidates = [(source, n["name"]) for n in sources[source]["ast"]["nodes"]
                      if n["nodeType"] == "ContractDefinition"]
        if not candidates:
            raise SystemExit(f"{name}: no deployable contract")
        source, contract = candidates[-1]
        methods = artifact["output"]["contracts"][source][contract]["evm"]["methodIdentifiers"]
        calls = parse_calls((tests_root / name).read_text(), methods)
        return {"test": name, "artifact": str(path), "source": source, "contract": contract,
                "calls": [c.manifest() for c in calls]}

    with ThreadPoolExecutor(max_workers=args.j) as pool:
        tests = list(pool.map(compile_one, selected))
    manifest = work / "manifest.json"
    exporter.write_json_atomic(manifest, {"tests": tests})
    subprocess.run([args.holbuild, "-j4", "build", "solidityDifferentialLib"], cwd=ROOT, check=True)
    log = work / "hol.log"
    with log.open("w") as stream:
        status = subprocess.run([args.holbuild, "-j1", "run", str(ROOT / "tools/semantic_expectations.sml")],
                                cwd=ROOT, stdin=subprocess.DEVNULL, stdout=stream, stderr=subprocess.STDOUT,
                                env={**os.environ, "SEMANTIC_EXPECTATIONS_MANIFEST": str(manifest)}).returncode
    executed: dict[str, dict[int, dict[str, Any]]] = {}
    preparations: dict[str, str] = {}
    complete = set()
    for line in log.read_text(errors="replace").splitlines():
        if not line.startswith(PREFIX):
            continue
        result = json.loads(line[len(PREFIX):])
        name = result.pop("test")
        if result.get("kind") == "complete":
            complete.add(name)
        elif result.get("kind") == "preparation":
            preparations[name] = result["reason"]
            complete.add(name)
        else:
            index = result.pop("index")
            executed.setdefault(name, {})[index] = result
    missing = set(selected) - complete
    if status or missing:
        raise SystemExit(f"HOL run failed: status {status}; {len(missing)} tests missing; see {log}")
    results = []
    for test in tests:
        calls = classify([Call(**c) for c in test["calls"]], executed.get(test["test"], {}))
        if test["test"] in preparations:
            for call in calls:
                call.update(status="not-runnable", reason="preparation: " + preparations[test["test"]])
        results.append({"test": test["test"], "status": test_status(calls), "calls": calls})
    result_report = {"format": "solidity-hol-semantic-expectations-v1", "solidity_pin": pin,
                     "core_revision": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
                     "test_counts": dict(Counter(t["status"] for t in results)),
                     "call_counts": dict(Counter(c["status"] for t in results for c in t["calls"])), "tests": results}
    exporter.write_json_atomic(args.output.with_suffix(".json"), result_report)
    args.output.with_suffix(".md").write_text(markdown(result_report))
    print(json.dumps({k: result_report[k] for k in ("test_counts", "call_counts")}))
    return 0


if __name__ == "__main__":
    sys.exit(main())
