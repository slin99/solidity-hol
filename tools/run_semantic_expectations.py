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


def decode_string(text: str) -> bytes:
    """Decode isoltest's byte escapes, including NUL and hex bytes."""
    result = bytearray()
    i = 0
    escapes = {"\\": b"\\", "n": b"\n", "r": b"\r", "t": b"\t", "0": b"\0"}
    while i < len(text):
        c = text[i]
        i += 1
        if c != "\\":
            result.extend(c.encode("utf-8"))
            continue
        if i == len(text):
            raise UnsupportedExpectation("trailing string escape")
        c = text[i]
        i += 1
        if c == "x":
            match = re.match(r"[0-9a-fA-F]{1,2}", text[i:])
            if not match:
                raise UnsupportedExpectation("hex escape needs one or two digits")
            result.append(int(match[0], 16))
            i += len(match[0])
        elif c in escapes:
            result.extend(escapes[c])
        else:
            raise UnsupportedExpectation(f"unsupported string escape: {c}")
    return bytes(result)


def strip_comments(text: str) -> str:
    """Remove paired # comments outside quoted strings."""
    return re.sub(r'"(?:[^"\\]|\\.)*"|#[^#]*#',
                  lambda m: m[0] if m[0].startswith('"') else "", text)


def encode_token(token: str) -> bytes:
    """The isoltest language encodes bytes directly, without ABI type inference."""
    alignment = re.fullmatch(r"(left|right)\((.*)\)", token)
    side = "right"
    if alignment:
        side, token = alignment.groups()
    if token.startswith('hex"') and token.endswith('"'):
        if alignment:
            raise UnsupportedExpectation("hex string tokens cannot be aligned")
        try:
            return bytes.fromhex(token[4:-1])
        except ValueError as error:
            raise UnsupportedExpectation(f"invalid hex bytes: {token}") from error
    if token.startswith('"') and token.endswith('"'):
        raw = decode_string(token[1:-1])
        if len(raw) > 32:
            raise UnsupportedExpectation("string token exceeds one ABI word")
        return raw.ljust(32, b"\0") if side != "right" or not alignment else raw.rjust(32, b"\0")
    if token in ("true", "false"):
        number = int(token == "true")
    elif re.fullmatch(r"-?(?:0x[0-9a-fA-F]+|[0-9]+)", token):
        number = int(token, 16 if "0x" in token else 10)
    else:
        raise UnsupportedExpectation(f"unsupported byte token: {token}")
    if not -(1 << 255) <= number < 1 << 256:
        raise UnsupportedExpectation(f"integer token outside 256 bits: {token}")
    number %= 1 << 256
    size = ((len(token) - 2 + 1) // 2 if token.startswith("0x")
            else max(1, (number.bit_length() + 7) // 8)) if alignment else 32
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
    observations: list[dict[str, str]] = field(default_factory=list)
    implicit: bool = False
    signature: str | None = None
    builtin: str | None = None
    builtin_arg: str | None = None
    events: list[dict[str, Any]] = field(default_factory=list)

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
        clean = line if line.startswith("~") else strip_comments(line).strip()
        if not clean:
            continue
        previous = (strip_comments(lines[-1]).rstrip()
                    if lines and not lines[-1].startswith(("gas ", "~")) else "")
        if line.startswith(("gas ", "~")) and lines:
            lines.append(line)
        elif re.match(r'(?:left\(|right\(|hex"|"|-?[0-9]|true\b|false\b|FAILURE\b)', clean):
            if not previous.endswith((":", ",", "->")):
                raise UnsupportedExpectation(f"cannot attribute parameter continuation: {line}")
            lines[-1] += " " + line
        elif clean.startswith("->"):
            if not previous or "->" in previous or previous.endswith((":", ",")):
                raise UnsupportedExpectation(f"cannot attribute result continuation: {line}")
            lines[-1] += " " + line
        elif re.match(r"(?:[A-Za-z_$][\w$]*|)\(", clean) or re.match(r"[A-Za-z_]\w*\s*(?::|->)", clean):
            lines.append(line)
        else:
            raise UnsupportedExpectation(f"cannot attribute expectation line: {line}")
    return lines


def parse_event(line: str) -> dict[str, Any]:
    """Read the logger, indexed topics and raw data of an isoltest event."""
    match = re.fullmatch(r"~ emit (.*?)(?: from (0x[0-9a-fA-F]+))?(?::\s*(.*))?", line)
    if not match:
        raise UnsupportedExpectation(f"unsupported event expectation: {line}")
    signature, logger, arguments = match.groups()
    topics, data = [], []
    for token in tokens(arguments or ""):
        if token.startswith("#"):
            raw = encode_bytes(token[1:])
            if len(raw) != 66:
                raise UnsupportedExpectation("event topic is not 32 bytes")
            topics.append(raw)
        else:
            data.append(encode_token(token))
    if signature != "<anonymous>" and not re.fullmatch(r"\w+\(.*\)", signature):
        raise UnsupportedExpectation(f"unsupported event signature: {signature}")
    return {"signature": signature, "logger": logger, "topics": topics,
            "data": "0x" + b"".join(data).hex()}


def parse_calls(text: str, methods: dict[str, str]) -> list[Call]:
    """Parse call arguments/results; unsupported transactions stop later replay."""
    calls: list[Call] = []
    sender = ACCOUNT
    try:
        lines = expectation_lines(text)
    except UnsupportedExpectation as error:
        return [Call(0, "[unsupported expectation block]", reason=str(error))]
    for original in lines:
        line = original if original.startswith(("gas ", "~")) else strip_comments(original).strip()
        if line.startswith(("gas ", "~")) and calls:
            if line.startswith("gas "):
                calls[-1].observations.append({"text": line, "status": "not-runnable",
                                              "reason": "gas is not modeled"})
            elif line.startswith("~ emit "):
                try:
                    calls[-1].events.append(parse_event(line))
                except UnsupportedExpectation as error:
                    calls[-1].reason = str(error)
            else:
                calls[-1].reason = calls[-1].reason or "unsupported side-effect observation"
                calls[-1].text += " " + original
            continue
        call = Call(len(calls), original, sender=str(sender))
        calls.append(call)
        comments = [m[0] for m in re.finditer(r'"(?:[^"\\]|\\.)*"|#[^#]*#', original)
                    if m[0].startswith("#")]
        if any(re.search(r"out[- ]of[- ]gas", comment, re.IGNORECASE) for comment in comments):
            call.reason = "out-of-gas expectation: gas is not modeled"
            continue
        account = re.fullmatch(r"account:\s*(\d+)\s*->\s*(.*)", line)
        builtin = re.fullmatch(r"(balance|storageEmpty)(?::\s*(0x[0-9a-fA-F]+))?\s*->\s*(.*)", line)
        if account:
            sender = ACCOUNT + int(account[1]) * 4096
            call.builtin = "account"
            call.builtin_arg = str(sender)
            result = account[2]
        elif builtin:
            call.builtin, call.builtin_arg, result = builtin.groups()
        if call.builtin:
            try:
                call.expected = {"returned": encode_bytes(result)}
            except UnsupportedExpectation as error:
                call.reason = str(error)
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
                call.signature = signature
                call.calldata = "0x" + encoded
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
    transaction_logs: list[dict[str, Any]] = []
    for call in calls:
        result = call.manifest()
        actual = executed.get(call.index)
        if actual is None:
            result.update(status="not-runnable", reason="no evaluator result")
        else:
            result.update(actual)
            if actual["status"] == "executed":
                if call.builtin:
                    result["logs"] = transaction_logs
                else:
                    transaction_logs = actual.get("logs", [])
                if call.reason:
                    result.update(status="not-runnable", reason=call.reason)
                elif call.builtin and call.events:
                    result.update(status="not-runnable", reason="event observations after builtin directives are not supported")
                elif (actual["actual"] == call.expected
                      and (call.implicit or result.get("logs", []) == actual.get("expected_logs", []))):
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


def result_records(text: str) -> list[dict[str, Any]]:
    """Read flushed result lines; a truncated final record belongs to an unfinished test."""
    records: list[dict[str, Any]] = []
    for line in text.splitlines(keepends=True):
        if not line.startswith(PREFIX):
            continue
        try:
            records.append(json.loads(line[len(PREFIX):]))
        except json.JSONDecodeError:
            if not line.endswith("\n"):
                break
            raise
    return records


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
              "Gas observations are recorded separately as untested because the core does not track gas. Agreement covers return/revert bytes and event logs.", "",
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
                if call.get("logs", []) != call.get("expected_logs", []):
                    lines.append(f"  Expected logs `{json.dumps(call.get('expected_logs', []))}`; got `{json.dumps(call.get('logs', []))}`.")
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
    parser.add_argument("--resume", action="store_true", help="reuse completed tests from the same input and runner sources")
    parser.add_argument("--holbuild", default="holbuild")
    parser.add_argument("--verify-bytecode", action="store_true", help="also execute compiled bytecode for mismatch triage")
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
                "calls": [c.manifest() for c in calls], "verify_bytecode": args.verify_bytecode}

    with ThreadPoolExecutor(max_workers=args.j) as pool:
        tests = list(pool.map(compile_one, selected))
    manifest = work / "manifest.json"
    fingerprint = hashlib.sha256()
    for name in subprocess.check_output(["git", "ls-files"], cwd=ROOT, text=True).splitlines():
        path = ROOT / name
        if path.suffix in (".sml", ".sig", ".py", ".toml") or name == "SOLIDITY_PIN":
            fingerprint.update(name.encode())
            fingerprint.update(path.read_bytes())
    for test in tests:
        fingerprint.update(Path(test["artifact"]).read_bytes())
    inputs = {"source_hash": fingerprint.hexdigest(), "tests": tests}
    completed: set[str] = set()
    logs: list[Path] = []
    if args.resume:
        if exporter.read_json(manifest) != inputs:
            raise SystemExit("cannot resume: test inputs or runner/evaluator sources changed")
        logs = sorted(work.glob("batch-*.log"))
        for log in logs:
            for result in result_records(log.read_text(errors="replace")):
                if result.get("kind") in ("complete", "preparation"):
                    completed.add(result["test"])
    elif manifest.exists():
        raise SystemExit(f"work directory already contains a run: use --resume or a new directory: {work}")
    else:
        exporter.write_json_atomic(manifest, inputs)
    subprocess.run([args.holbuild, "-j4", "build", "solidityDifferentialLib"], cwd=ROOT, check=True)
    pending = [test for test in tests if test["test"] not in completed]
    next_batch = 1 + max((int(log.stem.split("-")[1]) for log in logs), default=-1)
    status = 0
    # Each process bounds the lifetime of preparation/evaluation theorem state.
    for batch_index, offset in enumerate(range(0, len(pending), 16), next_batch):
        batch = work / f"batch-{batch_index:04d}.json"
        exporter.write_json_atomic(batch, {"tests": pending[offset:offset + 16]})
        log = batch.with_suffix(".log")
        logs.append(log)
        with log.open("w") as stream:
            status = subprocess.run([args.holbuild, "-j1", "run", str(ROOT / "tools/semantic_expectations.sml")],
                                    cwd=ROOT, stdin=subprocess.DEVNULL, stdout=stream, stderr=subprocess.STDOUT,
                                    env={**os.environ, "SEMANTIC_EXPECTATIONS_MANIFEST": str(batch)}).returncode
        if status:
            raise SystemExit(f"HOL run failed: status {status}; see {log}")
        print(f"Executed {len(completed) + min(offset + 16, len(pending))}/{len(tests)} tests", file=sys.stderr, flush=True)
    executed: dict[str, dict[int, dict[str, Any]]] = {}
    preparations: dict[str, str] = {}
    complete = set()
    for result in (result for log in logs for result in result_records(log.read_text(errors="replace"))):
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
                     "source_hash": inputs["source_hash"],
                     "core_revision": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
                     "untested_observations": dict(Counter(o["reason"] for t in results for c in t["calls"] for o in c["observations"])),
                     "test_counts": dict(Counter(t["status"] for t in results)),
                     "call_counts": dict(Counter(c["status"] for t in results for c in t["calls"])), "tests": results}
    exporter.write_json_atomic(args.output.with_suffix(".json"), result_report)
    args.output.with_suffix(".md").write_text(markdown(result_report))
    print(json.dumps({k: result_report[k] for k in ("test_counts", "call_counts")}))
    return 0


if __name__ == "__main__":
    sys.exit(main())
