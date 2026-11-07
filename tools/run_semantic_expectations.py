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
from isoltest_expectations import Parser, UnsupportedExpectation, decode_string

ROOT = Path(__file__).resolve().parents[1]
PREFIX = "expectation-result: "
ACCOUNT = 0x1212121212121212121212121212120000000012


def tokens(text: str) -> list[str]:
    """Read a complete comma-separated parameter list without skipping text."""
    parser = Parser(text)
    result = parser.parameters()
    parser.finish()
    return result


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
            raw = decode_string(token[4:-1]).decode("ascii")
            if not re.fullmatch(r"(?:[0-9a-fA-F]{2})*", raw):
                raise ValueError("only whole literal hex bytes are supported")
            return bytes.fromhex(raw)
        except (ValueError, UnicodeError) as error:
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


def parse_event(line: str) -> dict[str, Any]:
    """Parse an event's signature and raw indexed/data parameters structurally."""
    anonymous = line.startswith("~ emit <anonymous>")
    fragment = line.replace("<anonymous>", "_anonymous()", 1) if anonymous else line
    parser = Parser(fragment.removeprefix("~").strip(), comments=False)
    parser.expect("emit")
    # The anonymous marker is outside signature syntax.
    signature = parser.signature()
    if anonymous:
        signature = "<anonymous>"
    logger = None
    if parser.accept("from"):
        logger = parser.take().text
        if not re.fullmatch(r"0x[0-9a-fA-F]{40}", logger):
            raise UnsupportedExpectation("event logger must be a 20-byte address")
    topics, data = [], []
    if parser.accept(":"):
        while True:
            indexed = parser.accept("#")
            token = parser.parameter()
            if token is None or token == "FAILURE":
                raise UnsupportedExpectation("expected event byte parameter")
            raw = encode_token(token)
            if indexed:
                if len(raw) != 32:
                    raise UnsupportedExpectation("event topic is not 32 bytes")
                topics.append("0x" + raw.hex())
            else:
                data.append(raw)
            if not parser.accept(","):
                break
    parser.finish()
    return {"signature": signature, "logger": logger, "topics": topics,
            "data": "0x" + b"".join(data).hex()}


def expectation_source(text: str) -> str:
    """Retain line boundaries for side effects; comments are scanned as a block."""
    if "// ----" not in text:
        return ""
    lines = []
    for raw in text.split("// ----", 1)[1].splitlines():
        if not raw.strip():
            continue
        if not raw.lstrip().startswith("//"):
            raise UnsupportedExpectation("non-comment line after expectation separator")
        lines.append(raw.lstrip()[2:].strip())
    return "\n".join(lines)


def parse_calls(text: str, methods: dict[str, str]) -> list[Call]:
    """Validate the entire closed grammar before making any transaction runnable."""
    try:
        return parse_block(expectation_source(text), methods)
    except (UnsupportedExpectation, RecursionError) as error:
        return [Call(0, "[unsupported expectation block]", reason=str(error))]


def parse_block(source: str, methods: dict[str, str]) -> list[Call]:
    parser = Parser(source)
    calls: list[Call] = []
    sender = ACCOUNT
    blocked = None
    builtins = {"account", "balance", "storageEmpty", "isoltest_builtin_test", "isoltest_side_effects_test"}
    while parser.current.kind != "end":
        start = parser.current.start
        token_start = parser.position
        if parser.current.text == "gas":
            if not calls:
                raise UnsupportedExpectation("gas observation without a call")
            parser.take()
            mode = parser.identifier()
            if mode not in {"ir", "irOptimized", "legacy", "legacyOptimized", "ssaCFG", "ssaCFGOptimized"}:
                raise UnsupportedExpectation("unknown gas observation mode")
            parser.accept("code")
            parser.expect(":")
            parser.decimal()
            calls[-1].observations.append({"text": source[start:parser.end], "status": "not-runnable",
                                          "reason": "gas is not modeled"})
            continue
        if parser.current.kind == "effect":
            if not calls:
                raise UnsupportedExpectation("side-effect observation without a call")
            line = parser.take().text
            if line.startswith("~ emit "):
                if calls[-1].builtin:
                    raise UnsupportedExpectation("event observations after builtin directives are not supported")
                calls[-1].events.append(parse_event(line))
            else:
                blocked = "unsupported side-effect observation"
                calls[-1].text += " " + line
            continue
        name = parser.current.text
        bare_builtin = name in builtins and parser.tokens[parser.position + 1].text != "("
        signature = parser.take().text if bare_builtin else parser.signature()
        value = 0
        if parser.accept(","):
            value = int(parser.decimal())
            unit = parser.take().text
            if unit not in ("wei", "ether"):
                raise UnsupportedExpectation("call value needs wei or ether")
            value *= 10**18 if unit == "ether" else 1
            if value >= 1 << 256:
                raise UnsupportedExpectation("call value exceeds 256 bits")
        arguments = parser.parameters(required=True) if parser.accept(":") else []
        parser.comment()
        expected = parser.parameters() if parser.accept("->") else []
        parser.comment()
        original = " ".join(line.strip() for line in source[start:parser.end].splitlines() if line.strip())
        call = Call(len(calls), original, sender=str(sender), value=value, deploy=signature == "constructor()")
        if call.deploy and calls:
            raise UnsupportedExpectation("constructor must be the first call")
        calls.append(call)
        if "FAILURE" in arguments or "FAILURE" in expected[1:]:
            raise UnsupportedExpectation("FAILURE is supported only at the start of an expected result")
        argument_bytes = "0x" + b"".join(encode_token(t) for t in arguments).hex()
        reverted = bool(expected and expected[0] == "FAILURE")
        payload = "0x" + b"".join(encode_token(t) for t in expected[int(reverted):]).hex()
        call.expected = {"reverted" if reverted else "returned": "0x" if call.deploy else payload}
        if bare_builtin:
            if value:
                raise UnsupportedExpectation("builtin value transfers are not supported")
            call.builtin = signature
            if signature == "account":
                if len(arguments) != 1 or not re.fullmatch(r"[0-9]+", arguments[0]):
                    raise UnsupportedExpectation("account needs one decimal account number")
                if int(arguments[0]) > (1 << 31) - 1:
                    raise UnsupportedExpectation("account number exceeds the pinned host's signed integer range")
                sender = ACCOUNT + int(arguments[0]) * 4096
                if sender >= 1 << 160:
                    raise UnsupportedExpectation("account address exceeds 160 bits")
                call.builtin_arg = str(sender)
            elif signature == "balance":
                if len(arguments) > 1 or (arguments and not re.fullmatch(r"0x[0-9a-fA-F]{40}", arguments[0])):
                    raise UnsupportedExpectation("balance needs an optional 20-byte hex address")
                call.builtin_arg = arguments[0] if arguments else None
            elif signature == "storageEmpty":
                if arguments:
                    raise UnsupportedExpectation("storageEmpty takes no arguments")
            else:
                blocked = "unsupported isoltest builtin directive"
        elif call.deploy or signature == "()":
            call.calldata = argument_bytes
        elif signature in methods:
            call.calldata = "0x" + methods[signature] + argument_bytes[2:]
        else:
            call.signature, call.calldata = signature, argument_bytes
        comments = [token.text for token in parser.tokens[token_start:parser.position] if token.kind == "comment"]
        if any(re.search(r"out[- ]of[- ]gas", comment, re.IGNORECASE) for comment in comments):
            call.reason = "out-of-gas expectation: gas is not modeled"
            call.calldata = None
            call.expected = None
            call.signature = None
    if blocked:
        for call in calls:
            call.calldata = call.builtin = None
            call.reason = blocked
    elif not calls or not calls[0].deploy:
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
