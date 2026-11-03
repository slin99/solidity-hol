#!/usr/bin/env python3
"""Run the differential regression corpus and write a report.

The corpus (testdata/differential/corpus.json) lists source units with their
committed solc artifacts and concrete calls with expected outcomes. Building
the HOL theory solidityDifferentialCorpus imports and elaborates every unit,
checks its core, runs each call through both the deployed bytecode and the
evaluator, and proves one kernel-checked differential_agrees theorem per case;
the build fails if any suite or case does not agree.

Around that build this driver performs external checks that are not kernel
checked: the corpus is well formed, every artifact records the pinned compiler
and profile and was compiled from the current sources, the corpus theory
stages every artifact, and, given --solc, every artifact is reproduced byte for
byte by the pinned compiler. It writes report.json and report.md, and a
directory of reproduction material for every failure. It exits unsuccessfully
on any failure.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
from typing import Any

import export_solc_artifacts as exporter

ROOT = Path(__file__).resolve().parents[1]
CORPUS = Path("testdata/differential/corpus.json")
CORPUS_SCRIPT = Path("tests/solidityDifferentialCorpusScript.sml")
CORPUS_THEORY = "solidityDifferentialCorpusTheory"
CORPUS_FORMAT = "solidity-hol-differential-corpus-v1"
REPORT_FORMAT = "solidity-hol-differential-report-v1"
ARTIFACT_FORMAT = "solidity-hol-solc-artifact-v1"
RESULT_PREFIX = "differential-result: "
IDENTIFIER = re.compile(r"[A-Za-z][A-Za-z0-9_]*")
DECIMAL = re.compile(r"-?[0-9]+")
HEX = re.compile(r"0x(?:[0-9a-fA-F]{2})*")


class CorpusError(Exception):
    pass


# The corpus


# contract_address in tests/solidityDifferentialScript.sml
CONTRACT_ADDRESS = 0x1000
PEER_ADDRESS = 0x5000


def check_identifier(value: Any, what: str) -> str:
    if not isinstance(value, str) or IDENTIFIER.fullmatch(value) is None:
        raise CorpusError(f"{what} must be an identifier: {value!r}")
    return value


def check_argument(value: Any, what: str) -> None:
    if isinstance(value, bool) or isinstance(value, int):
        return
    if isinstance(value, str) and (DECIMAL.fullmatch(value) or HEX.fullmatch(value)):
        return
    raise CorpusError(
        f"{what} must be an integer, a boolean, a decimal string or 0x-prefixed hex: {value!r}"
    )


def check_expectation(value: Any, what: str) -> None:
    if not isinstance(value, dict) or len(value) != 1:
        raise CorpusError(f"{what} must have exactly one of return, returned, panic and revert")
    (kind, payload), = value.items()
    if kind == "return":
        if not isinstance(payload, list):
            raise CorpusError(f"{what}.return must be a list")
        for index, result in enumerate(payload):
            check_argument(result, f"{what}.return[{index}]")
    elif kind == "panic":
        if isinstance(payload, bool) or not (
            (isinstance(payload, int) and payload >= 0)
            or (isinstance(payload, str) and HEX.fullmatch(payload) and payload != "0x")
        ):
            raise CorpusError(f"{what}.panic must be a natural number or 0x-prefixed hex")
    elif kind in {"revert", "returned"}:
        if not isinstance(payload, str) or HEX.fullmatch(payload) is None:
            raise CorpusError(f"{what}.{kind} must be 0x-prefixed hex")
    else:
        raise CorpusError(f"{what} has unknown kind {kind!r}")


def word(value: Any) -> int | None:
    if isinstance(value, bool):
        return None
    if isinstance(value, str) and HEX.fullmatch(value):
        value = int(value[2:] or "0", 16)
    elif isinstance(value, str) and DECIMAL.fullmatch(value):
        value = int(value)
    if isinstance(value, int) and 0 <= value < 2**256:
        return value
    return None


def check_storage(value: Any, what: str) -> None:
    """Storage is an object from slot to value, each a 256-bit word given as an
    integer, a decimal string or 0x-prefixed hex; slots are strings."""
    if not isinstance(value, dict):
        raise CorpusError(f"{what} must be an object from slot to value")
    for slot, contents in value.items():
        if word(slot) is None:
            raise CorpusError(f"{what}: slot {slot!r} is not a 256-bit word")
        if word(contents) is None:
            raise CorpusError(f"{what}[{slot}] is not a 256-bit word: {contents!r}")


def check_word(value: Any, bits: int, what: str) -> None:
    number = word(value)
    if number is None or number >= 2**bits:
        raise CorpusError(f"{what} must be a {bits}-bit word: {value!r}")


def check_logs(value: Any, what: str) -> None:
    """Logs are a list of {"logger": address, "topics": [word, ...], "data": "0x..."},
    the logger the contract when absent."""
    if not isinstance(value, list):
        raise CorpusError(f"{what} must be a list")
    for index, log in enumerate(value):
        if not isinstance(log, dict) or not {"topics", "data"} <= set(log) <= {
                "logger", "topics", "data"}:
            raise CorpusError(f"{what}[{index}] must have topics, data and an optional logger")
        if "logger" in log:
            check_word(log["logger"], 160, f"{what}[{index}].logger")
        if not isinstance(log["topics"], list) or len(log["topics"]) > 4:
            raise CorpusError(f"{what}[{index}].topics must be a list of at most 4 words")
        for topic, topic_word in enumerate(log["topics"]):
            check_word(topic_word, 256, f"{what}[{index}].topics[{topic}]")
        if not isinstance(log["data"], str) or HEX.fullmatch(log["data"]) is None:
            raise CorpusError(f"{what}[{index}].data must be 0x-prefixed hex")


def check_call(case: dict[str, Any], what: str) -> None:
    """A case calls either raw calldata or a named function with arguments, or
    deploys the contract with the constructor's arguments or, as calldata,
    their raw encoding."""
    if "deploy" in case and (case["deploy"] is not True or "function" in case
                             or "storage" in case):
        raise CorpusError(f"{what}: deploy must be true and excludes function and storage")
    if "calldata" in case:
        if "function" in case or "args" in case:
            raise CorpusError(f"{what}: calldata excludes function and args")
        if not isinstance(case["calldata"], str) or HEX.fullmatch(case["calldata"]) is None:
            raise CorpusError(f"{what}: calldata must be 0x-prefixed hex")
        return
    if "deploy" not in case and (not isinstance(case.get("function"), str)
                                 or not case["function"]):
        raise CorpusError(f"{what}: function must be a string")
    args = case.get("args")
    if not isinstance(args, list):
        raise CorpusError(f"{what}: args must be a list")
    for index, arg in enumerate(args):
        check_argument(arg, f"{what}.args[{index}]")


def check_fuel(value: Any, what: str) -> None:
    if isinstance(value, bool) or not isinstance(value, int) or value <= 0:
        raise CorpusError(f"{what} must be a positive integer")


def load_corpus(path: Path) -> dict[str, Any]:
    try:
        corpus = exporter.read_json(path)
    except (OSError, json.JSONDecodeError) as error:
        raise CorpusError(f"{path}: {error}") from error
    if not isinstance(corpus, dict) or corpus.get("format") != CORPUS_FORMAT:
        raise CorpusError(f"{path}: format must be {CORPUS_FORMAT}")
    check_fuel(corpus.get("fuel"), "fuel")
    suites = corpus.get("suites")
    if not isinstance(suites, list) or not suites:
        raise CorpusError("suites must be a non-empty list")
    suite_names: set[str] = set()
    theorems: set[str] = set()
    for suite in suites:
        if not isinstance(suite, dict):
            raise CorpusError("a suite must be an object")
        name = check_identifier(suite.get("name"), "suite name")
        if name in suite_names:
            raise CorpusError(f"duplicate suite {name}")
        suite_names.add(name)
        for key in ("source", "contract", "artifact"):
            if not isinstance(suite.get(key), str) or not suite[key]:
                raise CorpusError(f"suite {name}: {key} must be a string")
        if "peer" in suite:
            peer = suite["peer"]
            if not isinstance(peer, dict) or set(peer) != {"source", "contract", "artifact"} \
                    or not all(isinstance(v, str) and v for v in peer.values()):
                raise CorpusError(
                    f"suite {name}: peer must have exactly source, contract and artifact strings")
        cases = suite.get("cases")
        if not isinstance(cases, list) or not cases:
            raise CorpusError(f"suite {name}: cases must be a non-empty list")
        case_names: set[str] = set()
        for case in cases:
            if not isinstance(case, dict):
                raise CorpusError(f"suite {name}: a case must be an object")
            case_name = check_identifier(case.get("name"), f"suite {name}: case name")
            what = f"{name}.{case_name}"
            if case_name in case_names:
                raise CorpusError(f"duplicate case {what}")
            case_names.add(case_name)
            theorem = f"{name}_{case_name}"
            if theorem in theorems:
                raise CorpusError(f"case {what} repeats theorem name {theorem}")
            theorems.add(theorem)
            check_call(case, what)
            if "sender" in case:
                check_word(case["sender"], 160, f"{what}.sender")
                if word(case["sender"]) in (CONTRACT_ADDRESS, PEER_ADDRESS):
                    raise CorpusError(
                        f"{what}.sender must not be the contract or peer address")
            if "value" in case:
                # the harness funds the sender with 2^128 wei, gas included
                check_word(case["value"], 127, f"{what}.value")
            if "logs" in case:
                check_logs(case["logs"], f"{what}.logs")
            check_expectation(case.get("expect"), f"{what}.expect")
            if "fuel" in case:
                check_fuel(case["fuel"], f"{what}.fuel")
            for key in ("storage", "final_storage", "peer_storage"):
                if key in case:
                    check_storage(case[key], f"{what}.{key}")
            if "peer_storage" in case and "peer" not in suite:
                raise CorpusError(f"{what}: peer_storage without a peer")
            unknown = set(case) - {"name", "function", "deploy", "args", "calldata", "sender",
                                   "value", "storage", "peer_storage", "expect",
                                   "final_storage", "logs", "fuel"}
            if unknown:
                raise CorpusError(f"{what}: unknown fields {sorted(unknown)}")
    return corpus


def case_theorem(suite: dict[str, Any], case: dict[str, Any]) -> str:
    return f"{suite['name']}_{case['name']}"


def suite_theorems(suite: dict[str, Any]) -> list[str]:
    prefix = f"corpus_{suite['name']}"
    return [f"{prefix}_elaborates", f"{prefix}_program_wf"]


# External checks


def check(name: str, subject: str, failure: str | None) -> dict[str, str]:
    result = {"check": name, "subject": subject, "status": "pass" if failure is None else "fail"}
    if failure is not None:
        result["detail"] = failure
    return result


def compiled_contracts(suite: dict[str, Any]) -> list[dict[str, str]]:
    """The suite's contract and its peer, if any: each a source, contract and artifact."""
    return [suite] + ([suite["peer"]] if "peer" in suite else [])


def read_artifact(root: Path, path: str) -> dict[str, Any]:
    artifact = exporter.read_json(root / path)
    if not isinstance(artifact, dict) or artifact.get("format") != ARTIFACT_FORMAT:
        raise CorpusError(f"{path}: format must be {ARTIFACT_FORMAT}")
    return artifact


def check_artifacts(root: Path, corpus: dict[str, Any]) -> list[dict[str, str]]:
    """Solc-free diagnostics and source freshness before the authoritative SML check.

    These checks do not admit an artifact: solidityPrepareLib enforces the full
    compiler/profile contract again when building the kernel-checked corpus.
    """
    pin = (root / exporter.PIN_FILE.relative_to(exporter.ROOT)).read_text(encoding="ascii").strip()
    profile = exporter.read_json(root / exporter.DEFAULT_PROFILE.relative_to(exporter.ROOT))
    checks: list[dict[str, str]] = []
    artifacts: dict[str, dict[str, Any] | None] = {}
    for suite in (c for s in corpus["suites"] for c in compiled_contracts(s)):
        path = suite["artifact"]
        if path not in artifacts:
            try:
                artifacts[path] = read_artifact(root, path)
            except (OSError, json.JSONDecodeError, CorpusError) as error:
                artifacts[path] = None
                checks.append(check("artifact-readable", path, str(error)))
                continue
            artifact = artifacts[path]
            checks.append(check("artifact-readable", path, None))
            recorded_pin = artifact.get("compiler", {}).get("pin")
            checks.append(check(
                "artifact-compiler-pin", path,
                None if recorded_pin == pin else f"records {recorded_pin}, SOLIDITY_PIN is {pin}",
            ))
            checks.append(check(
                "artifact-profile", path,
                None if artifact.get("profile") == profile
                else "recorded profile differs from the pinned profile",
            ))
            reported_version = artifact.get("compiler", {}).get("reportedVersion")
            identity = (exporter.VERSION_RE.search(reported_version)
                        if isinstance(reported_version, str) else None)
            identity_matches = (
                identity is not None
                and identity.group(1) == profile["compilerVersion"]
                and len(identity.group(2)) >= 8
                and pin.lower().startswith(identity.group(2).lower())
            )
            checks.append(check(
                "artifact-compiler-version", path,
                None if identity_matches else
                f"reported compiler {reported_version!r} does not match "
                f"{profile['compilerVersion']} at {pin}",
            ))
            expected_settings = {**profile["settings"], "outputSelection": exporter.OUTPUT_SELECTION}
            checks.append(check(
                "artifact-settings", path,
                None if artifact.get("input", {}).get("settings") == expected_settings
                else "Standard JSON settings differ from the pinned profile and output selection",
            ))
        artifact = artifacts[path]
        if artifact is None:
            continue
        source = suite["source"]
        subject = f"{path}:{source}"
        recorded_sources = artifact.get("input", {}).get("sources", {})
        if source not in recorded_sources:
            checks.append(check("source-fresh", subject, "the artifact was not compiled from this source"))
            continue
        for name, recorded in sorted(recorded_sources.items()):
            try:
                current = (root / name).read_text(encoding="utf-8")
            except OSError as error:
                checks.append(check("source-fresh", f"{path}:{name}", str(error)))
                continue
            checks.append(check(
                "source-fresh", f"{path}:{name}",
                None if recorded.get("content") == current
                else "the artifact was not compiled from the current source; regenerate it",
            ))
        bytecode = (
            artifact.get("output", {}).get("contracts", {}).get(source, {})
            .get(suite["contract"], {}).get("evm", {}).get("deployedBytecode", {}).get("object")
        )
        checks.append(check(
            "deployed-bytecode", f"{subject}:{suite['contract']}",
            None if isinstance(bytecode, str) and bytecode else "no deployed bytecode",
        ))
    return checks


def staged_files(script: str) -> set[str]:
    match = re.search(r"holbuild_extra_deps\s*\[(.*?)\]", script.split("fun holbuild_extra_deps", 1)[-1], re.S)
    return set(re.findall(r'"([^"]*)"', match.group(1))) if match else set()


def check_staging(root: Path, corpus_path: Path, corpus: dict[str, Any]) -> dict[str, str]:
    """The corpus theory must stage the corpus and every artifact, so that
    holbuild rebuilds it when any of them changes."""
    staged = staged_files((root / CORPUS_SCRIPT).read_text(encoding="utf-8"))
    wanted = {f"../{corpus_path.as_posix()}"} | {
        f"../{c['artifact']}" for s in corpus["suites"] for c in compiled_contracts(s)}
    missing = sorted(wanted - staged)
    return check(
        "corpus-staged", CORPUS_SCRIPT.as_posix(),
        None if not missing else f"holbuild_extra_deps does not list {', '.join(missing)}",
    )


def reproduce_artifacts(root: Path, corpus: dict[str, Any], solc: Path, regenerate: bool) -> list[dict[str, str]]:
    checks = []
    for path in sorted({c["artifact"] for s in corpus["suites"] for c in compiled_contracts(s)}):
        try:
            committed = read_artifact(root, path)
            sources = [root / name for name in committed["input"]["sources"]]
            fresh = exporter.build_artifact(solc, sources, exporter.DEFAULT_PROFILE)
        except (OSError, KeyError, json.JSONDecodeError, CorpusError, SystemExit) as error:
            checks.append(check("artifact-reproducible", path, str(error)))
            continue
        if regenerate:
            exporter.write_json_atomic(root / path, fresh)
            checks.append(check("artifact-regenerated", path, None))
        else:
            same = exporter.json_text(fresh) == (root / path).read_text(encoding="utf-8")
            checks.append(check(
                "artifact-reproducible", path,
                None if same else "the pinned compiler produces a different artifact",
            ))
    return checks


# The HOL run


def parse_results(text: str, prefix: str = RESULT_PREFIX) -> list[dict[str, Any]]:
    results = []
    for line in text.splitlines():
        if line.startswith(prefix):
            try:
                results.append(json.loads(line[len(prefix):]))
            except json.JSONDecodeError:
                pass
    return results


def run_hol(root: Path, holbuild: str, jobs: int | None, force: bool,
            build_args: list[str], theory: str = CORPUS_THEORY,
            prefix: str = RESULT_PREFIX) -> dict[str, Any]:
    command = [holbuild]
    if jobs is not None:
        command += ["-j", str(jobs)]
    command += ["build"] + (["--force=theory"] if force else []) + build_args + [theory]
    print("+", " ".join(command), flush=True)
    lines = []
    try:
        with subprocess.Popen(command, cwd=root, text=True, stdout=subprocess.PIPE,
                              stderr=subprocess.STDOUT) as proc:
            assert proc.stdout is not None
            for line in proc.stdout:
                sys.stdout.write(line)
                lines.append(line)
            status = proc.wait()
    except OSError as error:
        return {"command": command, "status": None, "error": str(error), "ran": False, "results": []}
    output = "".join(lines)
    logs = re.findall(r"child log: (.*)", output)
    log = Path(logs[-1].strip()) if logs else (
        root / ".holbuild" / "logs" / "current" / "solidity-hol" / theory / "build.log")
    ran = bool(logs) or re.search(rf"^{theory} built$", output, re.M) is not None
    results = []
    if ran:
        try:
            results = parse_results(log.read_text(encoding="utf-8", errors="replace"), prefix)
        except OSError:
            results = parse_results(output, prefix)
    return {"command": command, "status": status, "ran": ran, "results": results,
            "log": str(log) if ran else None}


# Reporting


def write_reproduction(root: Path, directory: Path, suite: dict[str, Any],
                       case: dict[str, Any] | None, result: dict[str, Any], fuel: int) -> None:
    directory.mkdir(parents=True, exist_ok=True)
    try:
        artifact = read_artifact(root, suite["artifact"])
    except (OSError, json.JSONDecodeError, CorpusError):
        artifact = None
    inputs = {"suite": suite["name"]}
    inputs.update({key: suite[key] for key in ("source", "contract", "artifact", "peer")
                   if key in suite})
    if case is not None:
        inputs.update({"case": case["name"],
                       **{key: case[key] for key in ("function", "deploy", "args", "calldata")
                          if key in case},
                       "sender": case.get("sender", "0x2000"),
                       "value": case.get("value", 0),
                       "storage": case.get("storage", {}),
                       "peer_storage": case.get("peer_storage", {}),
                       "expect": case["expect"],
                       "final_storage": case.get("final_storage", {}),
                       "logs": case.get("logs", []),
                       "fuel": case.get("fuel", fuel)})
    exporter.write_json_atomic(directory / "inputs.json", inputs)
    exporter.write_json_atomic(directory / "outcomes.json", result)
    if artifact is not None:
        exporter.write_json_atomic(directory / "compiler.json", {
            "compiler": artifact.get("compiler"),
            "profile": artifact.get("profile"),
            "settings": artifact.get("input", {}).get("settings"),
        })
        shutil.copyfile(root / suite["artifact"], directory / "artifact.json")
        for name, source in artifact.get("input", {}).get("sources", {}).items():
            target = directory / "sources" / name
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(source.get("content", ""), encoding="utf-8")


def summarise(report: dict[str, Any]) -> str:
    lines = ["# Differential corpus report", ""]
    hol = report["hol"]
    if hol is None:
        lines.append("The HOL corpus was not run (--no-hol).")
    else:
        lines.append(f"HOL command: `{' '.join(hol['command'])}` (status {hol['status']}).")
    lines += ["", "## Kernel-checked witnesses", "",
              "Theorems of solidityDifferentialCorpusTheory, proved by the HOL kernel "
              "(with cv_compute) when the theory was built.", "",
              "| theorem | status |", "| --- | --- |"]
    for witness in report["kernel_checked"]:
        lines.append(f"| `{witness['theorem']}` | {witness['status']} |")
    lines += ["", "## External checks", "",
              "Performed by this driver outside the kernel.", "",
              "| check | subject | status |", "| --- | --- | --- |"]
    for item in report["external_checks"]:
        status = item["status"] + (f": {item['detail']}" if "detail" in item else "")
        lines.append(f"| {item['check']} | `{item['subject']}` | {status} |")
    lines += ["", "## Failures", ""]
    if not report["failures"]:
        lines.append("None.")
    for failure in report["failures"]:
        lines.append(f"- {json.dumps(failure, sort_keys=True)}")
    return "\n".join(lines) + "\n"


def build_report(root: Path, corpus_path: Path, corpus: dict[str, Any],
                 checks: list[dict[str, str]], hol: dict[str, Any] | None,
                 report_dir: Path) -> dict[str, Any]:
    failures: list[dict[str, Any]] = [
        {"kind": "external-check", **item} for item in checks if item["status"] != "pass"
    ]
    kernel_checked: list[dict[str, Any]] = []
    fuel = corpus["fuel"]
    if hol is not None:
        results = hol["results"]
        suite_results = {r.get("suite"): r for r in results if r.get("kind") == "suite"}
        case_results = {(r.get("suite"), r.get("case")): r for r in results if r.get("kind") == "case"}
        built = hol["status"] == 0
        for suite in corpus["suites"]:
            suite_result = suite_results.get(suite["name"])
            if suite_result is None and built and hol["ran"]:
                suite_result = {"kind": "suite", "suite": suite["name"], "status": "missing",
                                "message": "no suite result was reported"}
            if suite_result is not None and suite_result.get("status") != "ok":
                failures.append({"kind": "suite", **suite_result})
                write_reproduction(root, report_dir / "failures" / suite["name"], suite, None,
                                   suite_result, fuel)
                continue
            if built or suite_result is not None:
                for theorem in suite_theorems(suite):
                    kernel_checked.append({"theorem": theorem, "suite": suite["name"],
                                           "status": "proved" if hol["ran"] else "proved (cached)"})
            for case in suite["cases"]:
                theorem = case_theorem(suite, case)
                result = case_results.get((suite["name"], case["name"]))
                if result is not None and result.get("status") == "agree":
                    kernel_checked.append({"theorem": theorem, "suite": suite["name"],
                                           "case": case["name"], "status": "proved",
                                           "outcome": result.get("outcome")})
                elif result is None and built and not hol["ran"]:
                    kernel_checked.append({"theorem": theorem, "suite": suite["name"],
                                           "case": case["name"], "status": "proved (cached)"})
                elif result is not None:
                    failures.append({"kind": "case", **result})
                    write_reproduction(root, report_dir / "failures" / suite["name"] / case["name"],
                                       suite, case, result, fuel)
                elif hol["ran"] and suite_result is not None:
                    failures.append({"kind": "case", "suite": suite["name"], "case": case["name"],
                                     "status": "missing", "message": "no result was reported"})
        if hol["status"] != 0 and not any(f["kind"] in ("suite", "case") for f in failures):
            failures.append({"kind": "hol-build", "status": hol["status"],
                             "message": hol.get("error", "the HOL build failed"),
                             "log": hol.get("log")})
    return {
        "format": REPORT_FORMAT,
        "corpus": corpus_path.as_posix(),
        "hol": None if hol is None else {k: hol[k] for k in ("command", "status", "ran") if k in hol},
        "kernel_checked": kernel_checked,
        "external_checks": checks,
        "failures": failures,
    }


def parse_args(argv: list[str] | None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--report-dir", type=Path, default=ROOT / "differential-report")
    parser.add_argument("--solc", type=Path, help="pinned solc, to check that artifacts reproduce")
    parser.add_argument("--regenerate", action="store_true",
                        help="rewrite the artifacts with --solc instead of checking them")
    parser.add_argument("--holbuild", default="holbuild")
    parser.add_argument("-j", "--jobs", type=int)
    parser.add_argument("--allow-cached", action="store_true",
                        help="accept a cached corpus theory instead of rebuilding it")
    parser.add_argument("--no-hol", action="store_true", help="run the external checks only")
    parser.add_argument("build_args", nargs="*",
                        help="extra holbuild build options, after --")
    args = parser.parse_args(argv)
    if args.regenerate and args.solc is None:
        parser.error("--regenerate needs --solc")
    return args


def main(argv: list[str] | None = None, root: Path = ROOT) -> int:
    args = parse_args(argv)
    try:
        corpus = load_corpus(root / CORPUS)
    except CorpusError as error:
        print(f"invalid corpus: {error}", file=sys.stderr)
        return 1
    checks: list[dict[str, str]] = []
    if args.solc is not None:
        checks += reproduce_artifacts(root, corpus, args.solc, args.regenerate)
    checks += check_artifacts(root, corpus)
    checks.append(check_staging(root, CORPUS, corpus))
    hol = None
    if not args.no_hol:
        hol = run_hol(root, args.holbuild, args.jobs, not args.allow_cached, args.build_args)
    report_dir = args.report_dir.resolve()
    if (report_dir / "failures").exists():
        shutil.rmtree(report_dir / "failures")
    report = build_report(root, CORPUS, corpus, checks, hol, report_dir)
    exporter.write_json_atomic(report_dir / "report.json", report)
    (report_dir / "report.md").write_text(summarise(report), encoding="utf-8")
    proved = sum(1 for w in report["kernel_checked"] if "case" in w)
    cases = sum(len(suite["cases"]) for suite in corpus["suites"])
    print(f"differential corpus: {proved}/{cases} cases kernel checked, "
          f"{sum(1 for c in checks if c['status'] == 'pass')}/{len(checks)} external checks passed, "
          f"{len(report['failures'])} failures; report in {report_dir}")
    return 0 if not report["failures"] and (hol is None or hol["status"] == 0) else 1


if __name__ == "__main__":
    sys.exit(main())
