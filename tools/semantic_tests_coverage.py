#!/usr/bin/env python3
"""Report how much of solc's semantic test corpus the semantics admits.

Every test under test/libsolidity/semanticTests of a solidity checkout at
SOLIDITY_PIN is compiled with the pinned compiler and profile, then prepared
(solidityPrepareLib: import, source validation, elaboration, core checking)
in HOL by tools/semantic_tests_coverage.sml. Each test is classified as
skipped by its own settings, a compile failure, an importer rejection, a
source rejection, an elaborator rejection, partially admitted (the unit is
admitted with some of its functions unsupported) or admitted (every function
supported). Admitted and partially admitted tests also count their functions
and the reasons of the unsupported ones. The tests' call expectations are not
run.

Preparation reports every blocker it finds, one line each, so features are
ranked by how many rejected tests they block, and by how many they alone
block, from those lines: FEATURES names the feature of a line, and a line it
doesn't name is its own feature.
"""

from __future__ import annotations

import argparse
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass, field
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import tomllib
from typing import Any

import export_solc_artifacts as exporter


ROOT = Path(__file__).resolve().parents[1]
TESTS_DIR = Path("test/libsolidity/semanticTests")
HOL_SCRIPT = ROOT / "tools" / "semantic_tests_coverage.sml"
REPORT_FORMAT = "solidity-hol-semantic-tests-coverage-v1"
RESULT_PREFIX = "coverage-result: "

SOURCE_MARKER = re.compile(r"^==== (Source|ExternalSource): (.*) ====\s*$")
SETTING = re.compile(r"^//\s*([A-Za-z][A-Za-z0-9]*)\s*:\s*(.*?)\s*$")
EVM_VERSIONS = [
    "homestead", "tangerineWhistle", "spuriousDragon", "byzantium", "constantinople",
    "petersburg", "istanbul", "berlin", "london", "paris", "shanghai", "cancun",
    "prague", "osaka", "amsterdam", "@future",
]

SKIPPED = "skipped"
COMPILE_FAILURE = "compile-failure"
IMPORT_REJECTED = "import-rejected"
ELABORATION_REJECTED = "elaboration-rejected"
ADMITTED = "admitted"
PARTIALLY_ADMITTED = "partially-admitted"
MALFORMED_INPUT = "malformed-input"
INVALID_CORE = "invalid-core"
SOURCE_REJECTED = "source-rejected"
GREEDY_STEPS = 20
CATEGORIES = [ADMITTED, PARTIALLY_ADMITTED, ELABORATION_REJECTED, IMPORT_REJECTED, COMPILE_FAILURE,
              MALFORMED_INPUT, SOURCE_REJECTED, INVALID_CORE, SKIPPED]


class TestFormatError(Exception):
    pass


# Test files


@dataclass
class SemanticTest:
    """A test file: its sources, by Standard JSON name, and its settings."""

    name: str
    sources: dict[str, str]
    settings: dict[str, str]


def read_test(tests_root: Path, path: Path) -> SemanticTest:
    """Parse a test as solc's TestCaseReader does: `==== Source: name ====` and
    `==== ExternalSource: [name=]path ====` markers split the sources, and the
    `// key: value` lines between `// ====` and `// ----` are its settings."""
    name = path.relative_to(tests_root).as_posix()
    sources: dict[str, list[str]] = {}
    current = name
    settings: dict[str, str] = {}
    in_settings = False
    for line in path.read_text(encoding="utf-8").splitlines(keepends=True):
        stripped = line.rstrip("\r\n")
        marker = SOURCE_MARKER.match(stripped)
        if marker is not None:
            kind, spec = marker.groups()
            if kind == "Source":
                current = spec
                sources[current] = []
            else:
                source_name, _, external = (part.strip() for part in spec.partition("="))
                external = external or source_name
                external_path = Path(os.path.normpath(path.parent / external))
                sources[source_name] = [external_path.read_text(encoding="utf-8")]
            continue
        if stripped.startswith("// ----"):
            break
        if stripped.startswith("// ===="):
            in_settings = True
        elif in_settings:
            setting = SETTING.match(stripped)
            if setting is None:
                raise TestFormatError(f"{name}: malformed setting {stripped!r}")
            settings[setting.group(1)] = setting.group(2)
        else:
            sources.setdefault(current, []).append(line)
    return SemanticTest(name, {k: "".join(v) for k, v in sources.items()}, settings)


def find_tests(tests_root: Path) -> list[Path]:
    """Test files, without the directories starting with `_` that hold
    external sources, which isoltest does not run either."""
    return sorted(
        path for path in tests_root.rglob("*.sol")
        if not any(part.startswith("_") for part in path.relative_to(tests_root).parts)
    )


def evm_version_admits(requirement: str, version: str) -> bool:
    """Whether `version` meets an `EVMVersion` setting such as `>=cancun`."""
    if requirement == "any":
        return True
    match = re.fullmatch(r"([<>=!]*)(.*)", requirement)
    assert match is not None
    comparator, required = match.groups()
    if required not in EVM_VERSIONS:
        raise TestFormatError(f"unknown EVM version {required!r}")
    a, b = EVM_VERSIONS.index(version), EVM_VERSIONS.index(required)
    comparisons = {">": a > b, ">=": a >= b, "<": a < b, "<=": a <= b, "=": a == b, "!": a != b}
    if comparator not in comparisons:
        raise TestFormatError(f"unknown EVM version comparator {comparator!r}")
    return comparisons[comparator]


def skip_reason(test: SemanticTest, profile: dict[str, Any]) -> str | None:
    """Why the test's own settings exclude it from the via-IR profile, if
    they do."""
    settings = test.settings
    if settings.get("compileViaYul", "also") == "false":
        return "legacy pipeline only (compileViaYul: false)"
    evm = settings.get("EVMVersion", "any")
    if not evm_version_admits(evm, profile["settings"]["evmVersion"]):
        return f"EVM version (EVMVersion: {evm})"
    revert_strings = settings.get("revertStrings", "default")
    if revert_strings != profile["settings"]["debug"]["revertStrings"]:
        return f"revert strings (revertStrings: {revert_strings})"
    return None


# Compilation


def compile_test(solc: Path, test: SemanticTest, profile_path: Path) -> dict[str, Any]:
    """Full compiler artifact; shared HOL preparation checks its provenance."""
    return exporter.build_artifact_from_sources(solc, test.sources, profile_path)


# The HOL run


def remote_configured() -> bool:
    """Keep configured remote setups from silently running coverage locally."""
    if any(os.environ.get(name) for name in (
            "HOLBUILD_REMOTE_CACHE_URL", "HOLBUILD_REMOTE_CACHE_CURL_CONFIG",
            "HOLBUILD_REMOTE_EXEC_CURL_CONFIG")):
        return True
    config = ROOT / ".holconfig.toml"
    if not config.is_file():
        return False
    with config.open("rb") as stream:
        remote = tomllib.load(stream).get("remote_cache", {})
    return bool(remote.get("url") or remote.get("curl_config"))


def read_hol_results(result_file: Path, log: Path, status: int,
                     units: list[tuple[str, Path]]) -> dict[str, dict[str, Any]]:
    results = {}
    for line in result_file.read_text(encoding="utf-8", errors="replace").splitlines():
        if line.startswith(RESULT_PREFIX):
            try:
                result = json.loads(line[len(RESULT_PREFIX):])
            except json.JSONDecodeError as error:
                raise SystemExit(f"malformed HOL result: {line!r}: {error}") from error
            results[result["test"]] = result
    missing = [name for name, _ in units if name not in results]
    if status != 0 or missing:
        tail = "".join(log.read_text(encoding="utf-8", errors="replace").splitlines(True)[-30:])
        raise SystemExit(f"the HOL run failed (status {status}, {len(missing)} tests "
                         f"without a result):\n{tail}")
    return results


def run_fleet_shard(holbuild: str, work: Path,
                    units: list[tuple[str, Path]]) -> dict[str, dict[str, Any]] | None:
    """Run one cached action; None means no coordinator was configured."""
    work.mkdir(parents=True, exist_ok=True)
    manifest = work / "manifest.txt"
    staged_units = []
    for index, (name, source) in enumerate(units):
        target = work / f"{index}.json"
        shutil.copyfile(source, target)
        staged_units.append((name, target))
    manifest.write_text("".join(f"{name}\t{path.name}\n" for name, path in staged_units),
                        encoding="utf-8")
    script = work / HOL_SCRIPT.name
    shutil.copyfile(HOL_SCRIPT, script)
    supports = [manifest]
    for source in (exporter.PIN_FILE, exporter.DEFAULT_PROFILE, exporter.OPTIMIZED_PROFILE):
        target = work / source.relative_to(ROOT)
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)
        supports.append(target)
    supports.extend(path for _, path in staged_units)
    command = [holbuild, "-j1", "run-action", "--remote-only", "--skip-checkpoints",
               "--skip-proof-steps", "--script", str(script),
               "--load", "solidityPrepareLib", "--output", "results.jsonl",
               "--outputs-dir", str(work / "outputs")]
    for support in supports:
        command.extend(["--support", str(support)])
    command.append("solidityElaborateTheory")
    print(f"+ {holbuild} run-action solidityElaborateTheory ({len(units)} tests)",
          file=sys.stderr, flush=True)
    log = work / "hol.log"
    with log.open("w", encoding="utf-8") as stream:
        status = subprocess.run(command, cwd=ROOT, stdin=subprocess.DEVNULL,
                                stdout=stream, stderr=subprocess.STDOUT).returncode
    action_log = log.read_text(encoding="utf-8", errors="replace")
    print(action_log, file=sys.stderr, end="", flush=True)
    if (status == 75 and "run-action --remote-only: no coordinator to run on; "
            "pass --remote-exec URL" in action_log):
        return None
    result_file = work / "outputs/solidity-hol/solidityElaborateTheory/results.jsonl"
    completed = re.search(r"^solidity-hol:solidityElaborateTheory [0-9a-f]{64} "
                          r"(?:done|cached)\b", action_log, re.M)
    if status != 0 or completed is None or not result_file.is_file():
        raise SystemExit(f"the HOL fleet action failed (status {status}):\n{action_log}")
    return read_hol_results(result_file, log, status, units)


def run_hol(holbuild: str, work: Path, units: list[tuple[str, Path]]) -> dict[str, dict[str, Any]]:
    """Prepare bounded batches on the fleet, or locally without remote configuration."""
    work = work.resolve()
    # `holbuild run` loads built theories but does not build them.
    build = [holbuild, "-j8", "build", "--skip-checkpoints", "--skip-proof-steps", "solidityPrepareLib",
             "solidityElaborateTheory"]
    print("+", " ".join(build), file=sys.stderr, flush=True)
    subprocess.run(build, cwd=ROOT, check=True)
    help_text = subprocess.run([holbuild, "--help"], cwd=ROOT, check=True,
                               capture_output=True, text=True).stdout
    configured = remote_configured()
    if "run-action" in help_text:
        shards = [units[i:i + 128] for i in range(0, len(units), 128)] or [[]]

        def run_shard(index: int) -> dict[str, dict[str, Any]] | None:
            return run_fleet_shard(holbuild, work / "shards" / f"{index:04}", shards[index])

        results = run_shard(0)
        if results is not None:
            # Each startup/export mutates the same holbuild project.
            for index in range(1, len(shards)):
                shard = run_shard(index)
                if shard is None:
                    raise SystemExit("the HOL fleet action failed: coordinator disappeared "
                                     "after the first shard")
                results.update(shard)
            return results
        if configured:
            raise SystemExit("the HOL fleet action failed: remote configuration exists but "
                             "no coordinator was selected")
    elif configured:
        raise SystemExit("holbuild has no run-action support; upgrade holbuild to use the "
                         "configured remote execution/cache instead of running coverage locally")

    local_manifest = work / "local-manifest.txt"
    local_manifest.write_text("".join(f"{name}\t{path.resolve()}\n" for name, path in units),
                              encoding="utf-8")
    command = [holbuild, "-j1", "run", str(HOL_SCRIPT)]
    print("+", " ".join(command), file=sys.stderr, flush=True)
    log = work / "hol.log"
    with log.open("w", encoding="utf-8") as stream:
        status = subprocess.run(
            command, cwd=ROOT, stdin=subprocess.DEVNULL, stdout=stream,
            stderr=subprocess.STDOUT,
            env={**os.environ, "SEMANTIC_TESTS_MANIFEST": str(local_manifest)},
        ).returncode
    return read_hol_results(log, log, status, units)


# Features


# The feature of a blocker line, by the first pattern it matches. A line is
# "<node type> <id>: <reason>" from the importer, or "<id>: <reason>" from
# source validation and elaboration.
FEATURES = [
    (r"^FunctionTypeName\b", "function types"),
    (r"^IndexRangeAccess\b", "array slices"),
    (r"^(TryStatement|TryCatchClause)\b", "try/catch"),
    (r"^UsingForDirective\b", "using for"),
    (r"^UserDefinedValueTypeDefinition\b|^UserDefinedTypeName\b.*only struct", "user-defined value types"),
    (r"^InlineAssembly\b", "inline assembly"),
    (r"^FunctionDefinition\b.*unsupported source unit member", "free functions"),
    (r"only internal library functions", "external library functions"),
    (r"unsupported library member", "library structs and events"),
    (r"inline arrays", "inline arrays"),
    (r"structConstructorCall", "struct constructors"),
    (r"contract creation", "contract creation"),
    (r"built-in", "built-ins"),
]
FEATURE_PATTERNS = [(re.compile(pattern), feature) for pattern, feature in FEATURES]
NODE_ID = re.compile(r"\b([A-Z][A-Za-z]*) [0-9]+: ")
HOL_ID = re.compile(r"^[0-9]+: ")


def reason(line: str) -> str:
    """A blocker line without its node ids, so equal reasons count once."""
    return NODE_ID.sub(r"\1: ", HOL_ID.sub("", line))


def feature(line: str) -> str:
    text = reason(line)
    return next((f for pattern, f in FEATURE_PATTERNS if pattern.search(text)), text)


# Classification


@dataclass
class Classification:
    """A test's category and, if HOL rejected it, every blocker it reported;
    if HOL admitted it, the functions calls reach and the reasons of the
    unsupported ones."""

    test: str
    category: str
    reason: str | None = None
    blockers: list[str] = field(default_factory=list)
    functions: int = 0
    unsupported: list[str] = field(default_factory=list)

    def features(self) -> set[str]:
        return {feature(b) for b in self.blockers}


def classify(test: str, hol: dict[str, Any]) -> Classification:
    status = hol["status"]
    if status not in CATEGORIES or status in (SKIPPED, COMPILE_FAILURE):
        raise ValueError(f"{test}: unknown HOL status {status!r}")
    blockers = hol.get("blockers", [])
    return Classification(test, status, "\n".join(blockers) or None, blockers,
                          hol.get("functions", 0), hol.get("unsupported", []))


# The report


@dataclass
class Report:
    pin: str
    profile: str
    results: list[Classification]

    def counts(self) -> Counter[str]:
        return Counter(r.category for r in self.results)

    def function_reasons(self) -> Counter[str]:
        """The reasons functions of admitted units are unsupported, without
        node ids, each counted once per function."""
        return Counter(line for r in self.results for unsupported in r.unsupported
                       for line in {reason(line) for line in unsupported.splitlines()})

    def rejected(self) -> list[Classification]:
        return [r for r in self.results if r.category in (IMPORT_REJECTED, ELABORATION_REJECTED, SOURCE_REJECTED)]

    def feature_ranking(self) -> list[dict[str, Any]]:
        """Features by how many rejected tests they occur in, with how many
        they are the only blocker of."""
        blocking: Counter[str] = Counter()
        only: Counter[str] = Counter()
        for r in self.rejected():
            features = r.features()
            blocking.update(features)
            if len(features) == 1:
                only.update(features)
        return [{"feature": f, "tests": n, "only_blocker": only[f]}
                for f, n in sorted(blocking.items(), key=lambda kv: (-kv[1], -only[kv[0]], kv[0]))]

    def greedy_order(self, limit: int) -> list[tuple[str, int]]:
        """Features in the order that admits the most rejected tests at each
        step, with the number admitted once all up to it are supported. Ties
        go to the feature occurring in more tests."""
        tests = [r.features() for r in self.rejected()]
        occurrences = Counter(f for features in tests for f in features)
        chosen: set[str] = set()
        order = []
        for _ in range(min(limit, len(occurrences))):
            def admitted(f: str) -> int:
                return sum(1 for features in tests if features <= chosen | {f})
            best = max(sorted(set(occurrences) - chosen),
                       key=lambda f: (admitted(f), occurrences[f]))
            order.append((best, admitted(best)))
            chosen.add(best)
        return order

    def json(self) -> dict[str, Any]:
        return {
            "format": REPORT_FORMAT,
            "solidity_pin": self.pin,
            "profile": self.profile,
            "counts": {c: self.counts()[c] for c in CATEGORIES},
            "functions": {"total": sum(r.functions for r in self.results),
                          "unsupported": sum(len(r.unsupported) for r in self.results)},
            "features": self.feature_ranking(),
            "greedy_order": [{"feature": f, "admitted": n} for f, n in self.greedy_order(GREEDY_STEPS)],
            "tests": [
                {"test": r.test, "category": r.category, "reason": r.reason,
                 "blockers": r.blockers, "features": sorted(r.features()),
                 "functions": r.functions, "unsupported": r.unsupported}
                for r in self.results
            ],
        }

    def markdown(self) -> str:
        counts = self.counts()
        total = len(self.results)
        lines = [
            "# Coverage of solc's semantic tests",
            "",
            "Generated by `tools/semantic_tests_coverage.py`; do not edit by hand.",
            "",
            f"Every test under `{TESTS_DIR.as_posix()}` of argotorg/solidity at "
            f"`{self.pin}` was compiled with profile `{self.profile}`, imported by "
            "`solidityPrepareLib`, including source validation, elaboration and full core checking. Call expectations "
            "(the `// ----` sections) are not run, so an admitted test is one the "
            "semantics accepts, not one it is known to agree on. A test is admitted "
            "when every function calls reach is supported, and partially admitted "
            "when the unit is admitted with some of them unsupported: those have no "
            "procedure and a call of them is refused.",
            "",
            "To regenerate it from the repository root, with the pinned solc and the "
            "tests checked out outside the repository:",
            "",
            "```sh",
            "git init ../solidity-tests && cd ../solidity-tests",
            "git remote add origin https://github.com/argotorg/solidity.git",
            f"git sparse-checkout set --no-cone {TESTS_DIR.as_posix()}",
            f"git fetch --depth 1 --filter=blob:none origin {self.pin}",
            "git checkout FETCH_HEAD && cd -",
            "tools/semantic_tests_coverage.py ../solidity-tests --solc /path/to/solc",
            "```",
            "",
            "| outcome | tests |",
            "| --- | ---: |",
        ]
        lines += [f"| {c} | {counts[c]} |" for c in CATEGORIES]
        lines += [f"| total | {total} |", ""]
        functions = sum(r.functions for r in self.results)
        unsupported = sum(len(r.unsupported) for r in self.results)
        lines += [
            "## Functions of admitted units",
            "",
            f"The {counts[ADMITTED] + counts[PARTIALLY_ADMITTED]} admitted and partially "
            f"admitted tests have {functions} functions that calls reach, library "
            f"functions included; {functions - unsupported} are supported and "
            f"{unsupported} unsupported, for these reasons (a function can have several):",
            "",
            "| reason | functions |",
            "| --- | ---: |",
        ]
        lines += [f"| {reason} | {n} |" for reason, n in self.function_reasons().most_common()]
        lines += [
            "",
            "## Features blocking rejected tests",
            "",
            "*tests* counts the rejected tests a feature blocks; *only blocker* the "
            "tests it alone blocks, which supporting it would admit unless it hides "
            "a blocker behind it.",
            "",
            "| feature | tests | only blocker |",
            "| --- | ---: | ---: |",
        ]
        lines += [f"| {f['feature']} | {f['tests']} | {f['only_blocker']} |" for f in self.feature_ranking()]
        lines += [
            "",
            "## Features in order of tests admitted",
            "",
            "Supporting the features in this order admits the most rejected tests at "
            "each step; *admitted* counts the tests admitted once every feature up to "
            "that row is supported. It ignores how hard a feature is.",
            "",
            "| step | feature | admitted |",
            "| ---: | --- | ---: |",
        ]
        lines += [f"| {i} | {f} | {n} |" for i, (f, n) in enumerate(self.greedy_order(GREEDY_STEPS), 1)]
        lines += ["", "## Skipped and compile failures", "", "| reason | tests |", "| --- | ---: |"]
        reasons = Counter(r.reason if r.category == SKIPPED else "compile failure"
                          for r in self.results if r.category in (SKIPPED, COMPILE_FAILURE))
        lines += [f"| {reason} | {n} |" for reason, n in sorted(reasons.items(), key=lambda kv: -kv[1])]
        for title, category in (("Admitted", ADMITTED),
                                ("Partially admitted", PARTIALLY_ADMITTED),
                                ("Source validation rejections", SOURCE_REJECTED),
                                ("Elaborator rejections", ELABORATION_REJECTED)):
            lines += ["", f"## {title}", ""]
            tests = [r for r in self.results if r.category == category]
            lines += [f"- `{r.test}`" + "".join(f"\n  - {b}" for b in r.blockers) for r in tests] or ["None."]
        return "\n".join(lines) + "\n"


def parse_args(argv: list[str] | None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("solidity", type=Path,
                        help="a checkout of argotorg/solidity at SOLIDITY_PIN")
    parser.add_argument("--solc", required=True, type=Path)
    parser.add_argument("--holbuild", default="holbuild")
    parser.add_argument("-j", "--jobs", type=int, default=os.cpu_count())
    parser.add_argument("--output", type=Path, default=ROOT / "docs" / "semantic-tests-coverage",
                        help="report path without extension; .md and .json are written")
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv)
    pin = exporter.PIN_FILE.read_text(encoding="ascii").strip()
    profile = exporter.read_json(exporter.DEFAULT_PROFILE)
    # Checked once here, so that every failure below is the test's own.
    exporter.compiler_identity(args.solc, profile["compilerVersion"], pin)
    tests_root = args.solidity / TESTS_DIR
    tests = [read_test(tests_root, path) for path in find_tests(tests_root)]

    results: dict[str, Classification] = {}
    to_compile = []
    for test in tests:
        reason = skip_reason(test, profile)
        if reason is not None:
            results[test.name] = Classification(test.name, SKIPPED, reason)
        else:
            to_compile.append(test)

    def compile_one(test: SemanticTest) -> tuple[SemanticTest, dict[str, Any] | str]:
        try:
            return test, compile_test(args.solc, test, exporter.DEFAULT_PROFILE)
        except SystemExit as error:
            return test, str(error)

    with tempfile.TemporaryDirectory(prefix="semantic-tests-") as temporary:
        work = Path(temporary)
        units = []
        with ThreadPoolExecutor(max_workers=args.jobs) as pool:
            for index, (test, outcome) in enumerate(pool.map(compile_one, to_compile)):
                if isinstance(outcome, str):
                    results[test.name] = Classification(test.name, COMPILE_FAILURE, outcome)
                    continue
                path = work / f"{index}.json"
                path.write_text(json.dumps(outcome), encoding="utf-8")
                units.append((test.name, path))
        print(f"{len(tests)} tests, {len(units)} compiled", file=sys.stderr, flush=True)
        hol = run_hol(args.holbuild, work, units)
    for name, _ in units:
        results[name] = classify(name, hol[name])

    report = Report(pin, exporter.DEFAULT_PROFILE.stem, [results[t.name] for t in tests])
    exporter.write_json_atomic(args.output.with_suffix(".json"), report.json())
    args.output.with_suffix(".md").write_text(report.markdown(), encoding="utf-8")
    counts = report.counts()
    print(", ".join(f"{counts[c]} {c}" for c in CATEGORIES), file=sys.stderr)
    return 1 if counts[MALFORMED_INPUT] or counts[INVALID_CORE] else 0


if __name__ == "__main__":
    sys.exit(main())
