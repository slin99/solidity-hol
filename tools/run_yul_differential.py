#!/usr/bin/env python3
"""Run the differential corpus through the Yul semantics and write a report.

The corpus (testdata/differential/corpus.json) is held to each case's
expectation twice already: by the elaborated core and by the deployed bytecode
in verifereum, one kernel-checked differential_agrees theorem per case
(tools/run_differential.py). This driver adds the third side. It compiles every
suite's source with the pinned solc into the Yul the compiler itself emitted,
at the three stages the design separates (docs/roadmap.md, milestone 2):

- ir, the code generator's own output;
- ir-optimized, what the Yul transformations leave with the optimizer off;
- optimized, the production build, the optimizer on with runs 200.

It then builds yulDifferentialCorpusTheory, which imports those ASTs with
syntax/yulImportLib.sml, runs every case at every stage through the Yul
semantics, and proves one yul_agrees theorem per case and stage, relating that
run to the bytecode run and to the case's expectation (yulDifferentialTheory).
A stage whose runtime object the importer does not admit is reported as not
admitted, and counted separately from the agreements; the cases of an
unadmitted stage are not run there.

The ASTs are generated here rather than committed: they are tens of megabytes
across the corpus. The small committed fixtures under testdata/yul/expected
test the importer itself, in CI, where the pinned compiler is not installed.

The whole run is hundreds of cases times three stages, far too long for CI, so this is
a documented tool. Its report (docs/yul-differential.md and .json by default)
is committed. Run it with the pinned compiler:

    python3 tools/run_yul_differential.py --solc ~/.local/opt/solc-0.8.37/solc
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
from typing import Any

import export_solc_artifacts as exporter
import export_solc_yul as yul_exporter
import run_differential as core

ROOT = Path(__file__).resolve().parents[1]


def display_path(path: Path) -> str:
    """A path as the documentation names it: under `~` when it is in the home
    directory, so the committed report does not carry one machine's layout."""
    try:
        return "~/" + path.resolve().relative_to(Path.home()).as_posix()
    except (ValueError, RuntimeError):
        return path.as_posix()
CORPUS_SCRIPT = Path("tests/yulDifferentialCorpusScript.sml")
YUL_ROOT = Path("testdata/yul/generated")
THEORY = "yulDifferentialCorpusTheory"
RESULT_PREFIX = "yul-differential-result: "
REPORT_FORMAT = "solidity-hol-yul-differential-report-v1"
OPTIMIZED_PROFILE = ROOT / "profiles" / "solc-0.8.37-via-ir-osaka-optimized.json"

# The stages of the run, and the artifact each is imported from. The
# optimizer-off artifact holds both of the stages the compiler defines; the
# production build is its own artifact.
IR = "ir"
IR_OPTIMIZED = "ir-optimized"
OPTIMIZED = "optimized"
STAGES = (IR, IR_OPTIMIZED, OPTIMIZED)
ARTIFACT_STAGES = (("ir", yul_exporter.DEFAULT_PROFILE),
                   ("optimized", OPTIMIZED_PROFILE))

AGREEMENT = "agree"
ADMISSION_FAILURES = ("import-rejected", "import-malformed", "error")


def deployed_bytecode(artifact: dict[str, Any], source: str, contract: str) -> str | None:
    """The deployed bytecode of one contract, or None when the output has none."""
    bytecode = (artifact.get("output", {}).get("contracts", {}).get(source, {})
                .get(contract, {}).get("evm", {}).get("deployedBytecode", {}).get("object"))
    return bytecode if isinstance(bytecode, str) and bytecode else None


def generate_artifacts(root: Path, corpus: dict[str, Any], solc: Path,
                       ) -> tuple[list[dict[str, str]], list[str]]:
    """Generate each suite's Yul artifacts, and check that the optimizer-off
    compile is the same program the corpus's bytecode comes from."""
    checks: list[dict[str, str]] = []
    written: list[str] = []
    for suite in corpus["suites"]:
        source = suite["source"]
        sources = {source: (root / source).read_text(encoding="utf-8")}
        try:
            corpus_artifact = core.read_artifact(root, suite["artifact"])
        except (OSError, json.JSONDecodeError, core.CorpusError) as error:
            checks.append(core.check("corpus-artifact-readable", suite["artifact"], str(error)))
            corpus_artifact = None
        for tag, profile in ARTIFACT_STAGES:
            path = YUL_ROOT / f"{suite['name']}.{tag}.json"
            written.append(path.as_posix())
            try:
                artifact = yul_exporter.build_yul_artifact(solc, sources, profile)
            except SystemExit as error:
                checks.append(core.check("yul-artifact-generated", path.as_posix(), str(error)))
                continue
            exporter.write_json_atomic(root / path, artifact)
            checks.append(core.check("yul-artifact-generated", path.as_posix(), None))
            if tag == "ir" and corpus_artifact is not None:
                fresh_code = deployed_bytecode(artifact, source, suite["contract"])
                corpus_code = deployed_bytecode(corpus_artifact, source, suite["contract"])
                if fresh_code is None or corpus_code is None:
                    detail = "no deployed bytecode in the " + (
                        "generated Yul artifact" if fresh_code is None
                        else "corpus artifact")
                else:
                    detail = None if fresh_code == corpus_code else (
                        "the optimizer-off compile's deployed bytecode differs from the corpus "
                        "artifact's, so its Yul does not describe the bytecode the corpus checks")
                checks.append(core.check("yul-artifact-is-the-same-program",
                                         path.as_posix(), detail))
    return checks, written


def check_staging(root: Path, written: list[str]) -> dict[str, str]:
    """The corpus theory stages every artifact it reads, so holbuild rebuilds it
    when the compiler, the profile or the corpus changes."""
    try:
        script = (root / CORPUS_SCRIPT).read_text(encoding="utf-8")
    except OSError as error:
        return core.check("yul-artifacts-staged", CORPUS_SCRIPT.as_posix(), str(error))
    staged = core.staged_files(script)
    want = {f"../{core.CORPUS.as_posix()}"} | {f"../{path}" for path in written}
    missing = sorted(want - staged)
    return core.check("yul-artifacts-staged", CORPUS_SCRIPT.as_posix(),
                      None if not missing else
                      f"holbuild_extra_deps does not list {', '.join(missing)}")


def build_report(corpus_path: Path, corpus: dict[str, Any], solc: Path,
                 checks: list[dict[str, str]], hol: dict[str, Any] | None) -> dict[str, Any]:
    failures: list[dict[str, Any]] = [
        {"kind": "external-check", **item} for item in checks if item["status"] != "pass"]
    admissions: list[dict[str, Any]] = []
    kernel_checked: list[dict[str, Any]] = []
    cases_run = 0
    if hol is not None:
        results = hol["results"]
        suite_results = {r.get("suite"): r for r in results if r.get("kind") == "suite"}
        stage_results = {(r.get("suite"), r.get("stage")): r
                         for r in results if r.get("kind") == "stage"}
        case_results = {(r.get("suite"), r.get("case"), r.get("stage")): r
                        for r in results if r.get("kind") == "case" and "stage" in r}
        stage_counts = {stage: {"cases_run": 0, "agreements": 0} for stage in STAGES}
        built = hol["status"] == 0
        expected = sum(len(suite["cases"]) for suite in corpus["suites"]) * len(STAGES)
        for suite in corpus["suites"]:
            suite_result = suite_results.get(suite["name"])
            if suite_result is None and built and hol["ran"]:
                suite_result = {"kind": "suite", "suite": suite["name"], "status": "missing",
                                "message": "no suite result was reported"}
            if suite_result is not None and suite_result.get("status") != "ok":
                failures.append({"kind": "suite", **suite_result})
            # A stage is admitted when the suite reports it and no stage line
            # says otherwise: the theory emits a stage line only when the
            # importer rejects one, so silence on its own is no evidence, and a
            # build that stopped early admits nothing.
            reported = set(suite_result.get("stages", [])) \
                if suite_result is not None and suite_result.get("status") == "ok" else set()
            admitted = set()
            for stage in STAGES:
                stage_result = stage_results.get((suite["name"], stage))
                rejected = stage_result is not None and stage_result.get("status") != "ok"
                admission = {"suite": suite["name"], "stage": stage,
                             "admitted": stage in reported and not rejected}
                if rejected:
                    admission.update(status=stage_result.get("status"),
                                     message=stage_result.get("message"))
                elif not admission["admitted"]:
                    admission.update(status="unreported" if suite_result is not None
                                     else "not run",
                                     message=(suite_result or {}).get("message"))
                if rejected:
                    failures.append({"kind": "admission", **admission})
                elif admission["admitted"]:
                    admitted.add(stage)
                admissions.append(admission)
            for case in suite["cases"]:
                for stage in STAGES:
                    if stage not in admitted:
                        continue
                    theorem = f"yul_{suite['name']}_{case['name']}_{stage.replace('-', '_')}"
                    result = case_results.get((suite["name"], case["name"], stage))
                    if result is not None:
                        cases_run += 1
                        stage_counts[stage]["cases_run"] += 1
                    if result is not None and result.get("status") == AGREEMENT:
                        stage_counts[stage]["agreements"] += 1
                        kernel_checked.append({"theorem": theorem, "suite": suite["name"],
                                               "case": case["name"], "stage": stage,
                                               "status": "proved" if hol["ran"]
                                                         else "proved (cached)",
                                               "outcome": result.get("outcome")})
                    elif result is not None:
                        failures.append({"kind": "case", "theorem": theorem, **result})
                    elif built and hol["ran"]:
                        failures.append({"kind": "case", "theorem": theorem,
                                         "suite": suite["name"], "case": case["name"],
                                         "stage": stage, "status": "missing",
                                         "message": "no result was reported"})
        for stage in STAGES:
            stage_counts[stage]["stages_admitted"] = sum(
                1 for a in admissions if a["stage"] == stage and a["admitted"])
            stage_counts[stage]["stages_expected"] = len(admissions) // len(STAGES)
        if hol["status"] != 0 and not any(f["kind"] in ("suite", "case") for f in failures):
            failures.append({"kind": "hol-build", "status": hol["status"],
                             "message": hol.get("error", "the HOL build failed"),
                             "log": hol.get("log")})
    else:
        # No HOL run, so nothing was admitted or run: the report says so
        # rather than leaving the stages out of it.
        stage_counts = {stage: {"stages_admitted": 0, "stages_expected": 0,
                                "cases_run": 0, "agreements": 0}
                        for stage in STAGES}
        expected = sum(len(suite["cases"]) for suite in corpus["suites"]) * len(STAGES)
    # A case's status beyond "agree" is what the report has to classify: an
    # inconclusive is a diagnostic on one side, not a disagreement, and the
    # totals say which of each there are.
    case_statuses: dict[str, int] = {}
    for failure in failures:
        if failure["kind"] == "case":
            case_statuses[failure["status"]] = case_statuses.get(failure["status"], 0) + 1
    return {
        "format": REPORT_FORMAT,
        "corpus": corpus_path.as_posix(),
        "solc": display_path(solc),
        "hol": None if hol is None else {k: hol[k] for k in ("command", "status", "ran")
                                         if k in hol},
        "stages": list(STAGES),
        "per_stage": stage_counts,
        "totals": {
            "stages_admitted": sum(1 for a in admissions if a["admitted"]),
            "stages_expected": len(admissions),
            "cases_run": cases_run,
            "cases_expected": expected,
            "agreements": len(kernel_checked),
            "case_statuses": dict(sorted(case_statuses.items(),
                                         key=lambda item: (-item[1], item[0]))),
        },
        "admissions": admissions,
        "kernel_checked": kernel_checked,
        "external_checks": checks,
        "failures": failures,
    }


def summarise(report: dict[str, Any]) -> str:
    totals = report["totals"]
    lines = ["# Yul three-way corpus report", "",
             "The differential corpus through the Yul the pinned compiler emitted for the "
             "same sources, at the three stages the design separates, held to the same "
             "expectation the core evaluator and the deployed bytecode are held to.",
             "",
             f"- corpus: `{report['corpus']}`",
             f"- compiler: `{report['solc']}`", ""]
    hol = report["hol"]
    if hol is None:
        lines.append("The HOL corpus was not run (--no-hol).")
    else:
        lines.append(f"HOL command: `{' '.join(hol['command'])}` (status {hol['status']}).")
    lines += ["", "## Totals", "",
              f"- stages admitted: {totals['stages_admitted']}/{totals['stages_expected']}",
              f"- cases run: {totals['cases_run']}/{totals['cases_expected']}",
              f"- agreements: {totals['agreements']}"]
    if totals["case_statuses"]:
        lines.append("- cases that are not agreements: " + ", ".join(
            f"{count} {status}" for status, count in totals["case_statuses"].items()))
    lines += ["",
              "| stage | admitted | cases run | agreements |", "| --- | ---: | ---: | ---: |"]
    for stage in report["stages"]:
        counts = report["per_stage"][stage]
        lines.append(f"| {stage} | {counts['stages_admitted']}/{counts['stages_expected']}"
                     f" | {counts['cases_run']} | {counts['agreements']} |")
    lines += ["", "## Admissions", "",
              "A stage the importer does not admit is reported here rather than worked "
              "around, and its cases are not run at that stage.", "",
              "| suite | stage | admitted | status |", "| --- | --- | --- | --- |"]
    for item in report["admissions"]:
        lines.append(f"| {item['suite']} | {item['stage']} | "
                     f"{'yes' if item['admitted'] else 'no'} | {item.get('status', '')} |")
    lines += ["", "## Kernel-checked witnesses", "",
              "Theorems of yulDifferentialCorpusTheory, proved by the HOL kernel (with "
              "cv_compute) when the theory was built. Each relates the Yul run to the "
              "bytecode run and to the case's expectation, and says what the run left in",
              "storage and in the log.",
              "", "| theorem | outcome |", "| --- | --- |"]
    for witness in report["kernel_checked"]:
        lines.append(f"| `{witness['theorem']}` | {json.dumps(witness.get('outcome'))} |")
    lines += ["", "## External checks", "",
              "Performed by this driver outside the kernel.", "",
              "| check | subject | status |", "| --- | --- | --- |"]
    for item in report["external_checks"]:
        status = item["status"] + (f": {item['detail']}" if "detail" in item else "")
        lines.append(f"| {item['check']} | `{item['subject']}` | {status} |")
    lines += ["", "## What is not an agreement", "",
              "Each case's status is one of agree, mismatch, unexpected, storage-mismatch, "
              "storage-unexpected, log-mismatch, log-unexpected, inconclusive or error; "
              "only agree is an agreement, and the rest are listed here with the status "
              "that classifies them. An inconclusive is a diagnostic on one side, not a "
              "disagreement. A case at a stage the importer did not admit is not a "
              "disagreement either: it is counted above as an admission. Failures of "
              "another kind -- a suite that would not prepare, an external check, the HOL "
              "build -- are listed here too.", ""]
    if not report["failures"]:
        lines.append("None.")
    for failure in report["failures"]:
        lines.append(f"- {json.dumps(failure, sort_keys=True)}")
    return "\n".join(lines) + "\n"


def parse_args(argv: list[str] | None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--solc", type=Path, required=True,
                        help="the pinned solc, to generate the Yul ASTs")
    parser.add_argument("--report-dir", type=Path, default=ROOT / "docs")
    parser.add_argument("--holbuild", default="holbuild")
    parser.add_argument("-j", "--jobs", type=int)
    parser.add_argument("--no-hol", action="store_true",
                        help="generate the artifacts and run the external checks only")
    parser.add_argument("build_args", nargs="*",
                        help="extra holbuild build options, after --")
    return parser.parse_args(argv)


def main(argv: list[str] | None = None, root: Path = ROOT) -> int:
    args = parse_args(argv)
    try:
        corpus = core.load_corpus(root / core.CORPUS)
    except core.CorpusError as error:
        print(f"invalid corpus: {error}", file=sys.stderr)
        return 1
    checks, written = generate_artifacts(root, corpus, args.solc)
    checks.append(check_staging(root, written))
    hol = None
    if not args.no_hol:
        hol = core.run_hol(root, args.holbuild, args.jobs, True, args.build_args,
                           theory=THEORY, prefix=RESULT_PREFIX)
    report = build_report(core.CORPUS, corpus, args.solc, checks, hol)
    report_dir = args.report_dir.resolve()
    exporter.write_json_atomic(report_dir / "yul-differential.json", report)
    (report_dir / "yul-differential.md").write_text(summarise(report), encoding="utf-8")
    totals = report["totals"]
    print(f"yul differential: {totals['agreements']}/{totals['cases_expected']} agreements, "
          f"{totals['stages_admitted']}/{totals['stages_expected']} stages admitted, "
          f"{len(report['failures'])} not agreements"
          + (f" ({', '.join(f'{c} {s}' for s, c in totals['case_statuses'].items())})"
             if totals['case_statuses'] else "") + ", "
          f"{sum(1 for c in checks if c['status'] == 'pass')}/{len(checks)} external checks "
          f"passed; report in {report_dir}")
    return 0 if not report["failures"] and (hol is None or hol["status"] == 0) else 1


if __name__ == "__main__":
    sys.exit(main())
