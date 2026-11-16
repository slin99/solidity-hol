#!/usr/bin/env python3
"""Differential fuzzing of generated programs (Layer 2).

Each seed's program (generate_solidity_programs.py) is compiled with the
pinned solc and profile, then prepared in HOL in batched fleet actions, as
semantic_tests_coverage.py prepares the semantic tests. The generator means
to stay inside the admitted subset, so a program that doesn't compile, or
that the core doesn't admit in full, is a generator bug: it is reported with
its blockers and dropped. The admitted programs are fuzzed by
run_differential_fuzz.py's Fuzzer: source against bytecode against pyrevm,
with its confirmation and shrinking.

pyrevm needs Python 3.11:

  uv run --python 3.11 --with pyrevm tools/run_program_fuzz.py \\
      --seeds 0:1000 --solc /path/to/pinned/solc --output DIR
"""

from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import asdict, dataclass, field
import json
import os
from pathlib import Path
import sys
from typing import Any

import export_solc_artifacts as exporter
from generate_solidity_programs import generate, parse_seeds
import run_differential_fuzz as fuzz
import semantic_tests_coverage as coverage


@dataclass(frozen=True)
class Program:
    """A seed's program: its source and artifact under the run directory."""
    seed: int
    directory: Path

    @property
    def name(self) -> str:
        return f"gen_{self.seed:06d}"

    @property
    def source(self) -> Path:
        return self.directory / f"{self.name}.sol"

    @property
    def artifact(self) -> Path:
        return self.directory / f"{self.name}.json"

    def target(self) -> dict[str, Any]:
        """The program as a run_differential_fuzz target; the artifact path is
        from the repository root, as HOL reads it from there."""
        return {"name": self.name, "source": self.source.name, "contract": "Gen",
                "artifact": os.path.relpath(self.artifact, fuzz.ROOT)}


@dataclass
class Admission:
    """What compiling and preparing the programs found: the admitted ones,
    and the others with their category and blockers, by name."""
    admitted: list[str] = field(default_factory=list)
    rejected: dict[str, dict[str, Any]] = field(default_factory=dict)

    def counts(self) -> dict[str, int]:
        found = Counter(r["category"] for r in self.rejected.values())
        found[coverage.ADMITTED] = len(self.admitted)
        return dict(sorted(found.items()))


def compile_programs(solc: Path, programs: list[Program]) -> dict[str, str]:
    """Write each program's source and artifact, reusing artifacts already
    written; the compile failures' messages, by name."""
    failures = {}
    for program in programs:
        if program.artifact.is_file():
            continue
        text = generate(program.seed)
        program.source.parent.mkdir(parents=True, exist_ok=True)
        program.source.write_text(text, encoding="utf-8")
        try:
            artifact = exporter.build_artifact_from_sources(
                solc, {program.source.name: text}, exporter.DEFAULT_PROFILE)
        except exporter.CompilationError as error:
            failures[program.name] = str(error)
            continue
        exporter.write_json_atomic(program.artifact, artifact)
    return failures


def admit(holbuild: str, output: Path, programs: list[Program],
          failures: dict[str, str]) -> Admission:
    """Prepare the compiled programs in HOL, once per run directory."""
    path = output / "admission.json"
    if path.is_file():
        return Admission(**json.loads(path.read_text()))
    compiled = [p for p in programs if p.name not in failures]
    hol = coverage.run_hol(holbuild, output / "admission",
                           [(p.name, p.artifact) for p in compiled]) if compiled else {}
    admission = Admission()
    for name, message in failures.items():
        admission.rejected[name] = {"category": coverage.COMPILE_FAILURE, "blockers": [message]}
    for p in compiled:
        result = coverage.classify(p.name, hol[p.name])
        if result.category == coverage.ADMITTED:
            admission.admitted.append(p.name)
        else:
            admission.rejected[p.name] = {
                "category": result.category,
                "blockers": result.blockers + result.unsupported + result.creation}
    exporter.write_json_atomic(path, asdict(admission))
    return admission


def markdown(seeds: range, admission: Admission, summary: dict[str, Any] | None) -> str:
    share = 100 * len(admission.admitted) / len(seeds)
    lines = ["# Program fuzzing", "",
             f"Seeds {seeds.start}:{seeds.stop}: {len(admission.admitted)} of {len(seeds)} "
             f"programs admitted ({share:.1f}%).", "",
             "| Programs | Count |", "| --- | ---: |"]
    lines += [f"| {category} | {n} |" for category, n in admission.counts().items()]
    if admission.rejected:
        lines += ["", "## Generator bugs (programs dropped)", ""]
        lines += [f"- `{name}` ({r['category']}): "
                  + "; ".join(b.splitlines()[0] for b in r["blockers"][:3])
                  for name, r in sorted(admission.rejected.items())]
    if summary is not None:
        lines += ["", fuzz.markdown(summary).replace("# Differential fuzzing", "## Fuzzing", 1)]
    return "\n".join(lines) + "\n"


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--seeds", type=parse_seeds, required=True, help="START:STOP")
    parser.add_argument("--solc", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True,
                        help="run directory: programs, admission, fuzzing, report")
    parser.add_argument("--admission-only", action="store_true",
                        help="compile and prepare the programs, but don't fuzz them")
    parser.add_argument("--fuzz-seed", type=int, default=0)
    parser.add_argument("--candidates", type=int, default=200,
                        help="candidates screened per function")
    parser.add_argument("-k", type=int, default=32, help="cases kept per program")
    parser.add_argument("--resume", action="store_true",
                        help="reuse the output's programs, admission and finished contracts")
    parser.add_argument("--shrink-rounds", type=int, default=8)
    parser.add_argument("--holbuild", default="holbuild")
    args = parser.parse_args(argv)
    output = args.output.resolve()
    if not args.resume and output.exists() and any(output.iterdir()):
        raise SystemExit(f"{output} is not empty; pass --resume to continue its run")
    programs = [Program(seed, output / "programs") for seed in args.seeds]
    failures = compile_programs(args.solc, programs)
    admission = admit(args.holbuild, output, programs, failures)
    summary = None
    if not args.admission_only and admission.admitted:
        by_name = {p.name: p for p in programs}
        targets_file = output / "targets.json"
        exporter.write_json_atomic(targets_file, {
            "targets": [by_name[name].target() for name in admission.admitted]})
        targets = fuzz.manifest_targets(targets_file)
        fuzz_output = output / "fuzz"
        fuzz.check_inputs(fuzz_output, fuzz.run_inputs(targets, args.fuzz_seed, args.candidates,
                                                       args.k), resume=args.resume)
        fuzzer = fuzz.Fuzzer(fuzz_output, seed=args.fuzz_seed, candidates=args.candidates,
                             k=args.k, evaluate=lambda work, entries: fuzz.run_fleet(
                                 args.holbuild, work, entries))
        summary = fuzzer.run(targets, max_batches=None, shrink_rounds=args.shrink_rounds)
    exporter.write_json_atomic(output / "report.json", {
        "seeds": [args.seeds.start, args.seeds.stop], "counts": admission.counts(),
        "admission": asdict(admission), "fuzz": summary})
    text = markdown(args.seeds, admission, summary)
    (output / "report.md").write_text(text, encoding="utf-8")
    print(text)
    return 1 if summary is not None and fuzz.failed(summary) else 0


if __name__ == "__main__":
    sys.exit(main())
