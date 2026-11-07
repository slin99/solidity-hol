#!/usr/bin/env python3
"""Refresh shared report snapshots once after merging feature changes."""

import argparse
from pathlib import Path
import subprocess
import sys


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("solidity", type=Path, help="solidity checkout at SOLIDITY_PIN")
    parser.add_argument("--solc", required=True, type=Path)
    parser.add_argument("-j", "--jobs", type=int, default=4)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    solc = str(args.solc.resolve())
    subprocess.run([
        sys.executable, "tools/semantic_tests_coverage.py", str(args.solidity.resolve()),
        "--solc", solc, "-j", str(args.jobs),
    ], cwd=root, check=True)
    subprocess.run([
        sys.executable, "tools/yul_reconnaissance.py", "--solc", solc,
        "--output", "testdata/yul/reconnaissance.json",
        "--report", "testdata/yul/reconnaissance.md",
    ], cwd=root, check=True)
    subprocess.run([
        sys.executable, "-m", "unittest", "discover", "-s", "tests",
        "-p", "check_generated_reports.py", "-v",
    ], cwd=root, check=True)


if __name__ == "__main__":
    main()
