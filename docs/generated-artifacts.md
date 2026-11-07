# Generated artifacts

Feature changes should merge independently. Shared report snapshots are refreshed
after merges, so a new fixture does not require every open feature branch to
rewrite the same reports or staging lists.

## Feature changes

Commit the implementation, its tests and documentation, and these fixture files:

- The feature's Solidity source under `testdata/differential/`.
- Its pinned compiler artifact under `testdata/differential/expected/`.
- Its suite under `testdata/differential/suites/<name>.json`, containing the
  `name`, `source`, `contract`, `artifact` and `cases` fields, plus optional
  peer and fuel settings. Copy the shape of an existing suite.

`testdata/differential/corpus.json` holds the format, default fuel and
`suite_directory`, relative to that config file. Python and HOL read every
`*.json` suite in filename order. Standalone corpora may still supply an inline
`suites` array instead. Do not edit the config or either corpus theory's
staging list to add a feature: their directory dependencies include new suite and
artifact files in the build inputs automatically.
Directory discovery requires holbuild 0.12.1 or later, which isolates staged
inputs per action so removed or renamed suites cannot survive from an older build.

Compile only the feature's artifact with `tools/export_solc_artifacts.py`, using
the pinned compiler and profile; see `--help` for multi-source inputs. Check the
feature with the usual commands from [differential-testing.md](differential-testing.md).
PR CI checks current sources against each compiler artifact and runs every core
differential case. Parser tests, report rendering, compiler/profile identity and
Yul dialect consistency remain in the Python suite.

Leave these shared snapshots unchanged in feature PRs:

| Files | Producer | Refresh |
| --- | --- | --- |
| `docs/semantic-tests-coverage.{json,md}` | `tools/semantic_tests_coverage.py` | Merge-window command below |
| `testdata/yul/reconnaissance.{json,md}` | `tools/yul_reconnaissance.py` | Merge-window command below |
| `docs/yul-differential.{json,md}` | `tools/run_yul_differential.py` | Separate three-way corpus run on the integrated branch |

These are snapshots of their last runs. A feature's CI does not claim that they
describe its new sources. Current-source freshness of reconnaissance is checked
by the refresh command, rather than by each feature's CI.

## Refreshing the integration branch

After merging a batch into `bot/opus/solidity-e2e`, its merge driver runs this
single job in a writable checkout at the merged head:

```sh
python3 tools/refresh_generated_reports.py /path/to/solidity-tests \
  --solc /path/to/pinned/solc -j4
```

The external Solidity checkout must contain `test/libsolidity/semanticTests`
at `SOLIDITY_PIN`; the setup is in the coverage report. The command regenerates
coverage and reconnaissance, then checks every reconnaissance source hash and
that every fixture appears. A failed stage stops the job. Commit only the four
report files after the whole command succeeds, as one report-refresh commit
on the integrated branch. The script does not commit or push.

To update the separate three-way Yul snapshot, run the existing driver on the
integrated branch:

```sh
python3 tools/run_yul_differential.py --solc /path/to/pinned/solc -j4
```

The Yul runner evaluates runtime objects only. Deployment cases currently fail
with `Yul deployment is unsupported`; a full snapshot refresh requires those
cases to be supported first. Keep the last snapshot until the full run succeeds.

Its large Yul ASTs under `testdata/yul/generated/` stay ignored. The per-feature
compiler artifacts are inputs to regression tests and stay committed; the
refresh job does not rewrite them or their hand-written call expectations.
