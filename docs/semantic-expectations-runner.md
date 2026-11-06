# Running upstream call expectations

The acceptance report in [semantic-tests-coverage.md](semantic-tests-coverage.md)
checks whether the core admits a source program. The expectation runner separately
executes those admitted programs against the upstream test's return values,
revert data and events. It runs on demand; the upstream corpus sweep is absent
from per-PR CI.

## Running

Use the pinned Solidity checkout described in the acceptance report, and the
same compiler executable:

```sh
python3 tools/run_semantic_expectations.py ../solidity-tests \
  --solc /path/to/solc-0.8.37 \
  --work-dir /path/to/sweep-work -j4
```

The work directory retains compiler artifacts, the ordered-call manifest and
`hol.log`. The runner writes `docs/semantic-expectations.json` and `.md`. Use
`--match substring` and `--output /path/to/report` for a focused run. A focused
report covers only its selected tests, rather than the whole acceptance set.

The runner selects tests marked admitted by the committed coverage JSON. It
reuses `semantic_tests_coverage.read_test` and `compile_test`, then rechecks
`solidityPrepareLib.prepare_artifact` before execution. Preparation changes are
reported as not runnable; this runner does not recompute or replace the blocker
scan. The compiler identity, corpus revision and profile must match the pin.

## Execution and comparison

The main source is the test's last `Source` section, and the target is its last
contract declaration, following isoltest. An omitted constructor expectation
causes an implicit zero-value deployment. The constructor runs through
`deploy_contract`; subsequent calls run through `call_contract`, sharing the
committed world and constructor-produced immutables. Calldata is the signature's
compiler-recorded selector followed by the expectation's raw bytes. `()` passes
raw calldata without a selector.

The expectation format describes bytes, not typed argument values: numeric and
boolean tokens occupy one word, quoted strings pad on the right, `hex"..."`
contributes unpadded bytes, and `left(...)`/`right(...)` specify alignment.
`FAILURE` expects a revert with the following exact bytes. Constructor
expectations compare success/failure only, as isoltest discards creation output.

A revert restores the pre-transaction world, including the value transfer.
Successful calls commit storage and balances. Logs and transient storage reset
between transactions. Account-selection and balance/storage builtins do not
advance blocks. The transaction environment follows the pinned isoltest host,
including its funded accounts, origin, block progression and first deployment
address. This differs from the maintained differential corpus's deliberately
distinct environment fields.

Calls agree only when their return/revert bytes and event logs match. Core
invalid completions and fuel exhaustion are not runnable. Unsupported input
syntax stops subsequent replay, since its effects on state are unknown;
unsupported output observations can still allow later transactions to run.
Gas observations are explicitly recorded as not runnable and counted separately
from calls, since gas is outside the core model. No gas agreement is implied.

Test results prioritize a disagreement over a not-runnable call; a fully
agreeing test has all of its calls agreeing. The JSON retains every call's
input, expectation, actual result and reason. Agreement checks the observations
the upstream test asks for, rather than all final storage; this differs from
[differential execution](differential-testing.md), which compares complete
storage against compiler bytecode as well.

## Format reference

The parser and host behavior are taken from Solidity at `SOLIDITY_PIN`:
[the expectation parser](https://github.com/argotorg/solidity/blob/f401782df49be312ea4ef52a2d467cf5183b5906/test/libsolidity/util/TestFileParser.cpp),
[byte encoding](https://github.com/argotorg/solidity/blob/f401782df49be312ea4ef52a2d467cf5183b5906/test/libsolidity/util/BytesUtils.cpp),
[semantic test execution](https://github.com/argotorg/solidity/blob/f401782df49be312ea4ef52a2d467cf5183b5906/test/libsolidity/SemanticTest.cpp),
and [the execution host](https://github.com/argotorg/solidity/blob/f401782df49be312ea4ef52a2d467cf5183b5906/test/EVMHost.cpp).
