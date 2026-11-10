# Differential execution

`tools/run_differential.py` checks the maintained corpus in
`testdata/differential/suites/*.json`, with shared settings in
`testdata/differential/corpus.json`. Each suite supplies a compiler artifact,
source unit and deployed contract; each case is a transaction to the contract
with initial storage and an expected result, final storage and logs. The
artifact compiles the source together with the files it imports, so its
contract's bases, interfaces and structs may be declared in any of them; the
runner checks that each of those files is the one the artifact was compiled
from.

Add a feature's suite as a separate file, then generate and commit its two
wrappers with `python3 tools/run_differential.py --write-theories --no-hol`.
Both runners discover suites automatically; adding one does not change another
suite's wrappers or cache keys.
Shared report snapshots are refreshed after merges, as described in
[generated-artifacts.md](generated-artifacts.md).

A case calls either a named function with arguments (`function`, `args`),
encoded after its selector, or raw `calldata`. Optional `sender` (default
`0x2000`) and `value` (default 0) set the transaction's sender and value, and
`logs` lists the expected logs as `{"logger": ..., "topics": [...], "data":
"0x..."}`, the logger the contract unless given (default: none). A suite may
name a `peer`, a contract (`source`, `contract`, `artifact`) whose deployed
code sits at `0x5000` with the case's `peer_storage`, for the contract to call;
the evaluator's high-level calls run it, and any call back into the contract,
as bytecode in Verifereum. The evaluator runs the same calldata
through the elaborated program's dispatcher (`solidityEntry`), so selector
lookup, payability, argument decoding, `receive` and `fallback` are compared
too. An expectation is `{"return": [...]}` for typed results,
`{"returned": "0x..."}` for exact return bytes, `{"panic": code}`, or
`{"revert": "0x..."}`. Raw calldata declares no return types; use `returned`
to check its successful return payload, or `{"return": []}` for empty data.
Dynamic bytes and strings are supplied as `0x` byte strings, preserving UTF-8,
NUL bytes and arbitrary binary contents.

A case with `"deploy": true` and the constructor's `args` (or, as
`calldata`, their raw encoding) is a creation instead: Verifereum runs a creation transaction whose data is the artifact's
initcode followed by the encoded arguments, and the evaluator runs the
program's creation procedure (`deploy_contract`) on the encoded arguments, at
the address the transaction creates (`address_for_create` of the sender at
nonce 0). Both observe that account, which starts with no code or storage,
so `storage` must be empty and `logger` names that address. A successful
creation is observed as returning the values of the contract's immutables: on
the bytecode side, the 32-byte words the created code holds at the first of
each immutable's `immutableReferences` offsets, in the artifact's order; on
the evaluator side, the ABI words of the values the creation left in its
immutables table. A contract without immutables its runtime code reads
returns no data, so its `return` expectation is `[]`. The rest of the
deployed code is not compared. The words are compared as the code holds
them, and the compiler writes an assigned value there without cleaning it,
so a creation that assigns an immutable a value with dirty high bits (from
inline assembly) shows as a disagreement even when every read of it agrees.

A call case may give the immutables' values, by name, as an object
`immutables` (not with `deploy`). They are patched into the runtime bytecode
at the immutable's `immutableReferences` offsets, given to the evaluator as
the immutables table `call_contract` takes, and to the Yul run by the names
its `loadimmutable` reads; an immutable the case leaves out is zero. The HOL corpus theory proves one
`differential_agrees` theorem per case. Diagnostic failures and exhausted fuel
are inconclusive, never agreement. Non-canonical assembly write-backs and
`bool`/enum storage bytes are checked separately in `solidityDirtyBitsTest`:
source execution must fail closed, while `solidityDirtyBitsBytecodeTest`
checks the compiler outcomes from `testdata/differential/fail_closed/`.
These cases are outside the agreement corpus.

Each suite has two committed theories under `tests/corpus/`:

- `solidityBytecodeCorpus_<suite>` encodes calls from the artifact's ABI and
  method selectors, runs Verifereum, and proves the expected complete observation
  for every case. It depends on the suite and compiler artifacts, not the source
  frontend or evaluator.
- `solidityDifferentialCorpus_<suite>` prepares the source and proves that its
  calldata, initial accounts and transaction equal the bytecode theory's inputs.
  It reuses those bytecode results and evaluates the source against the same
  expectation, saving the original `differential_agrees` theorem per case.

The input equality is kernel checked, so a difference between the artifact's
ABI encoding and the elaborated source fails the suite. The shared datatypes,
transaction setup and EVM observation functions live in `solidityBytecode`;
`solidityDifferential` retains the source execution and combined verdict.

The runner targets the suite theories directly. Their explicit fixture
lists let holbuild schedule them independently and reuse unchanged bytecode
results after a frontend change. Both runners reuse cached suite verdicts by
default; `--force` explicitly rebuilds suites. The source runner still accepts
`--allow-cached` for compatibility.
`--shard-count N --shard-index I` assigns each suite by the first 64 bits
of its name's SHA-256 digest modulo `N`. Adding a suite therefore does not move
existing suites between cache lineages. The shards are deterministic, disjoint
and cover the complete corpus. CI runs eight shards on separate runners, with
`-j2` inside each runner to stay within its memory limit. For example, the third
of eight shards can be reproduced locally with:

```sh
python3 tools/run_differential.py -j2 --shard-count 8 --shard-index 2
```

Each CI shard has its own holbuild snapshot lineage, so a later run restores
the corresponding shard rather than whichever matrix job saved most recently.
Push builds on `main` and `bot/opus/solidity-e2e` save snapshots that their
feature PRs can restore; PR-only snapshots are scoped to that PR and cannot
warm sibling PRs. Branch runs have separate concurrency groups so a later
merge cannot cancel a cache-warming run. Remove the integration-branch push
trigger when that branch is merged into `main`.
Source and Yul suite theories declare a `.results.jsonl` extra output beside
their scripts. holbuild caches and restores it with the theory, so reports
retain outcomes and stage admissions without an old build log. Missing suite
or case records fail the report, including on cache hits. Failed builds use
their diagnostic logs and ignore possibly stale result files.

`solidityDifferentialCorpus` remains a compatibility roll-up, refreshed with
integration reports. It owns no case definitions: ML consumers enumerating
`DB.definitions` must use the per-suite theory segments. A fresh checkout can
build any committed suite directly, for example:

```sh
holbuild -j4 build solidityDifferentialCorpus_storageTheory
```

The artifact goes through `solidityPrepareLib.prepare_artifact`, which checks
the pinned compiler/profile/settings contract, validates and elaborates the
source, and checks the full core program. The evaluator executes that core;
Verifereum executes the recorded bytecode. This comparison does not certify
the compiler or its artifact producer.

Both runs return an outcome, the complete committed storage of the tested
contract and the logs. Source frame completion rolls back writes on panic or revert before
comparison. The verdict compares total word-to-word storage functions by HOL
equality, so agreement includes every slot, including unlisted mapping keys and
cleared slots. The existing Verifereum from/to theorem and HOL's generic cv
equality rule evaluate this equality using the canonical sparse encoding,
which omits zero entries.

The expected store is the initial store with the case's final entries applied;
all unspecified slots are zero. Selected slots (variable roots and explicitly
listed initial/final slots) remain in diagnostic payloads and the existing
projection theorem. A complete-storage mismatch can therefore display equal
selected-slot lists. The negative mapping regression demonstrates this case.

Run the same checks as CI with:

```sh
python3 tools/run_differential.py -j2 \
  -- --max-heap 6000 --skip-checkpoints --skip-proof-steps
holbuild -j8 build --skip-checkpoints --skip-proof-steps solidityHolTheory
```

Pass `--solc /path/to/pinned/solc` to reproduce the compiler artifacts as well.
The upstream `semanticTests` acceptance report is a separate preparation check;
it does not execute those tests' call expectations. The separate
[expectation runner](semantic-expectations-runner.md) executes admitted tests
in order against their upstream observations, outside per-PR CI.

## The compiler's own Yul

Neither run above sees the Yul the compiler emitted: one evaluates the core
program the source elaborates to, the other the bytecode solc recorded. The
third run closes that gap, and it is the hinge the roadmap turns on — a
disagreement between the compiler's own IR and the bytecode compiled from it
is invisible to the two-sided comparison. `tools/run_yul_differential.py`
compiles the same sources with the pinned compiler and executes the imported
runtime or creation object in the Yul semantics.

It runs three stages separately, because they are three different programs:
`irAst`, the code generator's output; the `irOptimizedAst` of that same
compile, with the optimizer off, which is what the Yul transformations leave;
and the production build's `irOptimizedAst`, the optimizer on with
`runs: 200`. The importer (`syntax/yulImportLib.sml`) reads the JSON AST
alongside the text IR — the tree the compiler's own converter walks — and it
fails closed: a node kind, builtin or object form it does not know rejects the
stage rather than being worked around. The report counts a rejected stage
separately from a disagreement, and the stage's cases are not run there.

Each case at each stage gets one `yul_agrees` theorem
(`tests/yulDifferentialScript.sml`), which is the corpus's comparison with the
Yul run standing where the core run stands: the same calldata, the same
outcome, the complete committed storage, and the log the case declares. The
frame is the bytecode run's world — the same sender, value, calldata,
transaction parameters and peer contract — with the imported Yul in place of
the contract's own code, and the contract's deployed code left at its own
address, so that a case calling back into its own address runs the bytecode a
real transaction would (`Caller.bumpSelf`). A message call a Yul frame makes is
Verifereum's, through the same `run_external_call` the source evaluator's
high-level calls use; `docs/yul-call-design.md` says how.

A deployment executes the top-level creation code at the created address, with
empty calldata and the encoded constructor arguments appended to the stage's
actual initcode. Named object sizes and offsets come from the initcode and its
runtime suffix; layouts without that suffix are rejected. `codecopy` reads those
bytes, and `setimmutable` patches the copied runtime at its emitted offsets.
The returned bytes must match that runtime with its immutable patches. The
comparison then observes the immutable words, complete storage and logs, just
as the source/bytecode deployment comparison does. Unsupported object names and
layouts remain failures, including when the runtime object itself was admitted.

The ASTs are tens of megabytes across the corpus, so the tool generates them
with the pinned compiler instead of committing them. It also generates one
wrapper per suite under ignored `tests/yul-generated/`, with exact artifact
dependencies. The runtime-only Yul run is separate from PR CI. It writes the report, which is committed:

```sh
python3 tools/run_yul_differential.py --solc ~/.local/opt/solc-0.8.37/solc -j8
```

`docs/yul-differential.md` is the last run's result: the stages admitted, the
agreements, and every case that is not an agreement, with its status.
`--no-hol` runs the compiler-side checks alone.
