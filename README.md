# Solidity-HOL

Formal and executable [Solidity](https://soliditylang.org/) semantics in
[HOL4](https://hol-theorem-prover.org/), using concrete EVM storage and execution
from [Verifereum](https://verifereum.org/).

## Execution pipeline

The semantic definition is compiler artifact → imported source unit →
`elaborate_unit` → ordered core → fuel-indexed evaluator. There is no separate
source-unit execution relation. Elaboration names effectful intermediate
results and fixes evaluation order for the pinned compiler profile; core
operands are pure bindings or constants. Fuel bounds recursive calls and loop
iterations independently of EVM gas.

`solidityPrepareLib.prepare_artifact` is the checked entry point for artifact
consumers. It checks the artifact format, compiler version/commit, profile and
Standard JSON settings against `SOLIDITY_PIN` and
`profiles/solc-0.8.37-via-ir-osaka.json`, accepting the optimized variant only
with recorded unoptimized stack-depth failures (see [profiles.md](docs/profiles.md)).
It then imports and validates the source,
elaborates it, and checks the complete `wf_core_program` with `cv_eval`.
Success retains the checked artifact alongside the source/core terms and HOL theorems for source validation,
elaboration and core well-formedness. Artifact metadata checks run in SML;
they do not certify that the compiler produced the recorded output. The Python
runner's solc-free artifact checks provide earlier diagnostics; acceptance is
always decided by this SML preparation boundary.

Malformed artifacts, unsupported import/lowering, source-validation rejection
and invalid generated core have distinct diagnostics. Source validation also
contains supported-subset restrictions. Invalid generated core is an
implementation failure. Unexpected HOL evaluation failures propagate.

The raw importer and `elaborate_unit` remain available for reasoning and
frontend inspection. Their callers own the compiler/profile contract, source
validation and full core check. `prepare_unit` performs the semantic checks for
an already imported unit whose provenance the caller has established.

## Core and storage

A `core_program` owns its procedures, state variables, semantic type
declarations and storage layouts. `core_program_environment` derives the
checking/runtime environment from that program. Struct declarations describe
field identities and types even when there is no storage layout. Storage
layouts separately describe slots and offsets and must agree with the declared
fields. Enums retain their declaration identities. The importer erases user-defined
value types to their elementary underlying types and lowers their resolved
operators to internal calls.

The evaluator executes elementary scalar operations and conversions, locals,
tuples, structured control flow, internal calls, built-in failures, packed
state values, scalar-key mappings, storage arrays and storage struct members.
Assignment, compound assignment, increment and tuple writes share local or
captured-reference destinations. Non-canonical `bool` and enum storage bytes,
and non-canonical words written back to locals by inline assembly, fail with
`InvalidCompletion`: core source values carry no dirty bits. This applies to
storage array copies and ABI encoding too. `solidityStorage` owns packed access and
navigation; the evaluator owns bindings, frame checks and control flow.
Scalar writes, reference
rebinding and content copying are distinct core operations; the latter two
remain extension points rather than implemented aggregate semantics.

An inline assembly block (`AssemblyStmt`) runs on the Yul evaluator, over a
memory holding each memory `bytes` and `string` object where the compiler
allocates it (its length word at its address, then its bytes): it reads and
writes back the value-type locals it names, reads state variables' slots and
offsets and storage pointer locals' slots and offsets (assigning a pointer's
`x.slot` points it at that slot of the executing account), integer, `bool` and fixed-bytes constants, and the addresses of the memory
`bytes` and `string` locals it names as literals in its code, as the compiler
puts them, so its Yul functions see them too (a function's parameters and results may
reuse such a name in its body; a memory reference may not be assigned). Code
that can reach the block's normal exit may write at a literal address only in
the scratch space (an `if` or `switch` body or a Yul function's body that ends
in `return`, `revert` or `stop` may write anywhere), and a literal address and
length are read only at the free memory pointer and memory the block wrote
itself (an `mstore`, a call's output region or a `returndatacopy`, also in an
argument to the right, since arguments run right to left); at a computed
address, a block that exits normally may write only the scratch space, the byte
sequences' data words and the memory from the free memory pointer up, not their
length words or the free memory pointer itself; their bytes are read back, and
the writes from the free memory pointer up, the temporary memory the Solidity
docs allow a memory-safe block, are dropped. Whatever the address, a read outside the free memory pointer, the
zero slot, the byte sequences' words and the bytes the block wrote fails with
an `InvalidCompletion`. `return`/`stop`
end the frame with a `HaltCompletion`. `call` and `staticcall` run the
callee through the same `externalCall` adapter as high-level calls, with the
same fixed gas budget: `gas()` may only be a call's gas argument, where it
stands for that budget. The block sees the frame's return data as the
source's calls left it; after an `ecrecover`, whose return data the source
doesn't compute, `returndatasize`/`returndatacopy` must follow a call the
block made itself, else the block fails closed. In a
static frame a block naming `call` fails closed. Memory
expansion gas is not modelled, so a halting block's write far past the used
memory succeeds where the EVM runs out of gas. Memory/calldata execution and a memory
model shared with inline assembly beyond byte sequences remain unresolved. High-level external calls and
the low-level `call`, `staticcall` and `delegatecall` run the callee on
Verifereum through `externalCall`, a provisional adapter with a fixed gas
budget (a `gas` option caps it) and a fresh callee frame; a delegate call's
frame runs the callee's code in the caller's account. Creation is not
connected yet. Core well-formedness alone does not rule out `InvalidCompletion`:
for example, a storage write in a static frame is deliberately invalid.

## Yul

The compiler's runtime Yul object has its own AST, EVM dialect, machine and
fuel-indexed evaluator in `syntax/yulAST`, `semantics/yulDialect`,
`semantics/yulState` and `semantics/yulEvaluator`;
`semantics/yulEvaluatorProps` proves that a run which does not run out of fuel
gives the same answer at any larger fuel. Input outside the modelled subset is
an explicit invalid outcome rather than a value, as are two ill-formed inputs
the compiler rejects by itself: a `break` or `continue` in a `for` loop's post
block, and a call argument that is not exactly one value. The node kinds
and builtins the pinned compiler emits, per fixture and per stage of its Yul
pipeline — the unoptimized Yul, and the optimized artifact with the Yul
optimizer off and on — are enumerated in
[testdata/yul/reconnaissance.md](testdata/yul/reconnaissance.md).

## Validation

```sh
holbuild buildhol
holbuild -j8 build solidityHolTheory
python3 -m unittest discover -s tests -p 'test_*.py'
python3 tools/run_differential.py -j8
```

The differential corpus compares source evaluation with pinned compiler
bytecode in Verifereum, including complete committed contract storage. Slot
lists select diagnostics; they do not limit comparison. The upstream `semanticTests` coverage tool checks
preparation acceptance; it does not execute the tests' call expectations.
Each rejected test lists every blocker preparation reports, with its node
id; the tool only groups those lines under feature labels.
The coverage tool stages its compiler artifacts and pin/profile files for a
cached `holbuild run-action` batches of up to 128 tests on the configured
remote-execution fleet. Batches run serially because their startup/export
phases share holbuild's project mutation lock. Completed batches
can be reused after an interrupted run. Python 3.11 or later is required. Without
a configured fleet, it runs the preparation check locally. An older holbuild
without `run-action` needs an upgrade when remote execution/cache is configured;
otherwise it can use the local check. A configured fleet's execution failures stop
the coverage run instead of falling back locally.
See [differential-testing.md](docs/differential-testing.md),
[profiles.md](docs/profiles.md) and
[semantic-tests-coverage.md](docs/semantic-tests-coverage.md).
Run admitted upstream call expectations separately with
[`tools/run_semantic_expectations.py`](docs/semantic-expectations-runner.md);
this on-demand sweep does not run in per-PR CI.

Feature PRs include their own suite, compiler artifact and generated per-suite
source/bytecode theories; shared report
snapshots are refreshed after merges. See
[generated-artifacts.md](docs/generated-artifacts.md) for the commands and ownership.

See [implementation-blueprint.md](docs/implementation-blueprint.md) for module
ownership, evaluator interfaces and extension points.
