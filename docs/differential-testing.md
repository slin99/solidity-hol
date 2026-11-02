# Differential execution

`tools/run_differential.py` checks the maintained corpus in
`testdata/differential/corpus.json`. Each suite supplies a compiler artifact,
source unit and deployed contract; each case is a transaction to the contract
with initial storage and an expected result, final storage and logs.

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
too. Raw calldata declares no return types, so its `return` expectation is
`[]`.

A case with `"deploy": true` and the constructor's `args` (or, as
`calldata`, their raw encoding) is a creation instead: Verifereum runs a creation transaction whose data is the artifact's
initcode followed by the encoded arguments, and the evaluator runs the
program's creation procedure (`deploy_contract`) on the encoded arguments, at
the address the transaction creates (`address_for_create` of the sender at
nonce 0). Both observe that account, which starts with no code or storage,
so `storage` must be empty and `logger` names that address. A successful
creation is observed as returning no data, so its `return` expectation is
`[]`; the deployed code is not compared. The HOL corpus theory proves one
`differential_agrees` theorem per case. Diagnostic failures and exhausted fuel
are inconclusive, never agreement.

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
python3 tools/run_differential.py -j8 --allow-cached \
  -- --skip-checkpoints --skip-proof-steps
holbuild -j8 build --skip-checkpoints --skip-proof-steps solidityHolTheory
```

Pass `--solc /path/to/pinned/solc` to reproduce the compiler artifacts as well.
The upstream `semanticTests` acceptance report is a separate preparation check;
it does not execute those tests' call expectations.

## The compiler's own Yul

Neither run above sees the Yul the compiler emitted: one evaluates the core
program the source elaborates to, the other the bytecode solc recorded. The
third run closes that gap, and it is the hinge the roadmap turns on — a
disagreement between the compiler's own IR and the bytecode compiled from it
is invisible to the two-sided comparison. `tools/run_yul_differential.py`
compiles the same sources with the pinned compiler, imports the runtime Yul it
emitted, and executes that in the Yul semantics.

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

`delegatecall` is not implemented and the dialect does not name it, so a stage
that uses one is rejected at import rather than run wrongly.

The ASTs are tens of megabytes across the corpus, so the tool generates them
with the pinned compiler instead of committing them, and the run is far longer
than the rest of CI. It writes the report, which is committed:

```sh
python3 tools/run_yul_differential.py --solc ~/.local/opt/solc-0.8.37/solc -j8
```

`docs/yul-differential.md` is the last run's result: the stages admitted, the
agreements, and every case that is not an agreement, with its status.
`--no-hol` runs the compiler-side checks alone.
