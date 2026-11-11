# Semantics architecture

The executable semantics has one definition: import an analyzed compiler source
unit, elaborate it into an ordered core, then evaluate that core. Keeping one
checked preparation boundary and one storage path makes additions use the same
validation and execution rules as existing consumers.

## Preparation and declarations

`solidityPrepareLib.prepare_artifact` checks the pinned compiler, artifact format,
profile and Standard JSON settings (including the restricted
[stack-depth fallback](profiles.md#stack-depth-fallback)), imports and validates the normalized source,
elaborates it, and cv-evaluates the full `wf_core_program`. Differential tests
and the semanticTests acceptance scanner share this API. Metadata validation is
an SML check; source validation, elaboration and core checking return HOL
certificates. Metadata is not proof that the recorded compiler output is genuine.

When creation cannot be lowered, preparation retains the checked runtime
procedures and marks creation unsupported. Deployment then fails closed with
`ContractInvalid "unknown procedure"`; unsupported helpers remain excluded.

Malformed artifacts, unsupported import/lowering, source rejection and invalid
generated core are separate failures. Invalid generated core is an implementation
error. Lower-level importer/elaborator functions remain available; their callers
must establish provenance, source validity and full core well-formedness.

A `core_program` owns procedures, state variables, semantic declarations and keyed
storage layouts. `core_program_environment` derives both checker and runtime
environments from it. `StructDeclaration` records field identities and types even
without storage metadata. Layouts give relative slots, offsets and extents and
must agree with those declarations. Enums retain their semantic declarations. User-defined value types are
erased to their underlying elementary types by the importer; `wrap` and
`unwrap` use scalar conversions, and overloaded operators use internal calls.

Public state variables, constants and immutables may override external
functions. The importer removes the replaced function implementations along
`baseFunctions`, including transitive overrides, so the existing getter is the
only dispatch entry for that selector. Replaced implementations do not pull in
unused library dependencies. Custom errors accept elementary and enum
parameters; enums keep their declaration identity and encode as `uint8` through
the existing scalar ABI encoder.

## Destinations and storage

Elaboration represents an assignment destination as a local binding or an
already evaluated reference. `elab_destination`, `read_destination` and
`write_destination` are shared by assignment, compound assignment, increment
and scalar `delete`. Deletion writes the type's default without reading its
old value, so it preserves neighboring packed storage.
Tuple writes use the same helpers, retaining identifier-only target coverage and
right-to-left writes. The pinned profile evaluates the assignment RHS before
capturing a computed LHS. Snapshots keep earlier values stable while later
operands run. Postfix increment preserves its old value; compound assignment
reads and writes the captured location once.

Scalar state variables use `StateReferenceOperation`, `ReadOperation` and
`CaptureValueStmt`, like navigated storage. There is no second scalar-state
read/capture operation. `WriteScalarStmt`, `BindReferenceStmt` and
`CopyContentsStmt` remain distinct: changing an alias is not copying an aggregate.
The latter operations are extension points, not aggregate execution coverage.

`solidityStorage` owns concrete storage encoding, packed scalar access, mapping
hashing, array navigation, state references and struct-field navigation. Scalar
word extraction and replacement are shared by persistent and transient state;
state descriptors select the backend. Byte-sequence mapping keys use their
unpadded contents, read through the existing memory/calldata/storage byte path.
These
helpers take evaluated values/references and accounts; they do not evaluate core
atoms or change scopes. `solidityEvaluator` owns atom evaluation, bindings,
captured targets, frame checks and control flow. Its static-frame write rejection
is deliberate and remains `InvalidCompletion`.

## Evaluator interfaces and validation

The evaluator exposes unconditional block, loop and call equations in
`solidityEvaluatorProps`: `eval_block_cons`, `eval_block_append`,
`eval_loop_unfold` and `invoke_source_unfold`. Intermediate-result wrappers
prevent rewriting from duplicating unevaluated operations. Existing fuel
stability results keep their statements. Fuel bounds recursive depth, not EVM
gas; sibling statements reuse a bound.

These equations hold for arbitrary environments and runtime frames. They do not
claim type safety or progress. `wf_core_program` and typed arguments alone do
not imply execution avoids `InvalidCompletion`; runtime bindings, concrete
references, accounts and static-frame permissions matter. Preservation results
must state the exact premises of the operation they justify. No stronger
execution restriction is hidden in preparation to make a theorem hold.

Differential verdicts compare the complete committed contract storage, using
Verifereum's canonical zero-omitting cv encoding of its total storage map.
Explicit slot lists remain diagnostics. Revert/panic observations use the rolled
back world. A checked mutant that writes an otherwise unlisted mapping slot
proves why the former slot projection was incomplete. See
[differential-testing.md](differential-testing.md) for execution checks and
[semantic-tests-coverage.md](semantic-tests-coverage.md) for the separate
acceptance census.

## Extension points

Add a source form through normalized import/validation, ordered elaboration,
core checking and execution, then test it against the pinned compiler. Extend
the existing destination and storage interfaces when needed. Keep unsupported
source and invalid generated core distinguishable. The acceptance census tracks
which upstream tests prepare; executing upstream semanticTests expectations is
separate work.

Memory/calldata execution, a memory model compatible with inline assembly, and
aggregate aliasing/copying remain unresolved. Concrete CALL/CREATE experiments
below do not settle the source external-call context, transaction bookkeeping or
gas contract. Deployment and exact gas/refund correspondence also remain open.
Full type safety and whole-language coverage are later obligations.

## Concrete EVM boundary experiment

`execute_boundary` takes an **existing concrete EVM execution state** positioned
at a CALL-family or CREATE-family opcode. Concrete operand stack, input/output
memory, caller gas and caller checkpoints are supplied by the fixture/context.
It never rebuilds transaction state from the observable source projection.

1. Check the parsed opcode position.
2. Execute Verifereum's handled `step` (including precompile completion).
3. If a child remains on the stack, execute `run_call` for that entered frame.
4. Otherwise return the entry result immediately; do not run the caller suffix.

`observe_boundary` retains the entire returned concrete state. A normal result
reports the caller's stack word and returndata: CALL success flag, or CREATE
address/zero. Nested revert/exception is ordinarily a normal return with word
zero; the precise nested halt reason is not recoverable from this low-level
result. A singleton caller-entry failure or domain/semantic abort retains the raw result.
A nested caller-entry exception can pop the caller itself and return normally to
its parent; `BoundaryCallerExited` retains that concrete state. The source driver
must not resume the exited source frame. The handled result does not reveal its
precise halt reason. Malformed results also retain their concrete state. Wrong
opcode position and no-result outcomes remain distinct checks at the experiment
boundary, not Solidity reverts.

The pinned dependency's `vfmDecreasesGasTheory.run_call_eq_tr` unconditionally
shows `run_call` returns `SOME`. `boundary_execution_has_result` reuses it; no
source fuel is added. Well-formedness is still required for upstream preservation
laws. The generic CALL fixture has a proved `wf_state` condition on code and
stack sizes; the nested outer-rollback fixture is separately proved well formed.
Do not infer preservation hypotheses for arbitrary caller checkpoints from
termination alone. `solidityEVMBoundaryPropsTheory` now derives boundary
well-formedness preservation and unconditional transaction-parameter preservation.
For entered subtrees, an unaccessed slot keeps its value or becomes zero in an
account with nonce zero and empty code at subtree entry, with the exact upstream
checkpoint/access premises. CREATE can clear pre-existing storage there. See
[source-evm-adapter-contract.md](source-evm-adapter-contract.md) for the source
adapter's required inputs and entry/exit correspondence obligations.

### Executed proof witnesses

- Returned byte 0x2a reaches caller memory and returndata; invalid caller suffix
  is not executed.
- Successful SSTORE persists; SSTORE followed by REVERT restores storage while
  retaining revert bytes.
- INVALID is a low-level failed call, not an adapter semantic abort.
- STATICCALL rejects SSTORE; DELEGATECALL writes the caller's storage.
- Empty-code calls succeed; identity precompile completion during entry does
  not accidentally execute the caller suffix. Insufficient balance returns a
  failed call; successful value transfer occurs once; domain errors remain
  semantic aborts rather than ordinary low-level failure.
- Nested caller-entry out-of-gas exits to its parent, retains the concrete state,
  restores storage and stops before the parent suffix.
- CREATE installs initcode-returned runtime bytecode; reverted initcode and
  address collision retain the creator's incremented nonce. CREATE2 uses the
  salt/initcode-derived address.
- An outer frame reverting after an inner successful call undoes inner storage
  changes through genuine nested EVM checkpoints.
- Two calls with the same transaction state preserve transient storage. The
  harness supplies the second operand stack, but resets no transaction fields.
- Nonempty seeded accesses, domain data, transient storage and pending deletions
  survive success/revert. Saved current storage and transaction-original storage
  remain distinct; caller-tail metadata and an untouched slot are retained.
- Deployed A/B bytecode performs A -> B -> A reentry, then resumed outer A reads
  the callback's storage change and returns it. Both the initial invocation and
  the boundary state reached by its actual prefix are proved well formed.

Fixtures use bounded gas to test EVM mechanics. They make no compiler-equivalent
source gas claims. Exact gas/refunds/access-state laws, further domain and
value-transfer edge cases and full source correspondence need additional
witnesses/proofs. The reentry and bookkeeping witnesses are concrete finite
checks, not universal checkpoint/tail preservation or source simulation theorems. Creation fixtures execute real initcode but do not
constitute Solidity constructor/deployment semantics.
