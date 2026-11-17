# Source-facing EVM adapter contract

Status: interface obligations for review, **not** an implemented source adapter
or a proved simulation theorem. The concrete experiment in
`semantics/solidityEVMCallScript.sml` supplies the execution mechanism. The
source/context relation remains aligned with the intended Vyper-HOL #98 design.

The evaluator's high-level calls currently go through
`semantics/externalCallScript.sml`, a provisional adapter that does not meet
these obligations: it runs the callee in a fresh frame whose access set holds
only caller and callee and whose depth is one, under a fixed gas budget. The
transaction-original accounts and pending deletions are the exception: the
source world carries them (`original`, `to_delete`), each call or creation
takes them in and hands back what it left, and a frame that succeeds deletes
the pending accounts when the transaction settles (`settle_source_world`), so
SELFDESTRUCT follows EIP-6780 across the transaction's calls.

## Ownership boundary

The Solidity evaluator evaluates source operands and fixes their schedule before
requesting bytecode execution. The fixed Verifereum adapter executes the complete
nested subtree, including bytecode reentry, then supplies a result to the source
frame if that frame still exists. There is no arbitrary handler parameter and
no recursive source interpretation of external targets.

A source world is not a sufficient input to reconstruct an EVM invocation.
`project_evm_world` deliberately omits checkpoints, caller contexts, gas,
refunds, access sets and domain tracking; it keeps the transaction-original
accounts and pending deletions, which the source world carries.
The adapter must receive justified concrete boundary context separately. This is
execution/simulation context, not artificial EVM registers stored in Solidity
locals or heap state.

## Required inputs

| Input | Required information / obligation |
| --- | --- |
| Validated program environment | Resolved source calls, admitted call kind, ABI/layout information and compiler profile |
| Evaluated source request | Target, calldata or initcode, value, salt where relevant, explicit requested gas if present; no deferred effectful expressions |
| Source state | Meaningful frame, locals/heap, shared accounts/transient storage and logs after all operand effects |
| Concrete boundary context | Existing EVM invocation and caller contexts underneath it, current rollback state, transaction-original accounts, transaction parameters and domain mode |
| Concrete call-site representation | Code/parsed code/PC at the requested opcode; stack operands, calldata/initcode in concrete memory, output-memory destination |
| Execution evidence | Distinguished-frame gas observations and other simulation evidence needed to justify the concrete call site; not persistent world state |

The current CALL/CREATE experiment operates on the concrete input row only. It
requires the prepared state rather than constructing one from the other rows.
A future source adapter must establish the following correspondence, not assume
that filling missing fields with defaults is sound.

## Entry correspondence obligations

1. **Same distinguished activation:** source self/storage address, code context,
   caller, value, calldata, static restriction and deployment phase correspond
   to the concrete invocation. DELEGATECALL must distinguish code address from
   storage address and preserve inherited caller/value.
2. **Same current world:** source account and transient-storage views reflect
   all effects before the call. Caller-frame logs correspond under the chosen
   observation relation. Bytecode sees source writes already performed.
3. **Valid transaction history:** preserve transaction-original accounts,
   checkpoints, caller contexts, access sets, pending deletions, transaction
   parameters, refund counters and domain mode. Current storage need not equal
   original storage. Apply upstream storage-preservation hypotheses explicitly;
   they are not a consequence of `wf_state` alone.
4. **Correct opcode inputs:** the concrete stack/memory encode exactly the
   evaluated request. Output offsets and scratch allocation must be justified
   by the concrete-memory correspondence, not selected arbitrarily while
   claiming gas fidelity. Concrete parsed code agrees with actual code.
5. **Gas evidence:** preserve the user gas expression as an ordinary source
   operand. State precisely whether each observation concerns available gas,
   a requested budget, capped gas, or actual callee gas. EIP-150, stipends and
   opcode/memory/access overhead remain Verifereum mechanisms. A large fixed
   fixture budget is not a source compiler-correspondence policy.
6. **Well-formed concrete state:** establish Verifereum's frame/stack/gas/account
   invariants, including those relating caller gas to deeper contexts. Retain
   domain constraints rather than silently switching to unconstrained execution.

These obligations may be expressed by a relation rather than a uniquely
invertible projection. No final representation for supplying the witness has
been selected. In particular, this contract does not decide whether a source
entry receives concrete context as a separate argument or through an execution
wrapper. That remains a Vyper-HOL #98 alignment question.

## Operation and returned state

The concrete mechanism checks the boundary opcode, performs handled EVM entry,
and runs an entered child until it returns. Precompile completion may finish
inside entry. The caller suffix is not executed by the boundary driver.

| Concrete outcome | Source-side obligation |
| --- | --- |
| `BoundaryReturned` | Interpret CALL success flag or CREATE address/zero and returndata; preserve the complete concrete returned state; update shared source world before subsequent reads |
| `BoundaryCallerExited` | The distinguished caller itself exited during handled entry; do not resume its source continuation; retain parent-resumption state and finish that frame according to the established correspondence |
| `BoundaryAborted` | Preserve the raw EVM result/state; distinguish genuine caller failure from domain/semantic aborts rather than treating every case as a Solidity failed call |
| Wrong position / malformed result / no result | Explicit adapter error, not success or Solidity revert; malformed results retain concrete state for diagnosis |

A nested callee's REVERT, exceptional halt or insufficient-balance rejection
usually returns normally with a zero word. The handled low-level result need not
retain the precise callee exception reason. Solidity low-level calls observe
success and bytes; high-level ABI validation, revert bubbling and try/catch
classification belong to source execution after the response. If future proof
machinery needs exact halt reasons, it must obtain additional evidence rather
than infer them from empty returndata.

Nested execution may modify the distinguished account through reentry. Updating
only the callee's account on return would be incorrect: adopt all relevant EVM
world changes according to the relation. Restore source locals/scopes separately;
those are not bytecode-visible storage.

## Rollback, evidence and finalization

Successful callee effects remain provisional until the enclosing frame commits.
An enclosing revert must undo successful inner storage, balance, transient,
log and other rollback-governed effects. Call entry can add caller-owned access
information before taking the callee checkpoint; do not replace this discipline
with a blanket reset to the pre-opcode state on every failed call.

Transaction-original state is not simply an immutable copy of current accounts.
Verifereum stores it in `execution_state.originalAccounts`, separately from saved
rollback checkpoints. Creation setup deliberately resets the created account in
that field (`proceed_create` / `set_original`), while saved rollback accounts
retain pre-creation storage. A preservation theorem must account for that rule;
the CALL-only original-storage
witness is not a blanket immutability theorem for arbitrary CREATE subtrees.

Frame-local gas evidence belongs to the distinguished source activation only.
Opaque nested frames do not consume it, and revert does not restore its consumed
prefix. Source fuel remains separate and is not spent on Verifereum execution.
Transaction finalization, fees/refund caps, deletion processing and transient
storage clearing do not happen after each external call.

## Evidence now available

- `solidityEVMBoundaryPropsTheory`: boundary well-formedness preservation;
  unconditional transaction-parameter preservation; entered-subtree unaccessed
  slots keep their value, or become zero in an account with nonce zero and empty
  code at subtree entry, under exact upstream checkpoint/access hypotheses.
- `solidityEVMBookkeepingTestTheory`: nonempty seeded access/domain/deletion and
  transient state survive successful/reverted calls; current storage 9, caller
  checkpoint 9 and transaction-original storage 5 are kept distinct; successful
  write changes current storage to 1 without resetting the checkpoints; caller
  tail metadata and an untouched storage slot are preserved.
- `solidityEVMCreateTestTheory`: CREATE/CREATE2 clear storage in nonce-zero,
  code-empty targets without accessing those slots; failed initcode and enclosing
  reverts restore saved storage, including when creation occurs in a CALL subtree.
- `solidityEVMReentryTestTheory`: a well-formed outer A invocation executes its
  actual prefix to CALL, B reenters deployed A's callback branch, and resumed A
  observes storage 7 and returns byte 7. Original A storage remains 0. This is
  an EVM boundary witness, not a source-refinement theorem.

These facts constrain the source adapter contract but do not prove its entry
correspondence. Next work should resolve context supply and gas evidence with
upstream, then establish a source-step/body simulation rather than silently
strengthening a finite regression into a general theorem.
