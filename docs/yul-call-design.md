# How a Yul frame's message calls relate to Verifereum's `run_call`

Status: implemented. It adds `call`, `staticcall`, `delegatecall`,
`extcodesize`, `returndatasize`, `returndatacopy` and `gas` to
`semantics/yulEvaluatorScript.sml`, and two fields to the Yul frame; the limits
are listed at the end.

## The problem

The pinned compiler's via-IR Yul does not only compute: it reaches other
accounts. A contract that calls another contract emits `call` or `staticcall`,
reads what came back with `returndatasize` and `returndatacopy`, and asks for
its own gas with `gas`. Until those are evaluated, any contract whose body
calls out can be imported but not run, and the three-way corpus reports its
whole `external` suite as inconclusive rather than checking it.

Two things must be true of the answer. The call must be the *same* call the
bytecode would make — one call mechanics, not a second one that agrees only by
accident — and the Yul frame must stay a frame, not become an EVM execution
state. Verifereum already has the call mechanics: `run_call` in
`spec/vfmExecutionScript.sml`. Solidity-hol already has a caller of it that
builds exactly the one-frame state a message call needs:
`semantics/externalCallScript.sml`'s `run_external_call`, which the source
evaluator's high-level calls also go through. This design reuses that.

## The frame and its callees

A `yul_machine` (`semantics/yulStateScript.sml`) is the running Yul frame. Only
one thing about the call family is structural: a Yul frame never nests inside
another Yul frame. Yul frames are entered by whoever runs a contract's Yul —
here, the differential harness — and a Yul frame's callee is *always* bytecode,
run by Verifereum. So a call back into the frame's own address runs that
account's deployed bytecode, not its Yul. That is what the corpus needs: in
`Caller.bumpSelf`, `ISelf(address(this)).bump(by)` must run the same bytecode
that a real transaction would run, and it does.

The frame carries the call inputs, and two fields exist only for the call
family:

| Field | What the call family reads it for |
| --- | --- |
| `self_address` | the caller of every message call the frame makes |
| `accounts`, `transient`, `logs` | the world a call starts from and the world it leaves |
| `call_value`, `call_data` | the callee sees them only through its own frame; the caller's are untouched by a call |
| `memory`, `memory_size` | the call's input region, and its output region |
| `transaction_parameters` | inherited by the callee's frame, so `origin`, `chainid` and the block builtins agree |
| `return_data` | what `returndatasize` and `returndatacopy` read |
| `gas_limit` | what `gas` reports, and the most a call here can hand on |

`return_data` and `gas_limit` are inputs to the frame like `call_data`: the
frame's caller supplies them, and nothing in the frame writes `gas_limit`.

## The callee's run

`call` and `staticcall` share one definition, `yul_call`, differing only in the
`static` flag; `delegatecall` is the third use of it, below. It reads the input region out of the caller's memory, then hands
the call to `run_external_call`:

```
run_external_call m.self_address callee calldata value static
  (min gas m.gas_limit) m.accounts m.transient
  m.transaction_parameters
```

with `callee` the builtin's address argument, `gas` its gas argument capped at
the frame's budget, `calldata` the bytes the input
region now holds, and `value` the call's value argument (zero for
`staticcall`, which has none). Everything after that is Verifereum's: a fresh
one-frame state whose original accounts are the world after the value
transfer, whose access set holds caller and callee, and whose depth is one;
the value moves before the callee runs; a caller that cannot pay fails the
call without running it; a delegated account runs its delegate's code. The
result is a `call_outcome`: a success flag, the callee's return data, and the
world it left.

The caller's world follows the same rule the EVM's does:

| Outcome | Accounts, transient storage and logs | Yul's first return value | `return_data` |
| --- | --- | --- | --- |
| the callee stopped or returned | the callee's, with its logs after the caller's | 1 | the callee's output |
| the callee reverted | the caller's, unchanged | 0 | the revert data |
| the callee halted exceptionally | the caller's, unchanged | 0 | empty |

`run_external_call` answers `NONE` where the call leaves the model — a
recipient-balance overflow, a run outside the domain (one that ends in no
frame, in more than one, or in a `vfm_abort`), or a callee that ends with
accounts pending deletion. The builtin then answers
`YulInvalid "call outside the model"`, which
the corpus reports as a diagnostic. A call the model cannot make is never
guessed at. A caller that cannot pay is not one of these: it is a failed call,
a 0 with no return data.

The output region is written after the world update: `min(out_size,
returndatasize)` bytes, the same `TAKE r.size output` Verifereum's
`handle_exception` writes when a sub-frame returns. Bytes past that many are
left as they were rather than zeroed, and an output size of zero writes
nothing; an input size of zero reads nothing. Both regions are touched, so a
call expands the caller's memory to cover them, as the EVM's
`max_expansion_range` does.

## Return data

`return_data` is the frame's buffer for its *last* call, set by every `call`
and `staticcall` and never appended to. Before any call it is empty. It is a
separate thing from memory: the callee's output lands in it whether or not the
caller asked for an output region, which is why a caller can ask `call` for no
output at all and still read what came back.

- `returndatasize()` is `LENGTH return_data`.
- `returndatacopy(d, o, s)` copies `s` bytes from `o`. Reading past the end is
  the EVM's `OutOfBoundsRead` exceptional halt, so the builtin answers
  `YulInvalid "return data out of bounds"` — the frame's world rolls back, as
  `finish_yul_frame` says for any invalid.

## The seven builtins

| Builtin | Effect | Result |
| --- | --- | --- |
| `call(g, a, v, in, insz, out, outsz)` | `EffectCall` | success flag |
| `staticcall(g, a, in, insz, out, outsz)` | `EffectCall` | success flag |
| `delegatecall(g, a, in, insz, out, outsz)` | `EffectCall` | success flag |
| `extcodesize(a)` | `EffectCall` | `LENGTH (lookup_account a accounts).code` |
| `returndatasize()` | `EffectFrame` | `LENGTH return_data` |
| `returndatacopy(d, o, s)` | `EffectMemory` | none |
| `gas()` | `EffectFrame` | `gas_limit` |

The effects are the ones `semantics/yulDialectScript.sml` already gave these
names; this work changes the evaluator, not the classification. `extcodesize`
reads the account's own code and not a delegate's, which is what Verifereum's
`step_ext_code_size` does.

## `delegatecall`

A Yul `delegatecall` is the same construction as `call` with three
differences: the callee's *code* runs under the caller's own address, storage
and balance, its caller and call value are the frame's own, and the call moves
no value. `external_call_state` builds a state whose `to` is the callee, which
is `call`/`staticcall` semantics, so `yul_call` with its `delegate` flag set
hands the call to `run_delegate_call` instead, the builder the source's
low-level `a.delegatecall(data)` uses:

```
run_delegate_call m.self_address m.caller_address m.call_value callee calldata
  static (min gas m.gas_limit) m.accounts m.transient m.transaction_parameters
```

Its state's `to` is the frame's own address and its code the callee's (a
delegated account's delegate's; a precompile runs as the precompile). The call
mechanics is still `run_call`, and the outcome, the world and the return data
follow the same table as `call`'s.

## What the model does not do

- **Gas is not charged.** No step in the Yul evaluator costs gas, so
  `gas_limit` never falls and `gas()` reports the frame's whole budget. A
  call's own gas argument is what the callee gets, capped at the frame's
  budget, since the frame cannot hand on more than it holds; solc writes
  `gas()` there unless the source names a limit, in which case the limit is
  what the callee runs with. Since the
  callee runs as bytecode, *its* gas is accounted for by Verifereum, and a
  callee that needs more than the budget fails here as it would on chain.
- **A Yul frame is never entered by a static call.** The frame's own
  static-ness is not a field, so a `staticcall` *into* the top-level Yul frame
  would let it write storage and transient storage. The callee's static-ness
  is Verifereum's and is right. No corpus case needs the top-level frame to be static; giving the
  frame a static flag is a small change if one does.
