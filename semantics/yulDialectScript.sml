(* The EVM dialect of Yul: how the builtins in yulAST are spelled, and what
 * each one may touch.
 *
 * A builtin's spelling is the Yul name the compiler writes; builtin_of_name is
 * the total, fail-closed inverse an importer uses, and the round-trip theorem
 * below says every builtin has its name back. Anything else is not a builtin.
 *
 * The effect of a builtin is what a caller has to know to reason about it:
 * whether it reads or writes the frame's memory, the executing account's
 * storage, the frame's own fields, or the log, or ends the frame. It is
 * deliberately coarse -- one classification per builtin, not per access.
 *)
Theory yulDialect
Ancestors
  yulAST

Definition builtin_name_def:
  builtin_name YAdd = "add" ∧
  builtin_name YSub = "sub" ∧
  builtin_name YMul = "mul" ∧
  builtin_name YDiv = "div" ∧
  builtin_name YSDiv = "sdiv" ∧
  builtin_name YMod = "mod" ∧
  builtin_name YSMod = "smod" ∧
  builtin_name YExp = "exp" ∧
  builtin_name YSignExtend = "signextend" ∧
  builtin_name YLt = "lt" ∧
  builtin_name YGt = "gt" ∧
  builtin_name YSLt = "slt" ∧
  builtin_name YSGt = "sgt" ∧
  builtin_name YEq = "eq" ∧
  builtin_name YIsZero = "iszero" ∧
  builtin_name YAnd = "and" ∧
  builtin_name YOr = "or" ∧
  builtin_name YXor = "xor" ∧
  builtin_name YNot = "not" ∧
  builtin_name YShl = "shl" ∧
  builtin_name YShr = "shr" ∧
  builtin_name YSar = "sar" ∧
  builtin_name YKeccak256 = "keccak256" ∧
  builtin_name YMLoad = "mload" ∧
  builtin_name YMStore = "mstore" ∧
  builtin_name YMCopy = "mcopy" ∧
  builtin_name YSLoad = "sload" ∧
  builtin_name YSStore = "sstore" ∧
  builtin_name YCallDataLoad = "calldataload" ∧
  builtin_name YCallDataSize = "calldatasize" ∧
  builtin_name YCallValue = "callvalue" ∧
  builtin_name YMemoryGuard = "memoryguard" ∧
  builtin_name YCaller = "caller" ∧
  builtin_name YLoadImmutable = "loadimmutable" ∧
  builtin_name YLog1 = "log1" ∧
  builtin_name YLog3 = "log3" ∧
  builtin_name YAddress = "address" ∧
  builtin_name YOrigin = "origin" ∧
  builtin_name YChainId = "chainid" ∧
  builtin_name YNumber = "number" ∧
  builtin_name YTimestamp = "timestamp" ∧
  builtin_name YCoinbase = "coinbase" ∧
  builtin_name YLog0 = "log0" ∧
  builtin_name YLog2 = "log2" ∧
  builtin_name YLog4 = "log4" ∧
  builtin_name YGasPrice = "gasprice" ∧
  builtin_name YBaseFee = "basefee" ∧
  builtin_name YGasLimit = "gaslimit" ∧
  builtin_name YStop = "stop" ∧
  builtin_name YCall = "call" ∧
  builtin_name YStaticCall = "staticcall" ∧
  builtin_name YExtCodeSize = "extcodesize" ∧
  builtin_name YReturnDataSize = "returndatasize" ∧
  builtin_name YReturnDataCopy = "returndatacopy" ∧
  builtin_name YGas = "gas" ∧
  builtin_name YPop = "pop" ∧
  builtin_name YReturn = "return" ∧
  builtin_name YRevert = "revert" ∧
  builtin_name YCodeSize = "codesize" ∧
  builtin_name YCodeCopy = "codecopy" ∧
  builtin_name YDataSize = "datasize" ∧
  builtin_name YDataOffset = "dataoffset"
End

Definition builtin_of_name_def:
  builtin_of_name name =
    if name = "add" then SOME YAdd
    else if name = "sub" then SOME YSub
    else if name = "mul" then SOME YMul
    else if name = "div" then SOME YDiv
    else if name = "sdiv" then SOME YSDiv
    else if name = "mod" then SOME YMod
    else if name = "smod" then SOME YSMod
    else if name = "exp" then SOME YExp
    else if name = "signextend" then SOME YSignExtend
    else if name = "lt" then SOME YLt
    else if name = "gt" then SOME YGt
    else if name = "slt" then SOME YSLt
    else if name = "sgt" then SOME YSGt
    else if name = "eq" then SOME YEq
    else if name = "iszero" then SOME YIsZero
    else if name = "and" then SOME YAnd
    else if name = "or" then SOME YOr
    else if name = "xor" then SOME YXor
    else if name = "not" then SOME YNot
    else if name = "shl" then SOME YShl
    else if name = "shr" then SOME YShr
    else if name = "sar" then SOME YSar
    else if name = "keccak256" then SOME YKeccak256
    else if name = "mload" then SOME YMLoad
    else if name = "mstore" then SOME YMStore
    else if name = "mcopy" then SOME YMCopy
    else if name = "sload" then SOME YSLoad
    else if name = "sstore" then SOME YSStore
    else if name = "calldataload" then SOME YCallDataLoad
    else if name = "calldatasize" then SOME YCallDataSize
    else if name = "callvalue" then SOME YCallValue
    else if name = "memoryguard" then SOME YMemoryGuard
    else if name = "caller" then SOME YCaller
    else if name = "loadimmutable" then SOME YLoadImmutable
    else if name = "log1" then SOME YLog1
    else if name = "log3" then SOME YLog3
    else if name = "address" then SOME YAddress
    else if name = "origin" then SOME YOrigin
    else if name = "chainid" then SOME YChainId
    else if name = "number" then SOME YNumber
    else if name = "timestamp" then SOME YTimestamp
    else if name = "coinbase" then SOME YCoinbase
    else if name = "log0" then SOME YLog0
    else if name = "log2" then SOME YLog2
    else if name = "log4" then SOME YLog4
    else if name = "gasprice" then SOME YGasPrice
    else if name = "basefee" then SOME YBaseFee
    else if name = "gaslimit" then SOME YGasLimit
    else if name = "stop" then SOME YStop
    else if name = "call" then SOME YCall
    else if name = "staticcall" then SOME YStaticCall
    else if name = "extcodesize" then SOME YExtCodeSize
    else if name = "returndatasize" then SOME YReturnDataSize
    else if name = "returndatacopy" then SOME YReturnDataCopy
    else if name = "gas" then SOME YGas
    else if name = "pop" then SOME YPop
    else if name = "return" then SOME YReturn
    else if name = "revert" then SOME YRevert
    else if name = "codesize" then SOME YCodeSize
    else if name = "codecopy" then SOME YCodeCopy
    else if name = "datasize" then SOME YDataSize
    else if name = "dataoffset" then SOME YDataOffset
    else NONE
End

Datatype:
  yul_builtin_effect
  = EffectPure      (* only its arguments: the arithmetic, comparison and
                       bitwise operations, memoryguard, which is the identity
                       in the unoptimized IR, and pop, which discards its
                       argument *)
  | EffectMemory    (* reads or writes the frame's memory *)
  | EffectStorage   (* reads or writes the executing account's storage *)
  | EffectFrame     (* reads the frame: its call data, its call value, the
                       account it runs for, an immutable the constructor
                       patched into its code, the transaction and block it
                       runs in, its remaining gas, or the return data of its
                       last call *)
  | EffectCall      (* reaches other accounts: a message call, which reads
                       its input from memory, writes its output there and
                       changes the world, or another account's code size *)
  | EffectLog       (* appends a log entry, whose payload it reads from
                       memory: a touch like any other, so it can raise the
                       frame's memory size *)
  | EffectHalt      (* ends the frame, returning or reverting data from
                       memory *)
  | EffectObject    (* the running code, or the object's data and
                       subobjects *)
End

Definition builtin_effect_def:
  builtin_effect YAdd = EffectPure ∧
  builtin_effect YSub = EffectPure ∧
  builtin_effect YMul = EffectPure ∧
  builtin_effect YDiv = EffectPure ∧
  builtin_effect YSDiv = EffectPure ∧
  builtin_effect YMod = EffectPure ∧
  builtin_effect YSMod = EffectPure ∧
  builtin_effect YExp = EffectPure ∧
  builtin_effect YSignExtend = EffectPure ∧
  builtin_effect YLt = EffectPure ∧
  builtin_effect YGt = EffectPure ∧
  builtin_effect YSLt = EffectPure ∧
  builtin_effect YSGt = EffectPure ∧
  builtin_effect YEq = EffectPure ∧
  builtin_effect YIsZero = EffectPure ∧
  builtin_effect YAnd = EffectPure ∧
  builtin_effect YOr = EffectPure ∧
  builtin_effect YXor = EffectPure ∧
  builtin_effect YNot = EffectPure ∧
  builtin_effect YShl = EffectPure ∧
  builtin_effect YShr = EffectPure ∧
  builtin_effect YSar = EffectPure ∧
  builtin_effect YKeccak256 = EffectMemory ∧
  builtin_effect YMLoad = EffectMemory ∧
  builtin_effect YMStore = EffectMemory ∧
  builtin_effect YMCopy = EffectMemory ∧
  builtin_effect YSLoad = EffectStorage ∧
  builtin_effect YSStore = EffectStorage ∧
  builtin_effect YCallDataLoad = EffectFrame ∧
  builtin_effect YCallDataSize = EffectFrame ∧
  builtin_effect YCallValue = EffectFrame ∧
  builtin_effect YMemoryGuard = EffectPure ∧
  builtin_effect YCaller = EffectFrame ∧
  builtin_effect YLoadImmutable = EffectFrame ∧
  builtin_effect YLog1 = EffectLog ∧
  builtin_effect YLog3 = EffectLog ∧
  builtin_effect YAddress = EffectFrame ∧
  builtin_effect YOrigin = EffectFrame ∧
  builtin_effect YChainId = EffectFrame ∧
  builtin_effect YNumber = EffectFrame ∧
  builtin_effect YTimestamp = EffectFrame ∧
  builtin_effect YCoinbase = EffectFrame ∧
  builtin_effect YLog0 = EffectLog ∧
  builtin_effect YLog2 = EffectLog ∧
  builtin_effect YLog4 = EffectLog ∧
  builtin_effect YGasPrice = EffectFrame ∧
  builtin_effect YBaseFee = EffectFrame ∧
  builtin_effect YGasLimit = EffectFrame ∧
  builtin_effect YStop = EffectHalt ∧
  builtin_effect YCall = EffectCall ∧
  builtin_effect YStaticCall = EffectCall ∧
  builtin_effect YExtCodeSize = EffectCall ∧
  builtin_effect YReturnDataSize = EffectFrame ∧
  builtin_effect YReturnDataCopy = EffectMemory ∧
  builtin_effect YGas = EffectFrame ∧
  builtin_effect YPop = EffectPure ∧
  builtin_effect YReturn = EffectHalt ∧
  builtin_effect YRevert = EffectHalt ∧
  builtin_effect YCodeSize = EffectObject ∧
  builtin_effect YCodeCopy = EffectObject ∧
  builtin_effect YDataSize = EffectObject ∧
  builtin_effect YDataOffset = EffectObject
End

Theorem builtin_of_name_name:
  ∀b. builtin_of_name (builtin_name b) = SOME b
Proof
  Cases_on ‘b’ >> EVAL_TAC
QED

(* The four object-level builtins read the running code or the object's
 * layout, which the evaluator does not model, and it rejects them.
 *)
Theorem builtin_effect_object:
  ∀b. builtin_effect b = EffectObject ⇔
      b = YCodeSize ∨ b = YCodeCopy ∨ b = YDataSize ∨ b = YDataOffset
Proof
  Cases_on ‘b’ >> EVAL_TAC
QED
