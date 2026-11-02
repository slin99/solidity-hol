(* Yul, as the pinned compiler's via-IR output emits it.
 *
 * The tree is deep: statements, expressions and literals are separate
 * datatypes, and a call to a dialect builtin carries the builtin rather than
 * its name, so the dialect's builtin set is fixed here once and the evaluator
 * never has to look a name up to know what an operation is. Calls to
 * user-defined functions keep their name; resolving a name to a function is
 * the environment's job (yul_env, below), not the tree's.
 *
 * Names are strings throughout, as in the Yul text: the compiler emits unique
 * names, so a string-keyed environment is exact for this profile, and a name
 * the environment does not bind is an error rather than a guess.
 *
 * Scope is not recorded in the tree. A block, an if branch, a loop body and a
 * call each introduce a scope, and the evaluator pushes one wherever the
 * grammar says so; a body below is therefore a statement list, not a nested
 * block node.
 *
 * The builtins are those the pinned solc emits over the fixtures in
 * testdata/ in either of its Yul stages (see testdata/yul/reconnaissance.json;
 * the unittest tests/test_yul_reconnaissance.py checks the dialect's names
 * against it), plus the ones contracts beyond the corpus need: the executing
 * account, a three-topic log, a memory-to-memory copy and an immutable value
 * the constructor patched in.  The four object-level ones (codesize,
 * codecopy, datasize, dataoffset) read the running code or the object's
 * layout, which the evaluator does not model; the compiler emits them in
 * creation objects, and inline assembly can use codesize and codecopy
 * anywhere. They are here so the set is complete and the evaluator can
 * reject them rather than misread them.
 *)
Theory yulAST
Ancestors
  vfmTypes

Datatype:
  yul_builtin
  = (* arithmetic *)
    YAdd | YSub | YMul | YDiv | YSDiv | YMod | YSMod | YExp | YSignExtend
    (* comparison and bitwise *)
  | YLt | YGt | YSLt | YSGt | YEq | YIsZero | YAnd | YOr | YXor | YNot
  | YShl | YShr | YSar
    (* hashing, memory, storage *)
  | YKeccak256 | YMLoad | YMStore | YMCopy | YSLoad | YSStore
    (* frame and call data *)
  | YCallDataLoad | YCallDataSize | YCallValue | YMemoryGuard | YCaller
  | YLoadImmutable | YAddress
    (* the transaction and block *)
  | YOrigin | YGasPrice | YChainId | YNumber | YTimestamp | YCoinbase | YBaseFee
  | YGasLimit
    (* message calls, other accounts and the frame's gas *)
  | YCall | YStaticCall | YExtCodeSize | YReturnDataSize | YReturnDataCopy
  | YGas
    (* events *)
  | YLog0 | YLog1 | YLog2 | YLog3 | YLog4
    (* discards a value *)
  | YPop
    (* halting *)
  | YStop | YReturn | YRevert
    (* object level: the creation object only *)
  | YCodeSize | YCodeCopy | YDataSize | YDataOffset
End

Datatype:
  yul_literal
  = LitNumber bytes32
  | LitBytes (byte list)
  | LitBool bool
End

Datatype:
  yul_expr
  = YulLit yul_literal
  | YulName string
  | YulBuiltin yul_builtin (yul_expr list)
  | YulApply string (yul_expr list)
End

Datatype:
  yul_stmt
  = YulBlock (yul_stmt list)
    (* name, parameters, results, body *)
  | YulFunction string (string list) (string list) (yul_stmt list)
  | YulLet (string list) (yul_expr option)
  | YulAssign (string list) yul_expr
  | YulIf yul_expr (yul_stmt list)
    (* scrutinee, cases, default (empty when the switch has none) *)
  | YulSwitch yul_expr ((yul_literal # yul_stmt list) list) (yul_stmt list)
    (* prelude, condition, post, body *)
  | YulFor (yul_stmt list) yul_expr (yul_stmt list) (yul_stmt list)
  | YulBreak
  | YulContinue
  | YulLeave
  | YulExprStmt yul_expr
End

(* A function as the evaluator uses it: YulFunction, unpacked. *)
Datatype:
  yul_function = <|
    function_params : string list;
    function_results : string list;
    function_body : yul_stmt list
  |>
End

(* The functions a block's own statements define, innermost definition last.
 * The pinned compiler puts every definition directly in the object's code
 * block, so this is the whole environment for a compiled program; a function
 * nested inside a block is deliberately not collected, and calling it fails
 * closed.
 *)
Definition yul_env_def:
  yul_env [] = (FEMPTY : string |-> yul_function) ∧
  yul_env (YulFunction name params results body :: ss) =
    (yul_env ss) |+ (name, <| function_params := params;
                              function_results := results;
                              function_body := body |>) ∧
  yul_env (_ :: ss) = yul_env ss
End

Theorem yul_env_function:
  yul_env [YulFunction name params results body] =
  (FEMPTY : string |-> yul_function) |+
    (name, <| function_params := params; function_results := results;
              function_body := body |>)
Proof
  simp[yul_env_def]
QED

(* Every expression has a size, so a size-only measure can use it as a
 * positive quantity. *)
Theorem yul_expr_size_pos:
  ∀e. 0 < yul_expr_size e
Proof
  Cases_on `e` >> simp[fetch "-" "yul_expr_size_def"]
QED
