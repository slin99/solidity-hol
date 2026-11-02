(* Smoke tests for the Yul evaluator, run by cv_eval: straight-line code and
 * memory, storage, a battery over the arithmetic, comparison, bitwise and
 * memory builtins, loops with a break and with a continue, a call whose
 * arguments must be evaluated right to left, a switch, sign extension, a
 * revert inside a callee, and the invalid outcomes.  The semantics test set
 * for the Solidity evaluator is solidityEvaluatorTest.
 *)
Theory yulEvaluatorTest
Ancestors
  yulEvaluator cv_string_fmap
Libs
  cv_transLib wordsLib

(* The transaction and block a test frame runs in: distinct values, so a
 * test can tell which one a builtin read.
 *)
Definition yul_test_tx_params_def:
  yul_test_tx_params =
    <| origin := 0xA1w; gasPrice := 9; baseFeePerGas := 3;
       baseFeePerBlobGas := 0; blockNumber := 7; blockTimeStamp := 1700;
       blockCoinBase := 0xC0w; blockGasLimit := 30000; prevRandao := 0w;
       prevHashes := []; blobHashes := []; chainId := 5; authRefund := 0 |>
End

Definition yul_test_machine_def:
  yul_test_machine =
    <| accounts := empty_accounts; logs := []; self_address := 0w;
       caller_address := 0w; call_value := 0w; call_data := [];
       immutables := (FEMPTY : string |-> bytes32); memory := FEMPTY;
       memory_size := 0; scopes := [];
       transaction_parameters := yul_test_tx_params |>
End

Definition run_def:
  run fuel code = run_yul fuel code yul_test_machine
End

val () = cv_auto_trans run_def;

(* The frame the builtins that read it run on: an account of its own, a caller
 * that is not that account, and one immutable the constructor patched in under
 * the name "3".
 *)
Definition yul_frame_machine_def:
  yul_frame_machine =
    <| accounts := empty_accounts; logs := []; self_address := 0x1234w;
       caller_address := 0x5678w; call_value := 0w; call_data := [];
       immutables := (FEMPTY : string |-> bytes32) |+ ("3", 42w);
       memory := FEMPTY; memory_size := 0; scopes := [];
       transaction_parameters := yul_test_tx_params |>
End

Definition run_frame_def:
  run_frame fuel code = run_yul fuel code yul_frame_machine
End

val () = cv_auto_trans run_frame_def;

(* mstore(0, add(2, 3)) return(0, 32) *)
Definition add_code_def:
  add_code =
    [YulExprStmt (YulBuiltin YMStore
       [YulLit (LitNumber 0w);
        YulBuiltin YAdd [YulLit (LitNumber 2w); YulLit (LitNumber 3w)]]);
     YulExprStmt (YulBuiltin YReturn
       [YulLit (LitNumber 0w); YulLit (LitNumber 32w)])]
End

val () = cv_auto_trans add_code_def;

(* mstore(1, 5) return(0, 0) -- the return covers no memory, so the size it
 * leaves is the one mstore's own touch raised: a word crossing the 32-byte
 * boundary at offset 1 needs two words.
 *)
Definition touch_code_def:
  touch_code =
    [YulExprStmt (YulBuiltin YMStore
       [YulLit (LitNumber 1w); YulLit (LitNumber 5w)]);
     YulExprStmt (YulBuiltin YReturn
       [YulLit (LitNumber 0w); YulLit (LitNumber 0w)])]
End

val () = cv_auto_trans touch_code_def;

(* switch 2 { case 1 { mstore(0, 11) } case 2 { mstore(0, 22) } }
 * mstore(64, 66)
 * switch 5 { case 1 { mstore(32, 44) } default { mstore(32, 55) } }
 * switch 7 { case 1 { mstore(64, 77) } }
 * return(0, 96)
 * The first switch takes its second case, the second falls through to its
 * default, and the third has an empty default that runs nothing: word 0 is
 * 22, word 32 is 55, and word 64 is still the 66 written before the switch.
 *)
Definition switch_code_def:
  switch_code =
    [YulSwitch (YulLit (LitNumber 2w))
       [(LitNumber 1w, [YulExprStmt (YulBuiltin YMStore
                         [YulLit (LitNumber 0w); YulLit (LitNumber 11w)])]);
        (LitNumber 2w, [YulExprStmt (YulBuiltin YMStore
                         [YulLit (LitNumber 0w); YulLit (LitNumber 22w)])])] [];
     YulExprStmt (YulBuiltin YMStore
       [YulLit (LitNumber 64w); YulLit (LitNumber 66w)]);
     YulSwitch (YulLit (LitNumber 5w))
       [(LitNumber 1w, [YulExprStmt (YulBuiltin YMStore
                         [YulLit (LitNumber 32w); YulLit (LitNumber 44w)])])]
       [YulExprStmt (YulBuiltin YMStore
          [YulLit (LitNumber 32w); YulLit (LitNumber 55w)])];
     YulSwitch (YulLit (LitNumber 7w))
       [(LitNumber 1w, [YulExprStmt (YulBuiltin YMStore
                         [YulLit (LitNumber 64w); YulLit (LitNumber 77w)])])] [];
     YulExprStmt (YulBuiltin YReturn
       [YulLit (LitNumber 0w); YulLit (LitNumber 96w)])]
End

val () = cv_auto_trans switch_code_def;

(* mstore(0, signextend(0, 0xff)) mstore(32, signextend(31, 0x80)) return(0, 64)
 * One byte in view, sign bit set, so the first word is all ones; 31 leaves the
 * whole word in view, so the second is unchanged.
 *)
Definition sign_extend_code_def:
  sign_extend_code =
    [YulExprStmt (YulBuiltin YMStore
       [YulLit (LitNumber 0w);
        YulBuiltin YSignExtend
          [YulLit (LitNumber 0w); YulLit (LitNumber 0xFFw)]]);
     YulExprStmt (YulBuiltin YMStore
       [YulLit (LitNumber 32w);
        YulBuiltin YSignExtend
          [YulLit (LitNumber 31w); YulLit (LitNumber 0x80w)]]);
     YulExprStmt (YulBuiltin YReturn
       [YulLit (LitNumber 0w); YulLit (LitNumber 64w)])]
End

val () = cv_auto_trans sign_extend_code_def;

(* sstore(7, 42) mstore(0, sload(7)) return(0, 32) *)
Definition store_code_def:
  store_code =
    [YulExprStmt (YulBuiltin YSStore
       [YulLit (LitNumber 7w); YulLit (LitNumber 42w)]);
     YulExprStmt (YulBuiltin YMStore
       [YulLit (LitNumber 0w); YulBuiltin YSLoad [YulLit (LitNumber 7w)]]);
     YulExprStmt (YulBuiltin YReturn
       [YulLit (LitNumber 0w); YulLit (LitNumber 32w)])]
End

val () = cv_auto_trans store_code_def;

(* let acc := 0
 * for { let i := 0 } lt(i, 3) { i := add(i, 1)  j := add(j, 1) } {
 *   acc := add(acc, i)
 *   if eq(i, 2) { break } }
 * mstore(0, acc) mstore(32, j) return(0, 64)
 * The loop leaves when i reaches 2, so acc is 0 + 1 + 2.  j counts how often
 * the post statement ran: twice, because the break skipped it the last time
 * round and a break that ran it anyway would leave j at 3.
 *)
Definition loop_code_def:
  loop_code =
    [YulLet ["acc"] (SOME (YulLit (LitNumber 0w)));
     YulLet ["j"] (SOME (YulLit (LitNumber 0w)));
     YulFor
       [YulLet ["i"] (SOME (YulLit (LitNumber 0w)))]
       (YulBuiltin YLt [YulName "i"; YulLit (LitNumber 3w)])
       [YulAssign ["i"] (YulBuiltin YAdd [YulName "i"; YulLit (LitNumber 1w)]);
        YulAssign ["j"] (YulBuiltin YAdd [YulName "j"; YulLit (LitNumber 1w)])]
       [YulAssign ["acc"] (YulBuiltin YAdd [YulName "acc"; YulName "i"]);
        YulIf (YulBuiltin YEq [YulName "i"; YulLit (LitNumber 2w)]) [YulBreak]];
     YulExprStmt (YulBuiltin YMStore [YulLit (LitNumber 0w); YulName "acc"]);
     YulExprStmt (YulBuiltin YMStore [YulLit (LitNumber 32w); YulName "j"]);
     YulExprStmt (YulBuiltin YReturn
       [YulLit (LitNumber 0w); YulLit (LitNumber 64w)])]
End

val () = cv_auto_trans loop_code_def;

(* function f(a, b) -> c { c := add(a, b) }
 * function g(a) -> b { b := a  sstore(0, a) }
 * let r := f(g(1), g(2))
 * mstore(0, r) mstore(32, sload(0)) return(0, 64)
 * Arguments are evaluated right to left, so g(2) stores before g(1) does and
 * slot 0 ends up holding 1; the sum in the returned word proves both ran.
 *)
Definition call_code_def:
  call_code =
    [YulFunction "f" ["a"; "b"] ["c"]
       [YulAssign ["c"] (YulBuiltin YAdd [YulName "a"; YulName "b"])];
     YulFunction "g" ["a"] ["b"]
       [YulAssign ["b"] (YulName "a");
        YulExprStmt (YulBuiltin YSStore [YulLit (LitNumber 0w); YulName "a"])];
     YulLet ["r"] (SOME (YulApply "f"
       [YulApply "g" [YulLit (LitNumber 1w)];
        YulApply "g" [YulLit (LitNumber 2w)]]));
     YulExprStmt (YulBuiltin YMStore [YulLit (LitNumber 0w); YulName "r"]);
     YulExprStmt (YulBuiltin YMStore
       [YulLit (LitNumber 32w); YulBuiltin YSLoad [YulLit (LitNumber 0w)]]);
     YulExprStmt (YulBuiltin YReturn
       [YulLit (LitNumber 0w); YulLit (LitNumber 64w)])]
End

val () = cv_auto_trans call_code_def;

(* for {} 1 {} {} -- never leaves the loop. *)
Definition spin_code_def:
  spin_code =
    [YulFor [] (YulLit (LitNumber 1w)) [] []]
End

val () = cv_auto_trans spin_code_def;

Definition revert_code_def:
  revert_code =
    [YulExprStmt (YulBuiltin YRevert
       [YulLit (LitNumber 0w); YulLit (LitNumber 0w)])]
End

val () = cv_auto_trans revert_code_def;

Definition leave_code_def:
  leave_code =
    [YulIf (YulLit (LitNumber 1w)) [YulLeave];
     YulExprStmt (YulBuiltin YRevert
       [YulLit (LitNumber 0w); YulLit (LitNumber 0w)])]
End

val () = cv_auto_trans leave_code_def;

Definition unbound_code_def:
  unbound_code = [YulLet ["x"] (SOME (YulName "y"))]
End

val () = cv_auto_trans unbound_code_def;

(* One store per builtin, in the order the words are returned:
 *   sub(7, 3)          operand order
 *   div(1, 0)          a division by zero is zero
 *   sdiv(not(0), 0)    and so is a signed one, of minus one
 *   mod(5, 0)
 *   sar(255, not(0))   an arithmetic shift of a negative keeps the sign
 *   exp(2, 10)
 *   slt(not(0), 1)     a signed comparison: minus one is below one
 *   mload(0)           reads back what the first store wrote
 *   xor(12, 10)
 *   keccak256(0, 32)   the known hash of 32 zero bytes: stored last, in the
 *                      word after those, so that its own store cannot clobber
 *                      what it hashed
 *)
Definition builtins_code_def:
  builtins_code =
    [YulExprStmt (YulBuiltin YMStore
       [YulLit (LitNumber 288w); YulBuiltin YKeccak256
          [YulLit (LitNumber 0w); YulLit (LitNumber 32w)]]);
     YulExprStmt (YulBuiltin YMStore
       [YulLit (LitNumber 0w);
        YulBuiltin YSub [YulLit (LitNumber 7w); YulLit (LitNumber 3w)]]);
     YulExprStmt (YulBuiltin YMStore
       [YulLit (LitNumber 32w);
        YulBuiltin YDiv [YulLit (LitNumber 1w); YulLit (LitNumber 0w)]]);
     YulExprStmt (YulBuiltin YMStore
       [YulLit (LitNumber 64w);
        YulBuiltin YSDiv
          [YulBuiltin YNot [YulLit (LitNumber 0w)]; YulLit (LitNumber 0w)]]);
     YulExprStmt (YulBuiltin YMStore
       [YulLit (LitNumber 96w);
        YulBuiltin YMod [YulLit (LitNumber 5w); YulLit (LitNumber 0w)]]);
     YulExprStmt (YulBuiltin YMStore
       [YulLit (LitNumber 128w);
        YulBuiltin YSar
          [YulLit (LitNumber 255w); YulBuiltin YNot [YulLit (LitNumber 0w)]]]);
     YulExprStmt (YulBuiltin YMStore
       [YulLit (LitNumber 160w);
        YulBuiltin YExp [YulLit (LitNumber 2w); YulLit (LitNumber 10w)]]);
     YulExprStmt (YulBuiltin YMStore
       [YulLit (LitNumber 192w);
        YulBuiltin YSLt
          [YulBuiltin YNot [YulLit (LitNumber 0w)]; YulLit (LitNumber 1w)]]);
     YulExprStmt (YulBuiltin YMStore
       [YulLit (LitNumber 224w); YulBuiltin YMLoad [YulLit (LitNumber 0w)]]);
     YulExprStmt (YulBuiltin YMStore
       [YulLit (LitNumber 256w);
        YulBuiltin YXor [YulLit (LitNumber 12w); YulLit (LitNumber 10w)]]);
     YulExprStmt (YulBuiltin YReturn
       [YulLit (LitNumber 0w); YulLit (LitNumber 320w)])]
End

val () = cv_auto_trans builtins_code_def;

(* function g() { revert(0, 0) }
 * function f() { g()  sstore(0, 7) }
 * f() sstore(1, 9)
 * A revert inside a callee ends the whole frame, not just the callee: neither
 * store runs, and nothing the frame did is committed.
 *)
Definition revert_in_call_code_def:
  revert_in_call_code =
    [YulFunction "g" [] []
       [YulExprStmt (YulBuiltin YRevert
          [YulLit (LitNumber 0w); YulLit (LitNumber 0w)])];
     YulFunction "f" [] []
       [YulExprStmt (YulApply "g" []);
        YulExprStmt (YulBuiltin YSStore [YulLit (LitNumber 0w); YulLit (LitNumber 7w)])];
     YulExprStmt (YulApply "f" []);
     YulExprStmt (YulBuiltin YSStore [YulLit (LitNumber 1w); YulLit (LitNumber 9w)])]
End

val () = cv_auto_trans revert_in_call_code_def;

(* let acc := 0
 * for { let i := 0 } lt(i, 3) { i := add(i, 1) } {
 *   if eq(i, 1) { continue }
 *   acc := add(acc, i) }
 * mstore(0, acc) return(0, 32)
 * The iteration with i = 1 skips the accumulation but still runs the post, so
 * acc is 0 + 2; a continue that ran the rest of the body anyway would make it
 * 0 + 1 + 2.
 *)
Definition continue_code_def:
  continue_code =
    [YulLet ["acc"] (SOME (YulLit (LitNumber 0w)));
     YulFor
       [YulLet ["i"] (SOME (YulLit (LitNumber 0w)))]
       (YulBuiltin YLt [YulName "i"; YulLit (LitNumber 3w)])
       [YulAssign ["i"] (YulBuiltin YAdd [YulName "i"; YulLit (LitNumber 1w)])]
       [YulIf (YulBuiltin YEq [YulName "i"; YulLit (LitNumber 1w)]) [YulContinue];
        YulAssign ["acc"] (YulBuiltin YAdd [YulName "acc"; YulName "i"])];
     YulExprStmt (YulBuiltin YMStore [YulLit (LitNumber 0w); YulName "acc"]);
     YulExprStmt (YulBuiltin YReturn
       [YulLit (LitNumber 0w); YulLit (LitNumber 32w)])]
End

val () = cv_auto_trans continue_code_def;

(* let x, y := 1 *)
Definition bad_binding_code_def:
  bad_binding_code =
    [YulLet ["x"; "y"] (SOME (YulLit (LitNumber 1w)))]
End

val () = cv_auto_trans bad_binding_code_def;

Definition unknown_function_code_def:
  unknown_function_code = [YulExprStmt (YulApply "nope" [])]
End

val () = cv_auto_trans unknown_function_code_def;

Definition bad_builtin_arity_code_def:
  bad_builtin_arity_code =
    [YulExprStmt (YulBuiltin YAdd [YulLit (LitNumber 1w)])]
End

val () = cv_auto_trans bad_builtin_arity_code_def;

(* let x := 1  { let x := 2  mstore(0, x) }  mstore(32, x) return(0, 64)
 * A block runs in a scope of its own: the inner binding shadows the outer name
 * and is gone when the block ends, so the two stores hold 2 and then 1.
 *)
Definition block_code_def:
  block_code =
    [YulLet ["x"] (SOME (YulLit (LitNumber 1w)));
     YulBlock [YulLet ["x"] (SOME (YulLit (LitNumber 2w)));
               YulExprStmt (YulBuiltin YMStore [YulLit (LitNumber 0w); YulName "x"])];
     YulExprStmt (YulBuiltin YMStore [YulLit (LitNumber 32w); YulName "x"]);
     YulExprStmt (YulBuiltin YReturn
       [YulLit (LitNumber 0w); YulLit (LitNumber 64w)])]
End

val () = cv_auto_trans block_code_def;

(* mstore(0, "ab") return(0, 32)
 * A string literal is a value: its bytes left-aligned, the rest zero.
 *)
Definition string_literal_code_def:
  string_literal_code =
    [YulExprStmt (YulBuiltin YMStore
       [YulLit (LitNumber 0w); YulLit (LitBytes [0x61w; 0x62w])]);
     YulExprStmt (YulBuiltin YReturn
       [YulLit (LitNumber 0w); YulLit (LitNumber 32w)])]
End

val () = cv_auto_trans string_literal_code_def;

(* mstore(0, caller()) mstore(32, loadimmutable("3")) return(0, 64)
 * Both frame inputs come from the frame's caller: the sender that called the
 * account in, and the value the constructor patched in under the name "3".
 *)
Definition frame_code_def:
  frame_code =
    [YulExprStmt (YulBuiltin YMStore
       [YulLit (LitNumber 0w); YulBuiltin YCaller []]);
     YulExprStmt (YulBuiltin YMStore
       [YulLit (LitNumber 32w);
        YulBuiltin YLoadImmutable [YulLit (LitBytes [0x33w])]]);
     YulExprStmt (YulBuiltin YReturn
       [YulLit (LitNumber 0w); YulLit (LitNumber 64w)])]
End

val () = cv_auto_trans frame_code_def;

(* An immutable the frame's table does not carry is an error, not a zero. *)
Definition unknown_immutable_code_def:
  unknown_immutable_code =
    [YulExprStmt (YulBuiltin YLoadImmutable [YulLit (LitBytes [0x39w])])]
End

val () = cv_auto_trans unknown_immutable_code_def;

(* loadimmutable(3): a number is not a name, so the call is not the form the
 * dispatcher reads the immutables table for, and the value-based dispatch,
 * which has no case for it, makes it an error rather than a zero.
 *)
Definition immutable_number_code_def:
  immutable_number_code =
    [YulExprStmt (YulBuiltin YLoadImmutable [YulLit (LitNumber 3w)])]
End

val () = cv_auto_trans immutable_number_code_def;

(* mstore(0, "ab") log3(0, 2, 11, 22, 33)
 * The log's payload is the memory range the call names -- the two bytes just
 * written -- and its three topics are the three the call supplies.
 *)
Definition log3_code_def:
  log3_code =
    [YulExprStmt (YulBuiltin YMStore
       [YulLit (LitNumber 0w); YulLit (LitBytes [0x61w; 0x62w])]);
     YulExprStmt (YulBuiltin YLog3
       [YulLit (LitNumber 0w); YulLit (LitNumber 2w); YulLit (LitNumber 11w);
        YulLit (LitNumber 22w); YulLit (LitNumber 33w)])]
End

val () = cv_auto_trans log3_code_def;

(* mstore(0, address()) mstore(32, origin()) ... return(0, 288)
 * The executing account from the frame, the rest from its transaction and
 * block.
 *)
Definition environment_code_def:
  environment_code =
    MAP (λ(i, b). YulExprStmt (YulBuiltin YMStore
                     [YulLit (LitNumber (n2w (32 * i))); YulBuiltin b []]))
      [(0, YAddress); (1, YOrigin); (2, YChainId); (3, YNumber);
       (4, YTimestamp); (5, YCoinbase); (6, YGasPrice); (7, YBaseFee);
       (8, YGasLimit)] ++
    [YulExprStmt (YulBuiltin YReturn
       [YulLit (LitNumber 0w); YulLit (LitNumber 288w)])]
End

val () = cv_auto_trans environment_code_def;

(* mstore(0, "ab") log0(0, 2) log2(0, 1, 11, 22) log4(1, 1, 1, 2, 3, 4) *)
Definition log0_log2_code_def:
  log0_log2_code =
    [YulExprStmt (YulBuiltin YMStore
       [YulLit (LitNumber 0w); YulLit (LitBytes [0x61w; 0x62w])]);
     YulExprStmt (YulBuiltin YLog0
       [YulLit (LitNumber 0w); YulLit (LitNumber 2w)]);
     YulExprStmt (YulBuiltin YLog2
       [YulLit (LitNumber 0w); YulLit (LitNumber 1w); YulLit (LitNumber 11w);
        YulLit (LitNumber 22w)]);
     YulExprStmt (YulBuiltin YLog4
       [YulLit (LitNumber 1w); YulLit (LitNumber 1w); YulLit (LitNumber 1w);
        YulLit (LitNumber 2w); YulLit (LitNumber 3w); YulLit (LitNumber 4w)])]
End

val () = cv_auto_trans log0_log2_code_def;

(* stop() revert(0, 0): stop halts with no data, so the revert never runs *)
Definition stop_code_def:
  stop_code =
    [YulExprStmt (YulBuiltin YStop []);
     YulExprStmt (YulBuiltin YRevert
       [YulLit (LitNumber 0w); YulLit (LitNumber 0w)])]
End

val () = cv_auto_trans stop_code_def;

(* mstore(0, 0x1122334455667788) mcopy(32, 0, 32) return(32, 32)
 * The word read back is the one that was written, through the copy.
 *)
Definition mcopy_code_def:
  mcopy_code =
    [YulExprStmt (YulBuiltin YMStore
       [YulLit (LitNumber 0w); YulLit (LitNumber 0x1122334455667788w)]);
     YulExprStmt (YulBuiltin YMCopy
       [YulLit (LitNumber 32w); YulLit (LitNumber 0w); YulLit (LitNumber 32w)]);
     YulExprStmt (YulBuiltin YReturn
       [YulLit (LitNumber 32w); YulLit (LitNumber 32w)])]
End

val () = cv_auto_trans mcopy_code_def;

(* mstore(0, "abcd") mcopy(2, 0, 4) return(0, 6)
 * Source and destination overlap, and the four bytes read are the four that
 * were there before the copy began: a copy that wrote as it read would leave
 * 0x6162 6162 6162 instead.
 *)
Definition mcopy_overlap_code_def:
  mcopy_overlap_code =
    [YulExprStmt (YulBuiltin YMStore
       [YulLit (LitNumber 0w); YulLit (LitBytes [0x61w; 0x62w; 0x63w; 0x64w])]);
     YulExprStmt (YulBuiltin YMCopy
       [YulLit (LitNumber 2w); YulLit (LitNumber 0w); YulLit (LitNumber 4w)]);
     YulExprStmt (YulBuiltin YReturn
       [YulLit (LitNumber 0w); YulLit (LitNumber 6w)])]
End

val () = cv_auto_trans mcopy_overlap_code_def;

(* pop(1) mstore(0, 7) return(0, 32) *)
Definition pop_code_def:
  pop_code =
    [YulExprStmt (YulBuiltin YPop [YulLit (LitNumber 1w)]);
     YulExprStmt (YulBuiltin YMStore
       [YulLit (LitNumber 0w); YulLit (LitNumber 7w)]);
     YulExprStmt (YulBuiltin YReturn
       [YulLit (LitNumber 0w); YulLit (LitNumber 32w)])]
End

val () = cv_auto_trans pop_code_def;

(* let x := pop(1): pop yields nothing, so there is nothing to bind. *)
Definition pop_binding_code_def:
  pop_binding_code =
    [YulLet ["x"] (SOME (YulBuiltin YPop [YulLit (LitNumber 1w)]))]
End

val () = cv_auto_trans pop_binding_code_def;

(* let n := 0
 * for { let o := 0 } lt(o, 2) { o := add(o, 1) } {
 *   for { } lt(n, 9) { s } { n := add(n, 1) } }
 * mstore(0, n) return(0, 32)
 * s is break or continue, which Yul allows only in a loop's body.  Escaping
 * the inner loop's post, a break would end the outer loop with n = 1, and a
 * continue would run the outer post and return n = 2.
 *)
Definition post_escape_code_def:
  post_escape_code s =
    [YulLet ["n"] (SOME (YulLit (LitNumber 0w)));
     YulFor
       [YulLet ["o"] (SOME (YulLit (LitNumber 0w)))]
       (YulBuiltin YLt [YulName "o"; YulLit (LitNumber 2w)])
       [YulAssign ["o"] (YulBuiltin YAdd [YulName "o"; YulLit (LitNumber 1w)])]
       [YulFor []
          (YulBuiltin YLt [YulName "n"; YulLit (LitNumber 9w)])
          [s]
          [YulAssign ["n"] (YulBuiltin YAdd [YulName "n"; YulLit (LitNumber 1w)])]];
     YulExprStmt (YulBuiltin YMStore [YulLit (LitNumber 0w); YulName "n"]);
     YulExprStmt (YulBuiltin YReturn
       [YulLit (LitNumber 0w); YulLit (LitNumber 32w)])]
End

val () = cv_auto_trans post_escape_code_def;

(* function two() -> a, b { a := 1  b := 2 }
 * function none() { }
 * function f(x, y) -> s { s := add(x, y) }
 * mstore(0, f(args)) return(0, 32)
 * Each argument is one value.  Flattened, f(two()) and f(none(), 1, 2) both
 * hand f two values and return 3.
 *)
Definition argument_values_code_def:
  argument_values_code args =
    [YulFunction "two" [] ["a"; "b"]
       [YulAssign ["a"] (YulLit (LitNumber 1w));
        YulAssign ["b"] (YulLit (LitNumber 2w))];
     YulFunction "none" [] [] [];
     YulFunction "f" ["x"; "y"] ["s"]
       [YulAssign ["s"] (YulBuiltin YAdd [YulName "x"; YulName "y"])];
     YulExprStmt (YulBuiltin YMStore
       [YulLit (LitNumber 0w); YulApply "f" args]);
     YulExprStmt (YulBuiltin YReturn
       [YulLit (LitNumber 0w); YulLit (LitNumber 32w)])]
End

val () = cv_auto_trans argument_values_code_def;

Theorem add_returns_five:
  (run 20 add_code).completion = YulReturn (word_to_bytes_be (5w : bytes32))
Proof
  CONV_TAC cv_eval
QED

(* mstore's touch is what raises the size: nothing else in this program
 * touches memory.
 *)
Theorem mstore_raises_memory_size:
  (run 20 touch_code).machine.memory_size = 64
Proof
  CONV_TAC cv_eval
QED

Theorem switch_takes_the_matching_case_and_otherwise_the_default:
  (run 20 switch_code).completion =
  YulReturn (word_to_bytes_be (22w : bytes32) ++
             word_to_bytes_be (55w : bytes32) ++
             word_to_bytes_be (66w : bytes32))
Proof
  CONV_TAC cv_eval
QED

Theorem sign_extend_extends_the_sign:
  (run 20 sign_extend_code).completion =
  YulReturn (word_to_bytes_be (word_1comp (0w : bytes32)) ++
             word_to_bytes_be (0x80w : bytes32))
Proof
  CONV_TAC cv_eval
QED

Theorem storage_round_trips:
  (run 20 store_code).completion = YulReturn (word_to_bytes_be (42w : bytes32))
Proof
  CONV_TAC cv_eval
QED

Theorem builtins_agree_with_the_evm:
  (run 40 builtins_code).completion =
  YulReturn (word_to_bytes_be (4w : bytes32) ++
             word_to_bytes_be (0w : bytes32) ++
             word_to_bytes_be (0w : bytes32) ++
             word_to_bytes_be (0w : bytes32) ++
             word_to_bytes_be (word_1comp (0w : bytes32)) ++
             word_to_bytes_be (1024w : bytes32) ++
             word_to_bytes_be (1w : bytes32) ++
             word_to_bytes_be (4w : bytes32) ++
             word_to_bytes_be (6w : bytes32) ++
             word_to_bytes_be
               (0x290decd9548b62a8d60345a988386fc84ba6bc95484008f6362f93160ef3e563w : bytes32))
Proof
  CONV_TAC cv_eval
QED

Theorem loop_breaks_out:
  (run 20 loop_code).completion =
  YulReturn (word_to_bytes_be (3w : bytes32) ++ word_to_bytes_be (2w : bytes32))
Proof
  CONV_TAC cv_eval
QED

Theorem continue_runs_the_post_and_skips_the_rest:
  (run 20 continue_code).completion = YulReturn (word_to_bytes_be (2w : bytes32))
Proof
  CONV_TAC cv_eval
QED

Theorem revert_in_a_callee_ends_the_frame:
  (run 20 revert_in_call_code).completion = YulRevert [] ∧
  (run 20 revert_in_call_code).machine.accounts = yul_test_machine.accounts
Proof
  CONV_TAC cv_eval
QED

Theorem malformed_programs_are_invalid:
  (run 20 bad_binding_code).completion = YulInvalid "bad binding" ∧
  (run 20 unknown_function_code).completion = YulInvalid "unknown function" ∧
  (run 20 bad_builtin_arity_code).completion = YulInvalid "bad builtin call"
Proof
  CONV_TAC cv_eval
QED

Theorem a_block_shadows_and_is_popped:
  (run 20 block_code).completion =
  YulReturn (word_to_bytes_be (2w : bytes32) ++ word_to_bytes_be (1w : bytes32))
Proof
  CONV_TAC cv_eval
QED

(* The value of "ab" is 0x6162 shifted up to the top of the word, so that the
 * store puts 'a', 'b' and then zeros -- what the compiler's revert messages
 * rely on.
 *)
Theorem a_string_literal_is_left_aligned_bytes:
  (run 20 string_literal_code).completion =
  YulReturn (word_to_bytes_be (word_lsl (0x6162w : bytes32) 240))
Proof
  CONV_TAC cv_eval
QED

Theorem call_arguments_are_evaluated_right_to_left:
  (run 20 call_code).completion =
  YulReturn (word_to_bytes_be (3w : bytes32) ++ word_to_bytes_be (1w : bytes32))
Proof
  CONV_TAC cv_eval
QED

Theorem spin_exhausts_fuel:
  (run 5 spin_code).completion = YulOutOfFuel
Proof
  CONV_TAC cv_eval
QED

(* More fuel, same syntax: a longer run reaches a real answer, and the answer
 * is what the shorter one would have given had it had the fuel. *)
Theorem fuel_only_bounds_steps:
  (run 20 call_code).completion ≠ YulOutOfFuel ∧
  (run 200 call_code).completion = (run 20 call_code).completion
Proof
  CONV_TAC cv_eval
QED

Theorem revert_returns_no_data:
  (run 20 revert_code).completion = YulRevert []
Proof
  CONV_TAC cv_eval
QED

(* leave ends the frame's code, so the revert after it never runs. *)
Theorem leave_leaves_the_code:
  (run 20 leave_code).completion = YulLeave
Proof
  CONV_TAC cv_eval
QED

Theorem unbound_name_is_invalid:
  (run 20 unbound_code).completion = YulInvalid "unbound name"
Proof
  CONV_TAC cv_eval
QED

Theorem caller_and_immutable_come_from_the_frame:
  (run_frame 20 frame_code).completion =
  YulReturn (word_to_bytes_be (0x5678w : bytes32) ++
             word_to_bytes_be (42w : bytes32))
Proof
  CONV_TAC cv_eval
QED

Theorem an_immutable_the_frame_does_not_carry_is_invalid:
  (run_frame 20 unknown_immutable_code).completion =
  YulInvalid "unknown immutable"
Proof
  CONV_TAC cv_eval
QED

Theorem log3_appends_a_log_with_three_topics:
  (run 20 log3_code).completion = YulNormal ∧
  (run 20 log3_code).machine.logs =
    [<| logger := 0w; topics := [11w; 22w; 33w]; data := [0x61w; 0x62w] |>]
Proof
  CONV_TAC cv_eval
QED

Theorem a_loadimmutable_without_a_name_is_invalid:
  (run_frame 20 immutable_number_code).completion =
  YulInvalid "bad builtin call"
Proof
  CONV_TAC cv_eval
QED

Theorem mcopy_copies_memory:
  (run 20 mcopy_code).completion =
  YulReturn (word_to_bytes_be (0x1122334455667788w : bytes32))
Proof
  CONV_TAC cv_eval
QED

Theorem mcopy_reads_before_it_writes:
  (run 20 mcopy_overlap_code).completion =
  YulReturn [0x61w; 0x62w; 0x61w; 0x62w; 0x63w; 0x64w]
Proof
  CONV_TAC cv_eval
QED

Theorem pop_discards_its_argument_and_yields_none:
  (run 20 pop_code).completion = YulReturn (word_to_bytes_be (7w : bytes32)) ∧
  (run 20 pop_binding_code).completion = YulInvalid "bad binding"
Proof
  CONV_TAC cv_eval
QED

Theorem a_break_or_continue_in_a_loop_post_is_invalid:
  (run 20 (post_escape_code YulBreak)).completion =
    YulInvalid "break or continue in loop post" ∧
  (run 20 (post_escape_code YulContinue)).completion =
    YulInvalid "break or continue in loop post"
Proof
  CONV_TAC cv_eval
QED

Theorem environment_builtins_read_the_frame_transaction_and_block:
  (run_frame 20 environment_code).completion =
  YulReturn (word_to_bytes_be (0x1234w : bytes32) ++
             word_to_bytes_be (0xA1w : bytes32) ++
             word_to_bytes_be (5w : bytes32) ++
             word_to_bytes_be (7w : bytes32) ++
             word_to_bytes_be (1700w : bytes32) ++
             word_to_bytes_be (0xC0w : bytes32) ++
             word_to_bytes_be (9w : bytes32) ++
             word_to_bytes_be (3w : bytes32) ++
             word_to_bytes_be (30000w : bytes32))
Proof
  CONV_TAC cv_eval
QED

Theorem an_argument_that_is_not_one_value_is_invalid:
  (run 20 (argument_values_code [YulApply "two" []])).completion =
    YulInvalid "argument is not one value" ∧
  (run 20 (argument_values_code
             [YulApply "none" []; YulLit (LitNumber 1w);
              YulLit (LitNumber 2w)])).completion =
    YulInvalid "argument is not one value"
Proof
  CONV_TAC cv_eval
QED

Theorem log0_log2_and_log4_append_logs:
  (run 20 log0_log2_code).completion = YulNormal ∧
  (run 20 log0_log2_code).machine.logs =
    [<| logger := 0w; topics := []; data := [0x61w; 0x62w] |>;
     <| logger := 0w; topics := [11w; 22w]; data := [0x61w] |>;
     <| logger := 0w; topics := [1w; 2w; 3w; 4w]; data := [0x62w] |>]
Proof
  CONV_TAC cv_eval
QED

Theorem stop_halts_with_no_data:
  (run 20 stop_code).completion = YulReturn []
Proof
  CONV_TAC cv_eval
QED
