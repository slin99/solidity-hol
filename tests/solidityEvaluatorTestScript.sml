(* Smoke tests for the pure evaluator, run by cv_eval. The semantics test set
 * is solidityCoreProgramsTest.
 *)
Theory solidityEvaluatorTest
Ancestors
  solidityEvaluator
Libs
  cv_transLib wordsLib intLib

Overload u8 = “UintT 8”
Overload u256 = “UintT 256”
Overload k = “λi. ConstantAtom (IntegerValue i)”

Definition initial_state_def:
  initial_state = <|
    world := <| accounts := empty_accounts;
                transient := empty_transient_storage;
                logs := [] |>;
    frame := <| self_address := 0w; code_address := 0w; sender_address := 0w;
                call_value := 0; call_data := []; static_context := F;
                tx_params := <| origin := 0w; gasPrice := 0; baseFeePerGas := 0;
                  baseFeePerBlobGas := 0; blockNumber := 0; blockTimeStamp := 0;
                  blockCoinBase := 0w; blockGasLimit := 0; prevRandao := 0w;
                  prevHashes := []; blobHashes := []; chainId := 0;
                  authRefund := 0 |> |>;
    scopes := [];
    heap := FEMPTY;
    next_heap_id := 0;
    targets := FEMPTY
  |>
End

(* add(x, y) returns (r): checked uint8 addition. *)
Definition add_proc_def:
  add_proc = <|
    procedure_id := AstId 1;
    parameters := [(AstId 10, u8); (AstId 11, u8)];
    return_bindings := [(AstId 12, u8)];
    body := [
      DefineStmt (AstId 13) (SingleType u8)
        (ScalarOperation u8 CheckedArithmetic AddOp
           [BoundAtom (AstId 10); BoundAtom (AstId 11)]);
      ReturnStmt [BoundAtom (AstId 13)]]
  |>
End

(* sum(n) returns (acc): adds 1..n, breaking after 5; the loop body writes the
 * enclosing i and acc, and the condition prelude reruns every iteration.
 *)
Definition sum_proc_def:
  sum_proc = <|
    procedure_id := AstId 2;
    parameters := [(AstId 20, u256)];
    return_bindings := [(AstId 21, u256)];
    body := [
      DefineStmt (AstId 22) (SingleType u256) (ConvertOperation u256 (k 0));
      WhileStmt
        [DefineStmt (AstId 23) (SingleType BoolT)
           (ScalarOperation u256 UncheckedArithmetic LessThanOp
              [BoundAtom (AstId 22); BoundAtom (AstId 20)])]
        (BoundAtom (AstId 23))
        [DefineStmt (AstId 24) (SingleType u256)
           (ScalarOperation u256 CheckedArithmetic AddOp
              [BoundAtom (AstId 22); k 1]);
         CaptureBindingStmt (AstId 25) (AstId 22);
         WriteScalarStmt (AstId 25) u256 (BoundAtom (AstId 24));
         DefineStmt (AstId 26) (SingleType u256)
           (ScalarOperation u256 CheckedArithmetic AddOp
              [BoundAtom (AstId 21); BoundAtom (AstId 24)]);
         CaptureBindingStmt (AstId 27) (AstId 21);
         WriteScalarStmt (AstId 27) u256 (BoundAtom (AstId 26));
         DefineStmt (AstId 28) (SingleType BoolT)
           (ScalarOperation u256 UncheckedArithmetic EqualOp
              [BoundAtom (AstId 24); k 5]);
         IfStmt (BoundAtom (AstId 28)) [BreakStmt] [ContinueStmt]]]
  |>
End

(* fact(n): recursion, falling through to the return binding on n = 0. *)
Definition fact_proc_def:
  fact_proc = <|
    procedure_id := AstId 3;
    parameters := [(AstId 30, u256)];
    return_bindings := [(AstId 31, u256)];
    body := [
      DefineStmt (AstId 32) (SingleType BoolT)
        (ScalarOperation u256 UncheckedArithmetic EqualOp
           [BoundAtom (AstId 30); k 0]);
      IfStmt (BoundAtom (AstId 32))
        [ReturnStmt [k 1]]
        [DefineStmt (AstId 33) (SingleType u256)
           (ScalarOperation u256 CheckedArithmetic SubtractOp
              [BoundAtom (AstId 30); k 1]);
         DefineStmt (AstId 34) (SingleType u256)
           (InternalCallOperation (AstId 3) [BoundAtom (AstId 33)]);
         DefineStmt (AstId 35) (SingleType u256)
           (ScalarOperation u256 CheckedArithmetic MultiplyOp
              [BoundAtom (AstId 30); BoundAtom (AstId 34)]);
         ReturnStmt [BoundAtom (AstId 35)]]]
  |>
End

(* pair() returns (uint256, bool); first() destructures it. *)
Definition pair_proc_def:
  pair_proc = <|
    procedure_id := AstId 4;
    parameters := [];
    return_bindings := [(AstId 40, u256); (AstId 41, BoolT)];
    body := [ReturnStmt [k 7; ConstantAtom (BoolValue T)]]
  |>
End

Definition first_proc_def:
  first_proc = <|
    procedure_id := AstId 5;
    parameters := [];
    return_bindings := [(AstId 50, u256)];
    body := [
      DefineStmt (AstId 51) (ProductType [SingleType u256; SingleType BoolT])
        (InternalCallOperation (AstId 4) []);
      DefineStmt (AstId 52) (SingleType u256)
        (TupleComponentOperation 0 (BoundAtom (AstId 51)));
      ReturnStmt [BoundAtom (AstId 52)]]
  |>
End

Definition spin_proc_def:
  spin_proc = <|
    procedure_id := AstId 6;
    parameters := [];
    return_bindings := [];
    body := [WhileStmt [] (ConstantAtom (BoolValue T)) []]
  |>
End

(* A revert from a nested call carries its bytes out. *)
Definition fail_proc_def:
  fail_proc = <|
    procedure_id := AstId 7;
    parameters := [];
    return_bindings := [];
    body := [RevertStmt (ConstantAtom (BytesValue [0x01w; 0x02w]))]
  |>
End

Definition call_fail_proc_def:
  call_fail_proc = <|
    procedure_id := AstId 8;
    parameters := [];
    return_bindings := [(AstId 80, u256)];
    body := [
      DefineStmt (AstId 81) (ProductType []) (InternalCallOperation (AstId 7) []);
      ReturnStmt [k 1]]
  |>
End

(* The caller captures target 90 before a call whose callee reuses id 90;
 * the caller's target map must survive the call.
 *)
Definition callee_proc_def:
  callee_proc = <|
    procedure_id := AstId 9;
    parameters := [];
    return_bindings := [(AstId 91, u256)];
    body := [
      DefineStmt (AstId 92) (SingleType u256) (ConvertOperation u256 (k 9));
      CaptureBindingStmt (AstId 90) (AstId 91);
      WriteScalarStmt (AstId 90) u256 (BoundAtom (AstId 92))]
  |>
End

Definition caller_proc_def:
  caller_proc = <|
    procedure_id := AstId 100;
    parameters := [];
    return_bindings := [(AstId 101, u256)];
    body := [
      CaptureBindingStmt (AstId 90) (AstId 101);
      DefineStmt (AstId 102) (SingleType u256)
        (InternalCallOperation (AstId 9) []);
      WriteScalarStmt (AstId 90) u256 (BoundAtom (AstId 102))]
  |>
End

Definition test_program_def:
  test_program = <|
    procedures := [add_proc; sum_proc; fact_proc; pair_proc; first_proc;
                   spin_proc; fail_proc; call_fail_proc; callee_proc;
                   caller_proc];
    struct_layouts := []; type_declarations := [];
    state_variables := [];
    entry_procedure := AstId 1;
    external_functions := []; receive_procedure := NONE;
    fallback_procedure := NONE; creation_procedure := NONE
  |>
End

Definition test_env_def:
  test_env = core_program_environment test_program
End

Theorem test_program_wf:
  wf_core_program test_env test_program
Proof
  EVAL_TAC
QED

Definition run_def:
  run fuel f args = (invoke_source fuel test_env f args initial_state []).completion
End

val () = cv_auto_trans run_def;

Theorem add_ok:
  run 10 (AstId 1) [ScalarValue (IntegerValue 2); ScalarValue (IntegerValue 3)] =
  ReturnCompletion [ScalarValue (IntegerValue 5)]
Proof
  CONV_TAC cv_eval
QED

Theorem add_overflow_panics:
  run 10 (AstId 1) [ScalarValue (IntegerValue 255); ScalarValue (IntegerValue 1)] =
  PanicCompletion 0x11
Proof
  CONV_TAC cv_eval
QED

Theorem sum_runs_to_completion:
  run 10 (AstId 2) [ScalarValue (IntegerValue 3)] =
  ReturnCompletion [ScalarValue (IntegerValue 6)]
Proof
  CONV_TAC cv_eval
QED

Theorem sum_breaks:
  run 10 (AstId 2) [ScalarValue (IntegerValue 100)] =
  ReturnCompletion [ScalarValue (IntegerValue 15)]
Proof
  CONV_TAC cv_eval
QED

Theorem fact_recursion:
  run 10 (AstId 3) [ScalarValue (IntegerValue 5)] =
  ReturnCompletion [ScalarValue (IntegerValue 120)]
Proof
  CONV_TAC cv_eval
QED

Theorem deep_recursion_exhausts_fuel:
  run 3 (AstId 3) [ScalarValue (IntegerValue 5)] = FuelExhausted
Proof
  CONV_TAC cv_eval
QED

Theorem multiple_returns:
  run 10 (AstId 5) [] = ReturnCompletion [ScalarValue (IntegerValue 7)]
Proof
  CONV_TAC cv_eval
QED

Theorem infinite_loop_exhausts_fuel:
  run 20 (AstId 6) [] = FuelExhausted
Proof
  CONV_TAC cv_eval
QED

Theorem nested_revert:
  run 10 (AstId 8) [] = RevertCompletion [0x01w; 0x02w]
Proof
  CONV_TAC cv_eval
QED

Theorem caller_targets_survive_call:
  run 10 (AstId 100) [] = ReturnCompletion [ScalarValue (IntegerValue 9)]
Proof
  CONV_TAC cv_eval
QED

(* Storage: store(x) writes the uint8 state variable 200, at byte 1 of slot
 * 0, and returns it read back. *)

Definition counter_def:
  counter = <| state_id := AstId 200; state_type := u8; state_slot := 0w;
               state_offset := 1 |>
End

Definition store_proc_def:
  store_proc = <|
    procedure_id := AstId 20;
    parameters := [(AstId 21, u8)];
    return_bindings := [(AstId 22, u8)];
    body := [
      DefineStmt (AstId 25) (ReferenceType u8) (StateReferenceOperation (AstId 200));
      CaptureValueStmt (AstId 23) (BoundAtom (AstId 25));
      WriteScalarStmt (AstId 23) u8 (BoundAtom (AstId 21));
      DefineStmt (AstId 24) (SingleType u8) (ReadOperation u8 (BoundAtom (AstId 25)));
      ReturnStmt [BoundAtom (AstId 24)]]
  |>
End

Definition storage_program_def:
  storage_program vs = <|
    procedures := [store_proc];
    struct_layouts := []; type_declarations := [];
    state_variables := vs;
    entry_procedure := AstId 20;
    external_functions := []; receive_procedure := NONE;
    fallback_procedure := NONE; creation_procedure := NONE
  |>
End

Definition storage_wf_def:
  storage_wf vs ⇔
    wf_core_program (core_program_environment (storage_program vs))
      (storage_program vs)
End

Theorem storage_program_wf:
  storage_wf [counter]
Proof
  EVAL_TAC
QED

(* A variable that overruns its slot, one declared twice, and an undeclared
 * one are rejected. *)
Theorem storage_program_not_wf:
  ¬storage_wf [counter with state_offset := 32] ∧
  ¬storage_wf [counter; counter] ∧
  ¬storage_wf []
Proof
  EVAL_TAC
QED

Definition static_state_def:
  static_state =
    initial_state with frame := initial_state.frame with static_context := T
End

Definition run_store_def:
  run_store st x =
    (invoke_source 10 (core_program_environment (storage_program [counter]))
       (AstId 20) [ScalarValue (IntegerValue x)] st []).completion
End

val () = cv_auto_trans static_state_def;
val () = cv_auto_trans run_store_def;

Theorem store_reads_back:
  run_store initial_state 5 = ReturnCompletion [ScalarValue (IntegerValue 5)]
Proof
  CONV_TAC cv_eval
QED

(* The EVM halts exceptionally on SSTORE in a static frame. *)
Theorem static_store_invalid:
  run_store static_state 5 = InvalidCompletion "bad scalar write"
Proof
  CONV_TAC cv_eval
QED
