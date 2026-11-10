(* Smoke tests for the pure evaluator, run by cv_eval. The semantics test set
 * is solidityCoreProgramsTest.
 *)
Theory solidityEvaluatorTest
Ancestors
  solidityEvaluator solidityEntry
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
    next_heap_id := 0; immutables := FEMPTY;
    memory_allocated := 0;
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
    unsupported_procedures := []; procedures := [add_proc; sum_proc; fact_proc; pair_proc; first_proc;
                   spin_proc; fail_proc; call_fail_proc; callee_proc;
                   caller_proc];
    struct_layouts := []; type_declarations := [];
    state_variables := []; immutables := [];
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
    unsupported_procedures := []; procedures := [store_proc];
    struct_layouts := []; type_declarations := [];
    state_variables := vs; immutables := [];
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

(* Checked identity conversions preserve a calldata slice's offset and length. *)
Theorem calldata_identity_conversion:
  wf_core_value_type test_env (SingleType (LocatedT CalldataLoc BytesT)) ∧
  wf_core_operation test_env
    <| bindings := [(AstId 1, SingleType (LocatedT CalldataLoc BytesT))];
       targets := []; returns := []; in_loop := F |>
    (SingleType (LocatedT CalldataLoc BytesT))
    (ConvertOperation (LocatedT CalldataLoc BytesT) (BoundAtom (AstId 1))) ∧
  eval_pure_operation test_env
    [FEMPTY |+ (1, <| binding_type := SingleType (LocatedT CalldataLoc BytesT);
                      binding_value := ReferenceValue (CalldataReference 7 3 BytesT) |>)]
    (ConvertOperation (LocatedT CalldataLoc BytesT) (BoundAtom (AstId 1))) =
    ValueOk (ReferenceValue (CalldataReference 7 3 BytesT))
Proof
  CONV_TAC cv_eval
QED

(* The compiler inspects both length tags before its first storage write. *)
Definition static_byte_copy_def:
  static_byte_copy bad_src bad_dst =
    copy_byte_contents
      (StorageReference PersistentStorage 0w 0w 0 BytesT (LayoutId 1))
      (StorageReference PersistentStorage 0w 1w 0 BytesT (LayoutId 2))
      (static_state with world := static_state.world with accounts :=
        set_storage_word (set_storage_word empty_accounts 0w 0w bad_src) 0w 1w bad_dst)
End

val () = cv_auto_trans static_byte_copy_def;

Theorem invalid_source_header_precedes_static_copy_guard:
  static_byte_copy 64w 0w = INR (PanicCompletion 34)
Proof
  CONV_TAC cv_eval
QED

Theorem invalid_destination_header_precedes_static_copy_guard:
  static_byte_copy 0w 64w = INR (PanicCompletion 34)
Proof
  CONV_TAC cv_eval
QED

Theorem valid_headers_reach_static_copy_guard:
  static_byte_copy 0w 0w = INR (InvalidCompletion "byte copy in static frame")
Proof
  CONV_TAC cv_eval
QED

(* Encoding a corrupt storage argument panics before LOG's static guard. *)
Definition static_byte_event_def:
  static_byte_event header =
    (emit_event test_env NONE [(LocatedT MemoryLoc BytesT, F, BoundAtom (AstId 1))]
      (static_state with <|
        scopes := [FEMPTY |+ (1, <|
          binding_type := SingleType (LocatedT StorageLoc BytesT);
          binding_value := ReferenceValue
            (StorageReference PersistentStorage 0w 0w 0 BytesT (LayoutId 1)) |>)];
        world := static_state.world with accounts :=
          set_storage_word empty_accounts 0w 0w header |>) []).completion
End

val () = cv_auto_trans static_byte_event_def;

Theorem invalid_header_precedes_static_event_guard:
  static_byte_event 64w = PanicCompletion 34
Proof
  CONV_TAC cv_eval
QED

Theorem valid_header_reaches_static_event_guard:
  static_byte_event 0w = InvalidCompletion "emit in static frame"
Proof
  CONV_TAC cv_eval
QED

(* Inline assembly. asm(x) runs code with x bound to the block's "x" and
 * returns x; asm_caller() calls asm(7); halt() stops from a block. *)
Overload ylit = “λn. YulLit (LitNumber n)”

Definition asm_proc_def:
  asm_proc code = <|
    procedure_id := AstId 110;
    parameters := [(AstId 111, u256)];
    return_bindings := [(AstId 112, u256)];
    body := [AssemblyStmt code [("x", AssemblyLocal (AstId 111) u256)];
             ReturnStmt [BoundAtom (AstId 111)]]
  |>
End

Definition asm_caller_def:
  asm_caller = <|
    procedure_id := AstId 120;
    parameters := [];
    return_bindings := [(AstId 121, u256)];
    body := [
      DefineStmt (AstId 122) (SingleType u256)
        (InternalCallOperation (AstId 110) [k 7]);
      ReturnStmt [k 1]]
  |>
End

Definition halt_proc_def:
  halt_proc = <|
    procedure_id := AstId 130;
    parameters := [];
    return_bindings := [];
    body := [AssemblyStmt [YulExprStmt (YulBuiltin YStop [])] []]
  |>
End

Definition asm_env_def:
  asm_env code = core_program_environment <|
    unsupported_procedures := []; procedures := [asm_proc code; asm_caller; halt_proc];
    struct_layouts := []; type_declarations := [];
    state_variables := []; immutables := [];
    entry_procedure := AstId 110;
    external_functions := []; receive_procedure := NONE;
    fallback_procedure := NONE; creation_procedure := NONE
  |>
End

Definition run_asm_def:
  run_asm code st f args =
    (invoke_source 20 (asm_env code) f args st []).completion
End

Definition store_x_def:
  store_x = YulExprStmt (YulBuiltin YSStore [ylit 0w; YulName "x"])
End

Definition run_halt_def:
  run_halt creating =
    run_entry 20 (asm_env []) halt_proc [] initial_state.frame
      initial_state.world FEMPTY 0 creating
End

val () = cv_auto_trans asm_env_def;
val () = cv_auto_trans run_asm_def;
val () = cv_auto_trans store_x_def;
val () = cv_auto_trans run_halt_def;

Theorem asm_writes_local_back:
  run_asm [YulAssign ["x"] (YulBuiltin YAdd [YulName "x"; ylit 1w])]
    initial_state (AstId 110) [ScalarValue (IntegerValue 7)] =
  ReturnCompletion [ScalarValue (IntegerValue 8)]
Proof
  CONV_TAC cv_eval
QED

(* A static frame rejects a block naming sstore, even on a path not taken. *)
Theorem asm_static_store_invalid:
  run_asm [store_x] static_state (AstId 110) [ScalarValue (IntegerValue 7)] =
    InvalidCompletion "unsupported assembly builtin" ∧
  run_asm [YulIf (ylit 0w) [store_x]] static_state (AstId 110)
    [ScalarValue (IntegerValue 7)] =
    InvalidCompletion "unsupported assembly builtin"
Proof
  CONV_TAC cv_eval
QED

(* Scratch space round-trips; a write between it and the free memory
 * pointer (0x80 here) fails closed, and one from the free memory pointer up
 * is dropped. *)
Theorem asm_memory_outside_scratch_invalid:
  run_asm [YulExprStmt (YulBuiltin YMStore [ylit 0x20w; YulName "x"]);
           YulAssign ["x"] (YulBuiltin YMLoad [ylit 0x20w])]
    initial_state (AstId 110) [ScalarValue (IntegerValue 7)] =
    ReturnCompletion [ScalarValue (IntegerValue 7)] ∧
  run_asm [YulExprStmt (YulBuiltin YMStore [ylit 0x60w; YulName "x"])]
    initial_state (AstId 110) [ScalarValue (IntegerValue 7)] =
    InvalidCompletion "assembly wrote memory outside the scratch space and byte sequence data" ∧
  run_asm [YulExprStmt (YulBuiltin YMStore [ylit 0x80w; YulName "x"])]
    initial_state (AstId 110) [ScalarValue (IntegerValue 7)] =
    ReturnCompletion [ScalarValue (IntegerValue 7)]
Proof
  CONV_TAC cv_eval
QED

(* Memory byte sequences. asm_bytes(b) runs blocks one after another with b's
 * address bound to each block's "b" and returns its "r"; run_asm_blocks gives
 * the completion and b's bytes afterwards, b allocated with or without its
 * padding zeroed in the compiler's memory, and run_asm_bytes runs one block on
 * a zero-padded b. b is the first allocation, at 0x80. *)
Definition asm_blocks_def:
  (asm_blocks [] = [ReturnStmt [BoundAtom (AstId 142)]]) ∧
  (asm_blocks (code :: codes) =
    AssemblyStmt code [("b", AssemblyMemory (AstId 141) BytesT);
                       ("r", AssemblyLocal (AstId 142) u256)] ::
    asm_blocks codes)
End

Definition asm_bytes_proc_def:
  asm_bytes_proc codes = <|
    procedure_id := AstId 140;
    parameters := [(AstId 141, LocatedT MemoryLoc BytesT)];
    return_bindings := [(AstId 142, u256)];
    body := asm_blocks codes
  |>
End

Definition run_asm_blocks_def:
  run_asm_blocks padded codes bs =
    let (b, st) = allocate_bytes padded BytesT bs initial_state in
    let env = core_program_environment <|
      unsupported_procedures := []; procedures := [asm_bytes_proc codes];
      struct_layouts := []; type_declarations := [];
      state_variables := []; immutables := [];
      entry_procedure := AstId 140;
      external_functions := []; receive_procedure := NONE;
      fallback_procedure := NONE; creation_procedure := NONE |> in
    let r = invoke_source 20 env (AstId 140) [b] st [] in
    (r.completion, memory_bytes r.state (HeapId 1) BytesT)
End

Definition run_asm_bytes_def:
  run_asm_bytes code bs = run_asm_blocks T [code] bs
End

val () = cv_auto_trans run_asm_blocks_def;
val () = cv_auto_trans run_asm_bytes_def;

Overload yadd = “λe1 e2. YulBuiltin YAdd [e1; e2]”

(* The block sees b's address, length word and bytes; a byte or a whole word
 * written in b's data is read back (the bytes past the length are dropped);
 * a write to the length word fails closed, and one past the data's last word,
 * from the free memory pointer up, is dropped. *)
Theorem asm_memory_bytes:
  run_asm_bytes [YulAssign ["r"] (YulName "b")] [1w; 2w; 3w] =
    (ReturnCompletion [ScalarValue (IntegerValue 0x80)], SOME [1w; 2w; 3w]) ∧
  run_asm_bytes [YulAssign ["r"] (YulBuiltin YMLoad [YulName "b"])] [1w; 2w; 3w] =
    (ReturnCompletion [ScalarValue (IntegerValue 3)], SOME [1w; 2w; 3w]) ∧
  run_asm_bytes [YulAssign ["r"] (YulBuiltin YShr [ylit 232w;
                   YulBuiltin YMLoad [yadd (YulName "b") (ylit 32w)]])] [1w; 2w; 3w] =
    (ReturnCompletion [ScalarValue (IntegerValue 0x010203)], SOME [1w; 2w; 3w]) ∧
  run_asm_bytes [YulExprStmt (YulBuiltin YMStore8 [yadd (YulName "b") (ylit 33w); ylit 0xffw])]
    [1w; 2w; 3w] =
    (ReturnCompletion [ScalarValue (IntegerValue 0)], SOME [1w; 0xffw; 3w]) ∧
  run_asm_bytes [YulExprStmt (YulBuiltin YMStore [yadd (YulName "b") (ylit 32w); ylit 0xaabbw])]
    [1w; 2w; 3w] =
    (ReturnCompletion [ScalarValue (IntegerValue 0)], SOME [0w; 0w; 0w]) ∧
  run_asm_bytes [YulExprStmt (YulBuiltin YMStore [YulName "b"; ylit 1w])] [1w; 2w; 3w] =
    (InvalidCompletion "assembly wrote memory outside the scratch space and byte sequence data",
     SOME [1w; 2w; 3w]) ∧
  run_asm_bytes [YulExprStmt (YulBuiltin YMStore8 [yadd (YulName "b") (ylit 64w); ylit 1w])]
    [1w; 2w; 3w] =
    (ReturnCompletion [ScalarValue (IntegerValue 0)], SOME [1w; 2w; 3w])
Proof
  CONV_TAC cv_eval
QED

(* A block reads only the free memory pointer, the zero slot, b's words and
 * what it wrote, however the address is computed: scratch it hasn't written
 * and memory past b's last word fail closed; a zero-length read touches
 * nothing. The free memory pointer is past b's two words. *)
Theorem asm_memory_reads:
  run_asm_bytes [YulLet ["p"] (SOME (ylit 0x40w));
                 YulAssign ["r"] (YulBuiltin YMLoad [YulName "p"])] [1w; 2w; 3w] =
    (ReturnCompletion [ScalarValue (IntegerValue 0xc0)], SOME [1w; 2w; 3w]) ∧
  run_asm_bytes [YulExprStmt (YulBuiltin YMStore [ylit 0x40w; ylit 0x100w])]
    [1w; 2w; 3w] =
    (InvalidCompletion "assembly wrote memory outside the scratch space and byte sequence data",
     SOME [1w; 2w; 3w]) ∧
  run_asm_bytes [YulAssign ["r"] (YulBuiltin YMLoad [yadd (YulName "b") (ylit 0x60w)])]
    [1w; 2w; 3w] =
    (InvalidCompletion "assembly read memory it was not given", SOME [1w; 2w; 3w]) ∧
  run_asm_bytes [YulLet ["p"] (SOME (ylit 0w));
                 YulAssign ["r"] (YulBuiltin YMLoad [YulName "p"])] [1w; 2w; 3w] =
    (InvalidCompletion "assembly read memory it was not given", SOME [1w; 2w; 3w]) ∧
  run_asm_bytes [YulLet ["p"] (SOME (ylit 0w));
                 YulExprStmt (YulBuiltin YMStore [YulName "p"; ylit 5w]);
                 YulAssign ["r"] (YulBuiltin YMLoad [YulName "p"])] [1w; 2w; 3w] =
    (ReturnCompletion [ScalarValue (IntegerValue 5)], SOME [1w; 2w; 3w]) ∧
  run_asm_bytes [YulLet ["p"] (SOME (ylit 0x60w));
                 YulAssign ["r"] (YulBuiltin YMLoad [YulName "p"])] [1w; 2w; 3w] =
    (ReturnCompletion [ScalarValue (IntegerValue 0)], SOME [1w; 2w; 3w]) ∧
  run_asm_bytes [YulExprStmt (YulBuiltin YPop
                   [YulBuiltin YKeccak256 [yadd (YulName "b") (ylit 0x1000w); ylit 0w]])]
    [1w; 2w; 3w] =
    (ReturnCompletion [ScalarValue (IntegerValue 0)], SOME [1w; 2w; 3w]) ∧
  (* the first byte past b's word, and a word straddling its end *)
  run_asm_bytes [YulAssign ["r"] (YulBuiltin YMLoad [yadd (YulName "b") (ylit 0x40w)])]
    [1w; 2w; 3w] =
    (InvalidCompletion "assembly read memory it was not given", SOME [1w; 2w; 3w]) ∧
  run_asm_bytes [YulAssign ["r"] (YulBuiltin YMLoad [yadd (YulName "b") (ylit 0x21w)])]
    [1w; 2w; 3w] =
    (InvalidCompletion "assembly read memory it was not given", SOME [1w; 2w; 3w]) ∧
  (* a reader other than mload, and a builtin inside the block's own function *)
  run_asm_bytes [YulLet ["p"] (SOME (ylit 0w));
                 YulAssign ["r"] (YulBuiltin YKeccak256 [YulName "p"; ylit 64w])]
    [1w; 2w; 3w] =
    (InvalidCompletion "assembly read memory it was not given", SOME [1w; 2w; 3w]) ∧
  run_asm_bytes [YulFunction "f" ["q"] ["v"]
                   [YulAssign ["v"] (YulBuiltin YMLoad [YulName "q"])];
                 YulAssign ["r"] (YulApply "f" [ylit 0x20w])] [1w; 2w; 3w] =
    (InvalidCompletion "assembly read memory it was not given", SOME [1w; 2w; 3w])
Proof
  CONV_TAC cv_eval
QED

(* Memory from the free memory pointer (0xc0 here) up is the block's
 * temporary memory: it reads back what it wrote there, and the next block
 * starts without it. *)
Theorem asm_memory_temporary:
  run_asm_bytes [YulExprStmt (YulBuiltin YMStore [yadd (YulName "b") (ylit 0x40w); ylit 5w]);
                 YulAssign ["r"] (YulBuiltin YMLoad [yadd (YulName "b") (ylit 0x40w)])]
    [1w; 2w; 3w] =
    (ReturnCompletion [ScalarValue (IntegerValue 5)], SOME [1w; 2w; 3w]) ∧
  run_asm_blocks T
    [[YulExprStmt (YulBuiltin YMStore [ylit 0xc0w; ylit 5w])];
     [YulAssign ["r"] (YulBuiltin YMLoad [ylit 0xc0w])]] [1w; 2w; 3w] =
    (InvalidCompletion "assembly read memory it was not given", SOME [1w; 2w; 3w])
Proof
  CONV_TAC cv_eval
QED

(* Padding. When the compiler's memory need not hold zeros past b's last
 * byte, the block is not given those bytes: a read of b's data word fails
 * closed, while its data bytes alone may be read. A block that writes the
 * padding as zeros gives later blocks the padding; one that leaves it
 * unwritten does not, and nor does one that makes it dirty. *)
Theorem asm_memory_padding:
  run_asm_blocks F [[YulAssign ["r"] (YulBuiltin YMLoad [yadd (YulName "b") (ylit 32w)])]]
    [1w; 2w; 3w] =
    (InvalidCompletion "assembly read memory it was not given", SOME [1w; 2w; 3w]) ∧
  run_asm_blocks F
    [[YulExprStmt (YulBuiltin YMStore [ylit 0w; ylit 0w]);
      YulExprStmt (YulBuiltin YMCopy [ylit 0w; yadd (YulName "b") (ylit 32w); ylit 3w]);
      YulAssign ["r"] (YulBuiltin YShr [ylit 232w; YulBuiltin YMLoad [ylit 0w]])]]
    [1w; 2w; 3w] =
    (ReturnCompletion [ScalarValue (IntegerValue 0x010203)], SOME [1w; 2w; 3w]) ∧
  run_asm_blocks F
    [[YulExprStmt (YulBuiltin YMStore [yadd (YulName "b") (ylit 32w);
        YulBuiltin YShl [ylit 232w; ylit 0x010203w]])];
     [YulAssign ["r"] (YulBuiltin YShr [ylit 232w;
        YulBuiltin YMLoad [yadd (YulName "b") (ylit 32w)]])]] [1w; 2w; 3w] =
    (ReturnCompletion [ScalarValue (IntegerValue 0x010203)], SOME [1w; 2w; 3w]) ∧
  (* the unwritten padding is not read back as zeros *)
  run_asm_blocks F
    [[YulLet ["z"] (SOME (ylit 0w))];
     [YulAssign ["r"] (YulBuiltin YMLoad [yadd (YulName "b") (ylit 32w)])]] [1w; 2w; 3w] =
    (InvalidCompletion "assembly read memory it was not given", SOME [1w; 2w; 3w]) ∧
  run_asm_blocks T
    [[YulExprStmt (YulBuiltin YMStore8 [yadd (YulName "b") (ylit 35w); ylit 1w])];
     [YulAssign ["r"] (YulBuiltin YMLoad [yadd (YulName "b") (ylit 32w)])]] [1w; 2w; 3w] =
    (InvalidCompletion "assembly read memory it was not given", SOME [1w; 2w; 3w])
Proof
  CONV_TAC cv_eval
QED

(* return(...) in a callee ends the whole frame with its bytes. *)
Theorem asm_halt_passes_through_call:
  run_asm [YulExprStmt (YulBuiltin YMStore [ylit 0w; YulName "x"]);
           YulExprStmt (YulBuiltin YReturn [ylit 0w; ylit 32w])]
    initial_state (AstId 120) [] =
  HaltCompletion (REPLICATE 31 0w ++ [7w])
Proof
  CONV_TAC cv_eval
QED

(* A halt returns its bytes from a call frame and fails closed in a creation
 * frame. *)
Theorem asm_halt_in_creation_invalid:
  run_halt F = ContractReturned [] initial_state.world ∧
  run_halt T = ContractInvalid "assembly halt in a creation frame"
Proof
  CONV_TAC cv_eval
QED

(* What assembly_memory_ok admits: scratch written then read, the free
 * memory pointer read, and writes above the scratch space only in a block
 * that halts. *)
Theorem asm_memory_rule:
  assembly_memory_ok
    [YulExprStmt (YulBuiltin YMStore [ylit 0w; YulName "x"]);
     YulExprStmt (YulBuiltin YMStore [ylit 32w; YulName "x"]);
     YulAssign ["x"] (YulBuiltin YKeccak256 [ylit 0w; ylit 64w])] ∧
  ¬assembly_memory_ok [YulAssign ["x"] (YulBuiltin YMLoad [ylit 0w])] ∧
  assembly_memory_ok [YulAssign ["x"] (YulBuiltin YMLoad [ylit 64w])] ∧
  ¬assembly_memory_ok [YulAssign ["x"] (YulBuiltin YMLoad [ylit 65w])] ∧
  ¬assembly_memory_ok
    [YulExprStmt (YulBuiltin YMStore [ylit 1w; YulName "x"]);
     YulExprStmt (YulBuiltin YLog0 [ylit 0w; ylit 64w])] ∧
  ¬assembly_memory_ok [YulExprStmt (YulBuiltin YMStore [ylit 64w; YulName "x"])] ∧
  assembly_memory_ok
    [YulExprStmt (YulBuiltin YMStore [ylit 128w; YulName "x"]);
     YulExprStmt (YulBuiltin YReturn [ylit 128w; ylit 32w])] ∧
  (* computed addresses are checked as the block runs; zero lengths touch
     nothing *)
  assembly_memory_ok
    [YulExprStmt (YulBuiltin YMStore8 [yadd (YulName "b") (ylit 32w); ylit 1w]);
     YulAssign ["x"] (YulBuiltin YMLoad [YulName "b"])] ∧
  assembly_memory_ok [YulExprStmt (YulBuiltin YLog0 [ylit 128w; ylit 0w])] ∧
  ¬assembly_memory_ok [YulExprStmt (YulBuiltin YMStore [ylit 64w; YulName "b"])]
Proof
  EVAL_TAC
QED

(* call(gas(), a, 0, i, isz, o, osz) with literal arguments. *)
Definition ycall_def:
  ycall a i isz out osz =
    YulBuiltin YCall [YulBuiltin YGas []; a; ylit 0w; ylit i; ylit isz;
                      ylit out; ylit osz]
End

(* A call's literal output region counts as written for later reads, at most
 * what it asked for; its literal input must have been written, and its
 * output, like returndatacopy's, may go above the scratch space only in a
 * block that halts. A huge literal length is rejected without a byte walk. *)
Theorem asm_call_memory_rule:
  assembly_memory_ok
    [YulLet ["s"] (SOME (ycall (YulName "t") 0w 0w 0w 32w));
     YulAssign ["x"] (YulBuiltin YMLoad [ylit 0w])] ∧
  assembly_memory_ok
    [YulExprStmt (YulBuiltin YPop [ycall (YulName "t") 0w 0w 0w 32w]);
     YulAssign ["x"] (YulBuiltin YMLoad [ylit 0w])] ∧
  ¬assembly_memory_ok
    [YulLet ["s"] (SOME (ycall (YulName "t") 0w 0w 0w 32w));
     YulAssign ["x"] (YulBuiltin YMLoad [ylit 1w])] ∧
  assembly_memory_ok
    [YulExprStmt (YulBuiltin YMStore [ylit 0w; YulName "x"]);
     YulLet ["s"] (SOME (ycall (YulName "t") 0w 4w 0w 32w))] ∧
  ¬assembly_memory_ok [YulLet ["s"] (SOME (ycall (YulName "t") 0w 4w 0w 32w))] ∧
  ¬assembly_memory_ok [YulLet ["s"] (SOME (ycall (YulName "t") 0w 0w 128w 32w))] ∧
  assembly_memory_ok
    [YulLet ["s"] (SOME (ycall (YulName "t") 0w 0w 128w 32w));
     YulExprStmt (YulBuiltin YRevert [ylit 128w; ylit 32w])] ∧
  ¬assembly_memory_ok
    [YulExprStmt (YulBuiltin YReturnDataCopy [ylit 128w; ylit 0w; ylit 32w])] ∧
  ¬assembly_memory_ok
    [YulLet ["s"] (SOME (ycall (YulName "t") 0w 0w 0w 32w));
     YulAssign ["x"] (YulBuiltin YKeccak256 [ylit 0w; ylit (-1w)])]
Proof
  EVAL_TAC
QED

(* What assembly_calls_ok admits: gas() only as a call's gas argument, and
 * return data only after a statement that calls, earlier in the same or an
 * enclosing statement list. *)
Theorem asm_calls_rule:
  assembly_calls_ok
    [YulLet ["s"] (SOME (ycall (YulName "t") 0w 0w 0w 32w));
     YulIf (YulBuiltin YIsZero [YulName "s"])
       [YulExprStmt (YulBuiltin YReturnDataCopy
          [ylit 0w; ylit 0w; YulBuiltin YReturnDataSize []])];
     YulAssign ["x"] (YulBuiltin YReturnDataSize [])] ∧
  assembly_calls_ok
    [YulLet ["s"] (SOME (YulBuiltin YStaticCall
       [ylit 5000w; YulName "t"; ylit 0w; ylit 0w; ylit 0w; ylit 0w]));
     YulAssign ["x"] (YulBuiltin YReturnDataSize [])] ∧
  assembly_calls_ok
    [YulIf (YulBuiltin YIsZero [ycall (YulName "t") 0w 0w 0w 0w])
       [YulExprStmt (YulBuiltin YRevert [ylit 0w; YulBuiltin YReturnDataSize []])]] ∧
  ¬assembly_calls_ok
    [YulIf (YulBuiltin YIsZero [ycall (YulName "t") 0w 0w 0w 0w]) [];
     YulAssign ["x"] (YulBuiltin YReturnDataSize [])] ∧
  ¬assembly_calls_ok [YulAssign ["x"] (YulBuiltin YReturnDataSize [])] ∧
  ¬assembly_calls_ok [YulAssign ["x"] (YulBuiltin YGas [])] ∧
  ¬assembly_calls_ok
    [YulLet ["s"] (SOME (YulBuiltin YCall
       [ylit 0w; YulBuiltin YGas []; ylit 0w; ylit 0w; ylit 0w; ylit 0w; ylit 0w]))] ∧
  ¬assembly_calls_ok
    [YulAssign ["x"] (yadd (ycall (YulName "t") 0w 0w 0w 0w)
                            (YulBuiltin YReturnDataSize []))] ∧
  ¬assembly_calls_ok
    [YulIf (YulName "x") [YulLet ["s"] (SOME (ycall (YulName "t") 0w 0w 0w 0w))];
     YulAssign ["x"] (YulBuiltin YReturnDataSize [])] ∧
  ¬assembly_calls_ok
    [YulLet ["s"] (SOME (ycall (YulName "t") 0w 0w 0w 0w));
     YulFunction "f" [] ["r"] [YulAssign ["r"] (YulBuiltin YReturnDataSize [])]]
Proof
  EVAL_TAC
QED

(* Arguments run right to left: a call's output region covers a read in an
 * argument left of it, and its return data a read there, but not to its
 * right. A read at a literal address of computed length is checked as the
 * block runs, and a returndatacopy into the scratch space covers it. *)
Theorem asm_argument_order_rule:
  assembly_memory_ok
    [YulAssign ["x"] (YulBuiltin YAnd
       [YulBuiltin YMLoad [ylit 0w]; ycall (YulName "t") 0w 0w 0w 32w])] ∧
  ¬assembly_memory_ok
    [YulAssign ["x"] (YulBuiltin YAnd
       [ycall (YulName "t") 0w 0w 0w 32w; YulBuiltin YMLoad [ylit 0w]])] ∧
  assembly_calls_ok
    [YulAssign ["x"] (YulBuiltin YAnd
       [YulBuiltin YGt [YulBuiltin YReturnDataSize []; ylit 31w];
        ycall (YulName "t") 0w 0w 0w 32w])] ∧
  ¬assembly_calls_ok
    [YulAssign ["x"] (YulBuiltin YAnd
       [ycall (YulName "t") 0w 0w 0w 32w;
        YulBuiltin YGt [YulBuiltin YReturnDataSize []; ylit 31w]])] ∧
  assembly_memory_ok
    [YulExprStmt (YulBuiltin YRevert [ylit 0w; YulBuiltin YReturnDataSize []])] ∧
  assembly_memory_ok
    [YulExprStmt (YulBuiltin YReturnDataCopy [ylit 0w; ylit 0w; YulBuiltin YReturnDataSize []]);
     YulAssign ["x"] (YulBuiltin YMLoad [ylit 0w])] ∧
  ¬assembly_memory_ok
    [YulExprStmt (YulBuiltin YReturnDataCopy [ylit 64w; ylit 0w; YulBuiltin YReturnDataSize []])]
Proof
  EVAL_TAC
QED

(* A statement list that ends in a halt, and that break, continue or leave
 * cannot leave early, may write anywhere: an if or switch body, a Yul
 * function's body, or the whole block when its last switch halts in every
 * branch. *)
Theorem asm_halting_bodies_rule:
  assembly_memory_ok
    [YulIf (YulName "x")
       [YulExprStmt (YulBuiltin YMStore [ylit 0x80w; YulName "x"]);
        YulExprStmt (YulBuiltin YRevert [ylit 0x80w; ylit 32w])]] ∧
  ¬assembly_memory_ok
    [YulIf (YulName "x") [YulExprStmt (YulBuiltin YMStore [ylit 0x80w; YulName "x"])]] ∧
  ¬assembly_memory_ok
    [YulFor [] (ylit 1w) []
       [YulIf (YulName "x")
          [YulExprStmt (YulBuiltin YMStore [ylit 0x80w; YulName "x"]);
           YulIf (YulName "y") [YulBreak];
           YulExprStmt (YulBuiltin YRevert [ylit 0w; ylit 0w])]]] ∧
  assembly_memory_ok
    [YulFor [] (ylit 1w) []
       [YulIf (YulName "x")
          [YulExprStmt (YulBuiltin YMStore [ylit 0x80w; YulName "x"]);
           YulFor [] (YulName "y") [] [YulBreak];
           YulExprStmt (YulBuiltin YRevert [ylit 0w; ylit 0w])]]] ∧
  assembly_memory_ok
    [YulFunction "f" [] []
       [YulExprStmt (YulBuiltin YMStore [ylit 0x80w; ylit 1w]);
        YulExprStmt (YulBuiltin YRevert [ylit 0w; ylit 0w])]] ∧
  ¬assembly_memory_ok
    [YulFunction "f" [] []
       [YulExprStmt (YulBuiltin YMStore [ylit 0x80w; ylit 1w]);
        YulIf (YulName "y") [YulLeave];
        YulExprStmt (YulBuiltin YRevert [ylit 0w; ylit 0w])]] ∧
  assembly_memory_ok
    [YulExprStmt (YulBuiltin YMStore [ylit 0x80w; YulName "x"]);
     YulSwitch (YulName "x")
       [(LitNumber 0w, [YulExprStmt (YulBuiltin YRevert [ylit 0w; ylit 0w])])]
       [YulExprStmt (YulBuiltin YReturn [ylit 0x80w; ylit 32w])]] ∧
  ¬assembly_memory_ok
    [YulExprStmt (YulBuiltin YMStore [ylit 0x80w; YulName "x"]);
     YulSwitch (YulName "x")
       [(LitNumber 0w, [YulExprStmt (YulBuiltin YRevert [ylit 0w; ylit 0w])])] []]
Proof
  EVAL_TAC
QED

(* Callees at 0x5000 (returns the word 0x2a), 0x5001 (reverts with the word
 * 0xaa) and 0x5002 (no code). *)
Definition call_state_def:
  call_state =
    initial_state with world := (initial_state.world with accounts :=
      update_account 0x5001w
        (empty_account_state with
           code := [0x60w; 0xaaw; 0x60w; 0w; 0x52w; 0x60w; 0x20w; 0x60w; 0w; 0xfdw])
        (update_account 0x5000w
           (empty_account_state with
              code := [0x60w; 0x2aw; 0x60w; 0w; 0x52w; 0x60w; 0x20w; 0x60w; 0w; 0xf3w])
           empty_accounts))
End

val () = cv_auto_trans ycall_def;
val () = cv_auto_trans call_state_def;

(* A call runs the callee and leaves its output and return data; a failed one
 * is bubbled through the free memory pointer, as SafeERC20 does; a callee
 * returning less than asked leaves the scratch unwritten, so reading it fails
 * closed. A static frame refuses call but runs staticcall. *)
Theorem asm_calls_run:
  run_asm [YulExprStmt (YulBuiltin YPop [ycall (ylit 0x5000w) 0w 0w 0w 32w]);
           YulAssign ["x"] (yadd (YulBuiltin YMLoad [ylit 0w])
                                 (YulBuiltin YReturnDataSize []))]
    call_state (AstId 110) [ScalarValue (IntegerValue 7)] =
    ReturnCompletion [ScalarValue (IntegerValue 74)] ∧
  run_asm [YulIf (YulBuiltin YIsZero [ycall (ylit 0x5001w) 0w 0w 0w 0w])
             [YulLet ["p"] (SOME (YulBuiltin YMLoad [ylit 0x40w]));
              YulExprStmt (YulBuiltin YReturnDataCopy
                [YulName "p"; ylit 0w; YulBuiltin YReturnDataSize []]);
              YulExprStmt (YulBuiltin YRevert
                [YulName "p"; YulBuiltin YReturnDataSize []])]]
    call_state (AstId 110) [ScalarValue (IntegerValue 7)] =
    RevertCompletion (REPLICATE 31 0w ++ [0xaaw]) ∧
  run_asm [YulExprStmt (YulBuiltin YPop [ycall (ylit 0x5002w) 0w 0w 0w 32w]);
           YulAssign ["x"] (YulBuiltin YMLoad [ylit 0w])]
    call_state (AstId 110) [ScalarValue (IntegerValue 7)] =
    InvalidCompletion "assembly read memory it was not given" ∧
  run_asm [YulAssign ["x"] (ycall (ylit 0x5000w) 0w 0w 0w 32w)]
    (call_state with frame := call_state.frame with static_context := T)
    (AstId 110) [ScalarValue (IntegerValue 7)] =
    InvalidCompletion "unsupported assembly builtin" ∧
  run_asm [YulAssign ["x"] (YulBuiltin YStaticCall
             [YulBuiltin YGas []; ylit 0x5000w; ylit 0w; ylit 0w; ylit 0w; ylit 32w])]
    (call_state with frame := call_state.frame with static_context := T)
    (AstId 110) [ScalarValue (IntegerValue 7)] =
    ReturnCompletion [ScalarValue (IntegerValue 1)]
Proof
  CONV_TAC cv_eval
QED

(* Callees at 0x5003 (returns the bytes 01 02 03) and 0x5004 (reverts with
 * them): return data shorter than a word. *)
Definition short_return_state_def:
  short_return_state =
    initial_state with world := (initial_state.world with accounts :=
      update_account 0x5004w
        (empty_account_state with
           code := [0x62w; 1w; 2w; 3w; 0x60w; 0w; 0x52w; 0x60w; 3w; 0x60w; 0x1dw; 0xfdw])
        (update_account 0x5003w
           (empty_account_state with
              code := [0x62w; 1w; 2w; 3w; 0x60w; 0w; 0x52w; 0x60w; 3w; 0x60w; 0x1dw; 0xf3w])
           empty_accounts))
End

(* Bind low-level return bytes directly; a try's raw failure data is
 * materialized by the generic catch before the block reads it. *)
Definition return_bytes_proc_def:
  return_bytes_proc op code = <|
    procedure_id := AstId 150;
    parameters := [];
    return_bindings := [(AstId 154, u256)];
    body := [
      DefineStmt (AstId 151) (SingleType (LocatedT MemoryLoc BytesT))
        (BytesLiteralOperation BytesT []);
      DefineStmt (AstId 152)
        (ProductType [SingleType BoolT;
          case op of TryExternalCallOperation _ _ _ _ _ _ _ _ => RevertDataType
                   | _ => SingleType (LocatedT MemoryLoc BytesT)]) op] ++
      (case op of
         TryExternalCallOperation _ _ _ _ _ _ _ _ =>
           [DefineStmt (AstId 155) RevertDataType
              (TupleComponentOperation 1 (BoundAtom (AstId 152)));
            DefineStmt (AstId 153) (SingleType (LocatedT MemoryLoc BytesT))
              (MaterializeRevertDataOperation (BoundAtom (AstId 155)))]
       | _ =>
           [DefineStmt (AstId 153) (SingleType (LocatedT MemoryLoc BytesT))
              (TupleComponentOperation 1 (BoundAtom (AstId 152)))]) ++
      [AssemblyStmt code [("b", AssemblyMemory (AstId 153) BytesT);
                         ("r", AssemblyLocal (AstId 154) u256)];
      ReturnStmt [BoundAtom (AstId 154)]]
  |>
End

Definition run_return_bytes_def:
  run_return_bytes op code =
    let env = core_program_environment <|
      unsupported_procedures := []; procedures := [return_bytes_proc op code];
      struct_layouts := []; type_declarations := [];
      state_variables := []; immutables := [];
      entry_procedure := AstId 150;
      external_functions := []; receive_procedure := NONE;
      fallback_procedure := NONE; creation_procedure := NONE |> in
    (invoke_source 20 env (AstId 150) [] short_return_state []).completion
End

Definition short_static_def:
  short_static =
    LowLevelCallOperation ExternalStaticCall (ConstantAtom (AddressValue 0x5003w)) (k 0)
      NONE (BoundAtom (AstId 151))
End

Definition short_try_def:
  short_try =
    TryExternalCallOperation ExternalCall [1w; 2w; 3w; 4w] [] []
      (ConstantAtom (AddressValue 0x5004w)) (k 0) NONE []
End

(* Reads b's last data word, padding included; copies its three bytes. *)
Definition read_last_word_def:
  read_last_word =
    [YulAssign ["r"] (YulBuiltin YMLoad [yadd (YulName "b") (ylit 32w)])]
End

Definition copy_data_def:
  copy_data =
    [YulExprStmt (YulBuiltin YMStore [ylit 0w; ylit 0w]);
     YulExprStmt (YulBuiltin YMCopy [ylit 0w; yadd (YulName "b") (ylit 32w); ylit 3w]);
     YulAssign ["r"] (YulBuiltin YShr [ylit 232w; YulBuiltin YMLoad [ylit 0w]])]
End

val () = cv_auto_trans short_return_state_def;
val () = cv_auto_trans short_static_def;
val () = cv_auto_trans short_try_def;
val () = cv_auto_trans read_last_word_def;
val () = cv_auto_trans copy_data_def;
val () = cv_auto_trans run_return_bytes_def;

(* Bytes copied from return data, a staticcall's or a caught revert's, keep
 * the padding solc's memory leaves as it was: a block reading their last
 * word fails closed, while their bytes alone read as returned. *)
Theorem asm_return_data_padding:
  run_return_bytes short_static read_last_word =
    InvalidCompletion "assembly read memory it was not given" ∧
  run_return_bytes short_static copy_data =
    ReturnCompletion [ScalarValue (IntegerValue 0x010203)] ∧
  run_return_bytes short_try read_last_word =
    InvalidCompletion "assembly read memory it was not given" ∧
  run_return_bytes short_try copy_data =
    ReturnCompletion [ScalarValue (IntegerValue 0x010203)]
Proof
  CONV_TAC cv_eval
QED

(* A memory reference may not be assigned, except where a Yul function's
 * parameter or result reuses its name. *)
Theorem asm_memory_assign_rule:
  ¬assembly_assigns_ok ["b"] [YulAssign ["b"] (ylit 0w)] ∧
  ¬assembly_assigns_ok ["b"] [YulIf (ylit 1w) [YulAssign ["x"; "b"] (YulApply "f" [])]] ∧
  assembly_assigns_ok ["b"] [YulFunction "f" ["b"] [] [YulAssign ["b"] (ylit 0w)]] ∧
  assembly_assigns_ok ["b"] [YulFunction "f" [] ["b"] [YulAssign ["b"] (ylit 0w)]] ∧
  ¬assembly_assigns_ok ["b"] [YulFunction "f" ["x"] [] [YulAssign ["b"] (ylit 0w)]] ∧
  assembly_assigns_ok ["b"] [YulAssign ["x"] (YulName "b")]
Proof
  EVAL_TAC
QED
