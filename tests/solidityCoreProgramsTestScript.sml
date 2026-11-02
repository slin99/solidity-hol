(* Semantics unit tests: small hand-written core programs run through the pure
 * evaluator by cv_eval. Expected results are worked out from the language
 * definition, not taken from the compiler.
 *)
Theory solidityCoreProgramsTest
Ancestors
  solidityEvaluator
Libs
  cv_transLib wordsLib intLib

Overload u8 = “UintT 8”
Overload u256 = “UintT 256”
Overload k = “λi. ConstantAtom (IntegerValue i)”
Overload v = “λn. BoundAtom (AstId n)”
Overload iv = “λi. ScalarValue (IntegerValue i)”

(* Identifiers only need to be distinct within a procedure. *)

(* binop(x, y) returns (r): r = x op y, under the given arithmetic mode. *)
Definition binop_proc_def:
  binop_proc f ty mode op = <|
    procedure_id := AstId f;
    parameters := [(AstId 1, ty); (AstId 2, ty)];
    return_bindings := [(AstId 3, ty)];
    body := [
      DefineStmt (AstId 4) (SingleType ty)
        (ScalarOperation ty mode op [v 1; v 2]);
      ReturnStmt [v 4]]
  |>
End

(* count(n) returns (c, i): while (++i < n) { if (i % 2 == 1) continue;
 * c += 1; if (c == 3) break; }. The prelude writes the return binding i.
 *)
Definition count_proc_def:
  count_proc = <|
    procedure_id := AstId 6;
    parameters := [(AstId 1, u256)];
    return_bindings := [(AstId 2, u256); (AstId 3, u256)];
    body := [
      WhileStmt
        [DefineStmt (AstId 4) (SingleType u256)
           (ScalarOperation u256 CheckedArithmetic AddOp [v 3; k 1]);
         CaptureBindingStmt (AstId 5) (AstId 3);
         WriteScalarStmt (AstId 5) u256 (v 4);
         DefineStmt (AstId 6) (SingleType BoolT)
           (ScalarOperation u256 UncheckedArithmetic LessThanOp [v 4; v 1])]
        (v 6)
        [DefineStmt (AstId 7) (SingleType u256)
           (ScalarOperation u256 CheckedArithmetic RemainderOp [v 3; k 2]);
         DefineStmt (AstId 8) (SingleType BoolT)
           (ScalarOperation u256 UncheckedArithmetic EqualOp [v 7; k 1]);
         IfStmt (v 8) [ContinueStmt] [];
         DefineStmt (AstId 9) (SingleType u256)
           (ScalarOperation u256 CheckedArithmetic AddOp [v 2; k 1]);
         CaptureBindingStmt (AstId 10) (AstId 2);
         WriteScalarStmt (AstId 10) u256 (v 9);
         DefineStmt (AstId 11) (SingleType BoolT)
           (ScalarOperation u256 UncheckedArithmetic EqualOp [v 9; k 3]);
         IfStmt (v 11) [BreakStmt] []]]
  |>
End

(* nested(n) returns (s): i = 0; while (i < n) { i += 1; j = 0;
 * while (j < n) { j += 1; if (j == i) continue; if (i < j) break; s += j; } }
 * The inner break and continue leave the outer loop running.
 *)
Definition nested_proc_def:
  nested_proc = <|
    procedure_id := AstId 7;
    parameters := [(AstId 1, u256)];
    return_bindings := [(AstId 2, u256)];
    body := [
      DefineStmt (AstId 3) (SingleType u256) (ConvertOperation u256 (k 0));
      WhileStmt
        [DefineStmt (AstId 4) (SingleType BoolT)
           (ScalarOperation u256 UncheckedArithmetic LessThanOp [v 3; v 1])]
        (v 4)
        [DefineStmt (AstId 5) (SingleType u256)
           (ScalarOperation u256 CheckedArithmetic AddOp [v 3; k 1]);
         CaptureBindingStmt (AstId 6) (AstId 3);
         WriteScalarStmt (AstId 6) u256 (v 5);
         DefineStmt (AstId 7) (SingleType u256) (ConvertOperation u256 (k 0));
         WhileStmt
           [DefineStmt (AstId 8) (SingleType BoolT)
              (ScalarOperation u256 UncheckedArithmetic LessThanOp [v 7; v 1])]
           (v 8)
           [DefineStmt (AstId 9) (SingleType u256)
              (ScalarOperation u256 CheckedArithmetic AddOp [v 7; k 1]);
            CaptureBindingStmt (AstId 10) (AstId 7);
            WriteScalarStmt (AstId 10) u256 (v 9);
            DefineStmt (AstId 11) (SingleType BoolT)
              (ScalarOperation u256 UncheckedArithmetic EqualOp [v 9; v 3]);
            IfStmt (v 11) [ContinueStmt] [];
            DefineStmt (AstId 12) (SingleType BoolT)
              (ScalarOperation u256 UncheckedArithmetic LessThanOp [v 3; v 9]);
            IfStmt (v 12) [BreakStmt] [];
            DefineStmt (AstId 13) (SingleType u256)
              (ScalarOperation u256 CheckedArithmetic AddOp [v 2; v 9]);
            CaptureBindingStmt (AstId 14) (AstId 2);
            WriteScalarStmt (AstId 14) u256 (v 13)]]]
  |>
End

Definition fact_proc_def:
  fact_proc = <|
    procedure_id := AstId 8;
    parameters := [(AstId 1, u256)];
    return_bindings := [(AstId 2, u256)];
    body := [
      DefineStmt (AstId 3) (SingleType BoolT)
        (ScalarOperation u256 UncheckedArithmetic EqualOp [v 1; k 0]);
      IfStmt (v 3)
        [ReturnStmt [k 1]]
        [DefineStmt (AstId 4) (SingleType u256)
           (ScalarOperation u256 CheckedArithmetic SubtractOp [v 1; k 1]);
         DefineStmt (AstId 5) (SingleType u256)
           (InternalCallOperation (AstId 8) [v 4]);
         DefineStmt (AstId 6) (SingleType u256)
           (ScalarOperation u256 CheckedArithmetic MultiplyOp [v 1; v 5]);
         ReturnStmt [v 6]]]
  |>
End

(* Two sibling recursive calls, which share the caller's fuel. *)
Definition fib_proc_def:
  fib_proc = <|
    procedure_id := AstId 9;
    parameters := [(AstId 1, u256)];
    return_bindings := [(AstId 2, u256)];
    body := [
      DefineStmt (AstId 3) (SingleType BoolT)
        (ScalarOperation u256 UncheckedArithmetic LessThanOp [v 1; k 2]);
      IfStmt (v 3)
        [ReturnStmt [v 1]]
        [DefineStmt (AstId 4) (SingleType u256)
           (ScalarOperation u256 CheckedArithmetic SubtractOp [v 1; k 1]);
         DefineStmt (AstId 5) (SingleType u256)
           (InternalCallOperation (AstId 9) [v 4]);
         DefineStmt (AstId 6) (SingleType u256)
           (ScalarOperation u256 CheckedArithmetic SubtractOp [v 1; k 2]);
         DefineStmt (AstId 7) (SingleType u256)
           (InternalCallOperation (AstId 9) [v 6]);
         DefineStmt (AstId 8) (SingleType u256)
           (ScalarOperation u256 CheckedArithmetic AddOp [v 5; v 7]);
         ReturnStmt [v 8]]]
  |>
End

Definition divmod_proc_def:
  divmod_proc = <|
    procedure_id := AstId 10;
    parameters := [(AstId 1, u256); (AstId 2, u256)];
    return_bindings := [(AstId 3, u256); (AstId 4, u256)];
    body := [
      DefineStmt (AstId 5) (SingleType u256)
        (ScalarOperation u256 CheckedArithmetic DivideOp [v 1; v 2]);
      DefineStmt (AstId 6) (SingleType u256)
        (ScalarOperation u256 CheckedArithmetic RemainderOp [v 1; v 2]);
      ReturnStmt [v 5; v 6]]
  |>
End

(* swap() returns (a, b): (a, b) = divmod(17, 5); (a, b) = (b, a);
 * falling through to the return bindings.
 *)
Definition swap_proc_def:
  swap_proc = <|
    procedure_id := AstId 11;
    parameters := [];
    return_bindings := [(AstId 1, u256); (AstId 2, u256)];
    body := [
      DefineStmt (AstId 3) (ProductType [SingleType u256; SingleType u256])
        (InternalCallOperation (AstId 10) [k 17; k 5]);
      DefineStmt (AstId 4) (SingleType u256) (TupleComponentOperation 0 (v 3));
      DefineStmt (AstId 5) (SingleType u256) (TupleComponentOperation 1 (v 3));
      CaptureBindingStmt (AstId 6) (AstId 1);
      WriteScalarStmt (AstId 6) u256 (v 4);
      CaptureBindingStmt (AstId 7) (AstId 2);
      WriteScalarStmt (AstId 7) u256 (v 5);
      DefineStmt (AstId 8) (ProductType [SingleType u256; SingleType u256])
        (TupleOperation [v 2; v 1]);
      DefineStmt (AstId 9) (SingleType u256) (TupleComponentOperation 0 (v 8));
      DefineStmt (AstId 10) (SingleType u256) (TupleComponentOperation 1 (v 8));
      WriteScalarStmt (AstId 6) u256 (v 9);
      WriteScalarStmt (AstId 7) u256 (v 10)]
  |>
End

(* spin() returns (c): while (true) { unchecked { c += 1; } } *)
Definition spin_proc_def:
  spin_proc = <|
    procedure_id := AstId 12;
    parameters := [];
    return_bindings := [(AstId 1, u256)];
    body := [
      WhileStmt [] (ConstantAtom (BoolValue T))
        [DefineStmt (AstId 2) (SingleType u256)
           (ScalarOperation u256 UncheckedArithmetic AddOp [v 1; k 1]);
         CaptureBindingStmt (AstId 3) (AstId 1);
         WriteScalarStmt (AstId 3) u256 (v 2)]]
  |>
End

(* deep(n) returns (r): r = deep(n + 1), unbounded recursion. *)
Definition deep_proc_def:
  deep_proc = <|
    procedure_id := AstId 13;
    parameters := [(AstId 1, u256)];
    return_bindings := [(AstId 2, u256)];
    body := [
      DefineStmt (AstId 3) (SingleType u256)
        (ScalarOperation u256 CheckedArithmetic AddOp [v 1; k 1]);
      DefineStmt (AstId 4) (SingleType u256)
        (InternalCallOperation (AstId 13) [v 3]);
      ReturnStmt [v 4]]
  |>
End

(* inner(x) reverts with 0xdead when x == 0; middle(x) = inner(x) + 1;
 * outer(x) = middle(x) * 2.
 *)
Definition inner_proc_def:
  inner_proc = <|
    procedure_id := AstId 14;
    parameters := [(AstId 1, u256)];
    return_bindings := [(AstId 2, u256)];
    body := [
      DefineStmt (AstId 3) (SingleType BoolT)
        (ScalarOperation u256 UncheckedArithmetic EqualOp [v 1; k 0]);
      IfStmt (v 3) [RevertStmt (ConstantAtom (BytesValue [0xdew; 0xadw]))] [];
      ReturnStmt [v 1]]
  |>
End

Definition middle_proc_def:
  middle_proc = <|
    procedure_id := AstId 15;
    parameters := [(AstId 1, u256)];
    return_bindings := [(AstId 2, u256)];
    body := [
      DefineStmt (AstId 3) (SingleType u256)
        (InternalCallOperation (AstId 14) [v 1]);
      DefineStmt (AstId 4) (SingleType u256)
        (ScalarOperation u256 CheckedArithmetic AddOp [v 3; k 1]);
      ReturnStmt [v 4]]
  |>
End

Definition outer_proc_def:
  outer_proc = <|
    procedure_id := AstId 16;
    parameters := [(AstId 1, u256)];
    return_bindings := [(AstId 2, u256)];
    body := [
      DefineStmt (AstId 3) (SingleType u256)
        (InternalCallOperation (AstId 15) [v 1]);
      DefineStmt (AstId 4) (SingleType u256)
        (ScalarOperation u256 CheckedArithmetic MultiplyOp [v 3; k 2]);
      ReturnStmt [v 4]]
  |>
End

Definition programs_def:
  programs = <|
    procedures := [
      binop_proc 1 u8 CheckedArithmetic AddOp;
      binop_proc 2 u8 UncheckedArithmetic AddOp;
      binop_proc 3 u256 CheckedArithmetic SubtractOp;
      binop_proc 4 u256 UncheckedArithmetic SubtractOp;
      binop_proc 5 u256 UncheckedArithmetic DivideOp;
      count_proc; nested_proc; fact_proc; fib_proc; divmod_proc; swap_proc;
      spin_proc; deep_proc; inner_proc; middle_proc; outer_proc];
    struct_layouts := []; type_declarations := [];
    state_variables := [];
    entry_procedure := AstId 16;
    external_functions := []; receive_procedure := NONE;
    fallback_procedure := NONE; creation_procedure := NONE
  |>
End

Definition programs_env_def:
  programs_env = core_program_environment programs
End

Theorem programs_wf:
  wf_core_program programs_env programs
Proof
  EVAL_TAC
QED

Definition programs_state_def:
  programs_state = <|
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

(* The completion of procedure f called on integer arguments. *)
Definition run_program_def:
  run_program fuel f args =
    (invoke_source fuel programs_env (AstId f) (MAP iv args) programs_state
       []).completion
End

val () = cv_auto_trans run_program_def;

(* Checked and unchecked arithmetic *)

Theorem checked_add_overflow_panics:
  run_program 10 1 [200; 100] = PanicCompletion 0x11
Proof
  CONV_TAC cv_eval
QED

Theorem unchecked_add_wraps:
  run_program 10 2 [200; 100] = ReturnCompletion [iv 44]
Proof
  CONV_TAC cv_eval
QED

Theorem checked_sub_underflow_panics:
  run_program 10 3 [0; 1] = PanicCompletion 0x11
Proof
  CONV_TAC cv_eval
QED

Theorem unchecked_sub_wraps:
  run_program 10 4 [0; 1] = ReturnCompletion [iv (&(2 ** 256) - 1)]
Proof
  CONV_TAC cv_eval
QED

Theorem unchecked_division_by_zero_panics:
  run_program 10 5 [7; 0] = PanicCompletion 0x12
Proof
  CONV_TAC cv_eval
QED

Theorem unchecked_division:
  run_program 10 5 [7; 2] = ReturnCompletion [iv 3]
Proof
  CONV_TAC cv_eval
QED

(* Loops *)

Theorem loop_prelude_continue_exit:
  run_program 10 6 [5] = ReturnCompletion [iv 2; iv 5]
Proof
  CONV_TAC cv_eval
QED

Theorem loop_break:
  run_program 10 6 [100] = ReturnCompletion [iv 3; iv 6]
Proof
  CONV_TAC cv_eval
QED

Theorem nested_loops:
  run_program 10 7 [4] = ReturnCompletion [iv 10]
Proof
  CONV_TAC cv_eval
QED

(* Recursion, multiple returns and tuple assignment *)

Theorem factorial:
  run_program 25 8 [20] = ReturnCompletion [iv 2432902008176640000]
Proof
  CONV_TAC cv_eval
QED

Theorem fibonacci:
  run_program 15 9 [10] = ReturnCompletion [iv 55]
Proof
  CONV_TAC cv_eval
QED

Theorem multiple_returns:
  run_program 10 10 [17; 5] = ReturnCompletion [iv 3; iv 2]
Proof
  CONV_TAC cv_eval
QED

Theorem tuple_assignment:
  run_program 10 11 [] = ReturnCompletion [iv 2; iv 3]
Proof
  CONV_TAC cv_eval
QED

(* Fuel exhaustion *)

Theorem nonterminating_loop_exhausts_fuel:
  run_program 50 12 [] = FuelExhausted
Proof
  CONV_TAC cv_eval
QED

Theorem unbounded_recursion_exhausts_fuel:
  run_program 50 13 [0] = FuelExhausted
Proof
  CONV_TAC cv_eval
QED

Theorem deep_recursion_exhausts_fuel:
  run_program 5 8 [20] = FuelExhausted
Proof
  CONV_TAC cv_eval
QED

(* Reverts *)

Theorem revert_through_nested_calls:
  run_program 10 16 [0] = RevertCompletion [0xdew; 0xadw]
Proof
  CONV_TAC cv_eval
QED

Theorem nested_calls_return:
  run_program 10 16 [5] = ReturnCompletion [iv 12]
Proof
  CONV_TAC cv_eval
QED
