(* testdata/frontend/pure_core.sol through import, elaboration, the core
 * checker and the evaluator. Expected results are worked out from the
 * language definition; solidityDifferentialTest compares them against the
 * compiled bytecode.
 *)
Theory solidityElaborateTest
Ancestors
  solidityElaborate solidityImportTest
Libs
  cv_transLib intLib wordsLib

val elaborated = cv_eval “elaborate_unit pure_core”;

Definition pure_core_program_def:
  pure_core_program = ^(elaborated |> concl |> rhs |> optionSyntax.dest_some)
End

val () = cv_auto_trans pure_core_program_def;

Theorem pure_core_elaborates:
  elaborate_unit pure_core = SOME pure_core_program
Proof
  simp[elaborated, pure_core_program_def]
QED

Theorem pure_core_program_wf:
  wf_core_program (core_program_environment pure_core_program)
    pure_core_program
Proof
  EVAL_TAC
QED

Overload iv = “λi. ScalarValue (IntegerValue i)”
Overload bv = “λb. ScalarValue (BoolValue b)”

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

(* The procedure of a function of the fixture, by name. *)
Definition function_id_def:
  function_id name =
    case pure_core.unit_contracts of
      c :: _ =>
        (case FILTER (λf. f.fn_name = name) c.contract_functions of
           f :: _ => AstId f.fn_info.node_id
         | [] => AstId 0)
    | [] => AstId 0
End

Definition run_function_def:
  run_function fuel name args =
    (invoke_source fuel (core_program_environment pure_core_program)
       (function_id name) (MAP iv args) initial_state []).completion
End

val () = cv_auto_trans run_function_def;

Theorem add_returns:
  run_function 50 "add" [2; 3] = ReturnCompletion [iv 5]
Proof
  CONV_TAC cv_eval
QED

Theorem add_overflow_panics:
  run_function 50 "add" [200; 100] = PanicCompletion 0x11
Proof
  CONV_TAC cv_eval
QED

Theorem unchecked_add_wraps:
  run_function 50 "wrappingAdd" [200; 100] = ReturnCompletion [iv 44]
Proof
  CONV_TAC cv_eval
QED

Theorem while_prelude_continue_exit:
  run_function 50 "count" [5] = ReturnCompletion [iv 2; iv 5]
Proof
  CONV_TAC cv_eval
QED

Theorem while_break:
  run_function 50 "count" [100] = ReturnCompletion [iv 3; iv 6]
Proof
  CONV_TAC cv_eval
QED

(* The for loop skips 2 by continue, which still runs i++. *)
Theorem for_continue_increments:
  run_function 50 "sum" [5] = ReturnCompletion [iv 8]
Proof
  CONV_TAC cv_eval
QED

Theorem do_while_runs_once:
  run_function 50 "doubleUntil" [0] = ReturnCompletion [iv 2]
Proof
  CONV_TAC cv_eval
QED

Theorem do_while_loops:
  run_function 50 "doubleUntil" [7] = ReturnCompletion [iv 8]
Proof
  CONV_TAC cv_eval
QED

Theorem recursion:
  run_function 50 "fact" [5] = ReturnCompletion [iv 120]
Proof
  CONV_TAC cv_eval
QED

Theorem multiple_returns:
  run_function 50 "divmod" [17; 5] = ReturnCompletion [iv 3; iv 2]
Proof
  CONV_TAC cv_eval
QED

Theorem division_by_zero_panics:
  run_function 50 "divmod" [1; 0] = PanicCompletion 0x12
Proof
  CONV_TAC cv_eval
QED

Theorem tuple_assignment:
  run_function 50 "swap" [] = ReturnCompletion [iv 2; iv 3]
Proof
  CONV_TAC cv_eval
QED

Theorem locals_and_tuple_declarations:
  run_function 50 "locals" [10] = ReturnCompletion [iv 10]
Proof
  CONV_TAC cv_eval
QED

Theorem narrowing_conversion:
  run_function 50 "narrow" [300] = ReturnCompletion [iv 44; bv F]
Proof
  CONV_TAC cv_eval
QED

Theorem negate_overflow_panics:
  run_function 50 "negate" [-128] = PanicCompletion 0x11
Proof
  CONV_TAC cv_eval
QED

Theorem negate_returns:
  run_function 50 "negate" [5] = ReturnCompletion [iv (-5)]
Proof
  CONV_TAC cv_eval
QED

Theorem and_skips_division:
  run_function 50 "guardedDivide" [0] = ReturnCompletion [bv F]
Proof
  CONV_TAC cv_eval
QED

Theorem and_evaluates_division:
  run_function 50 "guardedDivide" [5] = ReturnCompletion [bv T]
Proof
  CONV_TAC cv_eval
QED

Theorem and_division_panics:
  run_function 50 "badDivide" [0] = PanicCompletion 0x12
Proof
  CONV_TAC cv_eval
QED

Theorem or_skips_increment:
  run_function 50 "shortCircuit" [10] = ReturnCompletion [bv T; iv 0]
Proof
  CONV_TAC cv_eval
QED

Theorem or_runs_increment:
  run_function 50 "shortCircuit" [1] = ReturnCompletion [bv T; iv 1]
Proof
  CONV_TAC cv_eval
QED

Theorem left_operand_panics_first:
  run_function 50 "panicOrder" [0] = PanicCompletion 0x11
Proof
  CONV_TAC cv_eval
QED

Theorem left_argument_panics_first:
  run_function 50 "argumentOrder" [0] = PanicCompletion 0x11
Proof
  CONV_TAC cv_eval
QED

Theorem compound_assignment_reads_after_rhs:
  run_function 50 "compoundOrder" [1] = ReturnCompletion [iv 10]
Proof
  CONV_TAC cv_eval
QED

Definition missing_struct_layout_unit_def:
  missing_struct_layout_unit =
    case struct_unit.unit_contracts of
      c :: cs =>
        (case c.contract_structs of
           s :: ss => struct_unit with unit_contracts :=
             (c with contract_structs := (s with struct_layout := NONE) :: ss) :: cs
         | [] => struct_unit)
    | [] => struct_unit
End
val () = cv_auto_trans missing_struct_layout_unit_def;

Theorem struct_layout_required_for_execution:
  IS_SOME (elaborate_unit struct_unit) ∧
  valid_src_unit missing_struct_layout_unit ∧
  case elaborate_unit missing_struct_layout_unit of
    SOME p => ¬wf_core_program (core_program_environment p) p
  | NONE => F
Proof
  rpt conj_tac >- CONV_TAC cv_eval >- CONV_TAC cv_eval >>
  CONV_TAC cv_eval
QED

(* A block a constructor runs may not halt, since the source installs no
 * runtime code from the returned bytes; elsewhere it may. *)
Theorem asm_halt_rejected_in_constructor:
  ∀info.
    ISL (elab_stmt
      <| functions := []; supers := []; structs := []; enums := []; events := [];
         variables := []; state := []; locations := []; immutables := [];
         constants := []; returns := []; placeholder := NONE;
         mode := CheckedArithmetic; creation := F; scope := 0;
         returns_id := 0; in_loop := F; bad_ids := [] |> 0
      (SrcInlineAssembly info [YulExprStmt (YulBuiltin YStop [])] [])) ∧
    elab_stmt
      <| functions := []; supers := []; structs := []; enums := []; events := [];
         variables := []; state := []; locations := []; immutables := [];
         constants := []; returns := []; placeholder := NONE;
         mode := CheckedArithmetic; creation := T; scope := 0;
         returns_id := 0; in_loop := F; bad_ids := [] |> 0
      (SrcInlineAssembly info [YulExprStmt (YulBuiltin YStop [])] []) =
    INR [(info.node_id, "assembly halt in a constructor")]
Proof
  gen_tac >> EVAL_TAC
QED

Theorem no_exponent_assignment:
  compound_operator (SOME SrcExp) = NONE ∧
  compound_operator (SOME SrcAdd) = SOME AddOp
Proof
  EVAL_TAC
QED

(* Statements the compiler does not produce: a declaration as the body of an
 * if or a loop (it must be a statement of a block), and a fractional literal
 * in a tuple, even at a hole. *)
Theorem declaration_body_and_tuple_fraction_rejected:
  let info = <| node_id := 0;
                node_location := <| loc_start := 0; loc_length := 0;
                                    loc_source := 0 |> |>;
      x = <| var_info := info with node_id := 1; var_name := "x"; var_scope := 0;
             var_type_name := SrcElementaryTypeName info "uint256" NONE;
             var_type_id := "t_uint256"; var_location := NONE |>;
      d = SrcVariableDeclarationStatement info [SOME 1] [SOME x] NONE;
      c = SrcLiteral info BoolLiteral "true" "t_bool";
      half = SrcLiteral info NumberLiteral "" "t_rational_1_by_2";
      ctx = <| functions := []; supers := []; structs := []; enums := [];
               events := []; variables := []; state := []; locations := [];
               immutables := []; constants := []; returns := [];
               placeholder := NONE; mode := CheckedArithmetic; creation := F;
               scope := 0; returns_id := 0; in_loop := F; bad_ids := [] |> in
    ISL (elab_stmt ctx 2 d) ∧
    elab_stmt ctx 2 (SrcIfStatement info c d NONE) = INR [(0, "declaration as a body")] ∧
    elab_stmt ctx 2 (SrcWhileStatement info c d) = INR [(0, "declaration as a body")] ∧
    elab_stmt ctx 2 (SrcVariableDeclarationStatement info [NONE] [NONE] (SOME half)) =
    INR [(0, "rational number value")]
Proof
  EVAL_TAC
QED

(* Rejection reasons: a list of statements reports every statement that
 * fails, and a statement after a failed declaration only its own blockers.
 * The declared variable is bound if its type is supported, and otherwise
 * a reference to it adds no blocker, the declaration having reported it. *)
val info0 = “<| node_id := 0;
                node_location := <| loc_start := 0; loc_length := 0;
                                    loc_source := 0 |> |>”;
fun at id = “^info0 with node_id := ^(numSyntax.term_of_int id)”;
val ctx0 = “<| functions := []; supers := []; structs := []; enums := [];
               events := []; variables := []; state := []; locations := [];
               immutables := []; constants := []; returns := [];
               placeholder := NONE; mode := CheckedArithmetic; creation := F;
               scope := 0; returns_id := 0; in_loop := F; bad_ids := [] |>”;
fun local_y tn = “<| var_info := ^(at 4); var_name := "y"; var_scope := 0;
                     var_type_name := ^tn; var_type_id := "t_uint256";
                     var_location := NONE |>”;
val supported_y = local_y “SrcElementaryTypeName ^(at 7) "uint256" NONE”;
val unsupported_y = local_y “SrcUnsupportedTypeName ^(at 7) "function type"”;
val read_y = “SrcExpressionStatement ^(at 5) (SrcIdentifier ^(at 6) "y" 4 "t_uint256")”;

Theorem independent_failures_all_report:
  elab_stmts ^ctx0 10 [SrcBreak ^(at 1); SrcContinue ^(at 2)] =
  INR [(1, "break outside a loop"); (2, "continue outside a loop")]
Proof
  EVAL_TAC
QED

Theorem failed_declaration_reference_adds_no_blocker:
  elab_stmts ^ctx0 10
    [SrcVariableDeclarationStatement ^(at 3) [SOME 4] [SOME ^unsupported_y]
       (SOME (SrcLiteral ^(at 8) NumberLiteral "1" "t_rational_1_by_1"));
     ^read_y] =
  INR [(7, "function type")] ∧
  elab_stmts ^ctx0 10
    [SrcVariableDeclarationStatement ^(at 3) [SOME 4] [SOME ^supported_y]
       (SOME (SrcLiteral ^(at 8) NumberLiteral "" "t_rational_1_by_2"));
     ^read_y] =
  INR [(8, "rational number value")]
Proof
  EVAL_TAC
QED

(* A function whose parameter or return variable fails still reports its
 * body's blockers; a reference to the failed parameter, or a return of a
 * value for the failed return variable, adds none. *)
val empty_contract =
  “<| contract_info := ^info0; contract_name := "C"; contract_scope := 0;
      contract_bases := []; contract_state_variables := [];
      contract_immutables := []; contract_initializers := [];
      contract_libraries := []; contract_constants := [];
      contract_base_arguments := []; contract_storage := [];
      contract_structs := []; contract_enums := []; contract_events := [];
      contract_modifiers := []; contract_functions := [];
      contract_library_functions := []; contract_getters := [] |>”;
fun function_of ps rs ss =
  “<| fn_info := ^(at 1); fn_name := "f"; fn_scope := 0;
      fn_kind := FunctionKind; fn_visibility := InternalVisibility;
      fn_mutability := NonpayableMut; fn_selector := NONE;
      fn_base_functions := []; fn_parameters_id := 2; fn_parameters := ^ps;
      fn_returns_id := 3; fn_returns := ^rs; fn_modifiers := [];
      fn_super_calls := []; fn_body := SrcBlock ^(at 9) ^ss;
      fn_unsupported := NONE |>”;
val break_11 = “SrcBreak ^(at 11)”;
val return_1 = “SrcReturn ^(at 12) 3
                  (SOME (SrcLiteral ^(at 13) NumberLiteral "1" "t_rational_1_by_1"))”;

val failed_parameter = function_of “[^unsupported_y]” “[] : src_variable list” “[^read_y; ^break_11]”;
val failed_return = function_of “[] : src_variable list” “[^unsupported_y]” “[^return_1; ^break_11]”;

Theorem failed_variables_keep_body_blockers:
  elab_function ^ctx0 ^empty_contract T F 10 ^failed_parameter =
  INR [(7, "function type"); (11, "break outside a loop")] ∧
  elab_function ^ctx0 ^empty_contract T F 10 ^failed_return =
  INR [(7, "function type"); (11, "break outside a loop")]
Proof
  EVAL_TAC
QED

(* A try statement of a call that elaborates but is not an external call
 * still reports both clauses' blockers. *)
Theorem unsupported_try_keeps_clause_blockers:
  elab_stmt ^ctx0 10
    (SrcTryStatement ^(at 19) (SrcLiteral ^(at 20) BoolLiteral "true" "t_bool")
       ^(at 21) [] (SrcBreak ^(at 11)) ^(at 22) ^supported_y (SrcContinue ^(at 12))) =
  INR [(19, "unsupported try statement"); (11, "break outside a loop");
       (12, "continue outside a loop")]
Proof
  EVAL_TAC
QED

(* The unit elaborates, so nothing in it fails. *)
Theorem pure_core_has_no_failures:
  unit_elaboration_failures T pure_core = []
Proof
  CONV_TAC cv_eval
QED

(* Edited units of solidityImportTest that pass valid_src_unit but whose
 * edited function fails elaboration, which checks it against the compiler's
 * annotations: preparation marks it unsupported. *)

(* an identifier naming no declaration *)
Theorem dangling_reference_fails_elaboration:
  unit_elaboration_failures T dangling_reference ≠ []
Proof
  CONV_TAC cv_eval
QED

(* an identifier annotated with another type than its variable's *)
Theorem identifier_type_mismatch_fails_elaboration:
  unit_elaboration_failures T identifier_type_mismatch ≠ []
Proof
  CONV_TAC cv_eval
QED

(* a comparison annotated with another type than bool *)
Theorem comparison_type_mismatch_fails_elaboration:
  unit_elaboration_failures T comparison_type_mismatch ≠ []
Proof
  CONV_TAC cv_eval
QED

(* a function used as a value *)
Theorem function_as_value_fails_elaboration:
  unit_elaboration_failures T function_as_value ≠ []
Proof
  CONV_TAC cv_eval
QED

(* a declaration statement whose assignments do not list its declaration *)
Theorem unlinked_declaration_fails_elaboration:
  unit_elaboration_failures T unlinked_declaration ≠ []
Proof
  CONV_TAC cv_eval
QED

(* a call with fewer arguments than parameters *)
Theorem call_arity_fails_elaboration:
  unit_elaboration_failures T call_arity ≠ []
Proof
  CONV_TAC cv_eval
QED

(* a pure function using a state variable *)
Theorem pure_writes_state_fails_elaboration:
  unit_elaboration_failures T pure_writes_state ≠ []
Proof
  CONV_TAC cv_eval
QED

(* a mapping read annotated with another value type *)
Theorem mapping_leaf_metadata_mismatch_fails_elaboration:
  unit_elaboration_failures T mapping_leaf_metadata_mismatch ≠ []
Proof
  CONV_TAC cv_eval
QED

(* an array read annotated with another element type *)
Theorem array_leaf_mismatch_fails_elaboration:
  unit_elaboration_failures T array_leaf_mismatch ≠ []
Proof
  CONV_TAC cv_eval
QED

(* a require message that is not a literal *)
Theorem nonliteral_builtin_message_fails_elaboration:
  unit_elaboration_failures T nonliteral_builtin_message ≠ []
Proof
  CONV_TAC cv_eval
QED

(* a struct member naming no member *)
Theorem struct_field_identity_mismatch_fails_elaboration:
  unit_elaboration_failures T struct_field_identity_mismatch ≠ []
Proof
  CONV_TAC cv_eval
QED

(* a struct member annotated with another type *)
Theorem struct_field_type_mismatch_fails_elaboration:
  unit_elaboration_failures T struct_field_type_mismatch ≠ []
Proof
  CONV_TAC cv_eval
QED

(* a call reaching no implemented function *)
Theorem unresolved_override_fails_elaboration:
  unit_elaboration_failures T unresolved_override ≠ []
Proof
  CONV_TAC cv_eval
QED

(* a conditional over storage references *)
Theorem storage_conditional_fails_elaboration:
  unit_elaboration_failures T storage_conditional ≠ []
Proof
  CONV_TAC cv_eval
QED

(* a conditional over stored bytes *)
Theorem stored_bytes_conditional_fails_elaboration:
  unit_elaboration_failures T stored_bytes_conditional ≠ []
Proof
  CONV_TAC cv_eval
QED

(* a conditional over tuples *)
Theorem tuple_conditional_fails_elaboration:
  unit_elaboration_failures T tuple_conditional ≠ []
Proof
  CONV_TAC cv_eval
QED

(* a conditional over calldata references *)
Theorem calldata_conditional_fails_elaboration:
  unit_elaboration_failures T calldata_conditional ≠ []
Proof
  CONV_TAC cv_eval
QED

(* a conditional over functions *)
Theorem function_conditional_fails_elaboration:
  unit_elaboration_failures T function_conditional ≠ []
Proof
  CONV_TAC cv_eval
QED
