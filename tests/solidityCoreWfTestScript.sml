(* Positive and negative well-formedness witnesses. *)
Theory solidityCoreWfTest
Ancestors
  solidityCoreWf
Libs
  intLib wordsLib cv_transLib

Overload u256 = “UintT 256”

Definition test_decls_def:
  test_decls = [(AstId 900, EnumDeclaration 3);
                (AstId 901, UserValueDeclaration (UintT 160))]
End

(* add(x, y) returns (r): r := x + y (checked). *)
Definition add_proc_def:
  add_proc = <|
    procedure_id := AstId 1;
    parameters := [(AstId 10, u256); (AstId 11, u256)];
    return_bindings := [(AstId 12, u256)];
    body := [
      DefineStmt (AstId 13) (SingleType u256)
        (ScalarOperation u256 CheckedArithmetic AddOp
           [BoundAtom (AstId 10); BoundAtom (AstId 11)]);
      ReturnStmt [BoundAtom (AstId 13)]
    ]
  |>
End

(* count(n): effectful condition prelude, capture/write, break/continue. *)
Definition count_proc_def:
  count_proc = <|
    procedure_id := AstId 2;
    parameters := [(AstId 20, u256)];
    return_bindings := [(AstId 21, u256)];
    body := [
      DefineStmt (AstId 22) (SingleType u256)
        (ConvertOperation u256 (ConstantAtom (IntegerValue 0)));
      WhileStmt
        [DefineStmt (AstId 23) (SingleType BoolT)
           (ScalarOperation u256 UncheckedArithmetic LessThanOp
              [BoundAtom (AstId 22); BoundAtom (AstId 20)])]
        (BoundAtom (AstId 23))
        [DefineStmt (AstId 24) (SingleType u256)
           (ScalarOperation u256 CheckedArithmetic AddOp
              [BoundAtom (AstId 22); ConstantAtom (IntegerValue 1)]);
         CaptureBindingStmt (AstId 25) (AstId 22);
         WriteScalarStmt (AstId 25) u256 (BoundAtom (AstId 24));
         DefineStmt (AstId 26) (SingleType BoolT)
           (ScalarOperation u256 UncheckedArithmetic EqualOp
              [BoundAtom (AstId 24); ConstantAtom (IntegerValue 10)]);
         IfStmt (BoundAtom (AstId 26)) [BreakStmt] [ContinueStmt]];
      ReturnStmt [BoundAtom (AstId 22)]
    ]
  |>
End

(* pair() returns (uint256, bool). *)
Definition pair_proc_def:
  pair_proc = <|
    procedure_id := AstId 3;
    parameters := [];
    return_bindings := [(AstId 30, u256); (AstId 31, BoolT)];
    body := [ReturnStmt [ConstantAtom (IntegerValue 7);
                         ConstantAtom (BoolValue T)]]
  |>
End

(* first(): destructure a multiple-return call; enum constant in range. *)
Definition first_proc_def:
  first_proc = <|
    procedure_id := AstId 4;
    parameters := [];
    return_bindings := [(AstId 40, u256)];
    body := [
      DefineStmt (AstId 41) (ProductType [SingleType u256; SingleType BoolT])
        (InternalCallOperation (AstId 3) []);
      DefineStmt (AstId 42) (SingleType u256)
        (TupleComponentOperation 0 (BoundAtom (AstId 41)));
      DefineStmt (AstId 43) (SingleType (EnumT (AstId 900)))
        (ConvertOperation (EnumT (AstId 900)) (ConstantAtom (IntegerValue 2)));
      ReturnStmt [BoundAtom (AstId 42)]
    ]
  |>
End

(* fact(n): recursive internal call. *)
Definition fact_proc_def:
  fact_proc = <|
    procedure_id := AstId 5;
    parameters := [(AstId 50, u256)];
    return_bindings := [(AstId 51, u256)];
    body := [
      DefineStmt (AstId 52) (SingleType BoolT)
        (ScalarOperation u256 UncheckedArithmetic EqualOp
           [BoundAtom (AstId 50); ConstantAtom (IntegerValue 0)]);
      IfStmt (BoundAtom (AstId 52))
        [ReturnStmt [ConstantAtom (IntegerValue 1)]]
        [DefineStmt (AstId 53) (SingleType u256)
           (ScalarOperation u256 CheckedArithmetic SubtractOp
              [BoundAtom (AstId 50); ConstantAtom (IntegerValue 1)]);
         DefineStmt (AstId 54) (SingleType u256)
           (InternalCallOperation (AstId 5) [BoundAtom (AstId 53)]);
         DefineStmt (AstId 55) (SingleType u256)
           (ScalarOperation u256 CheckedArithmetic MultiplyOp
              [BoundAtom (AstId 50); BoundAtom (AstId 54)]);
         ReturnStmt [BoundAtom (AstId 55)]]
    ]
  |>
End

(* Modifier-style wrapper: placeholder call, write own return binding,
 * postlude void call, then `return;` lowered to the return bindings.
 *)
Definition wrapper_proc_def:
  wrapper_proc = <|
    procedure_id := AstId 6;
    parameters := [];
    return_bindings := [(AstId 60, u256)];
    body := [
      DefineStmt (AstId 61) (SingleType u256)
        (InternalCallOperation (AstId 1)
           [ConstantAtom (IntegerValue 1); ConstantAtom (IntegerValue 2)]);
      CaptureBindingStmt (AstId 62) (AstId 60);
      WriteScalarStmt (AstId 62) u256 (BoundAtom (AstId 61));
      DefineStmt (AstId 63) (ProductType []) (InternalCallOperation (AstId 7) []);
      ReturnStmt [BoundAtom (AstId 60)]
    ]
  |>
End

Definition void_proc_def:
  void_proc = <|
    procedure_id := AstId 7;
    parameters := [];
    return_bindings := [];
    body := [RevertStmt (ConstantAtom (BytesValue []))]
  |>
End

(* convert(a, p): widening, payable address to integer via address, user
 * value type wrap and unwrap, signed integer to enum.
 *)
Definition convert_proc_def:
  convert_proc = <|
    procedure_id := AstId 9;
    parameters := [(AstId 90, UintT 8); (AstId 91, AddressT PayableAddress)];
    return_bindings := [(AstId 92, u256)];
    body := [
      DefineStmt (AstId 93) (SingleType u256)
        (ConvertOperation u256 (BoundAtom (AstId 90)));
      DefineStmt (AstId 94) (SingleType (AddressT NonpayableAddress))
        (ConvertOperation (AddressT NonpayableAddress) (BoundAtom (AstId 91)));
      DefineStmt (AstId 95) (SingleType (UintT 160))
        (ConvertOperation (UintT 160) (BoundAtom (AstId 94)));
      DefineStmt (AstId 96) (SingleType (UserValueT (AstId 901)))
        (ConvertOperation (UserValueT (AstId 901)) (BoundAtom (AstId 95)));
      DefineStmt (AstId 97) (SingleType (UintT 160))
        (ConvertOperation (UintT 160) (BoundAtom (AstId 96)));
      DefineStmt (AstId 98) (SingleType (IntT 8))
        (ConvertOperation (IntT 8) (ConstantAtom (IntegerValue (-1))));
      DefineStmt (AstId 99) (SingleType (EnumT (AstId 900)))
        (ConvertOperation (EnumT (AstId 900)) (BoundAtom (AstId 98)));
      ReturnStmt [BoundAtom (AstId 93)]
    ]
  |>
End

(* scope(n): a prelude binding used in the loop body; tuple construction and
 * projection.
 *)
Definition scope_proc_def:
  scope_proc = <|
    procedure_id := AstId 110;
    parameters := [(AstId 111, u256)];
    return_bindings := [(AstId 112, u256)];
    body := [
      WhileStmt
        [DefineStmt (AstId 113) (SingleType BoolT)
           (ScalarOperation u256 UncheckedArithmetic LessThanOp
              [BoundAtom (AstId 111); ConstantAtom (IntegerValue 3)])]
        (BoundAtom (AstId 113))
        [DefineStmt (AstId 114) (SingleType BoolT)
           (ScalarOperation BoolT UncheckedArithmetic EqualOp
              [BoundAtom (AstId 113); ConstantAtom (BoolValue T)]);
         BreakStmt];
      DefineStmt (AstId 115) (ProductType [SingleType u256; SingleType BoolT])
        (TupleOperation [BoundAtom (AstId 111); ConstantAtom (BoolValue F)]);
      DefineStmt (AstId 116) (SingleType BoolT)
        (TupleComponentOperation 1 (BoundAtom (AstId 115)));
      ReturnStmt [BoundAtom (AstId 111)]
    ]
  |>
End

Definition test_program_def:
  test_program = <|
    procedures := [add_proc; count_proc; pair_proc; first_proc; fact_proc;
                   wrapper_proc; void_proc; convert_proc; scope_proc];
    struct_layouts := []; type_declarations := test_decls;
    state_variables := [];
    entry_procedure := AstId 6;
    external_functions := []; receive_procedure := NONE;
    fallback_procedure := NONE; creation_procedure := NONE
  |>
End

Definition test_env_def:
  test_env = core_program_environment test_program
End

val () = cv_auto_trans test_env_def;

Theorem test_program_wf:
  wf_core_program test_env test_program
Proof
  EVAL_TAC
QED

(* Negative witnesses: each replaces one procedure body with a single defect. *)

Definition with_body_def:
  with_body body = <|
    procedure_id := AstId 8;
    parameters := [(AstId 80, u256)];
    return_bindings := [(AstId 81, u256)];
    body := body
  |>
End

val () = cv_auto_trans with_body_def;

Theorem unbound_atom_rejected:
  ¬wf_core_procedure test_env (with_body [ReturnStmt [BoundAtom (AstId 99)]])
Proof
  EVAL_TAC
QED

Theorem out_of_range_constant_rejected:
  ¬wf_core_procedure test_env (with_body [
     DefineStmt (AstId 82) (SingleType (UintT 8))
       (ConvertOperation (UintT 8) (ConstantAtom (IntegerValue 300)))])
Proof
  EVAL_TAC
QED

Theorem enum_constant_out_of_range_rejected:
  ¬wf_core_procedure test_env (with_body [
     DefineStmt (AstId 82) (SingleType (EnumT (AstId 900)))
       (ConvertOperation (EnumT (AstId 900)) (ConstantAtom (IntegerValue 3)))])
Proof
  EVAL_TAC
QED

Theorem call_arity_rejected:
  ¬wf_core_procedure test_env (with_body [
     DefineStmt (AstId 82) (SingleType u256)
       (InternalCallOperation (AstId 1) [BoundAtom (AstId 80)])])
Proof
  EVAL_TAC
QED

(* An external call to a constant address with the parameter as argument. *)
Definition external_call_body_def:
  external_call_body kind value = [
    DefineStmt (AstId 82) (SingleType u256)
      (ExternalCallOperation kind [1w; 2w; 3w; 4w] [u256] [u256]
         (ConstantAtom (AddressValue 0x5000w)) value
         [BoundAtom (AstId 80)])]
End

val () = cv_auto_trans external_call_body_def;

Theorem external_call_accepted:
  wf_core_procedure test_env
    (with_body (external_call_body ExternalCall (ConstantAtom (IntegerValue 1))))
Proof
  EVAL_TAC
QED

Theorem external_delegate_call_rejected:
  ¬wf_core_procedure test_env
     (with_body (external_call_body ExternalDelegateCall
                   (ConstantAtom (IntegerValue 0))))
Proof
  EVAL_TAC
QED

Theorem external_static_call_value_rejected:
  ¬wf_core_procedure test_env
     (with_body (external_call_body ExternalStaticCall
                   (ConstantAtom (IntegerValue 1))))
Proof
  EVAL_TAC
QED

Theorem unknown_procedure_rejected:
  ¬wf_core_procedure test_env (with_body [
     DefineStmt (AstId 82) (SingleType u256)
       (InternalCallOperation (AstId 77) [])])
Proof
  EVAL_TAC
QED

Theorem call_result_shape_rejected:
  ¬wf_core_procedure test_env (with_body [
     DefineStmt (AstId 82) (SingleType u256)
       (InternalCallOperation (AstId 3) [])])
Proof
  EVAL_TAC
QED

Theorem return_arity_rejected:
  ¬wf_core_procedure test_env (with_body [ReturnStmt []])
Proof
  EVAL_TAC
QED

Theorem break_outside_loop_rejected:
  ¬wf_core_procedure test_env (with_body [BreakStmt])
Proof
  EVAL_TAC
QED

(* Nested in a loop body, so the prelude's in_loop reset is what rejects it. *)
Theorem break_in_prelude_rejected:
  ¬wf_core_procedure test_env (with_body [
     WhileStmt [] (ConstantAtom (BoolValue T))
       [WhileStmt [BreakStmt] (ConstantAtom (BoolValue T)) []]])
Proof
  EVAL_TAC
QED

Theorem mismatched_operand_rejected:
  ¬wf_core_procedure test_env (with_body [
     DefineStmt (AstId 82) (SingleType BoolT)
       (ConvertOperation BoolT (ConstantAtom (BoolValue T)));
     DefineStmt (AstId 83) (SingleType u256)
       (ScalarOperation u256 CheckedArithmetic AddOp
          [BoundAtom (AstId 80); BoundAtom (AstId 82)])])
Proof
  EVAL_TAC
QED

Theorem nonbool_condition_rejected:
  ¬wf_core_procedure test_env (with_body [IfStmt (BoundAtom (AstId 80)) [] []])
Proof
  EVAL_TAC
QED

Theorem write_type_mismatch_rejected:
  ¬wf_core_procedure test_env (with_body [
     CaptureBindingStmt (AstId 82) (AstId 81);
     WriteScalarStmt (AstId 82) BoolT (ConstantAtom (BoolValue T))])
Proof
  EVAL_TAC
QED

Theorem bool_to_integer_rejected:
  ¬wf_core_procedure test_env (with_body [
     DefineStmt (AstId 82) (SingleType BoolT)
       (ConvertOperation BoolT (ConstantAtom (BoolValue T)));
     DefineStmt (AstId 83) (SingleType (UintT 8))
       (ConvertOperation (UintT 8) (BoundAtom (AstId 82)))])
Proof
  EVAL_TAC
QED

Theorem signed_to_wider_unsigned_rejected:
  ¬wf_core_procedure test_env (with_body [
     DefineStmt (AstId 82) (SingleType (IntT 8))
       (ConvertOperation (IntT 8) (ConstantAtom (IntegerValue 1)));
     DefineStmt (AstId 83) (SingleType (UintT 16))
       (ConvertOperation (UintT 16) (BoundAtom (AstId 82)))])
Proof
  EVAL_TAC
QED

Theorem signed_to_address_rejected:
  ¬wf_core_procedure test_env (with_body [
     DefineStmt (AstId 82) (SingleType (IntT 160))
       (ConvertOperation (IntT 160) (ConstantAtom (IntegerValue 1)));
     DefineStmt (AstId 83) (SingleType (AddressT NonpayableAddress))
       (ConvertOperation (AddressT NonpayableAddress) (BoundAtom (AstId 82)))])
Proof
  EVAL_TAC
QED

Theorem payable_address_to_integer_rejected:
  ¬wf_core_procedure test_env (with_body [
     DefineStmt (AstId 82) (SingleType (AddressT PayableAddress))
       (ConvertOperation (AddressT PayableAddress)
          (ConstantAtom (AddressValue 0w)));
     DefineStmt (AstId 83) (SingleType (UintT 160))
       (ConvertOperation (UintT 160) (BoundAtom (AstId 82)))])
Proof
  EVAL_TAC
QED

Theorem function_parameter_rejected:
  ¬wf_core_procedure test_env
     (with_body [] with parameters := [(AstId 80, FunctionT InternalFn PureMut [] [])])
Proof
  EVAL_TAC
QED

Theorem empty_enum_rejected:
  ¬wf_type_declaration test_env (EnumDeclaration 0)
Proof
  EVAL_TAC
QED

Theorem oversized_enum_rejected:
  ¬wf_type_declaration test_env (EnumDeclaration 257)
Proof
  EVAL_TAC
QED

Theorem undeclared_struct_field_rejected:
  ¬wf_type_declaration test_env
     (StructDeclaration [(AstId 1, StructT (AstId 12345))])
Proof
  EVAL_TAC
QED

Theorem enum_bound_admitted:
  wf_type_declaration test_env (EnumDeclaration 256)
Proof
  EVAL_TAC
QED

(* Events: at most four topics, counting topic 0 unless anonymous. *)
Definition indexed_args_def:
  indexed_args n = REPLICATE n (u256, T, BoundAtom (AstId 80))
End

Theorem emit_four_topics_admitted:
  wf_core_procedure test_env (with_body [
     EmitStmt (SOME 0w) (indexed_args 3 ++ [(BoolT, F, ConstantAtom (BoolValue T))]);
     EmitStmt NONE (indexed_args 4);
     ReturnStmt [BoundAtom (AstId 80)]])
Proof
  EVAL_TAC
QED

Theorem emit_five_topics_rejected:
  ¬wf_core_procedure test_env (with_body [
     EmitStmt (SOME 0w) (indexed_args 4); ReturnStmt [BoundAtom (AstId 80)]])
Proof
  EVAL_TAC
QED

Theorem emit_mistyped_argument_rejected:
  ¬wf_core_procedure test_env (with_body [
     EmitStmt NONE [(BoolT, F, BoundAtom (AstId 80))];
     ReturnStmt [BoundAtom (AstId 80)]])
Proof
  EVAL_TAC
QED

(* Dispatch: distinct 4-byte selectors of procedures with ABI parameters and
 * returns; receive and fallback take and return nothing.
 *)
Definition external_def:
  external selector f =
    <| selector := selector; external_procedure := AstId f; payable := F |>
End

Theorem dispatch_admitted:
  wf_core_dispatch test_env (test_program with <|
    external_functions := [external [1w; 2w; 3w; 4w] 1; external [1w; 2w; 3w; 5w] 6];
    receive_procedure := SOME (AstId 7);
    fallback_procedure := SOME (AstId 7, T) |>)
Proof
  EVAL_TAC
QED

Theorem duplicate_selector_rejected:
  ¬wf_core_dispatch test_env (test_program with
    external_functions := [external [1w; 2w; 3w; 4w] 1; external [1w; 2w; 3w; 4w] 6])
Proof
  EVAL_TAC
QED

Theorem short_selector_rejected:
  ¬wf_core_dispatch test_env (test_program with
    external_functions := [external [1w; 2w; 3w] 1])
Proof
  EVAL_TAC
QED

Theorem unknown_external_procedure_rejected:
  ¬wf_core_dispatch test_env (test_program with
    external_functions := [external [1w; 2w; 3w; 4w] 77])
Proof
  EVAL_TAC
QED

(* Calldata decodes and return data encodes only elementary types. *)
Theorem non_elementary_external_parameter_rejected:
  ¬wf_core_dispatch
     (test_env with procedures :=
        [(AstId 1, add_proc with parameters :=
                     [(AstId 10, UserValueT (AstId 901)); (AstId 11, u256)])])
     (test_program with external_functions := [external [1w; 2w; 3w; 4w] 1])
Proof
  EVAL_TAC
QED

Theorem non_elementary_external_return_rejected:
  ¬wf_core_dispatch
     (test_env with procedures :=
        [(AstId 1, add_proc with return_bindings :=
                     [(AstId 12, UserValueT (AstId 901))])])
     (test_program with external_functions := [external [1w; 2w; 3w; 4w] 1])
Proof
  EVAL_TAC
QED

Theorem receive_with_parameters_rejected:
  ¬wf_core_dispatch test_env (test_program with receive_procedure := SOME (AstId 1))
Proof
  EVAL_TAC
QED

(* Reference locations: struct 910 holds a mapping, 911 reaches it through an
 * array, 912 holds none, and 913 is recursive through a dynamic array.
 *)
Definition struct_env_def:
  struct_env = core_program_environment
    (test_program with type_declarations := [(AstId 910, StructDeclaration [(AstId 1, MappingT u256 u256)]);
     (AstId 911,
      StructDeclaration [(AstId 1, ArrayT (StructT (AstId 910)) NONE)]);
     (AstId 912, StructDeclaration [(AstId 1, u256)]);
     (AstId 913,
      StructDeclaration [(AstId 1, u256);
                         (AstId 2, ArrayT (StructT (AstId 913)) NONE)])])
End

Theorem memory_struct_mapping_rejected:
  ¬declared_type_ok struct_env (LocatedT MemoryLoc (StructT (AstId 910)))
Proof
  EVAL_TAC
QED

Theorem calldata_nested_struct_mapping_rejected:
  ¬declared_type_ok struct_env
     (LocatedT CalldataLoc (ArrayT (StructT (AstId 911)) NONE))
Proof
  EVAL_TAC
QED

Theorem memory_struct_parameter_mapping_rejected:
  ¬declared_type_ok struct_env
     (FunctionT InternalFn PureMut
        [LocatedT MemoryLoc (StructT (AstId 910))] [])
Proof
  EVAL_TAC
QED

Theorem storage_struct_mapping_admitted:
  declared_type_ok struct_env (LocatedT StorageLoc (StructT (AstId 911)))
Proof
  EVAL_TAC
QED

Theorem memory_struct_admitted:
  declared_type_ok struct_env (LocatedT MemoryLoc (StructT (AstId 912))) ∧
  declared_type_ok struct_env (LocatedT CalldataLoc (StructT (AstId 913)))
Proof
  EVAL_TAC
QED

(* Scope exit: prelude and body bindings, and a target captured in a branch,
 * are gone afterwards.
 *)
Theorem prelude_binding_escape_rejected:
  ¬wf_core_procedure test_env (with_body [
     WhileStmt [DefineStmt (AstId 82) (SingleType BoolT)
                  (ConvertOperation BoolT (ConstantAtom (BoolValue F)))]
       (BoundAtom (AstId 82)) [];
     IfStmt (BoundAtom (AstId 82)) [] []])
Proof
  EVAL_TAC
QED

Theorem body_binding_escape_rejected:
  ¬wf_core_procedure test_env (with_body [
     WhileStmt [] (ConstantAtom (BoolValue F))
       [DefineStmt (AstId 82) (SingleType u256)
          (ConvertOperation u256 (ConstantAtom (IntegerValue 1)))];
     ReturnStmt [BoundAtom (AstId 82)]])
Proof
  EVAL_TAC
QED

Theorem branch_target_escape_rejected:
  ¬wf_core_procedure test_env (with_body [
     IfStmt (ConstantAtom (BoolValue T))
       [CaptureBindingStmt (AstId 82) (AstId 81)] [];
     WriteScalarStmt (AstId 82) u256 (BoundAtom (AstId 80))])
Proof
  EVAL_TAC
QED

(* Tuples *)

Theorem tuple_index_out_of_range_rejected:
  ¬wf_core_procedure test_env (with_body [
     DefineStmt (AstId 82) (ProductType [SingleType u256; SingleType BoolT])
       (TupleOperation [BoundAtom (AstId 80); ConstantAtom (BoolValue F)]);
     DefineStmt (AstId 83) (SingleType u256)
       (TupleComponentOperation 2 (BoundAtom (AstId 82)))])
Proof
  CONV_TAC cv_eval
QED

Theorem product_constant_rejected:
  ¬wf_core_procedure test_env (with_body [
     DefineStmt (AstId 82) (ProductType [ProductType []; SingleType u256])
       (TupleOperation [ConstantAtom (IntegerValue 0); BoundAtom (AstId 80)])])
Proof
  EVAL_TAC
QED

Theorem product_capture_rejected:
  ¬wf_core_procedure test_env (with_body [
     DefineStmt (AstId 82) (ProductType []) (TupleOperation []);
     CaptureBindingStmt (AstId 83) (AstId 82)])
Proof
  EVAL_TAC
QED

(* Operator and conversion tables *)

Theorem arithmetic_on_bool_rejected:
  ¬wf_core_procedure test_env (with_body [
     DefineStmt (AstId 82) (SingleType BoolT)
       (ScalarOperation BoolT CheckedArithmetic AddOp
          [ConstantAtom (BoolValue T); ConstantAtom (BoolValue F)])])
Proof
  EVAL_TAC
QED

Theorem arithmetic_on_address_rejected:
  ¬wf_core_procedure test_env (with_body [
     DefineStmt (AstId 82) (SingleType (AddressT NonpayableAddress))
       (ScalarOperation (AddressT NonpayableAddress) CheckedArithmetic AddOp
          [ConstantAtom (AddressValue 0w); ConstantAtom (AddressValue 0w)])])
Proof
  EVAL_TAC
QED

Theorem bitwise_on_bool_rejected:
  ¬wf_core_procedure test_env (with_body [
     DefineStmt (AstId 82) (SingleType BoolT)
       (ScalarOperation BoolT UncheckedArithmetic BitAndOp
          [ConstantAtom (BoolValue T); ConstantAtom (BoolValue F)])])
Proof
  EVAL_TAC
QED

Theorem operand_count_rejected:
  ¬wf_core_procedure test_env (with_body [
     DefineStmt (AstId 82) (SingleType u256)
       (ScalarOperation u256 CheckedArithmetic AddOp [BoundAtom (AstId 80)])])
Proof
  EVAL_TAC
QED

Theorem extended_operators_accepted:
  wf_core_procedure test_env (with_body [
     DefineStmt (AstId 82) (SingleType u256)
       (ScalarOperation u256 UncheckedArithmetic ShiftLeftOp
          [BoundAtom (AstId 80); BoundAtom (AstId 80)]);
     DefineStmt (AstId 83) (SingleType u256)
       (ScalarOperation u256 CheckedArithmetic ExponentOp
          [BoundAtom (AstId 80); ConstantAtom (IntegerValue 2)]);
     DefineStmt (AstId 84) (SingleType BoolT)
       (ScalarOperation u256 UncheckedArithmetic LessThanOp
          [BoundAtom (AstId 82); BoundAtom (AstId 83)]);
     DefineStmt (AstId 85) (SingleType BoolT)
       (ScalarOperation BoolT UncheckedArithmetic BoolNotOp
          [BoundAtom (AstId 84)]);
     DefineStmt (AstId 86) (SingleType (IntT 256))
       (ConvertOperation (IntT 256) (ConstantAtom (IntegerValue (-1))));
     DefineStmt (AstId 87) (SingleType (IntT 256))
       (ScalarOperation (IntT 256) CheckedArithmetic NegateOp
          [BoundAtom (AstId 86)]);
     DefineStmt (AstId 88) (SingleType u256)
       (ScalarOperation u256 UncheckedArithmetic BitNotOp
          [BoundAtom (AstId 80)])])
Proof
  EVAL_TAC
QED

Theorem narrow_shift_amount_rejected:
  ¬wf_core_procedure test_env (with_body [
     DefineStmt (AstId 82) (SingleType (UintT 8))
       (ConvertOperation (UintT 8) (ConstantAtom (IntegerValue 1)));
     DefineStmt (AstId 83) (SingleType u256)
       (ScalarOperation u256 UncheckedArithmetic ShiftLeftOp
          [BoundAtom (AstId 80); BoundAtom (AstId 82)])])
Proof
  EVAL_TAC
QED

Theorem negate_unsigned_rejected:
  ¬wf_core_procedure test_env (with_body [
     DefineStmt (AstId 82) (SingleType u256)
       (ScalarOperation u256 CheckedArithmetic NegateOp [BoundAtom (AstId 80)])])
Proof
  EVAL_TAC
QED

Theorem bool_not_on_integer_rejected:
  ¬wf_core_procedure test_env (with_body [
     DefineStmt (AstId 82) (SingleType u256)
       (ScalarOperation u256 UncheckedArithmetic BoolNotOp
          [BoundAtom (AstId 80)])])
Proof
  EVAL_TAC
QED

Theorem enum_to_signed_rejected:
  ¬wf_core_procedure test_env (with_body [
     DefineStmt (AstId 82) (SingleType (EnumT (AstId 900)))
       (ConvertOperation (EnumT (AstId 900)) (ConstantAtom (IntegerValue 1)));
     DefineStmt (AstId 83) (SingleType (IntT 8))
       (ConvertOperation (IntT 8) (BoundAtom (AstId 82)))])
Proof
  EVAL_TAC
QED

Theorem bytes_width_mismatch_rejected:
  ¬wf_core_procedure test_env (with_body [
     DefineStmt (AstId 82) (SingleType (UintT 8))
       (ConvertOperation (UintT 8) (ConstantAtom (IntegerValue 1)));
     DefineStmt (AstId 83) (SingleType (FixedBytesT 2))
       (ConvertOperation (FixedBytesT 2) (BoundAtom (AstId 82)))])
Proof
  EVAL_TAC
QED

Theorem contract_parameter_rejected:
  ¬wf_core_procedure test_env
     (with_body [] with parameters := [(AstId 80, ContractT (AstId 1))])
Proof
  EVAL_TAC
QED

Theorem continue_outside_loop_rejected:
  ¬wf_core_procedure test_env (with_body [ContinueStmt])
Proof
  EVAL_TAC
QED

Theorem branch_local_escape_rejected:
  ¬wf_core_procedure test_env (with_body [
     IfStmt (ConstantAtom (BoolValue T))
       [DefineStmt (AstId 82) (SingleType u256)
          (ConvertOperation u256 (ConstantAtom (IntegerValue 1)))] [];
     ReturnStmt [BoundAtom (AstId 82)]])
Proof
  EVAL_TAC
QED

Theorem singleton_product_rejected:
  ¬wf_core_procedure test_env (with_body [
     DefineStmt (AstId 82) (ProductType [SingleType u256])
       (TupleOperation [BoundAtom (AstId 80)])])
Proof
  EVAL_TAC
QED

Theorem comparison_annotation_rejected:
  ¬wf_core_procedure test_env (with_body [
     DefineStmt (AstId 82) (SingleType u256)
       (ScalarOperation u256 UncheckedArithmetic EqualOp
          [BoundAtom (AstId 80); BoundAtom (AstId 80)])])
Proof
  EVAL_TAC
QED

Theorem shadowing_rejected:
  ¬wf_core_procedure test_env (with_body [
     DefineStmt (AstId 80) (SingleType u256)
       (ConvertOperation u256 (ConstantAtom (IntegerValue 1)))])
Proof
  EVAL_TAC
QED

Theorem write_without_capture_rejected:
  ¬wf_core_procedure test_env (with_body [
     WriteScalarStmt (AstId 81) u256 (BoundAtom (AstId 80))])
Proof
  EVAL_TAC
QED

Theorem reference_operation_rejected:
  ¬wf_core_procedure test_env (with_body [
     DefineStmt (AstId 82) (SingleType u256)
       (ReadOperation u256 (BoundAtom (AstId 80)))])
Proof
  EVAL_TAC
QED

Theorem duplicate_procedure_rejected:
  ¬wf_core_program
     (core_program_environment
        (test_program with procedures := add_proc :: test_program.procedures))
     (test_program with procedures := add_proc :: test_program.procedures)
Proof
  EVAL_TAC
QED

Theorem missing_entry_rejected:
  ¬wf_core_program test_env (test_program with entry_procedure := AstId 77)
Proof
  EVAL_TAC
QED

(* A captured storage reference is not a scalar binding: passing it to scalar
 * arithmetic or reading a whole mapping must fail validation.
 *)
Theorem mapping_reference_not_scalar:
  ¬wf_core_operation test_env
    <| bindings := [(AstId 1, ReferenceType (MappingT (IntT 8) (UintT 8)))];
       targets := []; returns := []; in_loop := F |>
    (SingleType (UintT 8))
    (ReadOperation (UintT 8) (BoundAtom (AstId 1)))
Proof
  EVAL_TAC
QED

Theorem mapping_key_signedness_checked:
  ¬wf_core_operation test_env
    <| bindings := [(AstId 1, ReferenceType (MappingT (IntT 8) (UintT 8)));
                   (AstId 2, SingleType (UintT 8))];
       targets := []; returns := []; in_loop := F |>
    (ReferenceType (UintT 8))
    (NavigateOperation (UintT 8) (BoundAtom (AstId 1))
       (IndexNavigation (BoundAtom (AstId 2))))
Proof
  EVAL_TAC
QED

Theorem mapping_leaf_annotation_checked:
  ¬wf_core_operation test_env
    <| bindings := [(AstId 1, ReferenceType (MappingT (IntT 8) (UintT 8)))];
       targets := []; returns := []; in_loop := F |>
    (ReferenceType (UintT 16))
    (NavigateOperation (UintT 16) (BoundAtom (AstId 1))
       (IndexNavigation (ConstantAtom (IntegerValue (-1)))))
Proof
  EVAL_TAC
QED

Theorem array_navigation_leaf_type_must_match:
  ¬wf_core_operation test_env
    <| bindings := [(AstId 1, ReferenceType (ArrayT (UintT 8) (SOME 35)))];
       targets := []; returns := []; in_loop := F |>
    (ReferenceType (UintT 16))
    (NavigateOperation (UintT 16) (BoundAtom (AstId 1))
       (IndexNavigation (ConstantAtom (IntegerValue 1))))
Proof
  EVAL_TAC
QED

Definition packed_struct_layout_def:
  packed_struct_layout = <|
    struct_id := AstId 950;
    struct_slots := 1;
    struct_fields :=
      [<| state_id := AstId 951; state_type := UintT 8;
          state_slot := 0w; state_offset := 0 |>;
       <| state_id := AstId 952; state_type := IntT 16;
          state_slot := 0w; state_offset := 1 |>]
  |>
End

Definition struct_layout_environment_def:
  struct_layout_environment layouts = core_program_environment
    <| procedures := []; state_variables := []; struct_layouts := layouts;
       type_declarations := MAP (λs. (s.struct_id, StructDeclaration
         (MAP (λv. (v.state_id, v.state_type)) s.struct_fields))) layouts;
       entry_procedure := AstId 0;
       external_functions := []; receive_procedure := NONE;
       fallback_procedure := NONE; creation_procedure := NONE |>
End

Theorem packed_struct_layout_checked:
  wf_core_environment (struct_layout_environment [packed_struct_layout])
Proof
  EVAL_TAC
QED

Theorem struct_declarations_must_match_layout:
  ¬wf_core_environment
    (struct_layout_environment [packed_struct_layout] with type_declarations := []) ∧
  ¬wf_core_environment
    (struct_layout_environment [packed_struct_layout] with type_declarations :=
      [(AstId 950, StructDeclaration [(AstId 951, UintT 16); (AstId 952, IntT 16)])])
Proof
  EVAL_TAC
QED

Theorem malformed_struct_fields_rejected:
  ¬wf_core_environment
    (struct_layout_environment [packed_struct_layout with struct_fields :=
      [<| state_id := AstId 951; state_type := UintT 16;
          state_slot := 0w; state_offset := 31 |>]]) ∧
  ¬wf_core_environment
    (struct_layout_environment [packed_struct_layout with struct_fields :=
      [<| state_id := AstId 951; state_type := UintT 8;
          state_slot := 1w; state_offset := 0 |>]]) ∧
  ¬wf_core_environment
    (struct_layout_environment [packed_struct_layout with struct_fields :=
      [<| state_id := AstId 951; state_type := StructT (AstId 950);
          state_slot := 0w; state_offset := 0 |>]])
Proof
  EVAL_TAC
QED

Theorem struct_field_ownership_checked:
  wf_core_operation (struct_layout_environment [packed_struct_layout])
    <| bindings := [(AstId 1, ReferenceType (StructT (AstId 950)))];
       targets := []; returns := []; in_loop := F |>
    (ReferenceType (UintT 8))
    (NavigateOperation (UintT 8) (BoundAtom (AstId 1)) (FieldNavigation (AstId 951))) ∧
  ¬wf_core_operation (struct_layout_environment [packed_struct_layout])
    <| bindings := [(AstId 1, ReferenceType (StructT (AstId 950)))];
       targets := []; returns := []; in_loop := F |>
    (ReferenceType (UintT 8))
    (NavigateOperation (UintT 8) (BoundAtom (AstId 1)) (FieldNavigation (AstId 999))) ∧
  ¬wf_core_operation (struct_layout_environment [packed_struct_layout])
    <| bindings := [(AstId 1, ReferenceType (StructT (AstId 950)))];
       targets := []; returns := []; in_loop := F |>
    (ReferenceType (UintT 8))
    (NavigateOperation (UintT 8) (BoundAtom (AstId 1)) (FieldNavigation (AstId 952)))
Proof
  EVAL_TAC
QED

Theorem recursive_struct_behind_mapping_checked:
  wf_core_environment
    (struct_layout_environment [packed_struct_layout with <|
      struct_slots := 2;
      struct_fields :=
        [<| state_id := AstId 951; state_type := UintT 8;
            state_slot := 0w; state_offset := 0 |>;
         <| state_id := AstId 952;
            state_type := MappingT (UintT 256) (StructT (AstId 950));
            state_slot := 1w; state_offset := 0 |>] |>])
Proof
  EVAL_TAC
QED

(* Array push must reject an absent binding, not leave a partial case. *)
Theorem array_push_missing_binding_rejected:
  ¬wf_core_operation test_env
    <| bindings := []; targets := []; returns := []; in_loop := F |>
    (ReferenceType (UintT 8)) (ArrayPushOperation (BoundAtom (AstId 1)) NONE)
Proof
  CONV_TAC cv_eval
QED

Definition layoutless_program_def:
  layoutless_program = test_program with type_declarations :=
    test_decls ++ [(AstId 960, StructDeclaration [(AstId 961, UintT 8)])]
End

val () = cv_auto_trans layoutless_program_def;

Theorem layoutless_struct_declaration_retained:
  wf_core_program (core_program_environment layoutless_program) layoutless_program ∧
  lookup_struct (core_program_environment layoutless_program) (AstId 960) =
    SOME [(AstId 961, UintT 8)] ∧
  lookup_struct_layout (core_program_environment layoutless_program) (AstId 960) = NONE
Proof
  CONV_TAC cv_eval
QED
