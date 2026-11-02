(* Architecture blueprint, not yet an admitted/executable Solidity subset.
 * All effectful child evaluations are ordered by elaboration into core blocks.
 *)
Theory solidityCore
Ancestors
  solidityAST vfmContext

Datatype:
  layout_id = LayoutId num
End

Datatype:
  heap_id = HeapId num
End

Datatype:
  storage_backend = PersistentStorage | TransientStorage
End

(* Captured locations, never source paths to reevaluate. The type identifies
 * the struct layout used by subsequent field navigation; layout_id preserves
 * the root declaration's identity through navigation.
 *)
Datatype:
  reference
  = StorageReference storage_backend address bytes32 num sol_type layout_id
  | MemoryReference heap_id num sol_type
  | CalldataReference num num sol_type
End

Datatype:
  scalar
  = BoolValue bool
  | IntegerValue int
  | AddressValue address
  | BytesValue (byte list)
  | InternalFunctionValue ast_id
  | ExternalFunctionValue address (byte list)
End

Datatype:
  runtime_value
  = ScalarValue scalar
  | ReferenceValue reference
  | TupleValue (runtime_value list)
End

(* Operands are pure: effects and intermediate results have already been named.
 * Types belong to operations/bindings, not integer payloads.
 *)
Datatype:
  core_value_type = SingleType sol_type | ReferenceType sol_type
                  | ProductType (core_value_type list)
End

Datatype:
  core_atom = BoundAtom ast_id | ConstantAtom scalar
End

Datatype:
  arithmetic_mode = CheckedArithmetic | UncheckedArithmetic
End

(* Other comparisons are derived: atoms are pure, so a > b is b < a and
 * a <= b is !(b < a). Shift amounts and exponents are uint256 operands;
 * elaboration widens a narrower unsigned right operand first.
 *)
Datatype:
  core_operator
  = AddOp | SubtractOp | MultiplyOp | DivideOp | RemainderOp | ExponentOp
  | ShiftLeftOp | ShiftRightOp
  | EqualOp | LessThanOp | BitAndOp | BitOrOp | BitXorOp
  | NegateOp | BitNotOp | BoolNotOp
End

Datatype:
  navigation = FieldNavigation ast_id | IndexNavigation core_atom
End

(* BindTarget includes local variables and temporaries. ReferenceFieldTarget
 * supports rebinding a reference-valued memory member, not storage copying.
 *)
Datatype:
  captured_target
  = BindTarget ast_id
  | ValueTarget reference
  | ReferenceFieldTarget heap_id num sol_type
End

Datatype:
  external_kind = ExternalCall | ExternalStaticCall | ExternalDelegateCall
End

(* The call and transaction context a body reads: msg.sender, msg.value,
 * address(this), tx.origin, tx.gasprice and the block's scalars.
 *)
Datatype:
  environment_field
  = MsgSender | MsgValue | SelfAddress | TxOrigin | TxGasPrice
  | BlockNumber | BlockTimestamp | BlockChainId | BlockCoinbase
  | BlockBaseFee | BlockGasLimit
End

(* ExternalCallOperation kind selector parameter_types return_types target
 * value arguments: a high-level call I(target).f{value: value}(arguments) of
 * the function with that selector and those ABI types.
 *)
Datatype:
  core_operation
  = ScalarOperation sol_type arithmetic_mode core_operator (core_atom list)
  | ConvertOperation sol_type core_atom
  | TupleOperation (core_atom list)
  | TupleComponentOperation num core_atom
  | ReadOperation sol_type core_atom
  | StateReferenceOperation ast_id
  | NavigateOperation sol_type core_atom navigation
  | ArrayLengthOperation core_atom
  | ArrayPushOperation core_atom (core_atom option)
  | ArrayPopOperation core_atom
  | InternalCallOperation ast_id (core_atom list)
  | ExternalCallOperation external_kind (byte list) (sol_type list)
      (sol_type list) core_atom core_atom (core_atom list)
  | EnvironmentOperation environment_field
End

(* Explicitly separate scalar writes, reference binding, and content copying.
 * Copy traversal is independently terminating, not fuel-indexed.
 * While/internal recursion need depth fuel; finite syntax/list traversal does not.
 *)
Datatype:
  core_stmt
  = DefineStmt ast_id core_value_type core_operation
  | CaptureBindingStmt ast_id ast_id
  | CaptureValueStmt ast_id core_atom
  | CaptureReferenceFieldStmt ast_id core_atom navigation
  | WriteScalarStmt ast_id sol_type core_atom
  | BindReferenceStmt ast_id sol_type core_atom
  | CopyContentsStmt sol_type sol_type core_atom core_atom
  | IfStmt core_atom (core_stmt list) (core_stmt list)
  | WhileStmt (core_stmt list) core_atom (core_stmt list)
  | ReturnStmt (core_atom list)
  | BreakStmt
  | ContinueStmt
  | RevertStmt core_atom
  | PanicStmt num
  (* topic0 (NONE for an anonymous event), then each argument with its type
   * and whether it is indexed *)
  | EmitStmt (bytes32 option) ((sol_type # bool # core_atom) list)
End

Datatype:
  core_procedure = <|
    procedure_id : ast_id;
    parameters : (ast_id # sol_type) list;
    return_bindings : (ast_id # sol_type) list;
    body : core_stmt list
  |>
End

(* A state variable of value type, at the slot and byte offset (from the
 * slot's low-order end) the compiler's storage layout gives.
 *)
Datatype:
  core_state_variable = <|
    state_id : ast_id;
    state_type : sol_type;
    state_slot : bytes32;
    state_offset : num
  |>
End

(* A struct's fields use declaration IDs and relative storage slots. *)
Datatype:
  core_struct_layout = <|
    struct_id : ast_id;
    struct_fields : core_state_variable list;
    struct_slots : num
  |>
End

(* Semantic declarations do not depend on storage layout metadata. *)
Datatype:
  core_type_declaration
  = EnumDeclaration num
  | UserValueDeclaration sol_type
  | StructDeclaration ((ast_id # sol_type) list)
End

(* A function calldata reaches by its 4-byte selector: its procedure and
 * whether it accepts value. *)
Datatype:
  core_external_function = <|
    selector : byte list;
    external_procedure : ast_id;
    payable : bool
  |>
End

(* Dispatch: external functions by selector; empty calldata reaches receive,
 * and any other unmatched calldata the fallback, given with whether it is
 * payable. Creation runs the creation procedure on the constructor's
 * arguments, given with whether it accepts value. *)
Datatype:
  core_program = <|
    procedures : core_procedure list;
    state_variables : core_state_variable list;
    struct_layouts : core_struct_layout list;
    type_declarations : (ast_id # core_type_declaration) list;
    entry_procedure : ast_id;
    external_functions : core_external_function list;
    receive_procedure : ast_id option;
    fallback_procedure : (ast_id # bool) option;
    creation_procedure : (ast_id # bool) option
  |>
End

(* Distinct completions: return is caught by procedure/wrapper invocation;
 * break/continue by loops. Errors/resources must not masquerade as reverts.
 *)
Datatype:
  source_completion
  = NormalCompletion
  | ReturnCompletion (runtime_value list)
  | BreakCompletion
  | ContinueCompletion
  | RevertCompletion (byte list)
  | PanicCompletion num
  | InvalidCompletion string
  | FuelExhausted
End

Definition is_abrupt_def:
  is_abrupt completion ⇔ completion ≠ NormalCompletion
End

Theorem fuel_is_not_revert:
  FuelExhausted ≠ RevertCompletion data
Proof
  simp[]
QED

Theorem reference_binding_is_not_copying:
  BindReferenceStmt target ty value ≠ CopyContentsStmt src_ty dst_ty src dst
Proof
  simp[]
QED
