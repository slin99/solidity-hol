(* Architecture blueprint, not yet an admitted/executable Solidity subset.
 * All effectful child evaluations are ordered by elaboration into core blocks.
 *)
Theory solidityCore
Ancestors
  solidityAST vfmContext yulAST

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
 * the root declaration's identity through navigation. An immutable is named
 * by its declaration: its value lives in the deployed code, not in storage.
 *)
Datatype:
  reference
  = StorageReference storage_backend address bytes32 num sol_type layout_id
  | MemoryReference heap_id num sol_type
  | CalldataReference num num sol_type
  | ImmutableReference ast_id
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
 * Types belong to operations/bindings, not integer payloads. SingleType
 * includes located reference values; ReferenceType denotes a captured lvalue,
 * including a scalar storage leaf.
 *)
Datatype:
  core_value_type = SingleType sol_type | ReferenceType sol_type
                  | ProductType (core_value_type list)
                  | RevertDataType
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
  | AddModOp | MulModOp
  | ShiftLeftOp | ShiftRightOp
  | EqualOp | LessThanOp | BitAndOp | BitOrOp | BitXorOp
  | NegateOp | BitNotOp | BoolNotOp
End

Datatype:
  navigation = FieldNavigation ast_id | IndexNavigation core_atom
End

(* BindTarget includes local variables and temporaries. ReferenceFieldTarget
 * is an element of a memory array (its heap object, index and element type):
 * a write stores a scalar or rebinds a reference, never copies contents.
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

Datatype:
  catch_kind = ErrorCatch | PanicCatch | GenericCatch
End

(* The call and transaction context a body reads: msg.sender, msg.value,
 * address(this), tx.origin, tx.gasprice and the block's scalars. msg.data is
 * the complete read-only calldata bytes, including the selector.
 *)
Datatype:
  environment_field
  = MsgSender | MsgValue | MsgData | SelfAddress | TxOrigin | TxGasPrice
  | BlockNumber | BlockTimestamp | BlockChainId | BlockCoinbase
  | BlockBaseFee | BlockGasLimit
End

(* DefaultMemoryOperation ty: the default value of a memory variable of type
 * ty. AllocateMemoryOperation ty n: new ty(n), a zeroed byte sequence or
 * dynamic array of length n. ArrayIndexOperation a i: element i of the memory
 * or calldata array a. CopyToMemoryOperation a: a new memory copy of the
 * calldata array a. Keccak256Operation a: the Keccak-256 hash of the memory
 * byte sequence a, as bytes32. EcrecoverOperation h v r s: ecrecover(h, v, r,
 * s), the address the signature (v, r, s) of the bytes32 hash h recovers, or
 * address(0) if it is invalid; v is a uint8 and r and s are bytes32.
 * AbiDecodeOperation types a: abi.decode(a, (types)) of the memory bytes a
 * into values of those elementary types, one value or a tuple of them.
 * AbiEncodeOperation selector types arguments: abi.encode(arguments) of the
 * arguments as those ABI types, after the four bytes of the selector if any,
 * as a new memory bytes. AbiEncodePackedOperation types arguments:
 * abi.encodePacked(arguments), each value in its own width and each byte
 * sequence as its contents, as a new memory bytes, or as a new memory string
 * (string.concat) when the result is defined as one.
 * ExternalCallOperation kind selector parameter_types return_types target
 * value gas arguments: a high-level call
 * I(target).f{value: value, gas: gas}(arguments) of the function with that
 * selector and those ABI types; with no gas option, the callee gets the gas
 * every call gives.
 * LowLevelCallOperation kind target value gas data: the low-level
 * target.call{value: value, gas: gas}(data), target.staticcall(data) or
 * target.delegatecall(data) of the memory bytes or bytes literal data,
 * giving whether it succeeded and its return data as a new memory bytes.
 *)
Datatype:
  core_operation
  = ScalarOperation sol_type arithmetic_mode core_operator (core_atom list)
  | ConvertOperation sol_type core_atom
  | TupleOperation (core_atom list)
  | TupleComponentOperation num core_atom
  | ReadOperation sol_type core_atom
  | StateReferenceOperation ast_id
  | ImmutableReferenceOperation ast_id
  | NavigateOperation sol_type core_atom navigation
  | DefaultMemoryOperation sol_type
  | NullMemoryOperation sol_type
  | BytesLiteralOperation sol_type (byte list)
  | AllocateMemoryOperation sol_type core_atom
  | BytesToFixedOperation num core_atom
  | ByteIndexOperation core_atom core_atom
  | ArrayIndexOperation core_atom core_atom
  (* Calldata view [start:end], with an omitted end using the current length. *)
  | CalldataSliceOperation core_atom core_atom (core_atom option)
  | CopyToMemoryOperation core_atom
  | ArrayLengthOperation core_atom
  | Keccak256Operation core_atom
  | EcrecoverOperation core_atom core_atom core_atom core_atom
  (* The addressed account's code size, without a memory bytes allocation. *)
  | CodeLengthOperation core_atom
  (* The addressed account's current balance. *)
  | BalanceOperation core_atom
  | AbiEncodeOperation (core_atom option) (sol_type list) (core_atom list)
  | AbiEncodePackedOperation (sol_type list) (core_atom list)
  | AbiDecodeOperation (sol_type list) core_atom
  (* A non-reverting typed catch decoder, and the generic catch's lazy copy
   * of the internal RevertDataType value into source memory. *)
  | TryDecodeErrorOperation catch_kind core_atom
  | MaterializeRevertDataOperation core_atom
  | ArrayPushOperation core_atom (core_atom option)
  | ArrayPopOperation core_atom
  | InternalCallOperation ast_id (core_atom list)
  | ExternalCallOperation external_kind (byte list) (sol_type list)
      (sol_type list) core_atom core_atom (core_atom option) (core_atom list)
  | LowLevelCallOperation external_kind core_atom core_atom (core_atom option)
      core_atom
  (* target.transfer(value): exact stipend, failure bytes forwarded, no
   * return-data allocation. *)
  | TransferOperation core_atom core_atom
  (* success flag, scalar returns, RevertDataType; only a failed EVM call
   * is caught. Operand and return-decoding failures still propagate. *)
  | TryExternalCallOperation external_kind (byte list) (sol_type list)
      (sol_type list) core_atom core_atom (core_atom option) (core_atom list)
  | EnvironmentOperation environment_field
End

(* What an inline assembly block's Yul variable stands for: a local of value
 * type (read on entry, written back on exit), the storage slot or byte offset
 * of a state variable (x.slot, x.offset), the slot or offset of the reference
 * a storage pointer local holds (assigning its slot rebinds the local), the
 * value of a constant of value type, held in an atom, or the memory address
 * of a local holding a memory byte sequence of the given type (bytes or
 * string). Only locals and storage pointer slots are assignable.
 *)
Datatype:
  assembly_reference
  = AssemblyLocal ast_id sol_type
  | AssemblySlot ast_id
  | AssemblyOffset ast_id
  | AssemblyPointerSlot ast_id
  | AssemblyPointerOffset ast_id
  | AssemblyConstant core_atom sol_type
  | AssemblyMemory ast_id sol_type
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
  (* revert E(args): the error's selector, its parameter types and the
   * arguments *)
  | RevertErrorStmt (byte list) (sol_type list) (core_atom list)
  | PanicStmt num
  (* topic0 (NONE for an anonymous event), then each argument with its type
   * and whether it is indexed *)
  | EmitStmt (bytes32 option) ((sol_type # bool # core_atom) list)
  (* assembly { code }, with the Yul names of the source declarations the
   * code refers to *)
  | AssemblyStmt (yul_stmt list) ((string # assembly_reference) list)
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
    state_backend : storage_backend;
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
 * arguments, given with whether it accepts value. The immutables are all the
 * contract's immutables, unread ones included, with their types: creation
 * reserves a memory word for each. The unsupported procedures are those of
 * functions the frontend could not model: they have no procedure, so the
 * dispatch entries naming them refuse, and no procedure can call them. *)
Datatype:
  core_program = <|
    procedures : core_procedure list;
    unsupported_procedures : ast_id list;
    state_variables : core_state_variable list;
    immutables : (ast_id # sol_type) list;
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
  (* an inline assembly return(p, s) or stop(): the frame ends with these
   * bytes as its return data *)
  | HaltCompletion (byte list)
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
