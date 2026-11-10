(* Static environment and well-formedness for the stage-2 pure core, with
 * value-type state variables.
 *
 * Admitted: scalar/convert/tuple/internal-call definitions, reads of state
 * variables, capture of locals and state variables and scalar writes to them,
 * and structured control flow. Bindings hold elementary types, enums and
 * user-defined value types, plus located memory and calldata byte sequences.
 * Function values are deferred together with indirect calls; contract types
 * are deferred until contract metadata (payability, bases) is in the
 * environment. Typed storage references support struct fields, mappings and
 * arrays, with scalar leaf reads/captures. Aggregate copies and external calls
 * remain rejected until their validation rules exist.
 *)
Theory solidityCoreWf
Ancestors
  solidityCore alist list option
Libs
  cv_transLib wordsLib intLib

Datatype:
  core_environment = <|
    procedures : (ast_id # core_procedure) list;
    state_variables : (ast_id # core_state_variable) list;
    immutables : (ast_id # sol_type) list;
    struct_layouts : (ast_id # core_struct_layout) list;
    type_declarations : (ast_id # core_type_declaration) list
  |>
End

Definition core_program_environment_def:
  core_program_environment (prog : core_program) = <|
    procedures := MAP (λp. (p.procedure_id, p)) prog.procedures;
    state_variables := MAP (λv. (v.state_id, v)) prog.state_variables;
    immutables := prog.immutables;
    struct_layouts := MAP (λs. (s.struct_id, s)) prog.struct_layouts;
    type_declarations := prog.type_declarations
  |>
End

Definition lookup_procedure_def:
  lookup_procedure env f = ALOOKUP env.procedures f
End

Definition lookup_state_variable_def:
  lookup_state_variable env x = ALOOKUP env.state_variables x
End

Definition lookup_struct_layout_def:
  lookup_struct_layout env id = ALOOKUP env.struct_layouts id
End

Definition lookup_enum_def:
  lookup_enum env id =
    case ALOOKUP env.type_declarations id of
      SOME (EnumDeclaration members) => SOME members
    | _ => NONE
End

Definition lookup_user_value_def:
  lookup_user_value env id =
    case ALOOKUP env.type_declarations id of
      SOME (UserValueDeclaration ty) => SOME ty
    | _ => NONE
End

Definition lookup_struct_def:
  lookup_struct env id =
    case ALOOKUP env.type_declarations id of
      SOME (StructDeclaration fields) => SOME fields
    | _ => NONE
End

(* Types *)

Definition is_elementary_type_def[simp]:
  (is_elementary_type BoolT ⇔ T) ∧
  (is_elementary_type (UintT _) ⇔ T) ∧
  (is_elementary_type (IntT _) ⇔ T) ∧
  (is_elementary_type (AddressT _) ⇔ T) ∧
  (is_elementary_type (FixedBytesT _) ⇔ T) ∧
  (is_elementary_type _ ⇔ F)
End

(* A value read or stored as a whole: an elementary type or an enum. *)
Definition is_stored_scalar_type_def[simp]:
  (is_stored_scalar_type (EnumT _) ⇔ T) ∧
  (is_stored_scalar_type ty ⇔ is_elementary_type ty)
End

(* Whether a mapping is reachable through array elements and struct fields.
 * The fuel bounds the struct nesting depth: a reachable mapping is reachable
 * without revisiting a struct, so the number of declarations suffices and
 * recursive structs terminate.
 *)
Definition mapping_reachable_def:
  (mapping_reachable env (n : num) (MappingT _ _) ⇔ T) ∧
  (mapping_reachable env n (ArrayT ty _) ⇔ mapping_reachable env n ty) ∧
  (mapping_reachable env n (StructT id) ⇔
    if n = 0 then F else
    case lookup_struct env id of
      SOME fields => mapping_reachable_types env (n - 1) (MAP SND fields)
    | NONE => F) ∧
  (mapping_reachable env n _ ⇔ F) ∧
  (mapping_reachable_types env n [] ⇔ F) ∧
  (mapping_reachable_types env n (ty :: tys) ⇔
    mapping_reachable env n ty ∨ mapping_reachable_types env n tys)
Termination
  WF_REL_TAC ‘inv_image ($< LEX $<) (λx. case x of
    INL (env, n, ty) => (n, sol_type_size ty)
  | INR (env, n, tys) => (n, list_size sol_type_size tys))’ >>
  rw[list_size_def]
End

(* Environment-aware type validation: declared ids resolve, and memory and
 * calldata types reach no mapping, including through struct fields.
 * valid_type_shape checks only the type's own structure.
 *)
Definition declared_type_ok_def:
  (declared_type_ok env (ArrayT ty _) ⇔ declared_type_ok env ty) ∧
  (declared_type_ok env (MappingT key value) ⇔
    declared_type_ok env key ∧ declared_type_ok env value) ∧
  (declared_type_ok env (StructT id) ⇔ IS_SOME (lookup_struct env id)) ∧
  (declared_type_ok env (EnumT id) ⇔ IS_SOME (lookup_enum env id)) ∧
  (declared_type_ok env (UserValueT id) ⇔ IS_SOME (lookup_user_value env id)) ∧
  (declared_type_ok env (ContractT _) ⇔ F) ∧
  (declared_type_ok env (FunctionT _ _ parameters returns) ⇔
    declared_types_ok env parameters ∧
    declared_types_ok env returns) ∧
  (declared_type_ok env (LocatedT loc ty) ⇔
    declared_type_ok env ty ∧
    (loc ≠ StorageLoc ⇒
     ¬mapping_reachable env (LENGTH env.type_declarations) ty)) ∧
  (declared_type_ok env _ ⇔ T) ∧
  (declared_types_ok env [] ⇔ T) ∧
  (declared_types_ok env (ty :: tys) ⇔
    declared_type_ok env ty ∧ declared_types_ok env tys)
Termination
  WF_REL_TAC ‘measure (λx. case x of
    INL (env, ty) => sol_type_size ty
  | INR (env, tys) => list_size sol_type_size tys)’ >>
  rw[solidityASTTheory.sol_type_size_def, list_size_def]
End

Definition is_function_type_def[simp]:
  (is_function_type (FunctionT _ _ _ _) ⇔ T) ∧
  (is_function_type _ ⇔ F)
End

(* Stage 2 bindings, parameters and returns are non-function value types. *)
Definition core_scalar_type_def:
  core_scalar_type env ty ⇔
    is_value_type ty ∧ ¬is_function_type ty ∧ valid_type_shape ty ∧
    declared_type_ok env ty
End

(* The bytes a value type occupies in a storage slot. An enum takes one byte;
 * user-defined value types are not stored yet.
 *)
Definition storage_bytes_def:
  storage_bytes ty =
    case ty of
      BoolT => SOME 1
    | EnumT _ => SOME 1
    | UintT n => SOME (n DIV 8)
    | IntT n => SOME (n DIV 8)
    | AddressT _ => SOME 20
    | FixedBytesT n => SOME n
    | _ => NONE
End

(* ReferenceType represents a captured storage location, even at a scalar
 * leaf. Struct declarations resolve through the environment's layout table.
 *)
Definition elementary_storage_type_ok_def:
  (elementary_storage_type_ok BoolT ⇔ T) ∧
  (elementary_storage_type_ok (UintT n) ⇔ valid_int_width n) ∧
  (elementary_storage_type_ok (IntT n) ⇔ valid_int_width n) ∧
  (elementary_storage_type_ok (AddressT _) ⇔ T) ∧
  (elementary_storage_type_ok (FixedBytesT n) ⇔ valid_fixed_bytes_width n) ∧
  (elementary_storage_type_ok _ ⇔ F)
End

(* Fixed arrays start on a slot boundary, including each nested row. Scalar
 * elements share slots without straddling a boundary. *)
Definition fixed_storage_slots_def:
  fixed_storage_slots env ty =
    case ty of
      ArrayT element (SOME n) =>
        if n = 0 then NONE else
        (case storage_bytes element of
           SOME b =>
             if b = 0 ∨ 32 < b then NONE else
             let per_slot = 32 DIV b in
             SOME ((n + per_slot - 1) DIV per_slot)
         | NONE => OPTION_MAP (λslots. n * slots)
                     (fixed_storage_slots env element))
    | BytesT => SOME 1
    | StringT => SOME 1
    | ArrayT _ NONE => SOME 1
    | MappingT _ _ => SOME 1
    | StructT id => OPTION_MAP (λs. s.struct_slots) (lookup_struct_layout env id)
    | _ => OPTION_MAP (K 1) (storage_bytes ty)
Termination
  WF_REL_TAC ‘measure (sol_type_size o SND)’
End

Definition storage_type_ok_def:
  (storage_type_ok env (ArrayT element (SOME n)) ⇔
    0 < n ∧ n < 2 ** 256 ∧ storage_type_ok env element ∧
    IS_SOME (fixed_storage_slots env (ArrayT element (SOME n)))) ∧
  (storage_type_ok env (MappingT key value) ⇔
    elementary_storage_type_ok key ∧ storage_type_ok env value) ∧
  (storage_type_ok env (ArrayT element NONE) ⇔ storage_type_ok env element) ∧
  (storage_type_ok env (StructT id) ⇔ IS_SOME (lookup_struct_layout env id)) ∧
  (storage_type_ok env (EnumT id) ⇔ IS_SOME (lookup_enum env id)) ∧
  (storage_type_ok env BytesT ⇔ T) ∧
  (storage_type_ok env StringT ⇔ T) ∧
  (storage_type_ok env ty ⇔ elementary_storage_type_ok ty)
End

(* Located byte sequences are values; captured lvalues use ReferenceType. *)
Definition byte_sequence_type_def:
  byte_sequence_type ty ⇔ ty = BytesT ∨ ty = StringT
End

Definition byte_sequence_value_type_def:
  byte_sequence_value_type ty ⇔
    case ty of
      LocatedT loc element => byte_sequence_type element
    | _ => F
End

(* What a memory reference denotes: a byte sequence, or an array whose
 * elements are elementary values or, as pointers, other memory objects. *)
Definition memory_object_type_def:
  (memory_object_type (ArrayT element length) ⇔
    valid_array_length length ∧
    ((is_elementary_type element ∧ valid_type_shape element) ∨
     memory_object_type element)) ∧
  (memory_object_type ty ⇔ byte_sequence_type ty)
End

(* What a storage pointer denotes: a byte sequence, an array, a mapping or a
 * struct. Its shape is checked against the environment by storage_type_ok. *)
Definition storage_object_type_def:
  storage_object_type ty ⇔
    case ty of
      ArrayT _ _ => T
    | MappingT _ _ => T
    | StructT _ => T
    | _ => byte_sequence_type ty
End

(* Whether an encoding of the type has a fixed size, with no offsets. *)
Definition static_object_type_def:
  (static_object_type (ArrayT element (SOME n)) ⇔ static_object_type element) ∧
  (static_object_type (ArrayT element NONE) ⇔ F) ∧
  (static_object_type ty ⇔ ¬byte_sequence_type ty)
End

(* What a calldata reference denotes: a byte sequence, or an array read in
 * place from its ABI encoding. A fixed-size array's elements are static, so
 * every dynamic object is reached through an offset and a length. *)
Definition calldata_object_type_def:
  (calldata_object_type (ArrayT element NONE) ⇔
    (is_elementary_type element ∧ valid_type_shape element) ∨
    calldata_object_type element) ∧
  (calldata_object_type (ArrayT element (SOME n)) ⇔
    memory_object_type (ArrayT element (SOME n)) ∧ static_object_type element) ∧
  (calldata_object_type ty ⇔ byte_sequence_type ty)
End

(* Located values: byte sequences in any location, memory and calldata arrays,
 * and storage pointers. *)
Definition located_value_type_def:
  located_value_type ty ⇔
    case ty of
      LocatedT MemoryLoc element => memory_object_type element
    | LocatedT CalldataLoc element => calldata_object_type element
    | LocatedT StorageLoc element => storage_object_type element
    | LocatedT loc element => byte_sequence_type element
    | _ => F
End

(* The type of an element of a memory or calldata array: a value, or a
 * reference in the array's location. *)
Definition element_type_def:
  element_type loc element =
    if is_stored_scalar_type element then element else LocatedT loc element
End

(* ABI values contain scalars (an enum as a uint8), byte sequences in
 * memory/calldata and memory arrays; storage pointers never cross an ABI
 * boundary. *)
Definition abi_value_type_def:
  abi_value_type ty ⇔
    is_stored_scalar_type ty ∨
    (located_value_type ty ∧
     case ty of LocatedT StorageLoc _ => F | _ => T)
End

Definition core_binding_type_def:
  core_binding_type env ty ⇔
    core_scalar_type env ty ∨
    (located_value_type ty ∧
     case ty of LocatedT StorageLoc element => storage_type_ok env element | _ => T)
End

(* The storage type a binding can be navigated through: a captured lvalue or a
 * storage pointer. *)
Definition storage_base_def:
  storage_base binding =
    case binding of
      SOME (ReferenceType ty) => SOME ty
    | SOME (SingleType (LocatedT StorageLoc ty)) => SOME ty
    | _ => NONE
End

(* ProductType is reserved for tuples and multiple returns: never singleton. *)
Definition wf_core_value_type_def:
  (wf_core_value_type env (SingleType ty) ⇔
    core_binding_type env ty) ∧
  (wf_core_value_type env (ReferenceType ty) ⇔ storage_type_ok env ty) ∧
  (wf_core_value_type env (ProductType tys) ⇔
    LENGTH tys ≠ 1 ∧ wf_core_value_types env tys) ∧
  (wf_core_value_types env [] ⇔ T) ∧
  (wf_core_value_types env (ty :: tys) ⇔
    wf_core_value_type env ty ∧ wf_core_value_types env tys)
Termination
  WF_REL_TAC ‘measure (λx. case x of
    INL (env, ty) => core_value_type_size ty
  | INR (env, tys) => list_size core_value_type_size tys)’ >>
  rw[solidityCoreTheory.core_value_type_size_def, list_size_def]
End

Definition wf_type_declaration_def:
  (wf_type_declaration env (EnumDeclaration members) ⇔
    0 < members ∧ members ≤ 256) ∧
  (wf_type_declaration env (UserValueDeclaration ty) ⇔
    is_elementary_type ty ∧ valid_type_shape ty) ∧
  (wf_type_declaration env (StructDeclaration fields) ⇔
    fields ≠ [] ∧ ALL_DISTINCT (MAP FST fields) ∧
    EVERY (λ(_, ty). valid_type_shape ty ∧ outer_location_free ty ∧
                     declared_type_ok env ty) fields)
End

(* Values *)

(* The n-bit two's complement range when signed, otherwise [0, 2 ** n). *)
Definition integer_in_range_def:
  integer_in_range signed n (i : int) ⇔
    if signed then -&(2 ** (n - 1)) ≤ i ∧ i < &(2 ** (n - 1))
    else 0 ≤ i ∧ i < &(2 ** n)
End

Definition elementary_scalar_has_type_def:
  (elementary_scalar_has_type BoolT (BoolValue _) ⇔ T) ∧
  (elementary_scalar_has_type (UintT n) (IntegerValue i) ⇔
    integer_in_range F n i) ∧
  (elementary_scalar_has_type (IntT n) (IntegerValue i) ⇔
    integer_in_range T n i) ∧
  (elementary_scalar_has_type (AddressT _) (AddressValue _) ⇔ T) ∧
  (elementary_scalar_has_type (FixedBytesT n) (BytesValue bs) ⇔
    LENGTH bs = n) ∧
  (elementary_scalar_has_type _ _ ⇔ F)
End

(* Function types never reach this relation: core_scalar_type excludes them. *)
Definition scalar_has_type_def:
  scalar_has_type env ty s ⇔
    case ty of
      EnumT id =>
        (case (lookup_enum env id, s) of
           (SOME members, IntegerValue i) => 0 ≤ i ∧ i < &members
         | _ => F)
    | UserValueT id =>
        (case lookup_user_value env id of
           SOME underlying => elementary_scalar_has_type underlying s
         | NONE => F)
    | _ => elementary_scalar_has_type ty s
End

(* Runtime typing seed for the evaluator's progress argument. Reference values
 * are not typed until reference/layout environments exist.
 *)
Definition value_has_type_def:
  (value_has_type env (SingleType ty) (ScalarValue s) ⇔
    scalar_has_type env ty s) ∧
  (value_has_type env (ReferenceType ty)
     (ReferenceValue (StorageReference PersistentStorage _ _ offset rty _)) ⇔
    ty = rty ∧ storage_type_ok env ty ∧
    (case storage_bytes ty of SOME b => offset + b ≤ 32 | NONE => offset = 0)) ∧
  (value_has_type env (SingleType (LocatedT CalldataLoc ty))
     (ReferenceValue (CalldataReference _ _ rty)) ⇔
    ty = rty ∧ calldata_object_type ty) ∧
  (value_has_type env (SingleType (LocatedT MemoryLoc ty))
     (ReferenceValue (MemoryReference _ 0 rty)) ⇔
    ty = rty ∧ memory_object_type ty) ∧
  (value_has_type env (SingleType (LocatedT StorageLoc ty))
     (ReferenceValue (StorageReference PersistentStorage _ _ 0 rty _)) ⇔
    ty = rty ∧ storage_object_type ty ∧ storage_type_ok env ty) ∧
  (value_has_type env (ProductType tys) (TupleValue vs) ⇔
    values_have_types env tys vs) ∧
  (value_has_type env _ _ ⇔ F) ∧
  (values_have_types env [] [] ⇔ T) ∧
  (values_have_types env (ty::tys) (v::vs) ⇔
    value_has_type env ty v ∧ values_have_types env tys vs) ∧
  (values_have_types env _ _ ⇔ F)
End

(* Checking context: bindings and captured targets share one id namespace. *)
Datatype:
  core_check_context = <|
    bindings : (ast_id # core_value_type) list;
    targets : (ast_id # sol_type) list;
    returns : sol_type list;
    in_loop : bool
  |>
End

Definition fresh_core_id_def:
  fresh_core_id ctx x ⇔
    ALOOKUP ctx.bindings x = NONE ∧ ALOOKUP ctx.targets x = NONE
End

Definition bind_core_id_def:
  bind_core_id x ty ctx = ctx with bindings := (x, ty) :: ctx.bindings
End

Definition capture_core_target_def:
  capture_core_target t ty ctx = ctx with targets := (t, ty) :: ctx.targets
End

(* Constants have no synthesized type, so atoms are checked against one. *)
Definition wf_core_atom_def:
  (wf_core_atom env ctx ty (BoundAtom x) ⇔
    ALOOKUP ctx.bindings x = SOME ty) ∧
  (wf_core_atom env ctx (SingleType ty) (ConstantAtom s) ⇔
    scalar_has_type env ty s) ∧
  (wf_core_atom env ctx _ (ConstantAtom _) ⇔ F)
End

(* A call's gas option, if it has one, is a uint256. *)
Definition wf_gas_atom_def:
  (wf_gas_atom env ctx NONE ⇔ T) ∧
  (wf_gas_atom env ctx (SOME g) ⇔ wf_core_atom env ctx (SingleType (UintT 256)) g)
End

(* ABI serialization consumes bytes from their original location. Literal
 * bytes are already available and need no heap object for encoding. A memory
 * array is encoded from its heap object. *)
Definition wf_abi_atom_def:
  wf_abi_atom env ctx ty a ⇔
    case ty of
      LocatedT _ (ArrayT element length) =>
        (case a of
           BoundAtom x =>
             (case ALOOKUP ctx.bindings x of
                SOME (SingleType (LocatedT loc actual)) =>
                  actual = ArrayT element length ∧ located_value_type (LocatedT loc actual)
              | _ => F)
         | _ => F)
    | LocatedT _ element =>
        byte_sequence_type element ∧
        (case a of
           ConstantAtom (BytesValue _) => T
         | BoundAtom x =>
             (case ALOOKUP ctx.bindings x of
                SOME (SingleType (LocatedT _ actual)) => element = actual
              | _ => F)
         | _ => F)
    | _ => wf_core_atom env ctx (SingleType ty) a
End

(* Operations *)

Definition wf_core_atoms_def:
  (wf_core_atoms env ctx [] [] ⇔ T) ∧
  (wf_core_atoms env ctx (ty :: tys) (a :: atoms) ⇔
    wf_core_atom env ctx ty a ∧ wf_core_atoms env ctx tys atoms) ∧
  (wf_core_atoms env ctx _ _ ⇔ F)
End

Theorem wf_core_atoms_list_rel:
  wf_core_atoms env ctx tys atoms ⇔ LIST_REL (wf_core_atom env ctx) tys atoms
Proof
  qid_spec_tac ‘atoms’ >> Induct_on ‘tys’ >> Cases_on ‘atoms’ >>
  simp[wf_core_atoms_def]
QED

Definition is_integer_type_def[simp]:
  (is_integer_type (UintT _) ⇔ T) ∧
  (is_integer_type (IntT _) ⇔ T) ∧
  (is_integer_type _ ⇔ F)
End

Definition is_bitwise_type_def[simp]:
  (is_bitwise_type (UintT _) ⇔ T) ∧
  (is_bitwise_type (IntT _) ⇔ T) ∧
  (is_bitwise_type (FixedBytesT _) ⇔ T) ∧
  (is_bitwise_type _ ⇔ F)
End

Definition is_ordered_type_def[simp]:
  (is_ordered_type (UintT _) ⇔ T) ∧
  (is_ordered_type (IntT _) ⇔ T) ∧
  (is_ordered_type (AddressT _) ⇔ T) ∧
  (is_ordered_type (FixedBytesT _) ⇔ T) ∧
  (is_ordered_type (EnumT _) ⇔ T) ∧
  (is_ordered_type _ ⇔ F)
End

Definition is_equality_type_def[simp]:
  (is_equality_type BoolT ⇔ T) ∧
  (is_equality_type ty ⇔ is_ordered_type ty)
End

(* The operation's sol_type is the left operand's type. The signature gives
 * every operand's type and the result type: comparisons yield BoolT, and the
 * shift amount and exponent are uint256. The arithmetic mode only matters for
 * operators that can overflow.
 *)
Definition scalar_operator_signature_def:
  scalar_operator_signature op ty =
    case op of
      AddOp => if is_integer_type ty then SOME ([ty; ty], ty) else NONE
    | SubtractOp => if is_integer_type ty then SOME ([ty; ty], ty) else NONE
    | MultiplyOp => if is_integer_type ty then SOME ([ty; ty], ty) else NONE
    | DivideOp => if is_integer_type ty then SOME ([ty; ty], ty) else NONE
    | RemainderOp => if is_integer_type ty then SOME ([ty; ty], ty) else NONE
    | ExponentOp =>
        if is_integer_type ty then SOME ([ty; UintT 256], ty) else NONE
    | AddModOp => if ty = UintT 256 then SOME ([ty; ty; ty], ty) else NONE
    | MulModOp => if ty = UintT 256 then SOME ([ty; ty; ty], ty) else NONE
    | ShiftLeftOp =>
        if is_bitwise_type ty then SOME ([ty; UintT 256], ty) else NONE
    | ShiftRightOp =>
        if is_bitwise_type ty then SOME ([ty; UintT 256], ty) else NONE
    | EqualOp => if is_equality_type ty then SOME ([ty; ty], BoolT) else NONE
    | LessThanOp => if is_ordered_type ty then SOME ([ty; ty], BoolT) else NONE
    | BitAndOp => if is_bitwise_type ty then SOME ([ty; ty], ty) else NONE
    | BitOrOp => if is_bitwise_type ty then SOME ([ty; ty], ty) else NONE
    | BitXorOp => if is_bitwise_type ty then SOME ([ty; ty], ty) else NONE
    | NegateOp => (case ty of IntT _ => SOME ([ty], ty) | _ => NONE)
    | BitNotOp => if is_bitwise_type ty then SOME ([ty], ty) else NONE
    | BoolNotOp => if ty = BoolT then SOME ([ty], ty) else NONE
End

(* Explicit elementary conversions as solc admits them, including the identity
 * used for moves and default initialization. A payable address converts to
 * integers and fixed bytes only through a non-payable address. Contract types
 * are not admitted (declared_type_ok), so their conversions are absent.
 * Truncation/panic behaviour belongs to evaluation.
 *)
Definition elementary_convertible_def:
  elementary_convertible src dst ⇔
    src = dst ∨
    case (src, dst) of
      (UintT _, UintT _) => T
    | (IntT _, IntT _) => T
    | (UintT m, IntT n) => m = n
    | (IntT m, UintT n) => m = n
    | (FixedBytesT _, FixedBytesT _) => T
    | (UintT m, FixedBytesT n) => m = 8 * n
    | (FixedBytesT m, UintT n) => n = 8 * m
    | (AddressT _, AddressT _) => T
    | (AddressT NonpayableAddress, UintT n) => n = 160
    | (UintT m, AddressT NonpayableAddress) => m = 160
    | (AddressT NonpayableAddress, FixedBytesT n) => n = 20
    | (FixedBytesT m, AddressT NonpayableAddress) => m = 20
    | (EnumT _, UintT _) => T
    | (UintT _, EnumT _) => T
    | (IntT _, EnumT _) => T
    | _ => F
End

(* User-defined value types wrap/unwrap through their underlying type. *)
Definition core_convertible_def:
  core_convertible env src dst ⇔
    elementary_convertible src dst ∨
    (case src of
       UserValueT id => lookup_user_value env id = SOME dst
     | _ => F) ∨
    (case dst of
       UserValueT id => lookup_user_value env id = SOME src
     | _ => F)
End

(* Implicit conversions, following isImplicitlyConvertibleTo in
 * libsolidity/ast/Types.cpp at SOLIDITY_PIN: identity, integer widening with
 * the same signedness (uintM to intN is never implicit), fixed bytes widening,
 * and address payable to address. Enums, user-defined value types and bool
 * convert implicitly only to themselves. Elaboration emits implicit
 * conversions as explicit ConvertOperations; each is also explicit.
 *)
Definition implicitly_convertible_def:
  implicitly_convertible src dst ⇔
    src = dst ∨
    case (src, dst) of
      (UintT m, UintT n) => m ≤ n
    | (IntT m, IntT n) => m ≤ n
    | (FixedBytesT m, FixedBytesT n) => m ≤ n
    | (AddressT PayableAddress, AddressT NonpayableAddress) => T
    | _ => F
End

(* The arrays an assignment copies into a storage array of type dst: the
 * same shape, a fixed-size dimension also into a dynamic one or a longer
 * fixed-size one, with leaves implicitly convertible. *)
Definition storage_copy_type_def:
  storage_copy_type src dst ⇔
    case (src, dst) of
      (ArrayT e l, ArrayT e' l') =>
        (case (l, l') of
           (_, NONE) => T
         | (SOME n, SOME m) => n ≤ m
         | _ => F) ∧ storage_copy_type e e'
    | (ArrayT _ _, _) => F
    | (_, ArrayT _ _) => F
    | _ => implicitly_convertible src dst
Termination
  WF_REL_TAC ‘measure (sol_type_size o FST)’ >>
  rw[solidityASTTheory.sol_type_size_def]
End

Theorem implicitly_convertible_explicit:
  implicitly_convertible src dst ⇒ core_convertible env src dst
Proof
  Cases_on ‘src’ >> Cases_on ‘dst’ >>
  rw[implicitly_convertible_def, core_convertible_def,
     elementary_convertible_def] >>
  gvs[AllCaseEqs()]
QED

Definition call_result_type_def[simp]:
  (call_result_type [] = ProductType []) ∧
  (call_result_type [ty] = SingleType ty) ∧
  (call_result_type tys = ProductType (MAP SingleType tys))
End

Definition environment_type_def:
  environment_type f =
    case f of
      MsgData => LocatedT CalldataLoc BytesT
    | MsgSender => AddressT NonpayableAddress
    | SelfAddress => AddressT NonpayableAddress
    | TxOrigin => AddressT NonpayableAddress
    | BlockCoinbase => AddressT PayableAddress
    | _ => UintT 256
End

(* Between bytes and string in one location, or the identity on a located
 * value: a reference keeps its object. *)
Definition reference_convertible_def:
  reference_convertible src dst ⇔
    (src = dst ∧ located_value_type src) ∨
    case (src, dst) of
      (LocatedT loc a, LocatedT loc' b) =>
        loc = loc' ∧ byte_sequence_type a ∧ byte_sequence_type b
    | _ => F
End

Definition wf_core_operation_def:
  (wf_core_operation env ctx annotation
     (ScalarOperation ty mode op args) ⇔
    core_scalar_type env ty ∧
    case scalar_operator_signature op ty of
      SOME (operand_tys, result) =>
        wf_core_atoms env ctx (MAP SingleType operand_tys) args ∧
        annotation = SingleType result
    | NONE => F) ∧
  (wf_core_operation env ctx annotation (ConvertOperation ty a) ⇔
    annotation = SingleType ty ∧
    case a of
      ConstantAtom s => scalar_has_type env ty s
    | BoundAtom x =>
        (case ALOOKUP ctx.bindings x of
           SOME (SingleType src) =>
             core_convertible env src ty ∨ reference_convertible src ty
         | _ => F)) ∧
  (wf_core_operation env ctx annotation (TupleOperation atoms) ⇔
    case annotation of
      ProductType tys => wf_core_atoms env ctx tys atoms
    | _ => F) ∧
  (wf_core_operation env ctx annotation (TupleComponentOperation n a) ⇔
    case a of
      BoundAtom x =>
        (case ALOOKUP ctx.bindings x of
           SOME (ProductType tys) =>
             if n < LENGTH tys then annotation = EL n tys else F
         | _ => F)
    | ConstantAtom _ => F) ∧
  (wf_core_operation env ctx annotation (StateReferenceOperation x) ⇔
    case lookup_state_variable env x of
      SOME v => annotation = ReferenceType v.state_type
    | NONE => F) ∧
  (wf_core_operation env ctx annotation (ImmutableReferenceOperation x) ⇔
    case ALOOKUP env.immutables x of
      SOME ty => annotation = ReferenceType ty
    | NONE => F) ∧
  (wf_core_operation env ctx annotation (ReadOperation ty a) ⇔
    (if storage_object_type ty then
       annotation = SingleType (LocatedT StorageLoc ty)
     else annotation = SingleType ty ∧ core_scalar_type env ty ∧
          IS_SOME (storage_bytes ty)) ∧
    wf_core_atom env ctx (ReferenceType ty) a) ∧
  (wf_core_operation env ctx annotation
     (NavigateOperation ty base (FieldNavigation field)) ⇔
    annotation = ReferenceType ty ∧
    case base of
      BoundAtom x =>
        (case storage_base (ALOOKUP ctx.bindings x) of
           SOME (StructT id) =>
             (case lookup_struct env id of
                SOME fields => ALOOKUP fields field = SOME ty
              | NONE => F)
         | _ => F)
    | _ => F) ∧
  (wf_core_operation env ctx annotation
     (NavigateOperation ty base (IndexNavigation index)) ⇔
    annotation = ReferenceType ty ∧
    case base of
      BoundAtom x =>
        (case ALOOKUP ctx.bindings x of
           SOME (SingleType (LocatedT loc BytesT)) =>
             loc ≠ CalldataLoc ∧ ty = FixedBytesT 1 ∧ wf_core_atom env ctx (SingleType (UintT 256)) index
         | b =>
           case storage_base b of
             SOME (MappingT key value) =>
               value = ty ∧ wf_core_atom env ctx (SingleType key) index
           | SOME (ArrayT element _) =>
               element = ty ∧ wf_core_atom env ctx (SingleType (UintT 256)) index
           | _ => F)
    | _ => F) ∧
  (wf_core_operation env ctx annotation (DefaultMemoryOperation ty) ⇔
    memory_object_type ty ∧ annotation = SingleType (LocatedT MemoryLoc ty)) ∧
  (wf_core_operation env ctx annotation (BytesLiteralOperation ty _) ⇔
    annotation = SingleType (LocatedT MemoryLoc ty) ∧ byte_sequence_type ty) ∧
  (wf_core_operation env ctx annotation (AllocateMemoryOperation ty length) ⇔
    annotation = SingleType (LocatedT MemoryLoc ty) ∧
    (byte_sequence_type ty ∨
     (memory_object_type ty ∧ case ty of ArrayT _ NONE => T | _ => F)) ∧
    wf_core_atom env ctx (SingleType (UintT 256)) length) ∧
  (wf_core_operation env ctx annotation (ByteIndexOperation a index) ⇔
    annotation = SingleType (FixedBytesT 1) ∧
    (wf_core_atom env ctx (SingleType (LocatedT CalldataLoc BytesT)) a ∨
     wf_core_atom env ctx (SingleType (LocatedT MemoryLoc BytesT)) a ∨
     wf_core_atom env ctx (SingleType (LocatedT StorageLoc BytesT)) a) ∧
    wf_core_atom env ctx (SingleType (UintT 256)) index) ∧
  (wf_core_operation env ctx annotation (ArrayIndexOperation a index) ⇔
    wf_core_atom env ctx (SingleType (UintT 256)) index ∧
    case a of
      BoundAtom x =>
        (case ALOOKUP ctx.bindings x of
           SOME (SingleType (LocatedT loc (ArrayT element length))) =>
             located_value_type (LocatedT loc (ArrayT element length)) ∧
             annotation = SingleType (element_type loc element)
         | _ => F)
    | _ => F) ∧
  (wf_core_operation env ctx annotation (CopyToMemoryOperation a) ⇔
    case (a, annotation) of
      (BoundAtom x, SingleType (LocatedT MemoryLoc ty)) =>
        (ALOOKUP ctx.bindings x = SOME (SingleType (LocatedT CalldataLoc ty)) ∨
         ALOOKUP ctx.bindings x = SOME (SingleType (LocatedT StorageLoc ty))) ∧
        located_value_type (LocatedT MemoryLoc ty) ∧ (case ty of ArrayT _ _ => T | _ => F)
    | _ => F) ∧
  (wf_core_operation env ctx annotation (Keccak256Operation a) ⇔
    annotation = SingleType (FixedBytesT 32) ∧
    wf_core_atom env ctx (SingleType (LocatedT MemoryLoc BytesT)) a) ∧
  (wf_core_operation env ctx annotation (EcrecoverOperation h v r s) ⇔
    annotation = SingleType (AddressT NonpayableAddress) ∧
    wf_core_atom env ctx (SingleType (FixedBytesT 32)) h ∧
    wf_core_atom env ctx (SingleType (UintT 8)) v ∧
    wf_core_atom env ctx (SingleType (FixedBytesT 32)) r ∧
    wf_core_atom env ctx (SingleType (FixedBytesT 32)) s) ∧
  (wf_core_operation env ctx annotation (CodeLengthOperation a) ⇔
    annotation = SingleType (UintT 256) ∧
    (wf_core_atom env ctx (SingleType (AddressT NonpayableAddress)) a ∨
     wf_core_atom env ctx (SingleType (AddressT PayableAddress)) a)) ∧
  (wf_core_operation env ctx annotation (AbiEncodeOperation selector tys args) ⇔
    annotation = SingleType (LocatedT MemoryLoc BytesT) ∧
    (case selector of
       NONE => T
     | SOME s => wf_core_atom env ctx (SingleType (FixedBytesT 4)) s) ∧
    EVERY (λty. abi_value_type ty ∧ valid_type_shape ty) tys ∧
    LIST_REL (wf_abi_atom env ctx) tys args) ∧
  (* A byte sequence argument is encoded where it is, in any location. *)
  (wf_core_operation env ctx annotation (AbiEncodePackedOperation tys args) ⇔
    (annotation = SingleType (LocatedT MemoryLoc BytesT) ∨
     annotation = SingleType (LocatedT MemoryLoc StringT)) ∧
    EVERY (λty. is_stored_scalar_type ty ∨
                case ty of
                  LocatedT MemoryLoc element => byte_sequence_type element
                | _ => F) tys ∧
    LIST_REL (wf_abi_atom env ctx) tys args) ∧
  (* Only call moves value. The data is packed where it is, so a bytes
     literal needs no memory copy. *)
  (wf_core_operation env ctx annotation
     (LowLevelCallOperation kind target value gas data) ⇔
    annotation = call_result_type [BoolT; LocatedT MemoryLoc BytesT] ∧
    wf_core_atom env ctx (SingleType (AddressT NonpayableAddress)) target ∧
    wf_core_atom env ctx (SingleType (UintT 256)) value ∧
    (kind ≠ ExternalCall ⇒ value = ConstantAtom (IntegerValue 0)) ∧
    wf_gas_atom env ctx gas ∧
    (case data of
       ConstantAtom (BytesValue _) => T
     | _ => wf_core_atom env ctx (SingleType (LocatedT MemoryLoc BytesT)) data)) ∧
  (wf_core_operation env ctx annotation (AbiDecodeOperation tys a) ⇔
    tys ≠ [] ∧ EVERY (λty. is_elementary_type ty ∧ valid_type_shape ty) tys ∧
    annotation = call_result_type tys ∧
    wf_core_atom env ctx (SingleType (LocatedT MemoryLoc BytesT)) a) ∧
  (wf_core_operation env ctx annotation (ArrayLengthOperation a) ⇔
    annotation = SingleType (UintT 256) ∧
    case a of
      BoundAtom x =>
        (case ALOOKUP ctx.bindings x of
           SOME (SingleType (LocatedT loc ty)) =>
             byte_sequence_type ty ∨ (case ty of ArrayT _ _ => T | _ => F)
         | SOME (ReferenceType (ArrayT _ NONE)) => T
         | _ => F)
    | _ => F) ∧
  (wf_core_operation env ctx annotation (ArrayPushOperation a value) ⇔
    case a of
      BoundAtom x =>
        (case storage_base (ALOOKUP ctx.bindings x) of
           SOME (ArrayT element NONE) =>
             storage_type_ok env element ∧
             annotation = ReferenceType element ∧
             (case value of
                NONE => T
              | SOME v =>
                  IS_SOME (storage_bytes element) ∧
                  wf_core_atom env ctx (SingleType element) v)
         | _ => F)
    | _ => F) ∧
  (wf_core_operation env ctx annotation (ArrayPopOperation a) ⇔
    annotation = ProductType [] ∧
    case a of
      BoundAtom x =>
        (case storage_base (ALOOKUP ctx.bindings x) of
           SOME (ArrayT element NONE) =>
             storage_type_ok env element ∧ IS_SOME (storage_bytes element)
         | _ => F)
    | _ => F) ∧
  (wf_core_operation env ctx annotation (InternalCallOperation f args) ⇔
    case lookup_procedure env f of
      SOME p =>
        wf_core_atoms env ctx (MAP (λ(_, ty). SingleType ty) p.parameters) args ∧
        annotation = call_result_type (MAP SND p.return_bindings)
    | NONE => F) ∧
  (wf_core_operation env ctx annotation (EnvironmentOperation f) ⇔
    annotation = SingleType (environment_type f)) ∧
  (* High-level calls pass elementary values; a view or pure callee is
     called statically, with no value. *)
  (wf_core_operation env ctx annotation
     (ExternalCallOperation kind selector params rets target value gas args) ⇔
    kind ≠ ExternalDelegateCall ∧ LENGTH selector = 4 ∧
    EVERY (λty. abi_value_type ty ∧ valid_type_shape ty) (params ++ rets) ∧
    (* Returndata belongs to the caller's memory, never its calldata. *)
    EVERY (λty. is_elementary_type ty ∨
                case ty of LocatedT MemoryLoc _ => T | _ => F) rets ∧
    wf_core_atom env ctx (SingleType (AddressT NonpayableAddress)) target ∧
    wf_core_atom env ctx (SingleType (UintT 256)) value ∧
    (kind = ExternalStaticCall ⇒ value = ConstantAtom (IntegerValue 0)) ∧
    wf_gas_atom env ctx gas ∧
    LIST_REL (wf_abi_atom env ctx) params args ∧
    annotation = call_result_type rets) ∧
  (wf_core_operation env ctx annotation
     (TryExternalCallOperation kind selector params rets target value gas args) ⇔
    kind ≠ ExternalDelegateCall ∧ LENGTH selector = 4 ∧
    EVERY (λty. abi_value_type ty ∧ valid_type_shape ty) params ∧
    EVERY (λty. is_stored_scalar_type ty ∧ valid_type_shape ty) rets ∧
    wf_core_atom env ctx (SingleType (AddressT NonpayableAddress)) target ∧
    wf_core_atom env ctx (SingleType (UintT 256)) value ∧
    (kind = ExternalStaticCall ⇒ value = ConstantAtom (IntegerValue 0)) ∧
    wf_gas_atom env ctx gas ∧
    LIST_REL (wf_abi_atom env ctx) params args ∧
    annotation = ProductType
      (MAP SingleType (BoolT :: rets ++ [LocatedT MemoryLoc BytesT]))) ∧
  (wf_core_operation env ctx annotation _ ⇔ F)
End

(* Revert payloads are provisional pre-encoded constants until ABI encoding:
 * the BytesValue is raw revert data of any length, not a bytesN scalar.
 *)
Definition provisional_revert_payload_def:
  (provisional_revert_payload (ConstantAtom (BytesValue _)) ⇔ T) ∧
  (provisional_revert_payload _ ⇔ F)
End

(* Event arguments are ABI values, and an indexed one is no array; the count
 * of indexed ones, which with topic0 must fit the four topics of a log.
 *)
Definition emit_indexed_count_def:
  (emit_indexed_count env ctx [] = SOME (0 : num)) ∧
  (emit_indexed_count env ctx ((ty, indexed, a) :: args) =
    if abi_value_type ty ∧ valid_type_shape ty ∧
       (indexed ⇒ ¬located_value_type ty ∨ byte_sequence_value_type ty) ∧
       wf_abi_atom env ctx ty a then
      case emit_indexed_count env ctx args of
        SOME n => SOME (if indexed then n + 1 else n)
      | NONE => NONE
    else NONE)
End

(* Statements: lexical scopes. A block's definitions and captures extend the
 * context for later statements in that block only; prelude definitions are
 * visible in the loop condition and body. Targets are therefore scoped like
 * bindings, and a runtime target map must be saved and restored per scope, or
 * capture must overwrite. Any single-typed binding may be captured, parameters
 * and temporaries included. Break/continue are only legal in a loop body (a
 * prelude is not one), and in_loop does not cross procedure boundaries.
 *)
(* The value types an inline assembly block reads and writes back as one
 * word. Enums and user-defined value types are left out: solc does not clean
 * a word written to one, so an out-of-range value would have no source
 * value. *)
Definition assembly_value_type_def[simp]:
  (assembly_value_type BoolT ⇔ T) ∧
  (assembly_value_type (UintT _) ⇔ T) ∧
  (assembly_value_type (IntT _) ⇔ T) ∧
  (assembly_value_type (AddressT _) ⇔ T) ∧
  (assembly_value_type (FixedBytesT _) ⇔ T) ∧
  (assembly_value_type _ ⇔ F)
End

(* The builtins an inline assembly block may not use. The source state keeps
 * no code, so the code and data builtins are left out, and so are
 * setimmutable and linkersymbol, which only the compiler's code uses. Gas,
 * calls and return data are limited by assembly_calls_ok instead. *)
Definition assembly_unsupported_def:
  assembly_unsupported =
    [YCodeSize; YCodeCopy; YDataSize; YDataOffset; YSetImmutable;
     YLinkerSymbol]
End

(* The builtins that change the world, which a static frame forbids. A call
 * may move value; staticcall is a static frame's call. *)
Definition assembly_state_writes_def:
  assembly_state_writes =
    [YSStore; YTStore; YLog0; YLog1; YLog2; YLog3; YLog4; YCall]
End

(* Whether a block's code calls none of the builtins in bad. *)
Definition assembly_expr_ok_def:
  (assembly_expr_ok bad (YulLit _) ⇔ T) ∧
  (assembly_expr_ok bad (YulName _) ⇔ T) ∧
  (assembly_expr_ok bad (YulBuiltin b es) ⇔
    ¬MEM b bad ∧ assembly_exprs_ok bad es) ∧
  (assembly_expr_ok bad (YulApply _ es) ⇔ assembly_exprs_ok bad es) ∧
  (* only the evaluator builds a checked call; source code has none *)
  (assembly_expr_ok bad (YulCheckedBuiltin _ _) ⇔ F) ∧
  (assembly_exprs_ok bad [] ⇔ T) ∧
  (assembly_exprs_ok bad (e :: es) ⇔
    assembly_expr_ok bad e ∧ assembly_exprs_ok bad es)
End

Definition assembly_stmt_ok_def:
  (assembly_stmt_ok bad (YulBlock ss) ⇔ assembly_stmts_ok bad ss) ∧
  (assembly_stmt_ok bad (YulFunction _ _ _ body) ⇔ assembly_stmts_ok bad body) ∧
  (assembly_stmt_ok bad (YulLet _ NONE) ⇔ T) ∧
  (assembly_stmt_ok bad (YulLet _ (SOME e)) ⇔ assembly_expr_ok bad e) ∧
  (assembly_stmt_ok bad (YulAssign _ e) ⇔ assembly_expr_ok bad e) ∧
  (assembly_stmt_ok bad (YulIf e body) ⇔
    assembly_expr_ok bad e ∧ assembly_stmts_ok bad body) ∧
  (assembly_stmt_ok bad (YulSwitch e cases default) ⇔
    assembly_expr_ok bad e ∧ assembly_cases_ok bad cases ∧
    assembly_stmts_ok bad default) ∧
  (assembly_stmt_ok bad (YulFor pre c post body) ⇔
    assembly_stmts_ok bad pre ∧ assembly_expr_ok bad c ∧
    assembly_stmts_ok bad post ∧ assembly_stmts_ok bad body) ∧
  (assembly_stmt_ok bad YulBreak ⇔ T) ∧
  (assembly_stmt_ok bad YulContinue ⇔ T) ∧
  (assembly_stmt_ok bad YulLeave ⇔ T) ∧
  (assembly_stmt_ok bad (YulExprStmt e) ⇔ assembly_expr_ok bad e) ∧
  (assembly_stmts_ok bad [] ⇔ T) ∧
  (assembly_stmts_ok bad (s :: ss) ⇔
    assembly_stmt_ok bad s ∧ assembly_stmts_ok bad ss) ∧
  (assembly_cases_ok bad [] ⇔ T) ∧
  (assembly_cases_ok bad ((_, body) :: cases) ⇔
    assembly_stmts_ok bad body ∧ assembly_cases_ok bad cases)
End

(* The memory a block may touch, where its addresses are literals. A block
 * starts from a memory holding the free memory pointer and the memory byte
 * sequences (bytes and string) and nothing else, so at a literal address it
 * may read only the free memory pointer and what it wrote itself earlier on
 * the same path; and a block that can exit normally may write at a literal
 * address only in the scratch space [0, 0x40). A read is covered by the
 * (start, length) ranges written at literal addresses before it in its
 * statement list or an enclosing one: an mstore's word, and a call's output
 * region, of which the callee may fill less (the runtime check then fails
 * the read closed). A block halts when its last statement is return, revert
 * or stop. An address the block computes (from a memory reference, say) is
 * checked as the block runs instead (assembly_result), and a read of length
 * zero touches nothing.
 *)
Definition yul_lit_def:
  (yul_lit (YulLit (LitNumber w)) = SOME (w2n (w : bytes32))) ∧
  (yul_lit _ = NONE)
End

(* The end of a range in ws holding byte a. *)
Definition range_end_def:
  (range_end [] a = NONE) ∧
  (range_end ((s, l) :: ws) a =
    if s ≤ a ∧ a < s + l then SOME (s + l) else range_end ws (a : num))
End

(* Whether the ranges ws cover [a, e), stepping to the end of a range holding
 * a. A range is stepped over at most once, so k = LENGTH ws steps suffice
 * whatever the lengths. *)
Definition memory_covered_def:
  (memory_covered 0 ws a e ⇔ e ≤ a) ∧
  (memory_covered (SUC k) ws a (e : num) ⇔
    e ≤ a ∨
    case range_end ws a of
      SOME b => memory_covered k ws b e
    | NONE => F)
End

Definition memory_read_ok_def:
  memory_read_ok ws p l ⇔
    yul_lit l = SOME 0 ∨
    case yul_lit p of
      NONE => T
    | SOME a =>
        case yul_lit l of
          SOME n => memory_covered (LENGTH ws) ws a (a + n)
        | NONE => F
End

Definition memory_write_ok_def:
  memory_write_ok halts p l ⇔
    halts ∨
    case yul_lit p of
      NONE => T
    | SOME a =>
        case l of
          SOME n => a + n ≤ 64n
        | NONE => F
End

Definition builtin_memory_ok_def:
  builtin_memory_ok halts ws b es ⇔
    case (b, es) of
      (YMLoad, [p]) =>
        memory_read_ok ws p (YulLit (LitNumber 32w))
    | (YMStore, [p; _]) => memory_write_ok halts p (SOME 32)
    | (YMStore8, [p; _]) => memory_write_ok halts p (SOME 1)
    | (YMCopy, [d; p; l]) =>
        memory_write_ok halts d (yul_lit l) ∧ memory_read_ok ws p l
    | (YCallDataCopy, [d; _; l]) => memory_write_ok halts d (yul_lit l)
    | (YReturnDataCopy, [d; _; l]) => memory_write_ok halts d (yul_lit l)
    | (YCall, [_; _; _; p; l; d; dl]) =>
        memory_read_ok ws p l ∧ memory_write_ok halts d (yul_lit dl)
    | (YStaticCall, [_; _; p; l; d; dl]) =>
        memory_read_ok ws p l ∧ memory_write_ok halts d (yul_lit dl)
    | (YKeccak256, [p; l]) => memory_read_ok ws p l
    | (YReturn, [p; l]) => memory_read_ok ws p l
    | (YRevert, [p; l]) => memory_read_ok ws p l
    | (YLog0, [p; l]) => memory_read_ok ws p l
    | (YLog1, p :: l :: _) => memory_read_ok ws p l
    | (YLog2, p :: l :: _) => memory_read_ok ws p l
    | (YLog3, p :: l :: _) => memory_read_ok ws p l
    | (YLog4, p :: l :: _) => memory_read_ok ws p l
    | (YMLoad, _) => F
    | (YMStore, _) => F
    | (YMStore8, _) => F
    | (YMCopy, _) => F
    | (YCallDataCopy, _) => F
    | (YReturnDataCopy, _) => F
    | (YCall, _) => F
    | (YStaticCall, _) => F
    | (YKeccak256, _) => F
    | (YReturn, _) => F
    | (YRevert, _) => F
    | (YLog0, _) => F
    | (YLog1, _) => F
    | (YLog2, _) => F
    | (YLog3, _) => F
    | (YLog4, _) => F
    | _ => T
End

(* The output region of a call, when its offset and size are literals. *)
Definition call_output_def:
  (call_output (YulBuiltin YCall [_; _; _; _; _; d; dl]) =
    case (yul_lit d, yul_lit dl) of
      (SOME a, SOME n) => [(a, n)]
    | _ => []) ∧
  (call_output (YulBuiltin YStaticCall [_; _; _; _; d; dl]) =
    case (yul_lit d, yul_lit dl) of
      (SOME a, SOME n) => [(a, n)]
    | _ => []) ∧
  (call_output _ = [])
End

(* The ranges a statement writes at literal addresses: an mstore's word, or
 * the output region of the call a let, an assignment or a pop takes. *)
Definition memory_store_def:
  (memory_store (YulExprStmt (YulBuiltin YMStore [p; _])) =
    case yul_lit p of
      SOME a => [(a, 32n)]
    | NONE => []) ∧
  (memory_store (YulExprStmt (YulBuiltin YPop [e])) = call_output e) ∧
  (memory_store (YulLet _ (SOME e)) = call_output e) ∧
  (memory_store (YulAssign _ e) = call_output e) ∧
  (memory_store _ = [])
End

Definition memory_expr_ok_def:
  (memory_expr_ok h ws (YulBuiltin b es) ⇔
    builtin_memory_ok h ws b es ∧ memory_exprs_ok h ws es) ∧
  (memory_expr_ok h ws (YulApply _ es) ⇔ memory_exprs_ok h ws es) ∧
  (memory_expr_ok h ws (YulCheckedBuiltin _ _) ⇔ F) ∧
  (memory_expr_ok h ws (YulLit _) ⇔ T) ∧
  (memory_expr_ok h ws (YulName _) ⇔ T) ∧
  (memory_exprs_ok h ws [] ⇔ T) ∧
  (memory_exprs_ok h ws (e :: es) ⇔
    memory_expr_ok h ws e ∧ memory_exprs_ok h ws es)
End

Definition memory_stmt_ok_def:
  (memory_stmt_ok h ws (YulBlock ss) ⇔ memory_stmts_ok h ws ss) ∧
  (memory_stmt_ok h ws (YulFunction _ _ _ body) ⇔
    memory_stmts_ok h [(0x40, 32)] body) ∧
  (memory_stmt_ok h ws (YulLet _ NONE) ⇔ T) ∧
  (memory_stmt_ok h ws (YulLet _ (SOME e)) ⇔ memory_expr_ok h ws e) ∧
  (memory_stmt_ok h ws (YulAssign _ e) ⇔ memory_expr_ok h ws e) ∧
  (memory_stmt_ok h ws (YulIf e body) ⇔
    memory_expr_ok h ws e ∧ memory_stmts_ok h ws body) ∧
  (memory_stmt_ok h ws (YulSwitch e cases default) ⇔
    memory_expr_ok h ws e ∧ memory_cases_ok h ws cases ∧
    memory_stmts_ok h ws default) ∧
  (memory_stmt_ok h ws (YulFor pre c post body) ⇔
    memory_stmts_ok h ws pre ∧ memory_expr_ok h ws c ∧
    memory_stmts_ok h ws post ∧ memory_stmts_ok h ws body) ∧
  (memory_stmt_ok h ws YulBreak ⇔ T) ∧
  (memory_stmt_ok h ws YulContinue ⇔ T) ∧
  (memory_stmt_ok h ws YulLeave ⇔ T) ∧
  (memory_stmt_ok h ws (YulExprStmt e) ⇔ memory_expr_ok h ws e) ∧
  (memory_stmts_ok h ws [] ⇔ T) ∧
  (memory_stmts_ok h ws (s :: ss) ⇔
    memory_stmt_ok h ws s ∧
    memory_stmts_ok h (memory_store s ++ ws) ss) ∧
  (memory_cases_ok h ws [] ⇔ T) ∧
  (memory_cases_ok h ws ((_, body) :: cases) ⇔
    memory_stmts_ok h ws body ∧ memory_cases_ok h ws cases)
End

Definition block_halts_def:
  (block_halts [] ⇔ F) ∧
  (block_halts [YulExprStmt (YulBuiltin b _)] ⇔ MEM b [YReturn; YRevert; YStop]) ∧
  (block_halts [_] ⇔ F) ∧
  (block_halts (_ :: s :: ss) ⇔ block_halts (s :: ss))
End

Definition assembly_memory_ok_def:
  assembly_memory_ok code ⇔ memory_stmts_ok (block_halts code) [(0x40, 32)] code
End

(* Gas and return data. The source keeps no gas and no return data buffer, so
 * gas() may only be a call's gas argument, where it stands for the budget
 * every call from the source gets; and returndatasize and returndatacopy may
 * only come after a statement of the block that calls (a let, assignment or
 * expression statement whose expression has a call or staticcall in it),
 * earlier in their statement list or an enclosing one, or inside an if, switch
 * or for whose condition calls. A Yul function's body
 * starts with no call made, and an expression sees only the statements before
 * it, since the order of its arguments' calls is the compiler's. *)
Definition expr_calls_def:
  (expr_calls (YulBuiltin b es) ⇔
    b = YCall ∨ b = YStaticCall ∨ exprs_calls es) ∧
  (expr_calls (YulApply _ es) ⇔ exprs_calls es) ∧
  (expr_calls _ ⇔ F) ∧
  (exprs_calls [] ⇔ F) ∧
  (exprs_calls (e :: es) ⇔ expr_calls e ∨ exprs_calls es)
End

Definition stmt_calls_def:
  (stmt_calls (YulLet _ (SOME e)) ⇔ expr_calls e) ∧
  (stmt_calls (YulAssign _ e) ⇔ expr_calls e) ∧
  (stmt_calls (YulExprStmt e) ⇔ expr_calls e) ∧
  (stmt_calls _ ⇔ F)
End

(* called: a call has been made; gas: the first argument may be gas(). *)
Definition call_expr_ok_def:
  (call_expr_ok called (YulBuiltin b es) ⇔
    b ≠ YGas ∧
    (called ∨ b ≠ YReturnDataSize ∧ b ≠ YReturnDataCopy) ∧
    call_args_ok called (b = YCall ∨ b = YStaticCall) es) ∧
  (call_expr_ok called (YulApply _ es) ⇔ call_args_ok called F es) ∧
  (call_expr_ok called (YulCheckedBuiltin _ _) ⇔ F) ∧
  (call_expr_ok called _ ⇔ T) ∧
  (call_args_ok called gas [] ⇔ T) ∧
  (call_args_ok called gas (e :: es) ⇔
    (gas ∧ e = YulBuiltin YGas [] ∨ call_expr_ok called e) ∧
    call_args_ok called F es)
End

Definition call_stmt_ok_def:
  (call_stmt_ok c (YulBlock ss) ⇔ call_stmts_ok c ss) ∧
  (call_stmt_ok c (YulFunction _ _ _ body) ⇔ call_stmts_ok F body) ∧
  (call_stmt_ok c (YulLet _ NONE) ⇔ T) ∧
  (call_stmt_ok c (YulLet _ (SOME e)) ⇔ call_expr_ok c e) ∧
  (call_stmt_ok c (YulAssign _ e) ⇔ call_expr_ok c e) ∧
  (call_stmt_ok c (YulIf e body) ⇔
    call_expr_ok c e ∧ call_stmts_ok (c ∨ expr_calls e) body) ∧
  (call_stmt_ok c (YulSwitch e cases default) ⇔
    call_expr_ok c e ∧ call_cases_ok (c ∨ expr_calls e) cases ∧
    call_stmts_ok (c ∨ expr_calls e) default) ∧
  (call_stmt_ok c (YulFor pre e post body) ⇔
    call_stmts_ok c pre ∧ call_expr_ok c e ∧
    call_stmts_ok (c ∨ expr_calls e) post ∧
    call_stmts_ok (c ∨ expr_calls e) body) ∧
  (call_stmt_ok c YulBreak ⇔ T) ∧
  (call_stmt_ok c YulContinue ⇔ T) ∧
  (call_stmt_ok c YulLeave ⇔ T) ∧
  (call_stmt_ok c (YulExprStmt e) ⇔ call_expr_ok c e) ∧
  (call_stmts_ok c [] ⇔ T) ∧
  (call_stmts_ok c (s :: ss) ⇔
    call_stmt_ok c s ∧ call_stmts_ok (c ∨ stmt_calls s) ss) ∧
  (call_cases_ok c [] ⇔ T) ∧
  (call_cases_ok c ((_, body) :: cases) ⇔
    call_stmts_ok c body ∧ call_cases_ok c cases)
End

Definition assembly_calls_ok_def:
  assembly_calls_ok code ⇔ call_stmts_ok F code
End

Definition assembly_reference_ok_def:
  assembly_reference_ok env ctx r ⇔
    case r of
      AssemblyLocal x ty =>
        ALOOKUP ctx.bindings x = SOME (SingleType ty) ∧ assembly_value_type ty
    | AssemblySlot x => IS_SOME (lookup_state_variable env x)
    | AssemblyOffset x => IS_SOME (lookup_state_variable env x)
    | AssemblyConstant a ty =>
        wf_core_atom env ctx (SingleType ty) a ∧ assembly_value_type ty
    | AssemblyMemory x ty =>
        ALOOKUP ctx.bindings x = SOME (SingleType (LocatedT MemoryLoc ty)) ∧
        byte_sequence_type ty
End

(* The names of a block's memory references. The block reads each as a
 * literal address, so it may not assign one; a Yul function's parameters and
 * results may reuse such a name for its body. *)
Definition assembly_memory_names_def:
  (assembly_memory_names [] = []) ∧
  (assembly_memory_names ((name, r) :: refs) =
    case r of
      AssemblyMemory _ _ => name :: assembly_memory_names refs
    | _ => assembly_memory_names refs)
End

Definition assembly_assigns_ok_def:
  (assembly_assign_ok xs (YulBlock ss) ⇔ assembly_assigns_ok xs ss) ∧
  (assembly_assign_ok xs (YulFunction _ params results body) ⇔
    assembly_assigns_ok (FILTER (λx. ¬MEM x (params ++ results)) xs) body) ∧
  (assembly_assign_ok xs (YulAssign ys _) ⇔ EVERY (λy. ¬MEM y xs) ys) ∧
  (assembly_assign_ok xs (YulIf _ body) ⇔ assembly_assigns_ok xs body) ∧
  (assembly_assign_ok xs (YulSwitch _ cases default) ⇔
    assembly_cases_assigns_ok xs cases ∧ assembly_assigns_ok xs default) ∧
  (assembly_assign_ok xs (YulFor pre _ post body) ⇔
    assembly_assigns_ok xs pre ∧ assembly_assigns_ok xs post ∧
    assembly_assigns_ok xs body) ∧
  (assembly_assign_ok xs _ ⇔ T) ∧
  (assembly_assigns_ok xs [] ⇔ T) ∧
  (assembly_assigns_ok xs (s :: ss) ⇔
    assembly_assign_ok xs s ∧ assembly_assigns_ok xs ss) ∧
  (assembly_cases_assigns_ok xs [] ⇔ T) ∧
  (assembly_cases_assigns_ok xs ((_, body) :: cases) ⇔
    assembly_assigns_ok xs body ∧ assembly_cases_assigns_ok xs cases)
End

Definition check_core_stmts_def:
  (check_core_stmts env ctx [] = SOME ctx) ∧
  (check_core_stmts env ctx (DefineStmt x ty op :: ss) =
    if fresh_core_id ctx x ∧ wf_core_value_type env ty ∧
       wf_core_operation env ctx ty op
    then check_core_stmts env (bind_core_id x ty ctx) ss
    else NONE) ∧
  (check_core_stmts env ctx (CaptureBindingStmt t x :: ss) =
    case ALOOKUP ctx.bindings x of
      SOME (SingleType ty) =>
        if fresh_core_id ctx t
        then check_core_stmts env (capture_core_target t ty ctx) ss
        else NONE
    | _ => NONE) ∧
  (check_core_stmts env ctx (CaptureValueStmt t a :: ss) =
    case a of
      BoundAtom x =>
        (case ALOOKUP ctx.bindings x of
           SOME (ReferenceType ty) =>
             if fresh_core_id ctx t ∧ core_scalar_type env ty ∧
                IS_SOME (storage_bytes ty)
             then check_core_stmts env (capture_core_target t ty ctx) ss
             else NONE
         | _ => NONE)
    | _ => NONE) ∧
  (check_core_stmts env ctx (CaptureReferenceFieldStmt t a (IndexNavigation i) :: ss) =
    case a of
      BoundAtom x =>
        (case ALOOKUP ctx.bindings x of
           SOME (SingleType (LocatedT MemoryLoc (ArrayT element length))) =>
             if fresh_core_id ctx t ∧
                memory_object_type (ArrayT element length) ∧
                wf_core_atom env ctx (SingleType (UintT 256)) i
             then check_core_stmts env
                    (capture_core_target t (element_type MemoryLoc element) ctx) ss
             else NONE
         | _ => NONE)
    | _ => NONE) ∧
  (check_core_stmts env ctx (BindReferenceStmt t ty a :: ss) =
    if ALOOKUP ctx.targets t = SOME ty ∧ located_value_type ty ∧
       wf_core_atom env ctx (SingleType ty) a
    then check_core_stmts env ctx ss else NONE) ∧
  (check_core_stmts env ctx (CopyContentsStmt src dst a b :: ss) =
    if (case (src, dst) of
          (LocatedT _ ty, LocatedT loc ty') =>
            if byte_sequence_type ty then
              byte_sequence_value_type src ∧ loc ≠ CalldataLoc ∧ ty = ty'
            else
              located_value_type src ∧ located_value_type dst ∧
              memory_object_type ty ∧ memory_object_type ty' ∧
              loc = StorageLoc ∧ storage_copy_type ty ty'
        | _ => F) ∧
       wf_core_atom env ctx (SingleType src) a ∧
       wf_core_atom env ctx (SingleType dst) b
    then check_core_stmts env ctx ss else NONE) ∧
  (check_core_stmts env ctx (WriteScalarStmt t ty a :: ss) =
    if core_scalar_type env ty ∧ ALOOKUP ctx.targets t = SOME ty ∧
       wf_core_atom env ctx (SingleType ty) a
    then check_core_stmts env ctx ss
    else NONE) ∧
  (check_core_stmts env ctx (IfStmt c ts es :: ss) =
    if wf_core_atom env ctx (SingleType BoolT) c ∧
       IS_SOME (check_core_stmts env ctx ts) ∧
       IS_SOME (check_core_stmts env ctx es)
    then check_core_stmts env ctx ss
    else NONE) ∧
  (check_core_stmts env ctx (WhileStmt prelude c body :: ss) =
    case check_core_stmts env (ctx with in_loop := F) prelude of
      NONE => NONE
    | SOME prelude_ctx =>
        if wf_core_atom env prelude_ctx (SingleType BoolT) c ∧
           IS_SOME (check_core_stmts env (prelude_ctx with in_loop := T) body)
        then check_core_stmts env ctx ss
        else NONE) ∧
  (check_core_stmts env ctx (ReturnStmt atoms :: ss) =
    if wf_core_atoms env ctx (MAP SingleType ctx.returns) atoms
    then check_core_stmts env ctx ss
    else NONE) ∧
  (check_core_stmts env ctx (BreakStmt :: ss) =
    if ctx.in_loop then check_core_stmts env ctx ss else NONE) ∧
  (check_core_stmts env ctx (ContinueStmt :: ss) =
    if ctx.in_loop then check_core_stmts env ctx ss else NONE) ∧
  (check_core_stmts env ctx (PanicStmt code :: ss) =
    check_core_stmts env ctx ss) ∧
  (check_core_stmts env ctx (RevertStmt a :: ss) =
    if provisional_revert_payload a then check_core_stmts env ctx ss
    else NONE) ∧
  (* Error arguments are elementary, as the ABI encoding of revert data
     requires. *)
  (check_core_stmts env ctx (RevertErrorStmt selector params args :: ss) =
    if LENGTH selector = 4 ∧
       EVERY (λty. is_elementary_type ty ∧ valid_type_shape ty) params ∧
       wf_core_atoms env ctx (MAP SingleType params) args
    then check_core_stmts env ctx ss else NONE) ∧
  (check_core_stmts env ctx (EmitStmt topic args :: ss) =
    case emit_indexed_count env ctx args of
      SOME n =>
        if n + (if IS_SOME topic then 1 else 0) ≤ 4
        then check_core_stmts env ctx ss else NONE
    | NONE => NONE) ∧
  (check_core_stmts env ctx (AssemblyStmt code refs :: ss) =
    if assembly_stmts_ok assembly_unsupported code ∧ assembly_memory_ok code ∧
       assembly_calls_ok code ∧
       ALL_DISTINCT (MAP FST refs) ∧
       EVERY (assembly_reference_ok env ctx) (MAP SND refs) ∧
       assembly_assigns_ok (assembly_memory_names refs) code
    then check_core_stmts env ctx ss else NONE) ∧
  (check_core_stmts env ctx (_ :: _) = NONE)
Termination
  WF_REL_TAC ‘measure (λ(env, ctx, ss). list_size core_stmt_size ss)’ >>
  rw[core_stmt_size_def, list_size_def]
End

Definition wf_core_stmts_def:
  wf_core_stmts env ctx ss ⇔ IS_SOME (check_core_stmts env ctx ss)
End

Definition wf_core_stmt_def:
  wf_core_stmt env ctx s ⇔ wf_core_stmts env ctx [s]
End

(* Procedures, environments and programs *)

Definition procedure_check_context_def:
  procedure_check_context (p : core_procedure) = <|
    bindings := MAP (λ(x, ty). (x, SingleType ty))
                  (p.parameters ++ p.return_bindings);
    targets := [];
    returns := MAP SND p.return_bindings;
    in_loop := F
  |>
End

(* Return bindings are in scope from entry, so the evaluator default-initialises
 * them and a body may not define them again; fall-through returns their
 * current values.
 *)
Definition wf_core_procedure_def:
  wf_core_procedure env (p : core_procedure) ⇔
    ALL_DISTINCT (MAP FST (p.parameters ++ p.return_bindings)) ∧
    EVERY (λ(_, ty). core_binding_type env ty)
      (p.parameters ++ p.return_bindings) ∧
    wf_core_stmts env (procedure_check_context p) p.body
End

(* A state variable has a stored value type that fits its slot. Distinct
 * variables are not checked to occupy disjoint bytes: layout calculation is
 * the compiler's.
 *)
Definition wf_core_state_variable_def:
  wf_core_state_variable env (v : core_state_variable) ⇔
    storage_type_ok env v.state_type ∧
    case storage_bytes v.state_type of
      SOME b => v.state_offset + b ≤ 32
    | NONE => v.state_offset = 0
End

(* Inline containment must be finite. Mappings and dynamic arrays terminate
 * layout traversal; recursive structs behind those containers are allowed. *)
Definition inline_storage_shape_def:
  (inline_storage_shape env (n : num) (ArrayT element (SOME _)) ⇔
    inline_storage_shape env n element) ∧
  (inline_storage_shape env n (StructT id) ⇔
    if n = 0 then F else
    case lookup_struct_layout env id of
      SOME s => inline_storage_types env (n - 1) (MAP (λv. v.state_type) s.struct_fields)
    | NONE => F) ∧
  (inline_storage_shape env n _ ⇔ T) ∧
  (inline_storage_types env n [] ⇔ T) ∧
  (inline_storage_types env n (ty :: tys) ⇔
    inline_storage_shape env n ty ∧ inline_storage_types env n tys)
Termination
  WF_REL_TAC ‘inv_image ($< LEX $<) (λx. case x of
    INL (env, n, ty) => (n, sol_type_size ty)
  | INR (env, n, tys) => (n, list_size sol_type_size tys))’ >>
  rw[list_size_def]
End

Definition wf_core_struct_layout_def:
  wf_core_struct_layout env (s : core_struct_layout) ⇔
    0 < s.struct_slots ∧ s.struct_slots < 2 ** 256 ∧
    s.struct_fields ≠ [] ∧ ALL_DISTINCT (MAP (λv. v.state_id) s.struct_fields) ∧
    lookup_struct env s.struct_id =
      SOME (MAP (λv. (v.state_id, v.state_type)) s.struct_fields) ∧
    inline_storage_shape env (LENGTH env.struct_layouts) (StructT s.struct_id) ∧
    EVERY (λv. wf_core_state_variable env v ∧
      case fixed_storage_slots env v.state_type of
        SOME slots => w2n v.state_slot + slots ≤ s.struct_slots
      | NONE => F) s.struct_fields
End

Definition wf_core_environment_def:
  wf_core_environment env ⇔
    ALL_DISTINCT (MAP FST env.procedures) ∧
    EVERY (λ(f, p). p.procedure_id = f ∧ wf_core_procedure env p)
      env.procedures ∧
    ALL_DISTINCT (MAP FST env.state_variables) ∧
    EVERY (λ(x, v). v.state_id = x ∧ wf_core_state_variable env v)
      env.state_variables ∧
    ALL_DISTINCT (MAP FST env.immutables) ∧
    EVERY (λ(_, ty). core_scalar_type env ty ∧ IS_SOME (storage_bytes ty))
      env.immutables ∧
    ALL_DISTINCT (MAP FST env.struct_layouts) ∧
    EVERY (λ(id, s). s.struct_id = id ∧ wf_core_struct_layout env s)
      env.struct_layouts ∧
    ALL_DISTINCT (MAP FST env.type_declarations) ∧
    EVERY (λ(_, decl). wf_type_declaration env decl) env.type_declarations
End

(* Calldata reaches procedures whose parameters and returns are ABI values,
 * the types the entry ABI-decodes and encodes; receive and the fallback take
 * and return nothing, and the creation procedure returns nothing. Each may
 * instead be an unsupported procedure, which has none, so that the entry
 * refuses rather than falling through to another one.
 *)
Definition abi_procedure_def:
  abi_procedure env f ⇔
    case lookup_procedure env f of
      SOME p =>
        EVERY (λ(_, ty). abi_value_type ty)
          (p.parameters ++ p.return_bindings)
    | NONE => F
End

Definition plain_procedure_def:
  plain_procedure env f ⇔
    case lookup_procedure env f of
      SOME p => p.parameters = [] ∧ p.return_bindings = []
    | NONE => F
End

Definition wf_core_dispatch_def:
  wf_core_dispatch env (prog : core_program) ⇔
    ALL_DISTINCT (MAP (λe. e.selector) prog.external_functions) ∧
    EVERY (λe. LENGTH e.selector = 4 ∧
               (abi_procedure env e.external_procedure ∨
                MEM e.external_procedure prog.unsupported_procedures))
      prog.external_functions ∧
    (case prog.receive_procedure of
       SOME f => plain_procedure env f ∨ MEM f prog.unsupported_procedures
     | NONE => T) ∧
    (case prog.fallback_procedure of
       SOME (f, _) => plain_procedure env f ∨ MEM f prog.unsupported_procedures
     | NONE => T) ∧
    (case prog.creation_procedure of
       SOME (f, _) =>
         MEM f prog.unsupported_procedures ∨
         (abi_procedure env f ∧
          case lookup_procedure env f of
            SOME p => p.return_bindings = [] ∧
              EVERY (λ(_, ty). is_elementary_type ty ∨
                       case ty of
                         LocatedT MemoryLoc _ => T
                       | EnumT _ => T
                       | _ => F) p.parameters
          | NONE => F)
     | NONE => T)
End

Definition wf_core_program_def:
  wf_core_program env (prog : core_program) ⇔
    env.procedures = MAP (λp. (p.procedure_id, p)) prog.procedures ∧
    env.state_variables = MAP (λv. (v.state_id, v)) prog.state_variables ∧
    env.immutables = prog.immutables ∧
    env.struct_layouts = MAP (λs. (s.struct_id, s)) prog.struct_layouts ∧
    wf_core_environment env ∧
    IS_SOME (lookup_procedure env prog.entry_procedure) ∧
    EVERY (λf. lookup_procedure env f = NONE) prog.unsupported_procedures ∧
    wf_core_dispatch env prog
End

(* Facts the evaluator can use under wf_core_program. *)

Theorem wf_core_environment_lookup:
  wf_core_environment env ∧ lookup_procedure env f = SOME p ⇒
    p.procedure_id = f ∧ wf_core_procedure env p
Proof
  rw[wf_core_environment_def, lookup_procedure_def] >>
  imp_res_tac ALOOKUP_MEM >>
  gvs[EVERY_MEM] >>
  first_x_assum drule >> simp[]
QED

Theorem wf_core_environment_user_value:
  wf_core_environment env ∧ lookup_user_value env id = SOME u ⇒
    is_elementary_type u
Proof
  rw[wf_core_environment_def, lookup_user_value_def, AllCaseEqs()] >>
  imp_res_tac ALOOKUP_MEM >> gvs[EVERY_MEM] >>
  first_x_assum drule >> simp[wf_type_declaration_def]
QED

Theorem wf_core_program_lookup:
  wf_core_program env prog ∧ lookup_procedure env f = SOME p ⇒
    p.procedure_id = f ∧ wf_core_procedure env p
Proof
  rw[wf_core_program_def] >> metis_tac[wf_core_environment_lookup]
QED

Theorem wf_core_program_entry:
  wf_core_program env prog ⇒
    ∃p. lookup_procedure env prog.entry_procedure = SOME p ∧
        p.procedure_id = prog.entry_procedure ∧ wf_core_procedure env p
Proof
  rw[wf_core_program_def, IS_SOME_EXISTS] >>
  metis_tac[wf_core_environment_lookup]
QED

Theorem core_program_environment_procedures:
  (core_program_environment prog).procedures =
    MAP (λp. (p.procedure_id, p)) prog.procedures
Proof
  simp[core_program_environment_def]
QED

(* The checked preparation boundary executes the complete checker through cv. *)
val () = cv_auto_trans core_program_environment_def;
val () = cv_auto_trans_rec mapping_reachable_def (
  WF_REL_TAC ‘inv_image ($< LEX $<) (λx. case x of
    INL (env, n, ty) => (cv$c2n n, cv_size ty)
  | INR (env, n, tys) => (cv$c2n n, cv_size tys))’ >>
  cv_termination_tac
);
val () = cv_auto_trans_rec declared_type_ok_def (
  WF_REL_TAC ‘measure (λx. case x of
    INL (env, ty) => cv_size ty
  | INR (env, tys) => cv_size tys)’ >> cv_termination_tac
);
val () = cv_auto_trans_rec wf_core_value_type_def (
  WF_REL_TAC ‘measure (λx. case x of
    INL (env, ty) => cv_size ty
  | INR (env, tys) => cv_size tys)’ >> cv_termination_tac
);
val () = cv_auto_trans_rec inline_storage_shape_def (
  WF_REL_TAC ‘inv_image ($< LEX $<) (λx. case x of
    INL (env, n, ty) => (cv$c2n n, cv_size ty)
  | INR (env, n, tys) => (cv$c2n n, cv_size tys))’ >> cv_termination_tac
);
val () = cv_auto_trans environment_type_def;
val () = cv_auto_trans wf_abi_atom_def;
val () = cv_auto_trans wf_gas_atom_def;
val () = cv_auto_trans (SPEC_ALL wf_core_operation_def);
val () = cv_auto_trans emit_indexed_count_def;
val () = cv_auto_trans assembly_unsupported_def;
val () = cv_auto_trans assembly_state_writes_def;
val () = cv_auto_trans assembly_expr_ok_def;
val () = cv_auto_trans assembly_stmt_ok_def;
val () = cv_auto_trans yul_lit_def;
val () = cv_auto_trans range_end_def;
val () = cv_auto_trans memory_covered_def;
val () = cv_auto_trans memory_read_ok_def;
val () = cv_auto_trans memory_write_ok_def;
val () = cv_auto_trans builtin_memory_ok_def;
val () = cv_auto_trans memory_expr_ok_def;
val () = cv_auto_trans call_output_def;
val () = cv_auto_trans memory_store_def;
val () = cv_auto_trans memory_stmt_ok_def;
val () = cv_auto_trans block_halts_def;
val () = cv_auto_trans assembly_memory_ok_def;
val () = cv_auto_trans expr_calls_def;
val () = cv_auto_trans stmt_calls_def;
val () = cv_auto_trans call_expr_ok_def;
val () = cv_auto_trans call_stmt_ok_def;
val () = cv_auto_trans assembly_calls_ok_def;
val () = cv_auto_trans assembly_value_type_def;
val () = cv_auto_trans assembly_reference_ok_def;
val () = cv_auto_trans assembly_memory_names_def;
val () = cv_auto_trans assembly_assigns_ok_def;
val () = cv_auto_trans fresh_core_id_def;
val () = cv_auto_trans bind_core_id_def;
val () = cv_auto_trans capture_core_target_def;
val check_core_stmts_pre_def = cv_auto_trans_pre_rec "check_core_stmts_pre"
  (SPEC_ALL check_core_stmts_def) (
  WF_REL_TAC ‘measure (λ(env, ctx, ss). cv_size ss)’ >> cv_termination_tac
);
Theorem core_check_context_in_loop_update[local]:
  (case ctx of core_check_context bs ts rs old => core_check_context bs ts rs flag) =
  (ctx with in_loop := flag)
Proof
  Cases_on ‘ctx’ >> simp[fetch "-" "core_check_context_fn_updates"]
QED

Theorem check_core_stmts_pre[cv_pre,local]:
  ∀env ctx ss. check_core_stmts_pre env ctx ss
Proof
  ho_match_mp_tac check_core_stmts_ind >> rpt strip_tac >>
  simp[Once check_core_stmts_pre_def, core_check_context_in_loop_update] >>
  rw[] >> fs[]
QED

val () = cv_auto_trans abi_procedure_def;
val () = cv_auto_trans plain_procedure_def;
val () = cv_auto_trans wf_core_dispatch_def;
val () = cv_auto_trans wf_core_program_def;
