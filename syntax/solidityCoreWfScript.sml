(* Static environment and well-formedness for the stage-2 pure core, with
 * value-type state variables.
 *
 * Admitted: scalar/convert/tuple/internal-call definitions, reads of state
 * variables, capture of locals and state variables and scalar writes to them,
 * and structured control flow. Bindings hold elementary types, enums and
 * user-defined value types, which are integers and addresses at runtime.
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
    struct_layouts : (ast_id # core_struct_layout) list;
    type_declarations : (ast_id # core_type_declaration) list
  |>
End

Definition core_program_environment_def:
  core_program_environment (prog : core_program) = <|
    procedures := MAP (λp. (p.procedure_id, p)) prog.procedures;
    state_variables := MAP (λv. (v.state_id, v)) prog.state_variables;
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

(* The bytes a value type occupies in a storage slot. Enums and user-defined
 * value types are not stored yet: reading an enum needs a choice of where an
 * out-of-range byte is rejected.
 *)
Definition storage_bytes_def:
  storage_bytes ty =
    case ty of
      BoolT => SOME 1
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
  (storage_type_ok env ty ⇔ elementary_storage_type_ok ty)
End

(* ProductType is reserved for tuples and multiple returns: never singleton. *)
Definition wf_core_value_type_def:
  (wf_core_value_type env (SingleType ty) ⇔ core_scalar_type env ty) ∧
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
      MsgSender => AddressT NonpayableAddress
    | SelfAddress => AddressT NonpayableAddress
    | TxOrigin => AddressT NonpayableAddress
    | BlockCoinbase => AddressT PayableAddress
    | _ => UintT 256
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
           SOME (SingleType src) => core_convertible env src ty
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
  (wf_core_operation env ctx annotation (ReadOperation ty a) ⇔
    annotation = SingleType ty ∧ core_scalar_type env ty ∧
    IS_SOME (storage_bytes ty) ∧ wf_core_atom env ctx (ReferenceType ty) a) ∧
  (wf_core_operation env ctx annotation
     (NavigateOperation ty base (FieldNavigation field)) ⇔
    annotation = ReferenceType ty ∧
    case base of
      BoundAtom x =>
        (case ALOOKUP ctx.bindings x of
           SOME (ReferenceType (StructT id)) =>
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
           SOME (ReferenceType (MappingT key value)) =>
             value = ty ∧ wf_core_atom env ctx (SingleType key) index
         | SOME (ReferenceType (ArrayT element _)) =>
             element = ty ∧ wf_core_atom env ctx (SingleType (UintT 256)) index
         | _ => F)
    | _ => F) ∧
  (wf_core_operation env ctx annotation (ArrayLengthOperation a) ⇔
    annotation = SingleType (UintT 256) ∧
    case a of
      BoundAtom x =>
        (case ALOOKUP ctx.bindings x of
           SOME (ReferenceType (ArrayT _ NONE)) => T
         | _ => F)
    | _ => F) ∧
  (wf_core_operation env ctx annotation (ArrayPushOperation a value) ⇔
    case a of
      BoundAtom x =>
        (case ALOOKUP ctx.bindings x of
           SOME (ReferenceType (ArrayT element NONE)) =>
             elementary_storage_type_ok element ∧
             annotation = ReferenceType element ∧
             (case value of
                NONE => T
              | SOME v => wf_core_atom env ctx (SingleType element) v)
         | _ => F)
    | _ => F) ∧
  (wf_core_operation env ctx annotation (ArrayPopOperation a) ⇔
    annotation = ProductType [] ∧
    case a of
      BoundAtom x =>
        (case ALOOKUP ctx.bindings x of
           SOME (ReferenceType (ArrayT element NONE)) => elementary_storage_type_ok element
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
     (ExternalCallOperation kind selector params rets target value args) ⇔
    kind ≠ ExternalDelegateCall ∧ LENGTH selector = 4 ∧
    EVERY (λty. is_elementary_type ty ∧ valid_type_shape ty) (params ++ rets) ∧
    wf_core_atom env ctx (SingleType (AddressT NonpayableAddress)) target ∧
    wf_core_atom env ctx (SingleType (UintT 256)) value ∧
    (kind = ExternalStaticCall ⇒ value = ConstantAtom (IntegerValue 0)) ∧
    wf_core_atoms env ctx (MAP SingleType params) args ∧
    annotation = call_result_type rets) ∧
  (wf_core_operation env ctx annotation _ ⇔ F)
End

(* Revert payloads are provisional pre-encoded constants until ABI encoding:
 * the BytesValue is raw revert data of any length, not a bytesN scalar.
 *)
Definition provisional_revert_payload_def:
  (provisional_revert_payload (ConstantAtom (BytesValue _)) ⇔ T) ∧
  (provisional_revert_payload _ ⇔ F)
End

(* Event arguments are elementary; the count of indexed ones, which with
 * topic0 must fit the four topics of a log.
 *)
Definition emit_indexed_count_def:
  (emit_indexed_count env ctx [] = SOME (0 : num)) ∧
  (emit_indexed_count env ctx ((ty, indexed, a) :: args) =
    if is_elementary_type ty ∧ valid_type_shape ty ∧
       wf_core_atom env ctx (SingleType ty) a then
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
  (check_core_stmts env ctx (WriteScalarStmt t ty a :: ss) =
    if ALOOKUP ctx.targets t = SOME ty ∧
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
  (check_core_stmts env ctx (EmitStmt topic args :: ss) =
    case emit_indexed_count env ctx args of
      SOME n =>
        if n + (if IS_SOME topic then 1 else 0) ≤ 4
        then check_core_stmts env ctx ss else NONE
    | NONE => NONE) ∧
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
    EVERY (λ(_, ty). core_scalar_type env ty)
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
    ALL_DISTINCT (MAP FST env.struct_layouts) ∧
    EVERY (λ(id, s). s.struct_id = id ∧ wf_core_struct_layout env s)
      env.struct_layouts ∧
    ALL_DISTINCT (MAP FST env.type_declarations) ∧
    EVERY (λ(_, decl). wf_type_declaration env decl) env.type_declarations
End

(* Calldata reaches procedures whose parameters and returns are elementary,
 * the types the entry ABI-decodes and encodes; receive and the fallback take
 * and return nothing, and the creation procedure returns nothing.
 *)
Definition abi_procedure_def:
  abi_procedure env f ⇔
    case lookup_procedure env f of
      SOME p =>
        EVERY (λ(_, ty). is_elementary_type ty)
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
    EVERY (λe. LENGTH e.selector = 4 ∧ abi_procedure env e.external_procedure)
      prog.external_functions ∧
    (case prog.receive_procedure of
       SOME f => plain_procedure env f
     | NONE => T) ∧
    (case prog.fallback_procedure of
       SOME (f, _) => plain_procedure env f
     | NONE => T) ∧
    (case prog.creation_procedure of
       SOME (f, _) =>
         abi_procedure env f ∧
         (case lookup_procedure env f of
            SOME p => p.return_bindings = []
          | NONE => F)
     | NONE => T)
End

Definition wf_core_program_def:
  wf_core_program env (prog : core_program) ⇔
    env.procedures = MAP (λp. (p.procedure_id, p)) prog.procedures ∧
    env.state_variables = MAP (λv. (v.state_id, v)) prog.state_variables ∧
    env.struct_layouts = MAP (λs. (s.struct_id, s)) prog.struct_layouts ∧
    wf_core_environment env ∧
    IS_SOME (lookup_procedure env prog.entry_procedure) ∧
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
val () = cv_auto_trans (SPEC_ALL wf_core_operation_def);
val () = cv_auto_trans emit_indexed_count_def;
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
