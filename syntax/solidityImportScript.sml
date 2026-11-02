(* Normalized source AST: the admitted subset of the pinned compiler's
 * analyzed Standard JSON AST, between the raw compiler output and the core.
 *
 * solidityImportLib builds these terms from a compiler artifact and fails
 * closed: an unknown nodeType, a missing required field, or a feature outside
 * the subset (public, constant, immutable or initialised state variables,
 * modifiers, super, named or try calls, built-ins other than
 * require, assert, revert, members of msg, tx and block and address(this), literal subdenominations,
 * inline arrays, type names other than elementary types, arrays and mappings, ...)
 * raises ImportError. Semantic nodes keep their compiler id and source range;
 * declarations are referred to by id, and names are diagnostic only. Type
 * annotations are kept as the compiler's encoded typeIdentifier and decoded
 * here, never from the display typeString.
 *
 * A unit holds its deployable contracts: those neither abstract, nor an
 * interface, nor a base of another contract of the unit. Each is flattened
 * along its linearization (src_contract); its bases must be in the same unit.
 *
 * Types are normalized from elementary, array and mapping type-name nodes; value
 * types are decoded from typeIdentifiers. Both yield only valid shapes (normalize_type_name_valid,
 * decode_type_identifier_valid). Literals keep their exact rational type.
 *
 * valid_src_unit then establishes, for an imported unit:
 *  - all node ids are distinct;
 *  - every parameter, return, local and state variable has a normalized
 *    elementary, array or mapping type, the default data location, and a
 *    type identifier agreeing with that type, and the enclosing function,
 *    block, for statement or one of the contract's bases as its scope; event
 *    parameters are elementary, scoped by their event;
 *  - the contract's bases are distinct and start with the contract itself;
 *  - the contract's storage layout lists its state variables in
 *    linearization order, bases first, each with its own typeIdentifier and
 *    a slot below 2 ** 256;
 *  - every identifier resolves, within its lexical scope, to a variable of the
 *    annotated type, or, as the callee of a call, to a function of the same
 *    contract, the most derived override of the one it names (call_table);
 *    calls have matching arity and are annotated with the callee's
 *    return types; conversions are annotated with their normalized target type;
 *    environment reads with their member's type; emits name an event of the
 *    contract with as many arguments as it has parameters;
 *  - declaration statements list exactly their declarations' ids as
 *    assignments, returns name the enclosing function's return list, break and
 *    continue occur in loop bodies, conditions are boolean;
 *  - functions, receive and fallback are pure, view, nonpayable or payable,
 *    and only non-pure ones refer to state variables; functions a more
 *    derived one overrides are not checked, since nothing reaches them;
 *    contracts are scoped by the unit, functions by a base of their contract;
 *  - operators belong to the admitted set and every other expression
 *    annotation decodes to an elementary, rational literal or tuple type.
 *
 * Left to elaboration: implicit conversions (operand and argument types
 * against commonType and parameter types, literal ranges), return value
 * arity and types, assignment target shapes and their types, and evaluation
 * order, which the AST does not record. Left to the compiler: storage layout
 * calculation, that view functions write no state variable, and the
 * override metadata: which declarations each function overrides, and that
 * functions come most derived first.
 *)
Theory solidityImport
Ancestors
  solidityAST ASCIInumbers string integer alist cv_std
  (* for the scalar layer's cv encodings of the AST types, so that every
   * descendant sees one encoding *)
  solidityScalar
Libs
  cv_transLib

(* Nodes *)

Datatype:
  src_location = <| loc_start : num; loc_length : num; loc_source : num |>
End

Datatype:
  node_info = <| node_id : num; node_location : src_location |>
End

(* ElementaryTypeName: name and, for addresses, stateMutability. *)
Datatype:
  src_type_name = SrcElementaryTypeName node_info string (string option)
                | SrcArrayTypeName node_info src_type_name num
                | SrcDynamicArrayTypeName node_info src_type_name
  | SrcMappingTypeName node_info src_type_name src_type_name
  | SrcStructTypeName node_info num string
End

Datatype:
  src_variable = <|
    var_info : node_info;
    var_name : string;
    var_scope : num;
    var_type_name : src_type_name;
    var_type_id : string;
    var_location : string
  |>
End

(* The last string of each expression is its typeIdentifier.
 * Identifier: name, referencedDeclaration.
 * Literal: kind, value.
 * UnaryOperation: operator, prefix, operand.
 * BinaryOperation: operator, operands, commonType.
 * Assignment: operator, left and right hand sides.
 * TupleExpression: components, NONE for a hole.
 * FunctionCall (kind functionCall): callee, positional arguments.
 * FunctionCall (kind typeConversion): target type name, argument.
 * Environment: a member of msg, tx or block, or address(this).
 * ExternalCall (I(target).f{value: v}(args)): the declaration of f, whether
 * a value is given, and the operands in evaluation order: the target, the
 * value if given, the positional arguments.
 *)
Datatype:
  src_builtin = RequireBuiltin | AssertBuiltin | RevertBuiltin
End

(* The declaration a high-level call refers to: an external or public
 * function of an interface or contract.
 *)
Datatype:
  src_external = <|
    ext_selector : byte list;
    ext_mutability : string;
    ext_parameters : src_variable list;
    ext_returns : src_variable list
  |>
End

Datatype:
  src_expr
  = SrcIdentifier node_info string num string
  | SrcArrayLength node_info src_expr string
  | SrcMemberAccess node_info src_expr num string
  | SrcArrayMember node_info string src_expr string
  | SrcLiteral node_info string string string
  | SrcUnaryOperation node_info string bool src_expr string
  | SrcBinaryOperation node_info string src_expr src_expr string string
  | SrcAssignment node_info string src_expr src_expr string
  | SrcIndexAccess node_info src_expr src_expr string
  | SrcTupleExpression node_info (src_expr option list) string
  | SrcFunctionCall node_info src_expr (src_expr list) string
  | SrcBuiltinCall node_info node_info src_builtin (src_expr option)
      (src_expr option) string
  | SrcTypeConversion node_info src_type_name src_expr string
  | SrcEnvironment node_info environment_field string
  | SrcExternalCall node_info src_external bool (src_expr list) string
End

(* VariableDeclarationStatement: assignments, declarations (NONE for a hole),
 * initial value. ForStatement: initialization, condition, loop expression,
 * body. Return: functionReturnParameters, expression. Emit: the event's id,
 * positional arguments.
 *)
Datatype:
  src_stmt
  = SrcBlock node_info (src_stmt list)
  | SrcUncheckedBlock node_info (src_stmt list)
  | SrcExpressionStatement node_info src_expr
  | SrcVariableDeclarationStatement node_info (num option list)
      (src_variable option list) (src_expr option)
  | SrcIfStatement node_info src_expr src_stmt (src_stmt option)
  | SrcWhileStatement node_info src_expr src_stmt
  | SrcDoWhileStatement node_info src_stmt src_expr
  | SrcForStatement node_info (src_stmt option) (src_expr option)
      (src_stmt option) src_stmt
  | SrcBreak node_info
  | SrcContinue node_info
  | SrcReturn node_info num (src_expr option)
  | SrcEmit node_info num (src_expr list)
End

(* Parameter lists are represented by their ids and declarations. The kind is
 * function, receive or fallback; the selector is that of an external or
 * public function. The base functions are the declarations it overrides,
 * directly or through other overridden declarations (the closure of the
 * compiler's baseFunctions).
 *)
Datatype:
  src_function = <|
    fn_info : node_info;
    fn_name : string;
    fn_scope : num;
    fn_kind : string;
    fn_visibility : string;
    fn_mutability : string;
    fn_selector : byte list option;
    fn_base_functions : num list;
    fn_parameters_id : num;
    fn_parameters : src_variable list;
    fn_returns_id : num;
    fn_returns : src_variable list;
    fn_body : src_stmt
  |>
End

(* An entry of the compiler's storageLayout: the state variable's id, its
 * slot, its byte offset from the slot's low-order end and its type label.
 *)
Datatype:
  src_storage_entry = <|
    storage_id : num;
    storage_slot : num;
    storage_offset : num;
    storage_type_id : string
  |>
End

Datatype:
  src_struct = <|
    struct_info : node_info;
    struct_scope : num;
    struct_members : src_variable list;
    struct_layout : (num # src_storage_entry list) option
  |>
End

(* An event: its topic 0 (the compiler's eventSelector, which an anonymous
 * event does not log) and its parameters, each with whether it is indexed.
 *)
Datatype:
  src_event = <|
    event_info : node_info;
    event_anonymous : bool;
    event_selector : byte list;
    event_parameters : (src_variable # bool) list
  |>
End

(* A contract flattened along its linearization (the compiler's
 * linearizedBaseContracts, most derived first, which bases lists): the
 * members of all its bases, functions most derived first, state variables in
 * storage order. Declarations without a body are left out. Initializers
 * give state variables (by id) their declared values; base arguments are
 * the base constructor arguments: the base giving them, the base whose
 * constructor takes them, and the arguments, in evaluation order.
 *)
Datatype:
  src_contract = <|
    contract_info : node_info;
    contract_name : string;
    contract_scope : num;
    contract_bases : num list;
    contract_state_variables : src_variable list;
    contract_initializers : (num # src_expr) list;
    contract_base_arguments : (num # num # src_expr list) list;
    contract_storage : src_storage_entry list;
    contract_structs : src_struct list;
    contract_events : src_event list;
    contract_functions : src_function list
  |>
End

Datatype:
  src_unit = <|
    unit_info : node_info;
    unit_path : string;
    unit_contracts : src_contract list
  |>
End

(* Types *)

(* Elementary type names, with the widths valid_type_shape requires. *)
Definition elementary_type_def:
  elementary_type name =
    if name = "bool" then SOME BoolT
    else if name = "address" then SOME (AddressT NonpayableAddress)
    else if name = "uint" then SOME (UintT 256)
    else if name = "int" then SOME (IntT 256)
    else if isPREFIX "uint" name then
      case fromDecString (DROP 4 name) of
        SOME n => if valid_int_width n then SOME (UintT n) else NONE
      | NONE => NONE
    else if isPREFIX "int" name then
      case fromDecString (DROP 3 name) of
        SOME n => if valid_int_width n then SOME (IntT n) else NONE
      | NONE => NONE
    else if isPREFIX "bytes" name then
      case fromDecString (DROP 5 name) of
        SOME n =>
          if valid_fixed_bytes_width n then SOME (FixedBytesT n) else NONE
      | NONE => NONE
    else NONE
End

Definition normalize_type_name_def:
  (normalize_type_name (SrcElementaryTypeName _ name mutability) =
    case elementary_type name of
      SOME (AddressT _) =>
        if mutability = SOME "nonpayable" then SOME (AddressT NonpayableAddress)
        else if mutability = SOME "payable" then SOME (AddressT PayableAddress)
        else NONE
    | SOME ty => if mutability = NONE then SOME ty else NONE
    | NONE => NONE) ∧
  (normalize_type_name (SrcArrayTypeName _ element n) =
    case normalize_type_name element of
      SOME ty => if 0 < n ∧ n < 2 ** 256 then SOME (ArrayT ty (SOME n))
                 else NONE
    | NONE => NONE) ∧
  (normalize_type_name (SrcStructTypeName _ id tid) =
    if isPREFIX "t_struct$_" tid ∧
       isPREFIX (REVERSE ("_$" ++ toString id ++ "_storage_ptr")) (REVERSE tid)
    then SOME (StructT (AstId id)) else NONE) ∧
  (normalize_type_name (SrcDynamicArrayTypeName _ element) =
    OPTION_MAP (λty. ArrayT ty NONE) (normalize_type_name element)) ∧
  (normalize_type_name (SrcMappingTypeName _ key value) =
    case (normalize_type_name key, normalize_type_name value) of
      (SOME k, SOME v) =>
        if is_elementary_type k then SOME (MappingT k v) else NONE
    | _ => NONE)
End

(* Decoded typeIdentifiers: elementary types, rational literal types (a
 * reduced numerator and positive denominator) and tuples of elementary types.
 *)
Datatype:
  src_value_type
  = SrcType sol_type
  | SrcRational int num
  | SrcTupleType (sol_type list)
End

Definition decode_elementary_identifier_def:
  decode_elementary_identifier s =
    if s = "t_address_payable" then SOME (AddressT PayableAddress)
    else if isPREFIX "t_" s ∧ s ≠ "t_uint" ∧ s ≠ "t_int" then
      elementary_type (DROP 2 s)
    else NONE
End

(* The fields of a string between occurrences of a separator: FIELDS for a
 * single separator character, by structural recursion so that it has a cv
 * translation (FIELDS' does not terminate under cv_auto_trans).
 *)
Definition separated_fields_def:
  (separated_fields sep acc [] = [REVERSE acc]) ∧
  (separated_fields sep acc (c :: cs) =
    if c = sep then REVERSE acc :: separated_fields sep "" cs
    else separated_fields sep (c :: acc) cs)
End

Definition rational_type_def:
  rational_type negative a b =
    case (fromDecString a, fromDecString b) of
      (SOME n, SOME d) =>
        if 0 < d then SOME (SrcRational (if negative then -&n else &n) d)
        else NONE
    | _ => NONE
End

(* "A_by_B" or "minus_A_by_B", after the "t_rational_" prefix. *)
Definition decode_rational_def:
  decode_rational s =
    case separated_fields #"_" "" s of
      [a; by; b] => if by = "by" then rational_type F a b else NONE
    | [minus; a; by; b] =>
        if minus = "minus" ∧ by = "by" then rational_type T a b else NONE
    | _ => NONE
End

(* OPT_MMAP I by direct recursion, which has a cv translation. *)
Definition all_some_def:
  (all_some [] = SOME []) ∧
  (all_some (x :: xs) =
    case (x, all_some xs) of
      (SOME y, SOME ys) => SOME (y :: ys)
    | _ => NONE)
End

Theorem all_some_OPT_MMAP:
  ∀xs. all_some xs = OPT_MMAP I xs
Proof
  Induct >> rw[all_some_def] >> Cases_on ‘h’ >> simp[] >>
  Cases_on ‘OPT_MMAP I xs’ >> simp[]
QED

(* A tuple component "_c_", from "t_tuple$_c1_$_c2_$...$". *)
Definition tuple_component_def:
  tuple_component p =
    if 2 ≤ LENGTH p ∧ isPREFIX "_" p ∧ isPREFIX "_" (REVERSE p) then
      decode_elementary_identifier (TAKE (LENGTH p - 2) (DROP 1 p))
    else NONE
End

Definition decode_type_identifier_def:
  decode_type_identifier s =
    if isPREFIX "t_rational_" s then decode_rational (DROP 11 s)
    else if s = "t_tuple$__$" then SOME (SrcTupleType [])
    else if isPREFIX "t_tuple$" s then
      case REVERSE (separated_fields #"$" "" (DROP 8 s)) of
        [] :: pieces =>
          OPTION_MAP SrcTupleType
            (all_some (MAP tuple_component (REVERSE pieces)))
      | _ => NONE
    else OPTION_MAP SrcType (decode_elementary_identifier s)
End

(* Normalized and decoded types are valid shapes. *)

Theorem elementary_type_valid:
  elementary_type name = SOME ty ⇒ valid_type_shape ty
Proof
  rw[elementary_type_def, AllCaseEqs()] >>
  simp[valid_type_shape_def, valid_int_width_def]
QED

Theorem elementary_type_outer_free[local]:
  elementary_type name = SOME ty ⇒ outer_location_free ty
Proof
  rw[elementary_type_def, AllCaseEqs()] >> simp[outer_location_free_def]
QED

Theorem elementary_mapping_key[local]:
  is_elementary_type ty ∧ valid_type_shape ty ⇒ valid_mapping_key ty
Proof
  Cases_on ‘ty’ >> simp[solidityCoreWfTheory.is_elementary_type_def, valid_type_shape_def,
                       valid_mapping_key_def]
QED

Theorem normalize_type_name_shape[local]:
  ∀ty. normalize_type_name tn = SOME ty ⇒
       valid_type_shape ty ∧ outer_location_free ty
Proof
  Induct_on ‘tn’ >> rw[normalize_type_name_def, AllCaseEqs()] >>
  imp_res_tac elementary_type_valid >>
  imp_res_tac elementary_type_outer_free >>
  gvs[valid_type_shape_def, outer_location_free_def, valid_array_length_def] >>
  metis_tac[elementary_mapping_key]
QED

Theorem normalize_type_name_valid:
  normalize_type_name tn = SOME ty ⇒ valid_type_shape ty
Proof
  metis_tac[normalize_type_name_shape]
QED

Theorem decode_elementary_identifier_valid:
  decode_elementary_identifier s = SOME ty ⇒ valid_type_shape ty
Proof
  rw[decode_elementary_identifier_def] >>
  imp_res_tac elementary_type_valid >> gvs[valid_type_shape_def]
QED

Theorem decode_type_identifier_valid:
  (decode_type_identifier s = SOME (SrcType ty) ⇒ valid_type_shape ty) ∧
  (decode_type_identifier s = SOME (SrcTupleType tys) ⇒
   EVERY valid_type_shape tys)
Proof
  ‘∀ps tys. all_some (MAP tuple_component ps) = SOME tys ⇒
            EVERY valid_type_shape tys’
    by (Induct >> rw[all_some_def, AllCaseEqs()] >>
        gvs[tuple_component_def] >>
        metis_tac[decode_elementary_identifier_valid]) >>
  rw[decode_type_identifier_def, decode_rational_def, rational_type_def,
     AllCaseEqs()] >>
  gvs[] >> metis_tac[decode_elementary_identifier_valid]
QED

(* The elementary type, or the integer value of an integer literal type, of a
 * typeIdentifier.
 *)
Definition identifier_type_def:
  identifier_type s =
    case decode_type_identifier s of
      SOME (SrcType ty) => SOME ty
    | _ => NONE
End

Definition identifier_integer_def:
  identifier_integer s =
    case decode_type_identifier s of
      SOME (SrcRational i d) => if d = 1 then SOME i else NONE
    | _ => NONE
End

(* Canonical compiler identifiers for the admitted storage types. Mapping
 * children are checked against their AST types, including nested mappings.
 *)
Definition storage_type_identifier_def:
  (storage_type_identifier BoolT = "t_bool") ∧
  (storage_type_identifier (UintT n) = "t_uint" ++ toString n) ∧
  (storage_type_identifier (IntT n) = "t_int" ++ toString n) ∧
  (storage_type_identifier (AddressT NonpayableAddress) = "t_address") ∧
  (storage_type_identifier (AddressT PayableAddress) = "t_address_payable") ∧
  (storage_type_identifier (FixedBytesT n) = "t_bytes" ++ toString n) ∧
  (storage_type_identifier (ArrayT element (SOME n)) =
    "t_array$_" ++ storage_type_identifier element ++ "_$" ++ toString n ++
    "_storage") ∧
  (storage_type_identifier (StructT (AstId id)) =
    "t_struct$__$" ++ toString id ++ "_storage") ∧
  (storage_type_identifier (ArrayT element NONE) =
    "t_array$_" ++ storage_type_identifier element ++ "_$dyn_storage") ∧
  (storage_type_identifier (MappingT key value) =
    "t_mapping$_" ++ storage_type_identifier key ++ "_$_" ++
    storage_type_identifier value ++ "_$") ∧
  (storage_type_identifier _ = "")
End

(* storageLayout uses parentheses and commas where AST identifiers use $_. *)
Definition storage_layout_identifier_def:
  (storage_layout_identifier (ArrayT element (SOME n)) =
    "t_array(" ++ storage_layout_identifier element ++ ")" ++ toString n ++
    "_storage") ∧
  (storage_layout_identifier (ArrayT element NONE) =
    "t_array(" ++ storage_layout_identifier element ++ ")dyn_storage") ∧
  (storage_layout_identifier (MappingT key value) =
    "t_mapping(" ++ storage_layout_identifier key ++ "," ++
    storage_layout_identifier value ++ ")") ∧
  (storage_layout_identifier (StructT (AstId id)) =
    "t_struct()" ++ toString id ++ "_storage") ∧
  (storage_layout_identifier ty = storage_type_identifier ty)
End

(* Struct names are display metadata; declaration IDs determine identity.
 * Keep every other character, including location/pointer suffixes. *)
Definition canonical_storage_identifier_def:
  (canonical_storage_identifier (mode : num) (skip : num) [] = []) ∧
  (canonical_storage_identifier mode skip (c :: cs) =
    if skip ≠ 0 then canonical_storage_identifier mode (skip - 1) cs
    else if mode = 1 then
      if c = #"_" ∧ isPREFIX "$" cs ∧ ¬isPREFIX "$$" cs then
        "_$" ++ canonical_storage_identifier 0 1 cs
      else canonical_storage_identifier 1 0 cs
    else if mode = 2 then
      if c = #")" then ")" ++ canonical_storage_identifier 0 0 cs
      else canonical_storage_identifier 2 0 cs
    else if isPREFIX "t_struct$_" (c :: cs) then
      "t_struct$_" ++ canonical_storage_identifier 1 9 cs
    else if isPREFIX "t_struct(" (c :: cs) then
      "t_struct(" ++ canonical_storage_identifier 2 8 cs
    else c :: canonical_storage_identifier 0 0 cs)
End

Definition source_type_matches_def:
  source_type_matches ty tid ⇔
    canonical_storage_identifier 0 0 tid = storage_type_identifier ty
End

(* A parameter, return or local variable: an elementary value type in the
 * default location, agreeing with its typeIdentifier.
 *)
Definition variable_type_def:
  variable_type (v : src_variable) =
    case normalize_type_name v.var_type_name of
      SOME ty =>
        if v.var_location = "default" ∧
           source_type_matches ty v.var_type_id
        then SOME ty else NONE
    | NONE => NONE
End

(* Struct fields use storage pointer identifiers for arrays and structs,
 * unlike state declarations. Mappings retain their ordinary identifier. *)
Definition field_variable_type_def:
  field_variable_type (v : src_variable) =
    case normalize_type_name v.var_type_name of
      SOME ty =>
        let suffix = case ty of ArrayT _ _ => "_ptr" | StructT _ => "_ptr" | _ => "" in
        if v.var_location = "default" ∧
           canonical_storage_identifier 0 0 v.var_type_id =
             storage_type_identifier ty ++ suffix
        then SOME ty else NONE
    | NONE => NONE
End

(* The type of a call to a function with these return types. *)
Definition call_value_type_def:
  (call_value_type [ty] = SrcType ty) ∧
  (call_value_type tys = SrcTupleType tys)
End

(* Ids *)

Definition type_name_ids_def:
  (type_name_ids (SrcElementaryTypeName info _ _) = [info.node_id]) ∧
  (type_name_ids (SrcArrayTypeName info element _) =
    info.node_id :: type_name_ids element) ∧
  (type_name_ids (SrcStructTypeName info _ _) = [info.node_id]) ∧
  (type_name_ids (SrcDynamicArrayTypeName info element) =
    info.node_id :: type_name_ids element) ∧
  (type_name_ids (SrcMappingTypeName info key value) =
    info.node_id :: type_name_ids key ++ type_name_ids value)
End

Definition variable_ids_def:
  variable_ids (v : src_variable) =
    v.var_info.node_id :: type_name_ids v.var_type_name
End

Definition expr_ids_def:
  (expr_ids (SrcIdentifier info _ _ _) = [info.node_id]) ∧
  (expr_ids (SrcMemberAccess info root_expr _ _) =
    info.node_id :: expr_ids root_expr) ∧
  (expr_ids (SrcArrayMember info _ root_expr _) =
    info.node_id :: expr_ids root_expr) ∧
  (expr_ids (SrcArrayLength info root_expr _) =
    info.node_id :: expr_ids root_expr) ∧
  (expr_ids (SrcLiteral info _ _ _) = [info.node_id]) ∧
  (expr_ids (SrcUnaryOperation info _ _ e _) = info.node_id :: expr_ids e) ∧
  (expr_ids (SrcBinaryOperation info _ l r _ _) =
    info.node_id :: expr_ids l ++ expr_ids r) ∧
  (expr_ids (SrcIndexAccess info b i _) =
    info.node_id :: expr_ids b ++ expr_ids i) ∧
  (expr_ids (SrcAssignment info _ l r _) =
    info.node_id :: expr_ids l ++ expr_ids r) ∧
  (expr_ids (SrcTupleExpression info cs _) =
    info.node_id :: component_ids cs) ∧
  (expr_ids (SrcFunctionCall info f args _) =
    info.node_id :: expr_ids f ++ exprs_ids args) ∧
  (expr_ids (SrcBuiltinCall info callee _ condition message _) =
    [info.node_id; callee.node_id] ++
    (case condition of NONE => [] | SOME c => expr_ids c) ++
    (case message of NONE => [] | SOME m => expr_ids m)) ∧
  (expr_ids (SrcTypeConversion info tn e _) =
    info.node_id :: type_name_ids tn ++ expr_ids e) ∧
  (expr_ids (SrcEnvironment info _ _) = [info.node_id]) ∧
  (expr_ids (SrcExternalCall info _ _ operands _) =
    info.node_id :: exprs_ids operands) ∧
  (component_ids [] = []) ∧
  (component_ids (NONE :: cs) = component_ids cs) ∧
  (component_ids (SOME e :: cs) = expr_ids e ++ component_ids cs) ∧
  (exprs_ids [] = []) ∧
  (exprs_ids (e :: es) = expr_ids e ++ exprs_ids es)
End

Definition option_expr_ids_def:
  (option_expr_ids NONE = []) ∧
  (option_expr_ids (SOME e) = expr_ids e)
End

Definition declarations_ids_def:
  (declarations_ids [] = []) ∧
  (declarations_ids (NONE :: ds) = declarations_ids ds) ∧
  (declarations_ids (SOME v :: ds) = variable_ids v ++ declarations_ids ds)
End

Definition stmt_ids_def:
  (stmt_ids (SrcBlock info ss) = info.node_id :: stmts_ids ss) ∧
  (stmt_ids (SrcUncheckedBlock info ss) = info.node_id :: stmts_ids ss) ∧
  (stmt_ids (SrcExpressionStatement info e) = info.node_id :: expr_ids e) ∧
  (stmt_ids (SrcVariableDeclarationStatement info _ decls init) =
    info.node_id :: declarations_ids decls ++ option_expr_ids init) ∧
  (stmt_ids (SrcIfStatement info c t e) =
    info.node_id :: expr_ids c ++ stmt_ids t ++ option_stmt_ids e) ∧
  (stmt_ids (SrcWhileStatement info c body) =
    info.node_id :: expr_ids c ++ stmt_ids body) ∧
  (stmt_ids (SrcDoWhileStatement info body c) =
    info.node_id :: stmt_ids body ++ expr_ids c) ∧
  (stmt_ids (SrcForStatement info init c next body) =
    info.node_id :: option_stmt_ids init ++ option_expr_ids c ++
    option_stmt_ids next ++ stmt_ids body) ∧
  (stmt_ids (SrcBreak info) = [info.node_id]) ∧
  (stmt_ids (SrcContinue info) = [info.node_id]) ∧
  (stmt_ids (SrcReturn info _ e) = info.node_id :: option_expr_ids e) ∧
  (stmt_ids (SrcEmit info _ args) = info.node_id :: exprs_ids args) ∧
  (option_stmt_ids NONE = []) ∧
  (option_stmt_ids (SOME s) = stmt_ids s) ∧
  (stmts_ids [] = []) ∧
  (stmts_ids (s :: ss) = stmt_ids s ++ stmts_ids ss)
End

Definition function_ids_def:
  function_ids (f : src_function) =
    f.fn_info.node_id :: f.fn_parameters_id :: f.fn_returns_id ::
    FLAT (MAP variable_ids (f.fn_parameters ++ f.fn_returns)) ++
    stmt_ids f.fn_body
End

Definition contract_ids_def:
  contract_ids (c : src_contract) =
    c.contract_info.node_id ::
    FLAT (MAP (λs. s.struct_info.node_id ::
      FLAT (MAP variable_ids s.struct_members)) c.contract_structs) ++
    FLAT (MAP variable_ids c.contract_state_variables) ++
    FLAT (MAP (λ(_, e). expr_ids e) c.contract_initializers) ++
    FLAT (MAP (λ(_, _, es). exprs_ids es) c.contract_base_arguments) ++
    FLAT (MAP (λe. e.event_info.node_id ::
      FLAT (MAP (variable_ids o FST) e.event_parameters)) c.contract_events) ++
    FLAT (MAP function_ids c.contract_functions)
End

Definition unit_ids_def:
  unit_ids (u : src_unit) =
    u.unit_info.node_id :: FLAT (MAP contract_ids u.unit_contracts)
End

(* Checking *)

Definition unary_operator_ok_def:
  unary_operator_ok op ⇔
    op = "++" ∨ op = "--" ∨ op = "-" ∨ op = "!" ∨ op = "~"
End

Definition binary_operator_ok_def:
  binary_operator_ok op ⇔
    op = "+" ∨ op = "-" ∨ op = "*" ∨ op = "/" ∨ op = "%" ∨ op = "**" ∨
    op = "<<" ∨ op = ">>" ∨ op = "&" ∨ op = "|" ∨ op = "^" ∨ op = "==" ∨
    op = "!=" ∨ op = "<" ∨ op = "<=" ∨ op = ">" ∨ op = ">=" ∨ op = "&&" ∨
    op = "||"
End

Definition assignment_operator_ok_def:
  assignment_operator_ok op ⇔
    op = "=" ∨ op = "+=" ∨ op = "-=" ∨ op = "*=" ∨ op = "/=" ∨ op = "%=" ∨
    op = "<<=" ∨ op = ">>=" ∨ op = "&=" ∨ op = "|=" ∨ op = "^="
End

(* Functions callable by id; variables in lexical scope; the contract's state
 * variables, if the function may read them; the innermost scope node; the
 * enclosing function's return list; whether in a loop body.
 *)
Datatype:
  import_env = <|
    functions : (num # src_function) list;
    structs : src_struct list;
    events : (num # src_event) list;
    variables : (num # sol_type) list;
    state : (num # sol_type) list;
    scope : num;
    returns_id : num;
    in_loop : bool
  |>
End

Definition source_struct_field_def:
  source_struct_field structs id field =
    case ALOOKUP (MAP (λs. (s.struct_info.node_id, s.struct_members)) structs) id of
      SOME fields =>
        (case ALOOKUP (MAP (λv. (v.var_info.node_id, v)) fields) field of
           SOME v => field_variable_type v
         | NONE => NONE)
    | NONE => NONE
End

(* Literal bytes are imported from solc's hexValue, including UTF-8 and NULs.
 * Dynamic strings are a later runtime increment. *)
Definition literal_message_def:
  (literal_message (SrcLiteral _ kind value tid) =
    if (kind = "string" ∨ kind = "unicodeString" ∨ kind = "hexString") ∧
       isPREFIX "t_stringliteral_" tid
    then SOME value else NONE) ∧
  (literal_message _ = NONE)
End

Definition builtin_shape_def:
  (builtin_shape AssertBuiltin condition message ⇔
    IS_SOME condition ∧ message = NONE) ∧
  (builtin_shape RequireBuiltin condition message ⇔
    IS_SOME condition ∧
    (case message of NONE => T | SOME m => IS_SOME (literal_message m))) ∧
  (builtin_shape RevertBuiltin condition message ⇔
    condition = NONE ∧
    (case message of NONE => T | SOME m => IS_SOME (literal_message m)))
End

(* The decoded type of a checked expression. *)
Definition check_expr_def:
  (check_expr (env : import_env) (SrcIdentifier _ _ x tid) =
    case ALOOKUP (env.variables ++ env.state) x of
      SOME ty =>
        if source_type_matches ty tid then SOME (SrcType ty)
        else NONE
    | NONE => NONE) ∧
  (check_expr env (SrcMemberAccess _ root_expr field tid) =
    case check_expr env root_expr of
      SOME (SrcType (StructT (AstId id))) =>
        (case source_struct_field env.structs id field of
           SOME ty => if source_type_matches ty tid then SOME (SrcType ty) else NONE
         | NONE => NONE)
    | _ => NONE) ∧
  (check_expr env (SrcIndexAccess _ root_expr index tid) =
    case (check_expr env root_expr, check_expr env index) of
      (SOME (SrcType (MappingT key value)), SOME _) =>
        if source_type_matches value tid then SOME (SrcType value) else NONE
    | (SOME (SrcType (ArrayT element _)), SOME index_type) =>
        if source_type_matches element tid ∧
           (case index_type of
              SrcType (UintT _) => T
            | SrcRational i d => 0 ≤ i ∧ d = 1
            | _ => F)
        then SOME (SrcType element) else NONE
    | _ => NONE) ∧
  (check_expr env (SrcArrayLength _ root_expr tid) =
    case check_expr env root_expr of
      SOME (SrcType (ArrayT _ _)) =>
        if tid = "t_uint256" then SOME (SrcType (UintT 256)) else NONE
    | _ => NONE) ∧
  (check_expr env (SrcArrayMember _ _ _ _) = NONE) ∧
  (check_expr env (SrcLiteral _ kind value tid) =
    if kind = "number" then
      case decode_type_identifier tid of
        SOME (SrcRational n d) => SOME (SrcRational n d)
      | _ => NONE
    else if kind = "bool" ∧ (value = "true" ∨ value = "false") ∧
            tid = "t_bool"
    then SOME (SrcType BoolT)
    else NONE) ∧
  (check_expr env (SrcUnaryOperation _ op _ e tid) =
    if unary_operator_ok op ∧ IS_SOME (check_expr env e) then
      case decode_type_identifier tid of
        SOME (SrcType ty) => SOME (SrcType ty)
      | _ => NONE
    else NONE) ∧
  (check_expr env (SrcBinaryOperation _ op l r common tid) =
    if binary_operator_ok op ∧ IS_SOME (check_expr env l) ∧
       IS_SOME (check_expr env r)
    then
      case (decode_type_identifier common, decode_type_identifier tid) of
        (SOME (SrcType _), SOME (SrcType ty)) => SOME (SrcType ty)
      | _ => NONE
    else NONE) ∧
  (check_expr env (SrcAssignment _ op l r tid) =
    if assignment_operator_ok op ∧ IS_SOME (check_expr env l) ∧
       IS_SOME (check_expr env r)
    then decode_type_identifier tid
    else NONE) ∧
  (check_expr env (SrcTupleExpression _ cs tid) =
    if check_components env cs then decode_type_identifier tid else NONE) ∧
  (check_expr env (SrcFunctionCall _ (SrcArrayMember _ member root_expr _) args tid) =
    case check_expr env root_expr of
      SOME (SrcType (ArrayT element NONE)) =>
        if ¬elementary_storage_type_ok element then NONE else
        if member = "push" ∧ args = [] ∧ source_type_matches element tid then
          SOME (SrcType element)
        else if tid = "t_tuple$__$" ∧ check_exprs env args ∧
                ((member = "push" ∧ LENGTH args = 1) ∨
                 (member = "pop" ∧ args = []))
        then SOME (SrcTupleType []) else NONE
    | _ => NONE) ∧
  (check_expr env (SrcFunctionCall _ (SrcIdentifier _ _ f _) args tid) =
    case ALOOKUP env.functions f of
      SOME callee =>
        (case (all_some (MAP variable_type callee.fn_returns),
               decode_type_identifier tid) of
           (SOME tys, SOME vt) =>
             if LENGTH args = LENGTH callee.fn_parameters ∧
                callee.fn_visibility ≠ "external" ∧ check_exprs env args ∧
                vt = call_value_type tys
             then SOME vt else NONE
         | _ => NONE)
    | NONE => NONE) ∧
  (check_expr env (SrcFunctionCall _ _ _ _) = NONE) ∧
  (check_expr env (SrcBuiltinCall _ _ builtin condition message tid) =
    if builtin_shape builtin condition message ∧ tid = "t_tuple$__$" ∧
       (case condition of NONE => T
        | SOME c => check_expr env c = SOME (SrcType BoolT))
    then SOME (SrcTupleType []) else NONE) ∧
  (check_expr env (SrcTypeConversion _ tn e tid) =
    case normalize_type_name tn of
      SOME ty =>
        if IS_SOME (check_expr env e) ∧
           decode_type_identifier tid = SOME (SrcType ty)
        then SOME (SrcType ty) else NONE
    | NONE => NONE) ∧
  (check_expr env (SrcEnvironment _ f tid) =
    if source_type_matches (environment_type f) tid
    then SOME (SrcType (environment_type f)) else NONE) ∧
  (* Value only for a payable callee, as the compiler requires; elaboration
     converts the target to an address. *)
  (check_expr env (SrcExternalCall _ callee with_value operands tid) =
    case (all_some (MAP variable_type callee.ext_parameters),
          all_some (MAP variable_type callee.ext_returns),
          decode_type_identifier tid) of
      (SOME params, SOME rets, SOME vt) =>
        if MEM callee.ext_mutability ["pure"; "view"; "nonpayable"; "payable"] ∧
           (with_value ⇒ callee.ext_mutability = "payable") ∧
           LENGTH operands = LENGTH params + (if with_value then 2 else 1) ∧
           check_exprs env operands ∧ vt = call_value_type rets
        then SOME vt else NONE
    | _ => NONE) ∧
  (check_components env [] ⇔ T) ∧
  (check_components env (NONE :: cs) ⇔ check_components env cs) ∧
  (check_components env (SOME e :: cs) ⇔
    IS_SOME (check_expr env e) ∧ check_components env cs) ∧
  (check_exprs env [] ⇔ T) ∧
  (check_exprs env (e :: es) ⇔
    IS_SOME (check_expr env e) ∧ check_exprs env es)
End

Definition check_condition_def:
  check_condition env c ⇔ check_expr env c = SOME (SrcType BoolT)
End

(* The local, if any, declared by one entry of a declaration statement, in
 * the current scope and with its normalized type.
 *)
Definition declare_local_def:
  (declare_local env NONE = SOME []) ∧
  (declare_local env (SOME (v : src_variable)) =
    case variable_type v of
      SOME ty =>
        if v.var_scope = env.scope then SOME [(v.var_info.node_id, ty)]
        else NONE
    | NONE => NONE)
End

(* A declaration statement: its assignments list its declarations' ids, a
 * declaration without initial value declares a single variable, and the
 * locals are visible after the statement only.
 *)
Definition declaration_id_def:
  (declaration_id NONE = NONE) ∧
  (declaration_id (SOME (v : src_variable)) = SOME v.var_info.node_id)
End

Definition check_declaration_def:
  check_declaration env assigned decls init =
    case all_some (MAP (declare_local env) decls) of
      NONE => NONE
    | SOME locals =>
        if decls ≠ [] ∧ assigned = MAP declaration_id decls ∧
           (case init of
              NONE => (case decls of [SOME _] => T | _ => F)
            | SOME e => IS_SOME (check_expr env e))
        then SOME (env with variables := FLAT locals ++ env.variables)
        else NONE
End

(* A for initialization: a declaration or an expression statement. *)
Definition check_for_init_def:
  (check_for_init env NONE = SOME env) ∧
  (check_for_init env (SOME (SrcVariableDeclarationStatement _ assigned decls
                               init)) =
    check_declaration env assigned decls init) ∧
  (check_for_init env (SOME (SrcExpressionStatement _ e)) =
    if IS_SOME (check_expr env e) then SOME env else NONE) ∧
  (check_for_init env (SOME _) = NONE)
End

(* The environment after a statement in a list: extended by a declaration,
 * unchanged by any other statement, which check_stmt checks.
 *)
Definition declaration_env_def:
  (declaration_env env (SrcVariableDeclarationStatement _ assigned decls init) =
    SOME (check_declaration env assigned decls init)) ∧
  (declaration_env env _ = NONE)
End

(* Statement lists return the environment after their declarations. *)
Definition check_stmts_def:
  (check_stmts env [] = SOME env) ∧
  (check_stmts env (s :: ss) =
    case declaration_env env s of
      SOME (SOME env') => check_stmts env' ss
    | SOME NONE => NONE
    | NONE => if check_stmt env s then check_stmts env ss else NONE) ∧
  (check_stmt env (SrcBlock info ss) ⇔
    IS_SOME (check_stmts (env with scope := info.node_id) ss)) ∧
  (check_stmt env (SrcUncheckedBlock info ss) ⇔
    IS_SOME (check_stmts (env with scope := info.node_id) ss)) ∧
  (check_stmt env (SrcExpressionStatement _ e) ⇔
    IS_SOME (check_expr env e)) ∧
  (check_stmt env (SrcVariableDeclarationStatement _ _ _ _) ⇔ F) ∧
  (check_stmt env (SrcIfStatement _ c t NONE) ⇔
    check_condition env c ∧ check_stmt env t) ∧
  (check_stmt env (SrcIfStatement _ c t (SOME e)) ⇔
    check_condition env c ∧ check_stmt env t ∧ check_stmt env e) ∧
  (check_stmt env (SrcWhileStatement _ c body) ⇔
    check_condition env c ∧ check_stmt (env with in_loop := T) body) ∧
  (check_stmt env (SrcDoWhileStatement _ body c) ⇔
    check_stmt (env with in_loop := T) body ∧ check_condition env c) ∧
  (check_stmt env (SrcForStatement info init c next body) ⇔
    case check_for_init (env with scope := info.node_id) init of
      NONE => F
    | SOME env' =>
        (case c of NONE => T | SOME c => check_condition env' c) ∧
        (case next of
           NONE => T
         | SOME (SrcExpressionStatement _ e) => IS_SOME (check_expr env' e)
         | SOME _ => F) ∧
        check_stmt (env' with in_loop := T) body) ∧
  (check_stmt env (SrcBreak _) ⇔ env.in_loop) ∧
  (check_stmt env (SrcContinue _) ⇔ env.in_loop) ∧
  (check_stmt env (SrcReturn _ returns_id e) ⇔
    returns_id = env.returns_id ∧
    case e of NONE => T | SOME e => IS_SOME (check_expr env e)) ∧
  (check_stmt env (SrcEmit _ ev args) ⇔
    case ALOOKUP env.events ev of
      SOME e => LENGTH args = LENGTH e.event_parameters ∧ check_exprs env args
    | NONE => F)
Termination
  WF_REL_TAC ‘measure (λx. case x of
                 INL (env, ss) => list_size src_stmt_size ss
               | INR (env, s) => src_stmt_size s)’ >>
  rw[fetch "-" "src_stmt_size_def", listTheory.list_size_def]
End

(* A variable declared by the node scope: a parameter or return variable of a
 * function, or a state variable of a contract.
 *)
Definition scoped_variable_def:
  scoped_variable scope (v : src_variable) =
    if v.var_scope = scope then
      case variable_type v of
        SOME ty => SOME (v.var_info.node_id, ty)
      | NONE => NONE
    else NONE
End

(* A state variable, declared by one of the contract's bases. *)
Definition state_variable_def:
  state_variable bases (v : src_variable) =
    if MEM v.var_scope bases then scoped_variable v.var_scope v else NONE
End

(* The function a call to each declaration runs: the most derived function
 * that is it or overrides it. Functions come most derived first; a
 * declaration without a body is reached through the functions overriding it.
 *)
Definition call_table_def:
  (call_table [] = []) ∧
  (call_table ((f : src_function) :: fs) =
    (f.fn_info.node_id, f) :: MAP (λx. (x, f)) f.fn_base_functions ++
    MAP (λ(x, g). (x, if MEM g.fn_info.node_id f.fn_base_functions then f else g))
      (call_table fs))
End

(* The functions no other function overrides: those calls and the dispatch
 * table can reach. *)
Definition live_functions_def:
  live_functions fs =
    let table = call_table fs in
    FILTER (λ(f : src_function).
              OPTION_MAP (λg. g.fn_info.node_id)
                (ALOOKUP table f.fn_info.node_id) = SOME f.fn_info.node_id) fs
End

(* The constructor a base declares, if any. *)
Definition contract_constructor_def:
  (contract_constructor x [] = NONE) ∧
  (contract_constructor x ((f : src_function) :: fs) =
    if f.fn_kind = "constructor" ∧ f.fn_scope = x then SOME f
    else contract_constructor x fs)
End

(* The variables the base constructor arguments a base gives see: the
 * parameters of its constructor. *)
Definition constructor_parameters_def:
  constructor_parameters x fs =
    case contract_constructor x fs of
      NONE => SOME []
    | SOME f => all_some (MAP (scoped_variable f.fn_info.node_id) f.fn_parameters)
End

(* A pure function sees no state variables. Whether a view function writes
 * one is the compiler's check.
 *)
Definition check_function_def:
  check_function structs events functions state bases (f : src_function) ⇔
    MEM f.fn_scope bases ∧
    (f.fn_kind = "function" ∨ f.fn_kind = "receive" ∨ f.fn_kind = "fallback" ∨
     f.fn_kind = "constructor") ∧
    (f.fn_mutability = "pure" ∨ f.fn_mutability = "view" ∨
     f.fn_mutability = "nonpayable" ∨ f.fn_mutability = "payable") ∧
    case (all_some (MAP (scoped_variable f.fn_info.node_id)
                     (f.fn_parameters ++ f.fn_returns)), f.fn_body) of
      (SOME variables, SrcBlock info ss) =>
        IS_SOME (check_stmts
          <| functions := functions; structs := structs; events := events;
             variables := variables;
             state := if f.fn_mutability = "pure" then [] else state;
             scope := info.node_id; returns_id := f.fn_returns_id;
             in_loop := F |> ss)
    | _ => F
End

(* The layout has an entry for each state variable, in order. *)
Definition storage_layout_ok_def:
  (storage_layout_ok fields [] [] ⇔ T) ∧
  (storage_layout_ok fields ((v : src_variable) :: vs) (e :: es) ⇔
     e.storage_id = v.var_info.node_id ∧
     (case (if fields then field_variable_type v else variable_type v) of
        SOME ty => canonical_storage_identifier 0 0 e.storage_type_id = storage_layout_identifier ty
      | NONE => F) ∧
     e.storage_slot < 2 ** 256 ∧ storage_layout_ok fields vs es) ∧
  (storage_layout_ok _ _ _ ⇔ F)
End

Definition check_struct_def:
  check_struct unit_id bases (s : src_struct) ⇔
    (MEM s.struct_scope bases ∨ s.struct_scope = unit_id) ∧
    s.struct_members ≠ [] ∧
    EVERY (λv. v.var_scope = s.struct_info.node_id ∧ IS_SOME (field_variable_type v))
      s.struct_members ∧
    case s.struct_layout of
      NONE => T
    | SOME (bytes, fields) =>
        0 < bytes ∧ bytes MOD 32 = 0 ∧ bytes DIV 32 < 2 ** 256 ∧
        storage_layout_ok T s.struct_members fields
End

(* Event parameters are elementary value types declared by the event. *)
Definition check_event_def:
  check_event (e : src_event) ⇔
    EVERY (λp. IS_SOME (scoped_variable e.event_info.node_id (FST p)))
      e.event_parameters
End

(* Initializers and base constructor arguments see the state variables and
 * call functions; base constructor arguments also see the parameters of the
 * constructor of the base giving them. *)
Definition initializer_env_def:
  initializer_env (c : src_contract) state =
    <| functions := call_table c.contract_functions;
       structs := c.contract_structs;
       events := MAP (λe. (e.event_info.node_id, e)) c.contract_events;
       variables := []; state := state; scope := c.contract_info.node_id;
       returns_id := c.contract_info.node_id; in_loop := F |>
End

Definition check_contract_def:
  check_contract unit_id (c : src_contract) ⇔
    c.contract_scope = unit_id ∧
    (case c.contract_bases of x :: _ => x = c.contract_info.node_id | [] => F) ∧
    ALL_DISTINCT c.contract_bases ∧
    EVERY (check_struct unit_id c.contract_bases) c.contract_structs ∧
    EVERY check_event c.contract_events ∧
    storage_layout_ok F c.contract_state_variables c.contract_storage ∧
    case all_some (MAP (state_variable c.contract_bases)
                     c.contract_state_variables) of
      SOME state =>
        EVERY (check_function c.contract_structs
                 (MAP (λe. (e.event_info.node_id, e)) c.contract_events)
                 (call_table c.contract_functions)
                 state c.contract_bases)
          (live_functions c.contract_functions) ∧
        EVERY (λ(x, e). IS_SOME (ALOOKUP state x) ∧
                        IS_SOME (check_expr (initializer_env c state) e))
          c.contract_initializers ∧
        EVERY (λ(x, b, args).
                 case constructor_parameters x c.contract_functions of
                   SOME ps => check_exprs (initializer_env c state with
                                             variables := ps) args
                 | NONE => F)
          c.contract_base_arguments
    | NONE => F
End

Definition valid_src_unit_def:
  valid_src_unit (u : src_unit) ⇔
    ALL_DISTINCT (unit_ids u) ∧
    EVERY (check_contract u.unit_info.node_id) u.unit_contracts
End

(* cv translation, so that imported units are checked by cv_eval. The
 * mutually recursive checkers terminate on the cv size of their syntax.
 *)

val () = cv_auto_trans decode_type_identifier_def;
val () = cv_auto_trans identifier_type_def;
val () = cv_auto_trans identifier_integer_def;
(* Keccak exports a partial HEX translation; decimal identifiers use the
 * existing total definition, including its out-of-range branch. *)
val total_hex_pre_def = cv_trans_pre "total_hex_pre" ASCIInumbersTheory.HEX;

Theorem total_hex_pre[cv_pre,local]:
  ∀n. total_hex_pre n
Proof
  rw[total_hex_pre_def] >> decide_tac
QED

val () = cv_auto_trans normalize_type_name_def;
val () = cv_auto_trans storage_type_identifier_def;
val () = cv_auto_trans canonical_storage_identifier_def;
val () = cv_auto_trans source_type_matches_def;
val () = cv_auto_trans storage_layout_identifier_def;
val () = cv_auto_trans variable_type_def;
val () = cv_auto_trans field_variable_type_def;
val () = cv_auto_trans call_value_type_def;
val () = cv_auto_trans_rec expr_ids_def (
  WF_REL_TAC ‘measure (λx. case x of
                 INL e => cv_size e
               | INR (INL cs) => cv_size cs
               | INR (INR es) => cv_size es)’ >>
  cv_termination_tac
);

val stmt_ids_pre_def = cv_auto_trans_pre_rec
  "stmt_ids_pre option_stmt_ids_pre stmts_ids_pre" stmt_ids_def (
  WF_REL_TAC ‘measure (λx. case x of
                 INL s => cv_size s
               | INR (INL s) => cv_size s
               | INR (INR ss) => cv_size ss)’ >>
  cv_termination_tac
);

Theorem stmt_ids_pre[cv_pre,local]:
  (∀v. stmt_ids_pre v) ∧ (∀v. stmts_ids_pre v) ∧ (∀v. option_stmt_ids_pre v)
Proof
  CONV_TAC (RAND_CONV (REWR_CONV CONJ_COMM)) >>
  ho_match_mp_tac stmt_ids_ind >> rpt strip_tac >>
  simp[Once stmt_ids_pre_def] >> rw[] >> fs[]
QED

val () = cv_auto_trans unit_ids_def;

val () = cv_auto_trans source_struct_field_def;
val () = cv_auto_trans literal_message_def;
val () = cv_auto_trans builtin_shape_def;

val check_expr_pre_def = cv_auto_trans_pre_rec
  "check_expr_pre check_components_pre check_exprs_pre" check_expr_def (
  WF_REL_TAC ‘measure (λx. case x of
                 INL (env, e) => cv_size e
               | INR (INL (env, cs)) => cv_size cs
               | INR (INR (env, es)) => cv_size es)’ >>
  cv_termination_tac
);

Theorem check_expr_pre[cv_pre,local]:
  (∀env e. check_expr_pre env e) ∧ (∀env cs. check_components_pre env cs) ∧
  (∀env es. check_exprs_pre env es)
Proof
  ho_match_mp_tac check_expr_ind >> rpt strip_tac >>
  simp[Once check_expr_pre_def] >> rw[] >> fs[]
QED

val () = cv_auto_trans declaration_id_def;
val () = cv_auto_trans declare_local_def;
val () = cv_auto_trans check_declaration_def;
val () = cv_auto_trans check_for_init_def;
val () = cv_auto_trans declaration_env_def;
val () = cv_auto_trans check_condition_def;

val check_stmts_pre_def = cv_auto_trans_pre_rec
  "check_stmts_pre check_stmt_pre" check_stmts_def (
  WF_REL_TAC ‘measure (λx. case x of
                 INL (env, ss) => cv_size ss
               | INR (env, s) => cv_size s)’ >>
  cv_termination_tac
);

Theorem check_stmts_pre[cv_pre,local]:
  (∀env ss. check_stmts_pre env ss) ∧ (∀env s. check_stmt_pre env s)
Proof
  ho_match_mp_tac check_stmts_ind >> rpt strip_tac >>
  simp[Once check_stmts_pre_def] >> rw[] >> fs[] >>
  (* record updates appear as cases on the environment *)
  Cases_on ‘env’ >> gvs[fetch "-" "import_env_fn_updates"] >>
  rename1 ‘check_for_init _ _ = SOME env'’ >>
  Cases_on ‘env'’ >> gvs[fetch "-" "import_env_fn_updates"]
QED

val () = cv_auto_trans scoped_variable_def;
val () = cv_auto_trans state_variable_def;
val () = cv_auto_trans call_table_def;
val () = cv_auto_trans contract_constructor_def;
val () = cv_auto_trans constructor_parameters_def;
val () = cv_auto_trans live_functions_def;
val () = cv_auto_trans storage_layout_ok_def;
val () = cv_auto_trans check_function_def;
val () = cv_auto_trans check_struct_def;
val () = cv_auto_trans check_event_def;
val () = cv_auto_trans initializer_env_def;
val () = cv_auto_trans check_contract_def;
val () = cv_auto_trans valid_src_unit_def;
