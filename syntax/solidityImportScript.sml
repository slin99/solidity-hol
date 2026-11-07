(* Normalized source AST: the admitted subset of the pinned compiler's
 * analyzed Standard JSON AST, between the raw compiler output and the core.
 *
 * solidityImportLib builds these terms from a compiler artifact and fails
 * closed: an unknown nodeType, a missing required field, or a feature outside
 * the subset (overriding state variables, file-level constants,
 * super other than in calls, named or try calls, built-ins other than
 * require, assert, revert, members of msg, tx and block, this and
 * type(T).max and .min for integer types T, literal subdenominations,
 * inline arrays, type names other than elementary, contract and struct types,
 * arrays and mappings, ...)
 * raises ImportError. Semantic nodes keep their compiler id and source range;
 * declarations are referred to by id, and names are diagnostic only. Type
 * annotations are kept as the compiler's encoded typeIdentifier and decoded
 * here, never from the display typeString.
 *
 * A unit holds its deployable contracts: those neither abstract, nor an
 * interface, nor a base of another contract of the unit. Each is flattened
 * along its linearization (src_contract); its bases, the functions it calls
 * and the structs it uses may come from any source unit of the compilation
 * (unit_sources), since the AST refers to declarations by id across files.
 * The internal functions, modifiers and constants of libraries it uses come
 * with it: L.f(args) and x.f(args), with f attached to x's type by a using
 * directive, are internal calls of f, the latter with x as the first
 * argument, and L.c names the constant c.
 *
 * A contract or interface type is read as address, its value at run time,
 * stored and ABI encoded as one: in type names, type identifiers and storage
 * layouts, and as the target of a conversion I(a). this is the contract's
 * own address.
 *
 * Types are normalized from elementary, array and mapping type-name nodes; value
 * types are decoded from typeIdentifiers. Both yield only valid shapes (normalize_type_name_valid,
 * decode_type_identifier_valid). Literals keep their exact rational type.
 *
 * valid_src_unit then establishes, for an imported unit:
 *  - each contract's node ids, with the unit's, are distinct (contracts
 *    share the declarations of a common base or library), and the unit is
 *    among its compilation's source units;
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
 *    contract, the most derived override of the one it names (call_table),
 *    or to an internal library function;
 *    calls have matching arity and are annotated with the callee's
 *    return types; conversions are annotated with their normalized target type;
 *    environment reads with their member's type; type(T).max and .min an
 *    integer type T, with T's type; emits name an event of the
 *    contract with as many arguments as it has parameters, and reverts with
 *    an error carry as many arguments as the error has parameters, which
 *    are of elementary types;
 *  - declaration statements list exactly their declarations' ids as
 *    assignments, returns name the enclosing function's return list, break and
 *    continue occur in loop bodies, conditions are boolean;
 *  - functions, receive and fallback are pure, view, nonpayable or payable,
 *    and only non-pure ones refer to state variables; functions a more
 *    derived one overrides are checked only when a super call reaches
 *    them, since nothing else does; a super call runs the first function
 *    with the name and parameter types of the one it names in a base after
 *    the caller's, and modifier bodies make none;
 *    contracts are scoped by the unit, functions by a base of their contract,
 *    structs by a base or a source unit of the compilation;
 *  - library functions are internal or private, scoped by a library distinct
 *    from the bases, and see no state variable;
 *  - constants are of elementary value types or byte sequences, declared by
 *    a base or a library, and their values refer to other constants only; an
 *    identifier may name a constant;
 *  - operators belong to the admitted set and every other expression
 *    annotation decodes to an elementary, rational literal or tuple type;
 *    an operation over literals the compiler types as an integer is that
 *    integer.
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
  (* an inline assembly block's code *)
  yulAST
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
  | SrcEnumTypeName node_info num
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
 * SuperCall (super.f(args)): the declaration of f the compiler resolved
 * from the caller's contract, positional arguments.
 * FunctionCall (kind typeConversion): target type name, argument.
 * Environment: a member of msg, tx or block, or this.
 * New (new T(n)): the type name of T, the length.
 * EnumValue (E.A): the enum's type name and the member's index.
 * ExternalCall (c.f{value: v}(args), c of a contract type): the declaration of f, whether
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

(* The error a revert statement names: its selector and parameters. *)
Datatype:
  src_error = <|
    error_selector : byte list;
    error_parameters : src_variable list
  |>
End

(* abi.encode, abi.encodePacked, abi.encodeWithSelector (the selector is the
 * first argument) and abi.encodeWithSignature (of the bytes of a literal
 * signature, which is not among the arguments). bytes.concat is
 * abi.encodePacked, and string.concat (AbiStringConcat) is too, as a string.
 *)
Datatype:
  abi_form = AbiPlain | AbiPacked | AbiWithSelector | AbiWithSignature (byte list)
           | AbiStringConcat
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
  | SrcConditional node_info src_expr src_expr src_expr string
  | SrcAssignment node_info string src_expr src_expr string
  | SrcIndexAccess node_info src_expr src_expr string
  | SrcTupleExpression node_info (src_expr option list) string
  | SrcFunctionCall node_info src_expr (src_expr list) (num list) string
  | SrcSuperCall node_info num (src_expr list) (num list) string
  | SrcBuiltinCall node_info node_info src_builtin (src_expr option)
      (src_expr option) string
  | SrcTypeConversion node_info src_type_name src_expr string
  | SrcEnvironment node_info environment_field string
  | SrcExternalCall node_info src_external bool (src_expr list) (num list) string
  | SrcTypeMember node_info string src_type_name string
  | SrcNew node_info src_type_name src_expr string
  | SrcEnumValue node_info src_type_name num string
  | SrcKeccak256 node_info node_info src_expr string
  | SrcSelector node_info (byte list) string
  | SrcAbiEncode node_info node_info abi_form (src_expr list) string
End

(* VariableDeclarationStatement: assignments, declarations (NONE for a hole),
 * initial value. ForStatement: initialization, condition, loop expression,
 * body. Return: functionReturnParameters, expression. Emit: the event's id,
 * positional arguments. RevertError: revert E(args), the error and the
 * positional arguments. InlineAssembly: the block's code, and each Solidity
 * variable it names, keyed by the name the code uses (x, or x.slot and
 * x.offset for a state variable's location).
 *)
Datatype:
  src_assembly_reference = SrcAssemblyValue num
                         | SrcAssemblySlot num
                         | SrcAssemblyOffset num
End

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
  | SrcEmit node_info num (src_expr list) (num list)
  | SrcRevertError node_info src_error (src_expr list) (num list)
  | SrcInlineAssembly node_info (yul_stmt list)
      ((string # src_assembly_reference) list)
  | SrcPlaceholder node_info
End

(* A modifier: its parameters and its body, where SrcPlaceholder runs the
 * rest of the function it modifies. *)
Datatype:
  src_modifier = <|
    modifier_info : node_info;
    modifier_parameters_id : num;
    modifier_parameters : src_variable list;
    modifier_body : src_stmt
  |>
End

(* Parameter lists are represented by their ids and declarations. The kind is
 * function, receive or fallback; the selector is that of an external or
 * public function. The base functions are the declarations it overrides,
 * directly or through other overridden declarations (the closure of the
 * compiler's baseFunctions). The modifiers are the modifier invocations, in
 * order: the modifier's id and the arguments. The super calls are the
 * declarations the body's super calls name.
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
    fn_modifiers : (num # src_expr list) list;
    fn_super_calls : num list;
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
 * give state variables (by id) their declared values; constants come with
 * their values; base arguments are
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
    contract_immutables : src_variable list;
    contract_initializers : (num # src_expr) list;
    (* the libraries whose functions or constants it uses *)
    contract_libraries : num list;
    contract_constants : (src_variable # src_expr) list;
    contract_base_arguments : (num # num # src_expr list) list;
    contract_storage : src_storage_entry list;
    contract_structs : src_struct list;
    (* the enums of the compilation, by id, with their member counts *)
    contract_enums : (num # num) list;
    contract_events : src_event list;
    contract_modifiers : src_modifier list;
    contract_functions : src_function list;
    (* the internal library functions it calls, also through each other *)
    contract_library_functions : src_function list;
    (* the public state variables, immutables and constants, each with its
     * getter's selector *)
    contract_getters : (num # byte list) list
  |>
End

Datatype:
  src_unit = <|
    unit_info : node_info;
    unit_path : string;
    unit_sources : num list;
    unit_contracts : src_contract list
  |>
End

(* Types *)

(* Elementary type names, with the widths valid_type_shape requires. *)
Definition elementary_type_def:
  elementary_type name =
    if name = "bytes" then SOME BytesT
    else if name = "string" then SOME StringT
    else if name = "bool" then SOME BoolT
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
  (normalize_type_name (SrcEnumTypeName _ id) = SOME (EnumT (AstId id))) ∧
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
  | SrcByteLiteral
  | SrcRational int num
  | SrcTupleType (sol_type list)
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

(* A memory array "t_array$_" ^ k, its base, then each dimension innermost
 * first: "_$dyn_memory_ptr" or "_$N_memory_ptr". Split at "$", the k + 1
 * prefixes are "t_array" and then "_t_array", the base is "_" b "_", and
 * each dimension but the last ends with "_". *)
Definition array_prefix_fields_def:
  (array_prefix_fields [] = 0n) ∧
  (array_prefix_fields (f :: fs) =
    if f = "_t_array" then array_prefix_fields fs + 1 else 0)
End

(* The pointer suffix of a memory or calldata type identifier. *)
Definition location_suffix_def:
  location_suffix loc =
    if loc = CalldataLoc then "_calldata_ptr"
    else if loc = StorageLoc then "_storage"
    else "_memory_ptr"
End

Definition array_dimensions_def:
  (array_dimensions loc ty [] = SOME ty) ∧
  (array_dimensions loc ty (l :: ls) =
    let suffix = if ls = [] then location_suffix loc
                 else location_suffix loc ++ "_" in
    if ¬isPREFIX (REVERSE suffix) (REVERSE l) then NONE else
    let digits = TAKE (LENGTH l - LENGTH suffix) l in
    let length =
      if digits = "dyn" then SOME NONE
      else case fromDecString digits of
             SOME n => if 0 < n then SOME (SOME n) else NONE
           | NONE => NONE in
    case length of
      SOME length => array_dimensions loc (ArrayT ty length) ls
    | NONE => NONE)
End

Definition array_base_def:
  array_base loc name =
    if name = "t_bytes" ++ location_suffix loc then SOME BytesT
    else if name = "t_string" ++ location_suffix loc then SOME StringT
    else if name = "t_address_payable" then SOME (AddressT PayableAddress)
    else if isPREFIX "t_" name ∧ name ≠ "t_uint" ∧ name ≠ "t_int" then
      case elementary_type (DROP 2 name) of
        SOME ty => if is_elementary_type ty then SOME ty else NONE
      | NONE => NONE
    else NONE
End

(* A memory, calldata or storage array type identifier, nested to any depth. *)
Definition decode_located_array_def:
  decode_located_array loc s =
    case separated_fields #"$" "" s of
      f :: fs =>
        if f ≠ "t_array" then NONE else
        let k = array_prefix_fields fs in
        (case DROP k fs of
           b :: dimensions =>
             if LENGTH dimensions ≠ k + 1 ∨ LENGTH b < 2 ∨ ¬isPREFIX "_" b ∨
                ¬isPREFIX "_" (REVERSE b) then NONE else
             (case array_base loc (TAKE (LENGTH b - 2) (DROP 1 b)) of
                SOME element =>
                  (case array_dimensions loc element dimensions of
                     SOME ty =>
                       if located_value_type (LocatedT loc ty) ∧
                          valid_type_shape (LocatedT loc ty)
                       then SOME (LocatedT loc ty) else NONE
                   | NONE => NONE)
              | NONE => NONE)
         | [] => NONE)
    | [] => NONE
End

Definition decode_elementary_identifier_def:
  decode_elementary_identifier s =
    if isPREFIX "t_array$_" s then
      (* The outer dimension's suffix names the location. A storage array
       * value is unlocated, as t_bytes_storage is. *)
      (if isPREFIX (REVERSE (location_suffix StorageLoc)) (REVERSE s) then
         case decode_located_array StorageLoc s of
           SOME (LocatedT _ ty) => SOME ty
         | _ => NONE
       else if isPREFIX (REVERSE (location_suffix CalldataLoc)) (REVERSE s) then
         decode_located_array CalldataLoc s
       else decode_located_array MemoryLoc s)
    else if s = "t_bytes_storage" then SOME BytesT
    else if s = "t_string_storage" then SOME StringT
    else if s = "t_bytes_memory_ptr" then SOME (LocatedT MemoryLoc BytesT)
    else if s = "t_string_memory_ptr" then SOME (LocatedT MemoryLoc StringT)
    else if s = "t_bytes_calldata_ptr" then SOME (LocatedT CalldataLoc BytesT)
    else if s = "t_string_calldata_ptr" then SOME (LocatedT CalldataLoc StringT)
    else if s = "t_bytes_storage_ptr" then SOME (LocatedT StorageLoc BytesT)
    else if s = "t_string_storage_ptr" then SOME (LocatedT StorageLoc StringT)
    else if s = "t_address_payable" then SOME (AddressT PayableAddress)
    else if isPREFIX "t_enum_" s then
      OPTION_MAP (λid. EnumT (AstId id)) (fromDecString (DROP 7 s))
    else if isPREFIX "t_" s ∧ s ≠ "t_uint" ∧ s ≠ "t_int" then
      elementary_type (DROP 2 s)
    else NONE
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

(* A tuple component "_c_", from "t_tuple$_c1_$_c2_$...$". Literal
 * byte sequences retain their source string kind here; elaboration supplies
 * the destination's bytes/string type and location when coercing the value. *)
Definition tuple_component_def:
  tuple_component p =
    if 2 ≤ LENGTH p ∧ isPREFIX "_" p ∧ isPREFIX "_" (REVERSE p) then
      let tid = TAKE (LENGTH p - 2) (DROP 1 p) in
      if isPREFIX "t_stringliteral_" tid then SOME StringT
      else decode_elementary_identifier tid
    else NONE
End

(* The components of a tuple identifier from its `$`-separated fields,
 * rejoining an array's fields: "_t_array" opens an array and a dimension,
 * the one field without a leading "_", closes one. *)
Definition tuple_identifier_components_def:
  (tuple_identifier_components (depth : num) acc [] =
    if depth = 0 ∧ acc = "" then SOME [] else NONE) ∧
  (tuple_identifier_components depth acc (f :: fs) =
    let component = if acc = "" then f else acc ++ "$" ++ f in
    let depth' = if f = "_t_array" then depth + 1
                 else if isPREFIX "_" f then depth else depth - 1 in
    if depth' = 0 then
      case tuple_identifier_components 0 "" fs of
        SOME cs => SOME (component :: cs)
      | NONE => NONE
    else tuple_identifier_components depth' component fs)
End

Definition decode_type_identifier_def:
  decode_type_identifier s =
    if isPREFIX "t_rational_" s then decode_rational (DROP 11 s)
    else if isPREFIX "t_stringliteral_" s then SOME SrcByteLiteral
    else if s = "t_tuple$__$" then SOME (SrcTupleType [])
    else if isPREFIX "t_tuple$" s then
      case REVERSE (separated_fields #"$" "" (DROP 8 s)) of
        [] :: pieces =>
          (case tuple_identifier_components 0 "" (REVERSE pieces) of
             SOME cs => OPTION_MAP SrcTupleType (all_some (MAP tuple_component cs))
           | NONE => NONE)
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
  rw[decode_elementary_identifier_def, decode_located_array_def, AllCaseEqs()] >>
  imp_res_tac elementary_type_valid >>
  gvs[valid_type_shape_def, outer_location_free_def, location_shape_ok_def,
      is_reference_type_def, contains_mapping_def]
QED

Theorem tuple_component_valid[local]:
  tuple_component p = SOME ty ⇒ valid_type_shape ty
Proof
  rw[tuple_component_def] >> gvs[valid_type_shape_def] >>
  metis_tac[decode_elementary_identifier_valid]
QED

Theorem decode_type_identifier_valid:
  (decode_type_identifier s = SOME (SrcType ty) ⇒ valid_type_shape ty) ∧
  (decode_type_identifier s = SOME (SrcTupleType tys) ⇒
   EVERY valid_type_shape tys)
Proof
  ‘∀ps tys. all_some (MAP tuple_component ps) = SOME tys ⇒
            EVERY valid_type_shape tys’
    by (Induct >> rw[all_some_def, AllCaseEqs()] >>
        gvs[] >> metis_tac[tuple_component_valid]) >>
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
  (storage_type_identifier (LocatedT loc ty) =
    if byte_sequence_type ty then
      (if ty = BytesT then "t_bytes" else "t_string") ++
      (case loc of MemoryLoc => "_memory_ptr" | CalldataLoc => "_calldata_ptr"
                 | StorageLoc => "_storage_ptr")
    else "") ∧
  (storage_type_identifier BytesT = "t_bytes_storage") ∧
  (storage_type_identifier StringT = "t_string_storage") ∧
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
  (storage_type_identifier (EnumT (AstId id)) = "t_enum_" ++ toString id) ∧
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

(* Memory and calldata types: an array's elements are values or pointers in
 * the same location. *)
Definition located_type_identifier_def:
  (located_type_identifier loc (ArrayT element length) =
    "t_array$_" ++ located_type_identifier loc element ++ "_$" ++
    (case length of SOME n => toString n | NONE => "dyn") ++ location_suffix loc) ∧
  (located_type_identifier loc BytesT = "t_bytes" ++ location_suffix loc) ∧
  (located_type_identifier loc StringT = "t_string" ++ location_suffix loc) ∧
  (located_type_identifier loc ty = storage_type_identifier ty)
End

Definition source_type_matches_def:
  source_type_matches ty tid ⇔
    canonical_storage_identifier 0 0 tid =
      case ty of
        LocatedT MemoryLoc element => located_type_identifier MemoryLoc element
      | LocatedT CalldataLoc element => located_type_identifier CalldataLoc element
      | _ => storage_type_identifier ty
End

(* A parameter, return or local variable: an elementary value type in the
 * default location, a byte sequence in any location or a memory array,
 * agreeing with its typeIdentifier.
 *)
Definition variable_type_def:
  variable_type (v : src_variable) =
    case normalize_type_name v.var_type_name of
      SOME ty =>
        if byte_sequence_type ty ∨
           (v.var_location ≠ "default" ∧ case ty of ArrayT _ _ => T | _ => F) then
          case (if v.var_location = "memory" then SOME MemoryLoc
                else if v.var_location = "calldata" then SOME CalldataLoc
                else if v.var_location = "storage" then SOME StorageLoc else NONE) of
            SOME loc =>
              if located_value_type (LocatedT loc ty) ∧
                 (loc = StorageLoc ⇒ byte_sequence_type ty) ∧
                 source_type_matches (LocatedT loc ty) v.var_type_id then
                SOME (LocatedT loc ty) else NONE
          | NONE => NONE
        else if v.var_location = "default" ∧ source_type_matches ty v.var_type_id
        then SOME ty else NONE
    | NONE => NONE
End

(* Canonical ABI types for encoded arguments and decoded returns. Actual
 * encoded byte references can retain their source location. *)
Definition call_variable_type_def:
  call_variable_type v =
    OPTION_MAP (λty. case ty of
      LocatedT CalldataLoc element => LocatedT MemoryLoc element
    | _ => ty) (variable_type v)
End

(* Event declarations omit an explicit location; analyzed byte parameters
 * carry memory identifiers. *)
Definition event_variable_type_def:
  event_variable_type (v : src_variable) =
    case normalize_type_name v.var_type_name of
      SOME ty =>
        if byte_sequence_type ty then
          if v.var_location = "default" ∧
             source_type_matches (LocatedT MemoryLoc ty) v.var_type_id then
            SOME (LocatedT MemoryLoc ty) else NONE
        else variable_type v
    | NONE => NONE
End

(* Struct fields use storage pointer identifiers for arrays and structs,
 * unlike state declarations. Mappings retain their ordinary identifier. *)
Definition field_variable_type_def:
  field_variable_type (v : src_variable) =
    case normalize_type_name v.var_type_name of
      SOME ty =>
        let suffix = case ty of ArrayT _ _ => "_ptr" | StructT _ => "_ptr"
                            | BytesT => "_ptr" | StringT => "_ptr" | _ => "" in
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
  (type_name_ids (SrcEnumTypeName info _) = [info.node_id]) ∧
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
  (expr_ids (SrcConditional info c t f _) =
    info.node_id :: expr_ids c ++ expr_ids t ++ expr_ids f) ∧
  (expr_ids (SrcIndexAccess info b i _) =
    info.node_id :: expr_ids b ++ expr_ids i) ∧
  (expr_ids (SrcAssignment info _ l r _) =
    info.node_id :: expr_ids l ++ expr_ids r) ∧
  (expr_ids (SrcTupleExpression info cs _) =
    info.node_id :: component_ids cs) ∧
  (expr_ids (SrcFunctionCall info f args _ _) =
    info.node_id :: expr_ids f ++ exprs_ids args) ∧
  (expr_ids (SrcSuperCall info _ args _ _) = info.node_id :: exprs_ids args) ∧
  (expr_ids (SrcBuiltinCall info callee _ condition message _) =
    [info.node_id; callee.node_id] ++
    (case condition of NONE => [] | SOME c => expr_ids c) ++
    (case message of NONE => [] | SOME m => expr_ids m)) ∧
  (expr_ids (SrcTypeConversion info tn e _) =
    info.node_id :: type_name_ids tn ++ expr_ids e) ∧
  (expr_ids (SrcEnvironment info _ _) = [info.node_id]) ∧
  (expr_ids (SrcTypeMember info _ tn _) = info.node_id :: type_name_ids tn) ∧
  (expr_ids (SrcEnumValue info tn _ _) = info.node_id :: type_name_ids tn) ∧
  (expr_ids (SrcKeccak256 info callee e _) =
    info.node_id :: callee.node_id :: expr_ids e) ∧
  (expr_ids (SrcSelector info _ _) = [info.node_id]) ∧
  (expr_ids (SrcAbiEncode info callee _ args _) =
    info.node_id :: callee.node_id :: exprs_ids args) ∧
  (expr_ids (SrcExternalCall info _ _ operands _ _) =
    info.node_id :: exprs_ids operands) ∧
  (expr_ids (SrcNew info tn e _) =
    info.node_id :: type_name_ids tn ++ expr_ids e) ∧
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
  (stmt_ids (SrcEmit info _ args _) = info.node_id :: exprs_ids args) ∧
  (stmt_ids (SrcRevertError info _ args _) = info.node_id :: exprs_ids args) ∧
  (stmt_ids (SrcInlineAssembly info _ _) = [info.node_id]) ∧
  (stmt_ids (SrcPlaceholder info) = [info.node_id]) ∧
  (option_stmt_ids NONE = []) ∧
  (option_stmt_ids (SOME s) = stmt_ids s) ∧
  (stmts_ids [] = []) ∧
  (stmts_ids (s :: ss) = stmt_ids s ++ stmts_ids ss)
End

Definition function_ids_def:
  function_ids (f : src_function) =
    f.fn_info.node_id :: f.fn_parameters_id :: f.fn_returns_id ::
    FLAT (MAP variable_ids (f.fn_parameters ++ f.fn_returns)) ++
    FLAT (MAP (exprs_ids o SND) f.fn_modifiers) ++ stmt_ids f.fn_body
End

Definition contract_ids_def:
  contract_ids (c : src_contract) =
    c.contract_info.node_id ::
    FLAT (MAP (λs. s.struct_info.node_id ::
      FLAT (MAP variable_ids s.struct_members)) c.contract_structs) ++
    MAP FST c.contract_enums ++
    FLAT (MAP variable_ids c.contract_state_variables) ++
    FLAT (MAP variable_ids c.contract_immutables) ++
    FLAT (MAP (λ(_, e). expr_ids e) c.contract_initializers) ++
    FLAT (MAP (λ(v, e). variable_ids v ++ expr_ids e) c.contract_constants) ++
    FLAT (MAP (λ(_, _, es). exprs_ids es) c.contract_base_arguments) ++
    FLAT (MAP (λe. e.event_info.node_id ::
      FLAT (MAP (variable_ids o FST) e.event_parameters)) c.contract_events) ++
    FLAT (MAP (λm. m.modifier_info.node_id :: m.modifier_parameters_id ::
      FLAT (MAP variable_ids m.modifier_parameters) ++ stmt_ids m.modifier_body)
      c.contract_modifiers) ++
    FLAT (MAP function_ids c.contract_functions) ++
    FLAT (MAP function_ids c.contract_library_functions)
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

(* Functions callable by id, and those super calls run, by the declaration
 * they name; variables in lexical scope; the contract's state
 * variables, if the function may read them; the constants and immutables,
 * which any function may read; the innermost scope node; the
 * enclosing function's return list; whether in a loop body.
 *)
Datatype:
  import_env = <|
    functions : (num # src_function) list;
    supers : (num # src_function) list;
    structs : src_struct list;
    enums : (num # num) list;
    events : (num # src_event) list;
    variables : (num # sol_type) list;
    state : (num # sol_type) list;
    locations : (num # sol_type) list;
    constants : (num # sol_type) list;
    scope : num;
    returns_id : num;
    in_loop : bool;
    in_modifier : bool
  |>
End

(* The members of the struct with node id id. *)
Definition source_struct_members_def:
  source_struct_members structs id =
    ALOOKUP (MAP (λs. (s.struct_info.node_id, s.struct_members)) structs) id
End

Definition source_struct_field_def:
  source_struct_field structs id field =
    case source_struct_members structs id of
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

(* type(T).max and type(T).min of an integer type T. *)
Definition type_bound_def:
  type_bound member ty =
    case ty of
      UintT n =>
        if member = "max" then SOME (&(2 ** n) - 1 : int)
        else if member = "min" then SOME 0 else NONE
    | IntT n =>
        if member = "max" then SOME (&(2 ** (n - 1)) - 1)
        else if member = "min" then SOME (-&(2 ** (n - 1))) else NONE
    | _ => NONE
End

(* A call's parameter order, for named arguments: none, or a permutation of
 * the positions of its n arguments. The elaborator passes the arguments in
 * that order. *)
Definition argument_order_ok_def:
  argument_order_ok (order : num list) n ⇔
    order = [] ∨
    (LENGTH order = n ∧ ALL_DISTINCT order ∧ EVERY (λi. i < n) order)
End

(* The decoded type of a checked expression. *)
(* An argument abi.encode* takes: a scalar or a byte sequence in any
 * location, or a literal; an integer literal only when not packed. *)
Definition abi_argument_type_def:
  abi_argument_type packed t ⇔
    case t of
      SrcType ty =>
        is_stored_scalar_type ty ∨ byte_sequence_type ty ∨
        (case ty of LocatedT _ element => byte_sequence_type element | _ => F)
    | SrcByteLiteral => T
    | SrcRational _ d => ¬packed ∧ d = 1
    | _ => F
End

Definition check_expr_def:
  (check_expr (env : import_env) (SrcIdentifier _ _ x tid) =
    case ALOOKUP (env.variables ++ env.state ++ env.constants) x of
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
    | (SOME (SrcType BytesT), SOME index_type) =>
        if tid = "t_bytes1" ∧
           (case index_type of SrcType (UintT _) => T | SrcRational _ _ => T | _ => F)
        then SOME (SrcType (FixedBytesT 1)) else NONE
    | (SOME (SrcType (LocatedT loc BytesT)), SOME index_type) =>
        if tid = "t_bytes1" ∧
           (case index_type of
              SrcType (UintT _) => T
            | SrcRational i d => 0 ≤ i ∧ d = 1
            | _ => F)
        then SOME (SrcType (FixedBytesT 1)) else NONE
    | (SOME (SrcType (LocatedT loc (ArrayT element _))), SOME index_type) =>
        if loc ≠ StorageLoc ∧ source_type_matches (element_type loc element) tid ∧
           (case index_type of
              SrcType (UintT _) => T
            | SrcRational i d => 0 ≤ i ∧ d = 1
            | _ => F)
        then SOME (SrcType (element_type loc element)) else NONE
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
      SOME (SrcType BytesT) =>
        if tid = "t_uint256" then SOME (SrcType (UintT 256)) else NONE
    | SOME (SrcType (LocatedT loc BytesT)) =>
        if tid = "t_uint256" then SOME (SrcType (UintT 256)) else NONE
    | SOME (SrcType (ArrayT _ _)) =>
        if tid = "t_uint256" then SOME (SrcType (UintT 256)) else NONE
    | SOME (SrcType (LocatedT loc (ArrayT _ _))) =>
        if loc ≠ StorageLoc ∧ tid = "t_uint256" then SOME (SrcType (UintT 256)) else NONE
    | _ => NONE) ∧
  (check_expr env (SrcArrayMember _ _ _ _) = NONE) ∧
  (check_expr env (SrcLiteral _ kind value tid) =
    if kind = "number" then
      case decode_type_identifier tid of
        SOME (SrcRational n d) => SOME (SrcRational n d)
      | _ => NONE
    else if (kind = "string" ∨ kind = "unicodeString" ∨ kind = "hexString") ∧
            isPREFIX "t_stringliteral_" tid then SOME SrcByteLiteral
    else if kind = "bool" ∧ (value = "true" ∨ value = "false") ∧
            tid = "t_bool"
    then SOME (SrcType BoolT)
    else NONE) ∧
  (check_expr env (SrcUnaryOperation _ op _ e tid) =
    if unary_operator_ok op ∧ IS_SOME (check_expr env e) then
      case decode_type_identifier tid of
        SOME (SrcType ty) => SOME (SrcType ty)
      | SOME (SrcRational i d) => if d = 1 then SOME (SrcRational i d) else NONE
      | _ => NONE
    else NONE) ∧
  (check_expr env (SrcBinaryOperation _ op l r common tid) =
    if binary_operator_ok op ∧ IS_SOME (check_expr env l) ∧
       IS_SOME (check_expr env r)
    then
      case (decode_type_identifier common, decode_type_identifier tid) of
        (SOME (SrcType _), SOME (SrcType ty)) => SOME (SrcType ty)
      | (_, SOME (SrcRational i d)) => if d = 1 then SOME (SrcRational i d) else NONE
      | _ => NONE
    else NONE) ∧
  (check_expr env (SrcConditional _ c t f tid) =
    case (check_expr env c, decode_type_identifier tid) of
      (SOME (SrcType BoolT), SOME (SrcType ty)) =>
        (* a value or a memory reference, which the result local can hold *)
        if (case ty of LocatedT loc _ => loc = MemoryLoc | _ => is_stored_scalar_type ty) ∧
           IS_SOME (check_expr env t) ∧ IS_SOME (check_expr env f)
        then SOME (SrcType ty) else NONE
    | _ => NONE) ∧
  (check_expr env (SrcAssignment _ op l r tid) =
    if assignment_operator_ok op ∧ IS_SOME (check_expr env l) ∧
       IS_SOME (check_expr env r)
    then decode_type_identifier tid
    else NONE) ∧
  (check_expr env (SrcTupleExpression _ cs tid) =
    if check_components env cs then decode_type_identifier tid else NONE) ∧
  (check_expr env (SrcFunctionCall _ (SrcArrayMember _ member root_expr _) args order tid) =
    if order ≠ [] then NONE else
    case check_expr env root_expr of
      SOME (SrcType (ArrayT element NONE)) =>
        if ¬(case element of EnumT _ => T | _ => elementary_storage_type_ok element)
        then NONE else
        if member = "push" ∧ args = [] ∧ source_type_matches element tid then
          SOME (SrcType element)
        else if tid = "t_tuple$__$" ∧ check_exprs env args ∧
                ((member = "push" ∧ LENGTH args = 1) ∨
                 (member = "pop" ∧ args = []))
        then SOME (SrcTupleType []) else NONE
    | _ => NONE) ∧
  (check_expr env (SrcFunctionCall _ (SrcIdentifier _ _ f _) args order tid) =
    case ALOOKUP env.functions f of
      SOME callee =>
        (case (all_some (MAP variable_type callee.fn_returns),
               decode_type_identifier tid) of
           (SOME tys, SOME vt) =>
             if LENGTH args = LENGTH callee.fn_parameters ∧
                argument_order_ok order (LENGTH args) ∧
                callee.fn_visibility ≠ "external" ∧ check_exprs env args ∧
                vt = call_value_type tys
             then SOME vt else NONE
         | _ => NONE)
    | NONE => NONE) ∧
  (check_expr env (SrcFunctionCall _ _ _ _ _) = NONE) ∧
  (check_expr env (SrcSuperCall _ r args order tid) =
    case ALOOKUP env.supers r of
      SOME callee =>
        (case (all_some (MAP variable_type callee.fn_returns),
               decode_type_identifier tid) of
           (SOME tys, SOME vt) =>
             if LENGTH args = LENGTH callee.fn_parameters ∧
                argument_order_ok order (LENGTH args) ∧
                callee.fn_visibility ≠ "external" ∧ check_exprs env args ∧
                vt = call_value_type tys
             then SOME vt else NONE
         | _ => NONE)
    | NONE => NONE) ∧
  (check_expr env (SrcBuiltinCall _ _ builtin condition message tid) =
    if builtin_shape builtin condition message ∧ tid = "t_tuple$__$" ∧
       (case condition of NONE => T
        | SOME c => check_expr env c = SOME (SrcType BoolT))
    then SOME (SrcTupleType []) else NONE) ∧
  (check_expr env (SrcTypeConversion _ tn e tid) =
    case normalize_type_name tn of
      SOME ty =>
        if ¬IS_SOME (check_expr env e) then NONE else
        (case decode_type_identifier tid of
          SOME (SrcType result) =>
            if result = ty ∨ (byte_sequence_type ty ∧
                (case result of LocatedT _ element => ty = element | _ => F)) then
              SOME (SrcType result) else NONE
        | _ => NONE)
    | NONE => NONE) ∧
  (check_expr env (SrcEnvironment _ f tid) =
    if source_type_matches (environment_type f) tid
    then SOME (SrcType (environment_type f)) else NONE) ∧
  (check_expr env (SrcEnumValue _ tn index tid) =
    case normalize_type_name tn of
      SOME (EnumT id) =>
        (case ALOOKUP (MAP (λ(n, members). (AstId n, members)) env.enums) id of
           SOME members =>
             if index < members ∧ source_type_matches (EnumT id) tid
             then SOME (SrcType (EnumT id)) else NONE
         | NONE => NONE)
    | _ => NONE) ∧
  (* keccak256 takes bytes memory; a literal, or bytes in another location
     (a state variable's is unlocated), converts to it as an argument would. *)
  (check_expr env (SrcKeccak256 _ _ e tid) =
    if source_type_matches (FixedBytesT 32) tid ∧
       (case check_expr env e of
          SOME SrcByteLiteral => T
        | SOME (SrcType BytesT) => T
        | SOME (SrcType (LocatedT _ BytesT)) => T
        | _ => F)
    then SOME (SrcType (FixedBytesT 32)) else NONE) ∧
  (* f.selector, E.selector: the selector the compiler records on the
     declaration, bytes4 or (for an event) bytes32. *)
  (check_expr env (SrcSelector _ bs tid) =
    if (LENGTH bs = 4 ∨ LENGTH bs = 32) ∧
       source_type_matches (FixedBytesT (LENGTH bs)) tid
    then SOME (SrcType (FixedBytesT (LENGTH bs))) else NONE) ∧
  (check_expr env (SrcTypeMember _ member tn tid) =
    case normalize_type_name tn of
      SOME ty =>
        if IS_SOME (type_bound member ty) ∧ source_type_matches ty tid
        then SOME (SrcType ty) else NONE
    | NONE => NONE) ∧
  (* Value only for a payable callee, as the compiler requires; elaboration
     converts the target to an address. *)
  (check_expr env (SrcExternalCall _ callee with_value operands order tid) =
    case (all_some (MAP call_variable_type callee.ext_parameters),
          all_some (MAP call_variable_type callee.ext_returns),
          decode_type_identifier tid) of
      (SOME params, SOME rets, SOME vt) =>
        if MEM callee.ext_mutability ["pure"; "view"; "nonpayable"; "payable"] ∧
           (with_value ⇒ callee.ext_mutability = "payable") ∧
           LENGTH operands = LENGTH params + (if with_value then 2 else 1) ∧
           argument_order_ok order (LENGTH params) ∧
           check_exprs env operands ∧ vt = call_value_type rets ∧
           (* calls returning enums are not supported yet *)
           EVERY (λty. case ty of EnumT _ => F | _ => T) rets
        then SOME vt else NONE
    | _ => NONE) ∧
  (* new T(n) of a byte sequence or dynamic memory array type. *)
  (check_expr env (SrcNew _ tn e tid) =
    case (normalize_type_name tn, check_expr env e) of
      (SOME ty, SOME length_type) =>
        if (byte_sequence_type ty ∨
            (memory_object_type ty ∧ case ty of ArrayT _ NONE => T | _ => F)) ∧
           (case length_type of
              SrcType (UintT _) => T
            | SrcRational i d => 0 ≤ i ∧ d = 1
            | _ => F) ∧
           source_type_matches (LocatedT MemoryLoc ty) tid
        then SOME (SrcType (LocatedT MemoryLoc ty)) else NONE
    | _ => NONE) ∧
  (* abi.encode* to memory bytes, or string.concat to a memory string; a
     selector given as an argument is a bytes4, and the other arguments are
     scalars or byte sequences (integer literals only unpacked, as the
     compiler requires). *)
  (check_expr env (SrcAbiEncode _ _ form args tid) =
    let ty = LocatedT MemoryLoc (if form = AbiStringConcat then StringT else BytesT) in
    if source_type_matches ty tid ∧
       (case (form, args) of
          (AbiWithSelector, s :: rest) =>
            check_expr env s = SOME (SrcType (FixedBytesT 4)) ∧
            check_abi_args env F rest
        | (AbiWithSelector, []) => F
        | (AbiPacked, _) => check_abi_args env T args
        | (AbiStringConcat, _) => check_abi_args env T args
        | _ => check_abi_args env F args)
    then SOME (SrcType ty) else NONE) ∧
  (check_components env [] ⇔ T) ∧
  (check_components env (NONE :: cs) ⇔ check_components env cs) ∧
  (check_components env (SOME e :: cs) ⇔
    IS_SOME (check_expr env e) ∧ check_components env cs) ∧
  (check_exprs env [] ⇔ T) ∧
  (check_exprs env (e :: es) ⇔
    IS_SOME (check_expr env e) ∧ check_exprs env es) ∧
  (check_abi_args env packed [] ⇔ T) ∧
  (check_abi_args env packed (e :: es) ⇔
    (case check_expr env e of
       SOME t => abi_argument_type packed t
     | NONE => F) ∧
    check_abi_args env packed es)
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
(* A local is checked for its type by the core program's check; here only
 * that each name resolves: a value to a local, a location to a state
 * variable, which a pure function can also name.
 *)
Definition check_assembly_reference_def:
  (check_assembly_reference env (SrcAssemblyValue x) ⇔
    IS_SOME (ALOOKUP env.variables x)) ∧
  (check_assembly_reference env (SrcAssemblySlot x) ⇔
    IS_SOME (ALOOKUP env.locations x)) ∧
  (check_assembly_reference env (SrcAssemblyOffset x) ⇔
    IS_SOME (ALOOKUP env.locations x))
End

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
  (check_stmt env (SrcEmit _ ev args order) ⇔
    case ALOOKUP env.events ev of
      SOME e => LENGTH args = LENGTH e.event_parameters ∧
                argument_order_ok order (LENGTH args) ∧ check_exprs env args
    | NONE => F) ∧
  (check_stmt env (SrcPlaceholder _) ⇔ env.in_modifier) ∧
  (check_stmt env (SrcRevertError _ err args order) ⇔
    LENGTH err.error_selector = 4 ∧
    case all_some (MAP variable_type err.error_parameters) of
      SOME params =>
        EVERY is_elementary_type params ∧ LENGTH args = LENGTH params ∧
        argument_order_ok order (LENGTH args) ∧ check_exprs env args
    | NONE => F) ∧
  (check_stmt env (SrcInlineAssembly _ _ refs) ⇔
    ALL_DISTINCT (MAP FST refs) ∧
    EVERY (check_assembly_reference env) (MAP SND refs))
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
    if ¬MEM v.var_scope bases then NONE else
    case normalize_type_name v.var_type_name of
      SOME ty =>
        if byte_sequence_type ty then
          if v.var_location = "default" ∧ source_type_matches ty v.var_type_id then
            SOME (v.var_info.node_id, ty) else NONE
        else scoped_variable v.var_scope v
    | NONE => NONE
End

(* A constant, declared by one of the given contracts or libraries, at the
 * type its references have: byte sequences are in memory. *)
Definition constant_variable_def:
  constant_variable bases (v : src_variable) =
    if ¬MEM v.var_scope bases ∨ v.var_location ≠ "default" then NONE else
    case normalize_type_name v.var_type_name of
      SOME ty =>
        let ty' = if byte_sequence_type ty then LocatedT MemoryLoc ty else ty in
        if (is_elementary_type ty ∨ byte_sequence_type ty) ∧
           source_type_matches ty' v.var_type_id
        then SOME (v.var_info.node_id, ty') else NONE
    | NONE => NONE
End

Definition constant_table_def:
  constant_table (c : src_contract) =
    all_some (MAP (constant_variable (c.contract_bases ++ c.contract_libraries) o FST)
                c.contract_constants)
End

(* An immutable, declared by one of the contract's bases, of elementary type. *)
Definition immutable_variable_def:
  immutable_variable bases (v : src_variable) =
    case state_variable bases v of
      SOME (x, ty) => if is_elementary_type ty then SOME (x, ty) else NONE
    | NONE => NONE
End

Definition immutable_table_def:
  immutable_table (c : src_contract) =
    all_some (MAP (immutable_variable c.contract_bases) c.contract_immutables)
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

(* The bases after x in the linearization, where a super call from a
 * function of x looks. *)
Definition later_bases_def:
  (later_bases x [] = []) ∧
  (later_bases x (y :: ys) = if x = y then ys else later_bases x ys)
End

(* The function a super call naming d runs: the first function, along the
 * bases given, with d's name and parameter types (the compiler's lookup,
 * from the deployed contract's linearization). *)
Definition super_target_def:
  (super_target fs (d : src_function) [] = NONE) ∧
  (super_target fs d (x :: xs) =
    case FILTER (λ(g : src_function).
                   g.fn_scope = x ∧ g.fn_kind = "function" ∧
                   g.fn_name = d.fn_name ∧
                   MAP variable_type g.fn_parameters =
                   MAP variable_type d.fn_parameters) fs of
      g :: _ => SOME g
    | [] => super_target fs d xs)
End

(* The functions the super calls of f run, by the declaration each names. *)
Definition super_table_def:
  super_table fs bases (f : src_function) =
    all_some (MAP (λr.
      case FILTER (λ(d : src_function). d.fn_info.node_id = r) fs of
        d :: _ => OPTION_MAP (λg. (r, g))
                    (super_target fs d (later_bases f.fn_scope bases))
      | [] => NONE) f.fn_super_calls)
End

Definition super_targets_def:
  (super_targets fs bases [] = []) ∧
  (super_targets fs bases (f :: rs) =
    (case super_table fs bases f of SOME t => MAP SND t | NONE => []) ++
    super_targets fs bases rs)
End

Definition add_functions_def:
  (add_functions rs [] = rs) ∧
  (add_functions rs ((g : src_function) :: gs) =
    add_functions
      (if MEM g.fn_info.node_id (MAP (λ(f : src_function). f.fn_info.node_id) rs)
       then rs else rs ++ [g]) gs)
End

(* The functions calls reach: the live ones and those super calls reach from
 * them. Each round adds a function or ends, so as many rounds as there are
 * functions suffice. *)
Definition reached_functions_def:
  (reached_functions fs bases 0 rs = rs) ∧
  (reached_functions fs bases (SUC k) rs =
    let rs' = add_functions rs (super_targets fs bases rs) in
    if LENGTH rs' = LENGTH rs then rs else reached_functions fs bases k rs')
End

(* The functions checked and elaborated: the live ones, then those only super
 * calls reach, which the dispatch table does not list. *)
Definition checked_functions_def:
  checked_functions fs bases =
    reached_functions fs bases (LENGTH fs) (live_functions fs)
End

(* The constructor a base declares, if any. *)
Definition contract_constructor_def:
  (contract_constructor x [] = NONE) ∧
  (contract_constructor x ((f : src_function) :: fs) =
    if f.fn_kind = "constructor" ∧ f.fn_scope = x then SOME f
    else contract_constructor x fs)
End

(* What a getter returns of a struct member: nothing for a mapping or an
 * array other than a byte sequence, as the compiler's getters skip them, or
 * the member, which must be a value or a byte sequence.
 *)
Definition getter_member_def:
  getter_member (v : src_variable) =
    case field_variable_type v of
      SOME (MappingT _ _) => SOME []
    | SOME (ArrayT _ _) => SOME []
    | SOME ty =>
        if is_stored_scalar_type ty ∨ byte_sequence_type ty
        then SOME [(SOME v.var_info.node_id, ty)] else NONE
    | NONE => NONE
End

(* What a getter returns of the value of type ty it reaches: the value, or a
 * struct's returned members in order, each with its member id. *)
Definition getter_results_def:
  getter_results structs ty =
    case ty of
      StructT (AstId id) =>
        (case source_struct_members structs id of
           SOME fields =>
             (case all_some (MAP getter_member fields) of
                SOME ms => if FLAT ms = [] then NONE else SOME (FLAT ms)
              | NONE => NONE)
         | NONE => NONE)
    | _ => if is_stored_scalar_type ty ∨ byte_sequence_type ty then SOME [(NONE, ty)]
           else NONE
End

(* The parameter types and the results of the getter of a public state
 * variable of type ty: a key for each mapping and an index for each array
 * along its type, down to a value, a byte sequence or a struct.
 *)
Definition getter_shape_def:
  getter_shape structs ty =
    case ty of
      MappingT key value =>
        if is_elementary_type key then
          OPTION_MAP (λ(ps, r). (key :: ps, r)) (getter_shape structs value)
        else NONE
    | ArrayT element _ =>
        OPTION_MAP (λ(ps, r). (UintT 256 :: ps, r)) (getter_shape structs element)
    | _ => OPTION_MAP (λrs. ([], rs)) (getter_results structs ty)
End

(* The variables the base constructor arguments a base gives see: the
 * parameters of its constructor. *)
Definition constructor_parameters_def:
  constructor_parameters x fs =
    case contract_constructor x fs of
      NONE => SOME []
    | SOME f => all_some (MAP (scoped_variable f.fn_info.node_id) f.fn_parameters)
End

(* A modifier invocation: arguments that see the function's variables, and
 * the modifier's body, which sees its parameters and the function's state
 * variables. A return in it has no return parameters (id 0). *)
Definition check_modifier_def:
  check_modifier modifiers env (x, args) ⇔
    case ALOOKUP modifiers x of
      NONE => F
    | SOME m =>
        LENGTH args = LENGTH m.modifier_parameters ∧ check_exprs env args ∧
        case (all_some (MAP (scoped_variable x) m.modifier_parameters),
              m.modifier_body) of
          (SOME variables, SrcBlock info ss) =>
            IS_SOME (check_stmts
              (env with <| supers := []; variables := variables;
                           scope := info.node_id; returns_id := 0;
                           in_modifier := T |>) ss)
        | _ => F
End

(* A pure function sees no state variables. Whether a view function writes
 * one is the compiler's check. Modifier arguments see the parameters but not
 * the return variables: the compiler's IR passes each modifier its own copies
 * of the return variables, which the elaborator does not model.
 *)
Definition check_function_def:
  check_function structs enums events functions fs modifiers state constants
                 bases (f : src_function) ⇔
    MEM f.fn_scope bases ∧
    (f.fn_kind = "function" ∨ f.fn_kind = "receive" ∨ f.fn_kind = "fallback" ∨
     f.fn_kind = "constructor") ∧
    (f.fn_mutability = "pure" ∨ f.fn_mutability = "view" ∨
     f.fn_mutability = "nonpayable" ∨ f.fn_mutability = "payable") ∧
    case (all_some (MAP (scoped_variable f.fn_info.node_id) f.fn_parameters),
          all_some (MAP (scoped_variable f.fn_info.node_id) f.fn_returns),
          f.fn_body) of
      (SOME ps, SOME rs, SrcBlock info ss) =>
        (case super_table fs bases f of
           NONE => F
         | SOME supers =>
        let env = <| functions := functions; supers := supers;
                     structs := structs; enums := enums; events := events;
                     variables := ps ++ rs;
                     state := if f.fn_mutability = "pure" then [] else state;
                     locations := state; constants := constants;
                     scope := info.node_id; returns_id := f.fn_returns_id;
                     in_loop := F; in_modifier := F |> in
        EVERY (check_modifier modifiers (env with variables := ps))
          f.fn_modifiers ∧
        IS_SOME (check_stmts env ss))
    | _ => F
End

(* The layout has an entry for each state variable, in order. *)
Definition storage_layout_ok_def:
  (storage_layout_ok fields [] [] ⇔ T) ∧
  (storage_layout_ok fields ((v : src_variable) :: vs) (e :: es) ⇔
     e.storage_id = v.var_info.node_id ∧
     (case (if fields then field_variable_type v
            else OPTION_MAP SND (state_variable [v.var_scope] v)) of
        SOME ty => canonical_storage_identifier 0 0 e.storage_type_id = storage_layout_identifier ty
      | NONE => F) ∧
     e.storage_slot < 2 ** 256 ∧ storage_layout_ok fields vs es) ∧
  (storage_layout_ok _ _ _ ⇔ F)
End

Definition check_struct_def:
  check_struct sources bases (s : src_struct) ⇔
    (MEM s.struct_scope bases ∨ MEM s.struct_scope sources) ∧
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
    EVERY (λp. (FST p).var_scope = e.event_info.node_id ∧
                  IS_SOME (event_variable_type (FST p)))
      e.event_parameters
End

(* Initializers and base constructor arguments see the state variables and
 * constants and call functions; base constructor arguments also see the
 * parameters of the constructor of the base giving them. *)
Definition initializer_env_def:
  initializer_env (c : src_contract) state constants =
    <| functions := call_table (c.contract_functions ++
                                c.contract_library_functions);
       supers := [];
       structs := c.contract_structs;
       enums := c.contract_enums;
       events := MAP (λe. (e.event_info.node_id, e)) c.contract_events;
       variables := []; state := state; locations := state;
       constants := constants; scope := c.contract_info.node_id;
       returns_id := c.contract_info.node_id; in_loop := F;
       in_modifier := F |>
End

(* A constant's value sees only the other constants: the compiler requires
 * it to be a compile-time constant. *)
Definition constant_env_def:
  constant_env (c : src_contract) constants =
    initializer_env c [] constants with functions := []
End

Definition check_contract_def:
  check_contract unit_id sources (c : src_contract) ⇔
    c.contract_scope = unit_id ∧
    (case c.contract_bases of x :: _ => x = c.contract_info.node_id | [] => F) ∧
    ALL_DISTINCT (c.contract_bases ++ c.contract_libraries) ∧
    EVERY (check_struct sources c.contract_bases) c.contract_structs ∧
    EVERY (λ(_, members). 0 < members ∧ members ≤ 256) c.contract_enums ∧
    EVERY check_event c.contract_events ∧
    storage_layout_ok F c.contract_state_variables c.contract_storage ∧
    case (all_some (MAP (state_variable c.contract_bases)
                      c.contract_state_variables), constant_table c,
          immutable_table c) of
      (SOME state, SOME constants, SOME immutables) =>
        EVERY (check_function c.contract_structs c.contract_enums
                 (MAP (λe. (e.event_info.node_id, e)) c.contract_events)
                 (call_table (c.contract_functions ++
                              c.contract_library_functions))
                 c.contract_functions
                 (MAP (λm. (m.modifier_info.node_id, m)) c.contract_modifiers)
                 state (constants ++ immutables) c.contract_bases)
          (checked_functions c.contract_functions c.contract_bases) ∧
        (* library functions see no state *)
        EVERY (λf. f.fn_kind = "function" ∧
                   (f.fn_visibility = "internal" ∨ f.fn_visibility = "private") ∧
                   check_function c.contract_structs c.contract_enums
                     (MAP (λe. (e.event_info.node_id, e)) c.contract_events)
                     (call_table (c.contract_functions ++
                                  c.contract_library_functions))
                     c.contract_library_functions
                     (MAP (λm. (m.modifier_info.node_id, m)) c.contract_modifiers)
                     [] constants c.contract_libraries f)
          c.contract_library_functions ∧
        EVERY (λ(x, e). IS_SOME (ALOOKUP (state ++ immutables) x) ∧
                        IS_SOME (check_expr (initializer_env c state
                                               (constants ++ immutables)) e))
          c.contract_initializers ∧
        EVERY (λ(_, e). IS_SOME (check_expr (constant_env c constants) e))
          c.contract_constants ∧
        ALL_DISTINCT (MAP FST c.contract_getters) ∧
        EVERY (λ(x, selector).
                 LENGTH selector = 4 ∧
                 case ALOOKUP (state ++ immutables) x of
                   SOME ty => IS_SOME (getter_shape c.contract_structs ty)
                 | NONE => IS_SOME (ALOOKUP constants x))
          c.contract_getters ∧
        EVERY (λ(x, b, args).
                 case constructor_parameters x c.contract_functions of
                   SOME ps => check_exprs (initializer_env c state
                                             (constants ++ immutables) with
                                             variables := ps) args
                 | NONE => F)
          c.contract_base_arguments
    | _ => F
End

Definition valid_src_unit_def:
  valid_src_unit (u : src_unit) ⇔
    EVERY (λc. ALL_DISTINCT (u.unit_info.node_id :: contract_ids c))
      u.unit_contracts ∧
    MEM u.unit_info.node_id u.unit_sources ∧
    EVERY (check_contract u.unit_info.node_id u.unit_sources) u.unit_contracts
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
val () = cv_auto_trans located_type_identifier_def;
val () = cv_auto_trans source_type_matches_def;
val () = cv_auto_trans storage_layout_identifier_def;
val () = cv_auto_trans variable_type_def;
val () = cv_auto_trans call_variable_type_def;
val () = cv_auto_trans event_variable_type_def;
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

val () = cv_auto_trans source_struct_members_def;
val () = cv_auto_trans source_struct_field_def;
val () = cv_auto_trans argument_order_ok_def;
val () = cv_auto_trans literal_message_def;
val () = cv_auto_trans builtin_shape_def;
val () = cv_auto_trans type_bound_def;

val check_expr_pre_def = cv_auto_trans_pre_rec
  "check_expr_pre check_components_pre check_exprs_pre check_abi_args_pre" check_expr_def (
  WF_REL_TAC ‘measure (λx. case x of
                 INL (env, e) => cv_size e
               | INR (INL (env, cs)) => cv_size cs
               | INR (INR (INL (env, es))) => cv_size es
               | INR (INR (INR (env, packed, es))) => cv_size es)’ >>
  cv_termination_tac
);

Theorem check_expr_pre[cv_pre,local]:
  (∀env e. check_expr_pre env e) ∧ (∀env cs. check_components_pre env cs) ∧
  (∀env es. check_exprs_pre env es) ∧ (∀env packed es. check_abi_args_pre env packed es)
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
val () = cv_auto_trans check_assembly_reference_def;

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
val () = cv_auto_trans constant_variable_def;
val () = cv_auto_trans constant_table_def;
val () = cv_auto_trans immutable_variable_def;
val () = cv_auto_trans immutable_table_def;
val () = cv_auto_trans getter_member_def;
val () = cv_auto_trans getter_results_def;
val () = cv_auto_trans getter_shape_def;
val () = cv_auto_trans call_table_def;
val () = cv_auto_trans contract_constructor_def;
val () = cv_auto_trans constructor_parameters_def;
val () = cv_auto_trans live_functions_def;
val () = cv_auto_trans later_bases_def;
val () = cv_auto_trans super_target_def;
val () = cv_auto_trans super_table_def;
val () = cv_auto_trans super_targets_def;
val () = cv_auto_trans add_functions_def;
val () = cv_auto_trans reached_functions_def;
val () = cv_auto_trans checked_functions_def;
val () = cv_auto_trans storage_layout_ok_def;
val () = cv_auto_trans check_modifier_def;
val () = cv_auto_trans check_function_def;
val () = cv_auto_trans check_struct_def;
val () = cv_auto_trans check_event_def;
val () = cv_auto_trans initializer_env_def;
val () = cv_auto_trans constant_env_def;
val () = cv_auto_trans check_contract_def;
val () = cv_auto_trans valid_src_unit_def;
