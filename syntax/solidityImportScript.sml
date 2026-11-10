(* Normalized source AST: the admitted subset of the pinned compiler's
 * analyzed Standard JSON AST, between the raw compiler output and the core.
 * docs/frontend-boundary.md lists the admitted subset.
 *
 * solidityImportLib builds these terms from a compiler artifact and fails
 * closed: an unknown nodeType, a missing required field, or a feature outside
 * the subset raises ImportError. Semantic nodes keep their compiler id and
 * source range; declarations are referred to by id, and names are diagnostic
 * only. Type annotations are kept as the compiler's encoded typeIdentifier
 * and decoded here, never from the display typeString.
 *
 * A unit holds its deployable contracts: those neither abstract, nor an
 * interface, nor a base of another contract of the unit. Each is flattened
 * along its linearization (src_contract); its bases, the functions it calls
 * and the structs it uses may come from any source unit of the compilation
 * (unit_sources), since the AST refers to declarations by id across files.
 * The internal functions, modifiers and constants of libraries it uses come
 * with it.
 *
 * A function whose body, modifiers or header fall outside the subset is kept
 * with the reasons (fn_unsupported, one line per unsupported node), and with
 * placeholders for the nodes the importer could not represent: dropping it
 * would let a lookup or a super call fall through to a function it overrides,
 * and its selector to the fallback. Calls of unsupported functions resolve
 * to nothing (function_table), and elaboration skips them.
 *
 * valid_src_unit checks what holds for the unit as a whole: distinct ids,
 * declarations, function and modifier headers, storage layout, state
 * variables, constants, getters and bases. Function bodies, and the
 * expressions of initializers, base-constructor arguments and constant
 * values, are checked where solidityElaborate elaborates them.
 * unit_rejections lists the checks a unit fails, with the node each is about.
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

(* The compiler's kinds and operators, decoded once by the importer. *)
Datatype:
  src_function_kind = FunctionKind | ConstructorKind | ReceiveKind | FallbackKind
End

Datatype:
  src_visibility
  = PublicVisibility | ExternalVisibility | InternalVisibility | PrivateVisibility
End

Datatype:
  literal_kind
  = NumberLiteral | BoolLiteral | StringLiteral | UnicodeStringLiteral
  | HexStringLiteral
End

Datatype:
  src_unary_operator
  = SrcIncrement | SrcDecrement | SrcNegate | SrcNot | SrcBitNot | SrcDelete
End

Datatype:
  src_binary_operator
  = SrcAdd | SrcSub | SrcMul | SrcDiv | SrcMod | SrcExp | SrcShl | SrcShr
  | SrcBitAnd | SrcBitOr | SrcBitXor | SrcEq | SrcNe | SrcLt | SrcLe | SrcGt
  | SrcGe | SrcAnd | SrcOr
End

(* ElementaryTypeName: name and, for addresses, stateMutability. *)
Datatype:
  src_type_name = SrcElementaryTypeName node_info string (address_payability option)
                | SrcArrayTypeName node_info src_type_name num
                | SrcDynamicArrayTypeName node_info src_type_name
  | SrcMappingTypeName node_info src_type_name src_type_name
  | SrcStructTypeName node_info num string
  | SrcEnumTypeName node_info num
  | SrcUnsupportedTypeName node_info string
End

Datatype:
  src_variable = <|
    var_info : node_info;
    var_name : string;
    var_scope : num;
    var_type_name : src_type_name;
    var_type_id : string;
    var_location : data_location option
  |>
End

(* The last string of each expression is its typeIdentifier.
 * Identifier: name, referencedDeclaration.
 * Literal: kind, value.
 * UnaryOperation: operator, prefix, operand.
 * BinaryOperation: operator, operands, commonType.
 * Assignment: the operator of a compound assignment, left and right hand
 * sides.
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
 * Unsupported (and its type name and statement counterparts): a node the
 * importer can't represent, with the importer's line saying why and the
 * children it could import, so that elaboration rejects it and still reports
 * the blockers under and beside it.
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
    ext_mutability : state_mutability;
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
           | AbiCall (string list)
           | AbiStringConcat
End

(* A call option, {value: v} or {gas: g}, in a call's source order. *)
Datatype:
  call_option = ValueOption | GasOption
End

(* a.call, a.staticcall and a.delegatecall of an address. *)
Datatype:
  low_level_kind = LowLevelCall | LowLevelStaticCall | LowLevelDelegateCall
End

Datatype:
  src_expr
  = SrcIdentifier node_info string num string
  | SrcArrayLength node_info src_expr string
  | SrcMemberAccess node_info src_expr num string
  | SrcArrayMember node_info string src_expr string
  | SrcLiteral node_info literal_kind string string
  | SrcUnaryOperation node_info src_unary_operator bool src_expr string
  | SrcBinaryOperation node_info src_binary_operator src_expr src_expr string string
  | SrcConditional node_info src_expr src_expr src_expr string
  | SrcAssignment node_info (src_binary_operator option) src_expr src_expr string
  | SrcIndexAccess node_info src_expr src_expr string
  | SrcTupleExpression node_info (src_expr option list) string
  | SrcFunctionCall node_info src_expr (src_expr list) (num list) string
  | SrcSuperCall node_info num (src_expr list) (num list) string
  | SrcBaseCall node_info num (src_expr list) (num list) string
  | SrcBuiltinCall node_info node_info src_builtin (src_expr option)
      (src_expr option) string
  | SrcTypeConversion node_info src_type_name src_expr string
  | SrcEnvironment node_info environment_field string
  | SrcExternalCall node_info src_external (call_option list) (src_expr list)
      (num list) string
  | SrcTypeMember node_info string src_type_name string
  | SrcNew node_info src_type_name src_expr string
  | SrcEnumValue node_info src_type_name num string
  | SrcKeccak256 node_info node_info src_expr string
  | SrcModular node_info node_info core_operator (src_expr list) string
  | SrcAddressCodeLength node_info node_info src_expr string
  | SrcSelector node_info (byte list) string
  | SrcEcrecover node_info node_info (src_expr list) string
  | SrcAbiEncode node_info node_info abi_form (src_expr list) string
  | SrcAbiDecode node_info node_info src_expr (src_type_name list) string
  | SrcLowLevelCall node_info node_info low_level_kind (call_option list)
      (src_expr list) string
  | SrcUnsupportedExpr node_info string (src_expr list)
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
  | SrcTryStatement node_info src_expr
      node_info (src_variable list) src_stmt node_info src_variable src_stmt
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
  | SrcUnsupportedStmt node_info string (src_expr list) (src_stmt list)
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
 * declarations the body's super calls name. An unsupported function is one
 * the frontend could not model, with the reason: it keeps its place, so that
 * overrides and super calls resolve as the compiler resolves them, but it is
 * neither checked nor elaborated, and nothing may call it; the reason has a
 * line for each node the importer could not represent, which may be left in
 * the body, modifiers and header as placeholders.
 *)
Datatype:
  src_function = <|
    fn_info : node_info;
    fn_name : string;
    fn_scope : num;
    fn_kind : src_function_kind;
    fn_visibility : src_visibility;
    fn_mutability : state_mutability;
    fn_selector : byte list option;
    fn_base_functions : num list;
    fn_parameters_id : num;
    fn_parameters : src_variable list;
    (* Nominal compiler types, before runtime erasure, for super lookup. *)
    fn_nominal_parameters : string list;
    fn_returns_id : num;
    fn_returns : src_variable list;
    fn_modifiers : (num # src_expr list) list;
    fn_super_calls : num list;
    fn_static_calls : num list;
    fn_body : src_stmt;
    fn_unsupported : string option
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
    (* Static calls in initializers and inheritance specifiers. *)
    contract_static_calls : num list;
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
      SOME (AddressT _) => OPTION_MAP AddressT mutability
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
  (normalize_type_name (SrcUnsupportedTypeName _ _) = NONE) ∧
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
 * byte sequences retain their source string kind here, and integer literals
 * stand as uint256 (int256 when negative); elaboration coerces the literal
 * itself to its destination's type. *)
Definition tuple_component_def:
  tuple_component p =
    if 2 ≤ LENGTH p ∧ isPREFIX "_" p ∧ isPREFIX "_" (REVERSE p) then
      let tid = TAKE (LENGTH p - 2) (DROP 1 p) in
      if isPREFIX "t_stringliteral_" tid then SOME StringT
      else if isPREFIX "t_rational_" tid then
        case decode_rational (DROP 11 tid) of
          SOME (SrcRational i d) =>
            if d = 1 then SOME (if i < 0 then IntT 256 else UintT 256) else NONE
        | _ => NONE
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
  rw[tuple_component_def, AllCaseEqs()] >>
  gvs[valid_type_shape_def, solidityASTTheory.valid_int_width_def] >>
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
           (IS_SOME v.var_location ∧ case ty of ArrayT _ _ => T | _ => F) then
          case v.var_location of
            SOME loc =>
              if located_value_type (LocatedT loc ty) ∧
                 (loc = StorageLoc ⇒ byte_sequence_type ty) ∧
                 source_type_matches (LocatedT loc ty) v.var_type_id then
                SOME (LocatedT loc ty) else NONE
          | NONE => NONE
        else if v.var_location = NONE ∧ source_type_matches ty v.var_type_id
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
          if v.var_location = NONE ∧
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
        if v.var_location = NONE ∧
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

(* The type abi.decode gives a value it decodes as this type: the compiler
 * types a decoded address as address payable. *)
Definition decoded_type_def:
  (decoded_type (AddressT _) = AddressT PayableAddress) ∧
  (decoded_type ty = ty)
End

(* Ids *)

Definition type_name_ids_def:
  (type_name_ids (SrcElementaryTypeName info _ _) = [info.node_id]) ∧
  (type_name_ids (SrcArrayTypeName info element _) =
    info.node_id :: type_name_ids element) ∧
  (type_name_ids (SrcStructTypeName info _ _) = [info.node_id]) ∧
  (type_name_ids (SrcEnumTypeName info _) = [info.node_id]) ∧
  (type_name_ids (SrcUnsupportedTypeName info _) = [info.node_id]) ∧
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
  (expr_ids (SrcBaseCall info _ args _ _) = info.node_id :: exprs_ids args) ∧
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
  (expr_ids (SrcModular info callee _ args _) =
    info.node_id :: callee.node_id :: exprs_ids args) ∧
  (expr_ids (SrcAddressCodeLength info member e _) =
    info.node_id :: member.node_id :: expr_ids e) ∧
  (expr_ids (SrcSelector info _ _) = [info.node_id]) ∧
  (expr_ids (SrcEcrecover info callee args _) =
    info.node_id :: callee.node_id :: exprs_ids args) ∧
  (expr_ids (SrcAbiEncode info callee _ args _) =
    info.node_id :: callee.node_id :: exprs_ids args) ∧
  (expr_ids (SrcLowLevelCall info callee _ _ operands _) =
    info.node_id :: callee.node_id :: exprs_ids operands) ∧
  (expr_ids (SrcAbiDecode info callee e tns _) =
    info.node_id :: callee.node_id :: expr_ids e ++ FLAT (MAP type_name_ids tns)) ∧
  (expr_ids (SrcExternalCall info _ _ operands _ _) =
    info.node_id :: exprs_ids operands) ∧
  (expr_ids (SrcNew info tn e _) =
    info.node_id :: type_name_ids tn ++ expr_ids e) ∧
  (expr_ids (SrcUnsupportedExpr info _ es) = info.node_id :: exprs_ids es) ∧
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
  (stmt_ids (SrcTryStatement info call ok ps body err reason handler) =
    [info.node_id; ok.node_id; err.node_id] ++ expr_ids call ++
    FLAT (MAP variable_ids ps) ++ variable_ids reason ++
    stmt_ids body ++ stmt_ids handler) ∧
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
  (stmt_ids (SrcUnsupportedStmt info _ es ss) =
    info.node_id :: exprs_ids es ++ stmts_ids ss) ∧
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
    if kind ≠ NumberLiteral ∧ kind ≠ BoolLiteral ∧
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

(* The ABI type of a parameter of the function abi.encodeCall names, by its
 * type identifier: a scalar as itself; a byte sequence in any location as a
 * memory one, whose encoding does not depend on its location. *)
Definition abi_call_parameter_def:
  abi_call_parameter tid =
    case decode_type_identifier tid of
      SOME (SrcType ty) =>
        if is_stored_scalar_type ty then SOME ty else
        (case ty of
           LocatedT _ element =>
             if byte_sequence_type element
             then SOME (LocatedT MemoryLoc element) else NONE
         | _ => NONE)
    | _ => NONE
End

(* A parameter, return variable, state variable, or catch binding declared by
 * the node scope. *)
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
          if v.var_location = NONE ∧ source_type_matches ty v.var_type_id then
            SOME (v.var_info.node_id, ty) else NONE
        else scoped_variable v.var_scope v
    | NONE => NONE
End

(* A constant, declared by one of the given contracts or libraries, at the
 * type its references have: byte sequences are in memory. *)
Definition constant_variable_def:
  constant_variable bases (v : src_variable) =
    if ¬MEM v.var_scope bases ∨ IS_SOME v.var_location then NONE else
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

(* The call table of what may be called: without the entries of a key whose
 * function is unsupported, all of them, so that a lookup never falls through
 * to a function that one overrides. *)
Definition function_table_def:
  function_table fs =
    let table = call_table fs in
    FILTER (λ(x, _). case ALOOKUP table x of
                       SOME (g : src_function) => g.fn_unsupported = NONE
                     | NONE => F) table
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
                   g.fn_scope = x ∧ g.fn_kind = FunctionKind ∧
                   g.fn_name = d.fn_name ∧
                   g.fn_nominal_parameters = d.fn_nominal_parameters ∧
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

(* The functions super calls reach from rs; an unsupported function never
 * runs, so its super calls reach nothing. *)
Definition super_targets_def:
  (super_targets fs bases [] = []) ∧
  (super_targets fs bases (f :: rs) =
    (if f.fn_unsupported ≠ NONE then [] else
     case super_table fs bases f of SOME t => MAP SND t | NONE => []) ++
    super_targets fs bases rs)
End

Definition add_functions_def:
  (add_functions rs [] = rs) ∧
  (add_functions rs ((g : src_function) :: gs) =
    add_functions
      (if MEM g.fn_info.node_id (MAP (λ(f : src_function). f.fn_info.node_id) rs)
       then rs else rs ++ [g]) gs)
End

(* Statically named base implementations, without virtual redirection. *)
Definition static_targets_def:
  (static_targets fs [] = []) ∧
  (static_targets fs ((f : src_function) :: rs) =
    (if f.fn_unsupported ≠ NONE then [] else
     FILTER (λ(g : src_function). MEM g.fn_info.node_id f.fn_static_calls) fs) ++
    static_targets fs rs)
End

(* The functions calls reach: the live ones and those super calls reach from
 * them. Each round adds a function or ends, so as many rounds as there are
 * functions suffice. *)
Definition reached_functions_def:
  (reached_functions fs bases 0 rs = rs) ∧
  (reached_functions fs bases (SUC k) rs =
    let rs' = add_functions rs
                (super_targets fs bases rs ++ static_targets fs rs) in
    if LENGTH rs' = LENGTH rs then rs else reached_functions fs bases k rs')
End

(* The live functions and implementations reached by super or static calls. *)
Definition checked_functions_def:
  checked_functions fs bases =
    reached_functions fs bases (LENGTH fs) (live_functions fs)
End

(* Initializers also reach static implementations, even without a constructor. *)
Definition checked_contract_functions_def:
  checked_contract_functions (c : src_contract) =
    reached_functions c.contract_functions c.contract_bases
      (LENGTH c.contract_functions)
      (add_functions (live_functions c.contract_functions)
         (FILTER (λf. MEM f.fn_info.node_id c.contract_static_calls)
            c.contract_functions))
End

(* The constructor a base declares, if any. *)
Definition contract_constructor_def:
  (contract_constructor x [] = NONE) ∧
  (contract_constructor x ((f : src_function) :: fs) =
    if f.fn_kind = ConstructorKind ∧ f.fn_scope = x then SOME f
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

(* What a function's header must satisfy, whether or not its body is
 * supported: its declaring base, its kind and mutability, and the types of
 * its parameters and results. A failing header rejects the unit, since only
 * a body is confined to its function. *)
Definition function_header_ok_def:
  function_header_ok bases (f : src_function) ⇔
    MEM f.fn_scope bases ∧
    IS_SOME (all_some (MAP (scoped_variable f.fn_info.node_id) f.fn_parameters)) ∧
    IS_SOME (all_some (MAP (scoped_variable f.fn_info.node_id) f.fn_returns))
End

(* Likewise the types of a modifier's parameters. *)
Definition modifier_header_ok_def:
  modifier_header_ok (m : src_modifier) ⇔
    IS_SOME (all_some (MAP (scoped_variable m.modifier_info.node_id)
                         m.modifier_parameters))
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

(* Event parameters belong to their declaration; emit sites check their types. *)
Definition check_event_def:
  check_event (e : src_event) ⇔
    EVERY (λp. (FST p).var_scope = e.event_info.node_id)
      e.event_parameters
End

(* The super calls of f reach supported functions. *)
Definition supported_supers_def:
  supported_supers (c : src_contract) (f : src_function) ⇔
    case super_table c.contract_functions c.contract_bases f of
      SOME supers => EVERY (λ(_, g). g.fn_unsupported = NONE) supers
    | NONE => T
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
    EVERY (function_header_ok c.contract_bases)
      (checked_contract_functions c) ∧
    EVERY (λf. f.fn_kind = FunctionKind ∧
               (f.fn_visibility = InternalVisibility ∨
                f.fn_visibility = PrivateVisibility) ∧
               function_header_ok c.contract_libraries f)
      c.contract_library_functions ∧
    EVERY modifier_header_ok c.contract_modifiers ∧
    case (all_some (MAP (state_variable c.contract_bases)
                      c.contract_state_variables), constant_table c,
          immutable_table c) of
      (SOME state, SOME constants, SOME immutables) =>
        EVERY (λ(x, _). IS_SOME (ALOOKUP (state ++ immutables) x))
          c.contract_initializers ∧
        ALL_DISTINCT (MAP FST c.contract_getters) ∧
        EVERY (λ(x, selector).
                 LENGTH selector = 4 ∧
                 case ALOOKUP (state ++ immutables) x of
                   SOME ty => IS_SOME (getter_shape c.contract_structs ty)
                 | NONE => IS_SOME (ALOOKUP constants x))
          c.contract_getters ∧
        EVERY (λ(x, _, _).
                 IS_SOME (constructor_parameters x c.contract_functions))
          c.contract_base_arguments
    | _ => F
End

(* Why a unit fails the source check: each failing conjunct of
 * check_contract and of the checks it is made of, with the id of the node it
 * is about (a contract, struct, enum, event, function, modifier, state
 * variable or base) and a tag naming the check. *)
Definition rejected_unless_def:
  rejected_unless b (id : num) (tag : string) = if b then [] else [(id, tag)]
End

Definition function_header_rejections_def:
  function_header_rejections bases (f : src_function) =
    rejected_unless (MEM f.fn_scope bases) f.fn_info.node_id "function scope" ++
    rejected_unless
      (IS_SOME (all_some (MAP (scoped_variable f.fn_info.node_id) f.fn_parameters)))
      f.fn_info.node_id "parameter type" ++
    rejected_unless
      (IS_SOME (all_some (MAP (scoped_variable f.fn_info.node_id) f.fn_returns)))
      f.fn_info.node_id "return type"
End

Definition struct_rejections_def:
  struct_rejections sources bases (s : src_struct) =
    rejected_unless (MEM s.struct_scope bases ∨ MEM s.struct_scope sources)
      s.struct_info.node_id "struct scope" ++
    rejected_unless (s.struct_members ≠ []) s.struct_info.node_id "empty struct" ++
    rejected_unless
      (EVERY (λv. v.var_scope = s.struct_info.node_id ∧ IS_SOME (field_variable_type v))
         s.struct_members) s.struct_info.node_id "struct member" ++
    case s.struct_layout of
      NONE => []
    | SOME (bytes, fields) =>
        rejected_unless (0 < bytes ∧ bytes MOD 32 = 0 ∧ bytes DIV 32 < 2 ** 256)
          s.struct_info.node_id "struct layout size" ++
        rejected_unless (storage_layout_ok T s.struct_members fields)
          s.struct_info.node_id "struct layout"
End

Definition contract_rejections_def:
  contract_rejections unit_id sources (c : src_contract) =
    rejected_unless (c.contract_scope = unit_id) c.contract_info.node_id
      "contract scope" ++
    rejected_unless
      (case c.contract_bases of x :: _ => x = c.contract_info.node_id | [] => F)
      c.contract_info.node_id "linearization" ++
    rejected_unless (ALL_DISTINCT (c.contract_bases ++ c.contract_libraries))
      c.contract_info.node_id "duplicate bases" ++
    FLAT (MAP (struct_rejections sources c.contract_bases) c.contract_structs) ++
    FLAT (MAP (λ(x, members). rejected_unless (0 < members ∧ members ≤ 256) x "enum size")
            c.contract_enums) ++
    FLAT (MAP (λe. rejected_unless (check_event e) e.event_info.node_id
                     "event parameter") c.contract_events) ++
    rejected_unless
      (storage_layout_ok F c.contract_state_variables c.contract_storage)
      c.contract_info.node_id "storage layout" ++
    FLAT (MAP (function_header_rejections c.contract_bases)
            (checked_contract_functions c)) ++
    FLAT (MAP (λf. rejected_unless (f.fn_kind = FunctionKind) f.fn_info.node_id
                     "library function kind" ++
                   rejected_unless (f.fn_visibility = InternalVisibility ∨
                                    f.fn_visibility = PrivateVisibility)
                     f.fn_info.node_id "library function visibility" ++
                   function_header_rejections c.contract_libraries f)
            c.contract_library_functions) ++
    FLAT (MAP (λm. rejected_unless (modifier_header_ok m) m.modifier_info.node_id
                     "modifier parameter type") c.contract_modifiers) ++
    rejected_unless
      (IS_SOME (all_some (MAP (state_variable c.contract_bases)
                            c.contract_state_variables)))
      c.contract_info.node_id "state variable type" ++
    rejected_unless (IS_SOME (constant_table c)) c.contract_info.node_id "constant" ++
    rejected_unless (IS_SOME (immutable_table c)) c.contract_info.node_id "immutable" ++
    case (all_some (MAP (state_variable c.contract_bases)
                      c.contract_state_variables), constant_table c,
          immutable_table c) of
      (SOME state, SOME constants, SOME immutables) =>
        FLAT (MAP (λ(x, _). rejected_unless (IS_SOME (ALOOKUP (state ++ immutables) x))
                              x "initializer") c.contract_initializers) ++
        rejected_unless (ALL_DISTINCT (MAP FST c.contract_getters))
          c.contract_info.node_id "duplicate getters" ++
        FLAT (MAP (λ(x, selector).
                     rejected_unless (LENGTH selector = 4) x "getter selector" ++
                     rejected_unless
                       (case ALOOKUP (state ++ immutables) x of
                          SOME ty => IS_SOME (getter_shape c.contract_structs ty)
                        | NONE => IS_SOME (ALOOKUP constants x)) x "getter type")
                c.contract_getters) ++
        FLAT (MAP (λ(x, _, _).
                     rejected_unless (IS_SOME (constructor_parameters x c.contract_functions))
                       x "base constructor parameters") c.contract_base_arguments)
    | _ => []
End

Definition unit_rejections_def:
  unit_rejections (u : src_unit) =
    FLAT (MAP (λc. rejected_unless (ALL_DISTINCT (u.unit_info.node_id :: contract_ids c))
                     c.contract_info.node_id "duplicate node ids") u.unit_contracts) ++
    rejected_unless (MEM u.unit_info.node_id u.unit_sources) u.unit_info.node_id
      "unit not among its sources" ++
    FLAT (MAP (contract_rejections u.unit_info.node_id u.unit_sources) u.unit_contracts)
End

Definition valid_src_unit_def:
  valid_src_unit (u : src_unit) ⇔ NULL (unit_rejections u)
End

Theorem rejected_unless_nil[local,simp]:
  rejected_unless b x t = [] ⇔ b
Proof
  rw[rejected_unless_def]
QED

Theorem FLAT_MAP_nil[local]:
  FLAT (MAP f l) = [] ⇔ EVERY (λx. f x = []) l
Proof
  Induct_on ‘l’ >> simp[]
QED

Theorem function_header_rejections_nil[local]:
  function_header_rejections bases f = [] ⇔ function_header_ok bases f
Proof
  simp[function_header_rejections_def, function_header_ok_def, CONJ_ASSOC]
QED

Theorem struct_rejections_nil[local]:
  struct_rejections sources bases s = [] ⇔ check_struct sources bases s
Proof
  simp[struct_rejections_def, check_struct_def] >>
  Cases_on ‘s.struct_layout’ >> simp[CONJ_ASSOC] >>
  rename1 ‘SOME p’ >> Cases_on ‘p’ >> simp[CONJ_ASSOC]
QED

Theorem contract_rejections_nil[local]:
  contract_rejections unit_id sources c = [] ⇔ check_contract unit_id sources c
Proof
  simp[contract_rejections_def, check_contract_def, FLAT_MAP_nil,
       struct_rejections_nil, function_header_rejections_nil] >>
  Cases_on ‘all_some (MAP (state_variable c.contract_bases)
                        c.contract_state_variables)’ >>
  Cases_on ‘constant_table c’ >> Cases_on ‘immutable_table c’ >>
  simp[FLAT_MAP_nil, listTheory.EVERY_MEM, pairTheory.FORALL_PROD, CONJ_ASSOC]
QED

(* The conjuncts unit_rejections lists. *)
Theorem valid_src_unit_checks:
  valid_src_unit u ⇔
    EVERY (λc. ALL_DISTINCT (u.unit_info.node_id :: contract_ids c))
      u.unit_contracts ∧
    MEM u.unit_info.node_id u.unit_sources ∧
    EVERY (check_contract u.unit_info.node_id u.unit_sources) u.unit_contracts
Proof
  simp[valid_src_unit_def, unit_rejections_def, listTheory.NULL_EQ, FLAT_MAP_nil,
       contract_rejections_nil, CONJ_ASSOC, listTheory.EVERY_MEM]
QED

(* The functions of a unit's contracts that calls reach, then their library
 * functions: each one's id, name, and reason if unsupported. *)
Definition unit_functions_def:
  unit_functions (u : src_unit) =
    FLAT (MAP (λc.
      MAP (λ(f : src_function). (f.fn_info.node_id, f.fn_name, f.fn_unsupported))
        (checked_contract_functions c ++
         c.contract_library_functions)) u.unit_contracts)
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
val () = cv_auto_trans decoded_type_def;
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
val () = cv_auto_trans function_table_def;
val () = cv_auto_trans contract_constructor_def;
val () = cv_auto_trans constructor_parameters_def;
val () = cv_auto_trans live_functions_def;
val () = cv_auto_trans later_bases_def;
val () = cv_auto_trans super_target_def;
val () = cv_auto_trans super_table_def;
val () = cv_auto_trans super_targets_def;
val () = cv_auto_trans add_functions_def;
val () = cv_auto_trans static_targets_def;
val () = cv_auto_trans reached_functions_def;
val () = cv_auto_trans checked_functions_def;
val () = cv_auto_trans checked_contract_functions_def;
val () = cv_auto_trans storage_layout_ok_def;
val () = cv_auto_trans function_header_ok_def;
val () = cv_auto_trans modifier_header_ok_def;
val () = cv_auto_trans check_struct_def;
val () = cv_auto_trans check_event_def;
val () = cv_auto_trans supported_supers_def;
val () = cv_auto_trans check_contract_def;
val () = cv_auto_trans rejected_unless_def;
val () = cv_auto_trans function_header_rejections_def;
val () = cv_auto_trans struct_rejections_def;
val () = cv_auto_trans contract_rejections_def;
val () = cv_auto_trans unit_rejections_def;
val () = cv_auto_trans valid_src_unit_def;
val () = cv_auto_trans unit_functions_def;
