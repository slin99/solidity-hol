(* Import of the pinned compiler's AST for testdata/frontend/pure_core.sol,
 * testdata/differential/storage.sol and other differential fixtures, and
 * negative fixtures derived from them by edits to the JSON.
 *)
Theory solidityImportTest
Ancestors
  solidityImport
Libs
  solidityImportLib cv_transLib intLib wordsLib

(* Read by holbuild's dependency scanner, which stages the fixture. *)
fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps [
  "../testdata/frontend/expected/pure_core.json",
  "../testdata/differential/expected/storage.json",
  "../testdata/differential/expected/mappings.json",
  "../testdata/differential/expected/storage_arrays.json",
  "../testdata/differential/expected/dynamic_storage_arrays.json",
  "../testdata/differential/expected/builtins.json",
  "../testdata/differential/expected/storage_structs.json",
  "../testdata/differential/expected/inheritance.json",
  "../testdata/differential/expected/imports.json",
  "../testdata/differential/expected/errors.json",
  "../testdata/differential/expected/type_bounds.json",
  "../testdata/differential/expected/using_for.json",
  "../testdata/differential/expected/contract_types.json",
  "../testdata/differential/expected/hashes.json",
  "../testdata/differential/expected/conditionals.json",
  "../testdata/differential/expected/encode_calls.json",
  "../testdata/differential/expected/bytes_constants.json"
]

val fixture = "../testdata/frontend/expected/pure_core.json"
val source = "testdata/frontend/pure_core.sol"

Definition pure_core_def:
  pure_core = ^(import_artifact fixture source)
End

val () = cv_auto_trans pure_core_def;

Theorem pure_core_valid:
  valid_src_unit pure_core
Proof
  CONV_TAC cv_eval
QED

Theorem pure_core_signatures:
  MAP (λf. (f.fn_name, OPT_MMAP variable_type f.fn_parameters,
            OPT_MMAP variable_type f.fn_returns))
    (HD pure_core.unit_contracts).contract_functions =
  [("add", SOME [UintT 8; UintT 8], SOME [UintT 8]);
   ("wrappingAdd", SOME [UintT 8; UintT 8], SOME [UintT 8]);
   ("count", SOME [UintT 256], SOME [UintT 256; UintT 256]);
   ("sum", SOME [UintT 256], SOME [UintT 256]);
   ("doubleUntil", SOME [UintT 256], SOME [UintT 256]);
   ("fact", SOME [UintT 256], SOME [UintT 256]);
   ("divmod", SOME [UintT 256; UintT 256], SOME [UintT 256; UintT 256]);
   ("swap", SOME [], SOME [UintT 256; UintT 256]);
   ("locals", SOME [UintT 256], SOME [UintT 256]);
   ("narrow", SOME [UintT 256], SOME [UintT 8; BoolT]);
   ("negate", SOME [IntT 8], SOME [IntT 8]);
   ("identity", SOME [AddressT NonpayableAddress; FixedBytesT 4],
    SOME [AddressT NonpayableAddress; FixedBytesT 4]);
   ("guardedDivide", SOME [UintT 256], SOME [BoolT]);
   ("badDivide", SOME [UintT 256], SOME [BoolT]);
   ("shortCircuit", SOME [UintT 256], SOME [BoolT; UintT 256]);
   ("panicOrder", SOME [UintT 256], SOME [UintT 256]);
   ("argumentOrder", SOME [UintT 256], SOME [UintT 256; UintT 256]);
   ("compoundOrder", SOME [UintT 256], SOME [UintT 256]);
   ("checkedBranchOverwrite", SOME [UintT 8; BoolT], SOME [UintT 8])]
Proof
  EVAL_TAC
QED

Theorem type_name_normalization:
  normalize_type_name (SrcElementaryTypeName i "uint" NONE) =
    SOME (UintT 256) ∧
  normalize_type_name (SrcElementaryTypeName i "uint7" NONE) = NONE ∧
  normalize_type_name (SrcElementaryTypeName i "bytes33" NONE) = NONE ∧
  normalize_type_name (SrcElementaryTypeName i "bytes" NONE) = SOME BytesT ∧
  normalize_type_name (SrcElementaryTypeName i "string" NONE) = SOME StringT ∧
  normalize_type_name (SrcElementaryTypeName i "address" (SOME "payable")) =
    SOME (AddressT PayableAddress) ∧
  normalize_type_name (SrcElementaryTypeName i "address" NONE) = NONE ∧
  normalize_type_name (SrcElementaryTypeName i "bool" (SOME "payable")) = NONE
Proof
  EVAL_TAC
QED

Theorem type_identifier_decoding:
  decode_type_identifier "t_rational_minus_7_by_2" =
    SOME (SrcRational (-7) 2) ∧
  decode_type_identifier "t_rational_1_by_0" = NONE ∧
  decode_type_identifier "t_tuple$_t_uint256_$_t_bool_$" =
    SOME (SrcTupleType [UintT 256; BoolT]) ∧
  decode_type_identifier "t_tuple$__$" = SOME (SrcTupleType []) ∧
  decode_type_identifier "t_tuple$_t_bool_$_t_rational_0_by_1_$" =
    SOME (SrcTupleType [BoolT; UintT 256]) ∧
  decode_type_identifier "t_tuple$_t_rational_minus_1_by_1_$_t_bool_$" =
    SOME (SrcTupleType [IntT 256; BoolT]) ∧
  decode_type_identifier "t_tuple$_t_rational_1_by_2_$_t_bool_$" = NONE ∧
  decode_type_identifier "t_address_payable" =
    SOME (SrcType (AddressT PayableAddress)) ∧
  decode_type_identifier "t_uint7" = NONE ∧
  decode_type_identifier "t_uint" = NONE ∧
  decode_type_identifier "t_string_memory_ptr" = SOME (SrcType (LocatedT MemoryLoc StringT)) ∧
  decode_type_identifier "t_bytes_memory_ptr" = SOME (SrcType (LocatedT MemoryLoc BytesT))
Proof
  EVAL_TAC
QED

(* Negative fixtures: the fixture's AST with one edit to the first node, in
 * document order, of a given nodeType.
 *)

fun artifact_part path keys =
  JSONUtil.get (JSONParser.parseFile path,
    [JSONUtil.SEL "output"] @ map JSONUtil.SEL keys)

val ast = artifact_part fixture ["sources", source, "ast"]
val contracts = artifact_part fixture ["contracts", source]

fun is_node ty =
  JSONUtil.testField "nodeType" (fn JSON.STRING s => s = ty | _ => false)

fun edit_first_where p what f v =
  let
    val edited = ref false
    fun go v =
      if !edited then v
      else case v of
             JSON.OBJECT kvs =>
               if p v then (edited := true; f v)
               else JSON.OBJECT (map (fn (k, x) => (k, go x)) kvs)
           | JSON.ARRAY vs => JSON.ARRAY (map go vs)
           | _ => v
    val result = go v
  in
    if !edited then result else raise Fail ("no " ^ what)
  end

fun edit_first ty = edit_first_where (is_node ty) (ty ^ " node")

fun set_field k x (JSON.OBJECT kvs) =
      JSON.OBJECT (map (fn (k', y) => if k' = k then (k', x) else (k', y)) kvs)
  | set_field _ _ v = v

fun drop_field k (JSON.OBJECT kvs) =
      JSON.OBJECT (List.filter (fn (k', _) => k' <> k) kvs)
  | drop_field _ v = v

fun type_identifier tid =
  set_field "typeDescriptions"
    (JSON.OBJECT [("typeIdentifier", JSON.STRING tid),
                  ("typeString", JSON.STRING "")])

(* How an edited unit fails import: Unsupported when an import error rejects
 * the unit, UnsupportedFunction when it imports with a function marked
 * unsupported (an unsupported construct in a body or a modifier rejects that
 * function only), Malformed when the compiler JSON is malformed. *)
datatype import_failure = Unsupported | UnsupportedFunction | Malformed

(* How an edited unit fails import, with the reason; NONE when everything
 * imports. *)
fun import_rejection units v contracts =
  let
    fun reason t =
      if type_of t <> ``:src_function`` then NONE else
      case Lib.total TypeBase.dest_record t of
        SOME (_, fields) =>
          (case Lib.assoc1 "fn_unsupported" fields of
             SOME (_, r) =>
               if optionSyntax.is_some r
               then SOME (stringSyntax.fromHOLstring (optionSyntax.dest_some r))
               else NONE
           | NONE => NONE)
      | NONE => NONE
    val tm = import_source_unit units v contracts
  in
    case find_terms (isSome o reason) tm of
      t :: _ => SOME (UnsupportedFunction, valOf (reason t))
    | [] => NONE
  end
  handle ImportError msg => SOME (Unsupported, msg)
       | MalformedInput msg => SOME (Malformed, msg)

fun failure_name Unsupported = "unit rejection"
  | failure_name UnsupportedFunction = "unsupported function"
  | failure_name Malformed = "malformed input"

fun import_units_error_with expected units contracts name v =
  case import_rejection units v contracts of
    NONE => raise Fail (name ^ ": imported")
  | SOME (actual, msg) =>
      if actual = expected then ()
      else raise Fail (name ^ ": expected " ^ failure_name expected ^ ", got " ^
                       failure_name actual ^ ": " ^ msg)

fun import_error_with expected = import_units_error_with expected []

val import_error = import_error_with Unsupported contracts
val function_error = import_error_with UnsupportedFunction contracts
val malformed_input = import_error_with Malformed contracts

(* An edited unit that imports, as a cv-translated constant. *)
fun edited_unit_with contracts name v =
  let
    val tm = import_source_unit [] v contracts
    val def = new_definition (name ^ "_def", mk_eq (mk_var (name, type_of tm), tm))
  in
    cv_auto_trans def
  end

val edited_unit = edited_unit_with contracts

(* Unknown forms, missing annotations and unsupported features fail import. *)

val () = function_error "unknown statement"
  (edit_first "Break" (set_field "nodeType" (JSON.STRING "UnknownStatement")) ast)
val () = function_error "unknown expression"
  (edit_first "Literal" (set_field "nodeType" (JSON.STRING "IndexRangeAccess")) ast)
val () = malformed_input "missing type annotation"
  (edit_first "Identifier" (drop_field "typeDescriptions") ast)
val () = malformed_input "missing declaration reference"
  (edit_first "Identifier" (drop_field "referencedDeclaration") ast)
val () = malformed_input "missing common type"
  (edit_first "BinaryOperation" (drop_field "commonType") ast)
val () = malformed_input "function as state variable"
  (edit_first "FunctionDefinition"
     (set_field "nodeType" (JSON.STRING "VariableDeclaration")) ast)
val () = function_error "modifier invocation of unknown kind"
  (edit_first "FunctionDefinition"
     (set_field "modifiers"
        (JSON.ARRAY [JSON.OBJECT [("kind", JSON.STRING "unknownInvocation")]]))
     ast)
val () = function_error "a named argument naming no parameter"
  (edit_first "FunctionCall"
     (set_field "names" (JSON.ARRAY [JSON.STRING "noSuchParameter"])) ast)
(* (fact)({n: ...}): the callee names no declaration to take the parameter
 * names from, so the call fails import as unsupported, naming the cause. *)
val () =
  let
    fun parenthesize (callee as JSON.OBJECT kvs) =
          JSON.OBJECT
            ([("nodeType", JSON.STRING "TupleExpression"),
              ("isInlineArray", JSON.BOOL false),
              ("components", JSON.ARRAY [callee])] @
             List.filter (fn (k, _) => k = "id" orelse k = "src" orelse
                                       k = "typeDescriptions") kvs)
      | parenthesize v = v
    fun edit call =
      case JSONUtil.findField call "expression" of
        SOME callee =>
          set_field "names" (JSON.ARRAY [JSON.STRING "n"])
            (set_field "expression" (parenthesize callee) call)
      | NONE => raise Fail "a call without a callee"
  in
    case import_rejection [] (edit_first "FunctionCall" edit ast) contracts of
      NONE => raise Fail "named arguments of a parenthesized callee: imported"
    | SOME (k, msg) =>
        if k = UnsupportedFunction andalso
           String.isSubstring "named arguments are not supported" msg then ()
        else raise Fail ("named arguments of a parenthesized callee: " ^ msg)
  end
val () = import_error "base outside the compilation"
  (edit_first "ContractDefinition"
     (fn c => set_field "linearizedBaseContracts"
                (JSON.ARRAY [JSONUtil.lookupField c "id", JSON.INT 999999]) c)
     ast)

(* Builtin references outside call position remain unsupported; the rejection
 * names the identifier's node.
 *)
val () =
  case import_rejection []
         (edit_first "Identifier"
            (set_field "referencedDeclaration" (JSON.INT ~18)) ast) contracts of
    NONE => raise Fail "built-in: imported"
  | SOME (k, msg) =>
      if k = UnsupportedFunction andalso String.isPrefix "Identifier " msg andalso
         String.isSubstring ": built-in " msg
      then ()
      else raise Fail ("built-in: " ^ msg)

(* Duplicate and dangling ids and inconsistent types import but are invalid. *)

val unit_id = JSONUtil.lookupField ast "id"

val () = edited_unit "duplicate_id"
  (edit_first "Literal" (set_field "id" unit_id) ast)

val () = edited_unit "dangling_reference"
  (edit_first "Identifier"
     (set_field "referencedDeclaration" (JSON.INT 999999)) ast)

(* The first identifier is the uint8 parameter x of add. *)
val () = edited_unit "identifier_type_mismatch"
  (edit_first "Identifier" (type_identifier "t_uint256") ast)

(* A reference to the function add used as a value. *)
val add_id =
  JSONUtil.get (ast, [JSONUtil.SEL "nodes", JSONUtil.SUB 1,
                      JSONUtil.SEL "nodes", JSONUtil.SUB 0, JSONUtil.SEL "id"])

val () = edited_unit "function_as_value"
  (edit_first "Identifier" (set_field "referencedDeclaration" add_id) ast)

val () = edited_unit "declaration_type_mismatch"
  (edit_first "VariableDeclaration" (type_identifier "t_bool") ast)

val () = edited_unit "wrong_scope"
  (edit_first "VariableDeclaration" (set_field "scope" (JSON.INT 999999)) ast)

val () = edited_unit "unlinked_declaration"
  (edit_first "VariableDeclarationStatement"
     (set_field "assignments" (JSON.ARRAY [JSON.NULL])) ast)

(* The first comparison, ++i < n in count, annotated as a uint256. *)
val () = edited_unit "comparison_type_mismatch"
  (edit_first_where
     (fn v => is_node "BinaryOperation" v andalso
              JSONUtil.testField "operator" (fn JSON.STRING s => s = "<" | _ => false) v)
     "comparison" (type_identifier "t_uint256") ast)

(* The first call is fact(n - 1). *)
val () = edited_unit "call_arity"
  (edit_first "FunctionCall" (set_field "arguments" (JSON.ARRAY [])) ast)

Theorem duplicate_id_rejected:
  ¬valid_src_unit duplicate_id
Proof
  CONV_TAC cv_eval
QED

Theorem declaration_type_mismatch_rejected:
  ¬valid_src_unit declaration_type_mismatch
Proof
  CONV_TAC cv_eval
QED

Theorem wrong_scope_rejected:
  ¬valid_src_unit wrong_scope
Proof
  CONV_TAC cv_eval
QED

(* State variables and the storage layout *)

val storage_fixture = "../testdata/differential/expected/storage.json"
val storage_source = "testdata/differential/storage.sol"

Definition storage_unit_def:
  storage_unit = ^(import_artifact storage_fixture storage_source)
End

val () = cv_auto_trans storage_unit_def;

Theorem storage_unit_layout:
  MAP (λe. (e.storage_slot, e.storage_offset, e.storage_type_id))
    (HD storage_unit.unit_contracts).contract_storage =
  [(0, 0, "t_uint256"); (1, 0, "t_uint8"); (1, 1, "t_int16");
   (1, 3, "t_bool"); (1, 4, "t_address"); (1, 24, "t_bytes4");
   (2, 0, "t_uint128"); (2, 16, "t_uint128"); (3, 0, "t_int256")]
Proof
  EVAL_TAC
QED

val storage_ast =
  artifact_part storage_fixture ["sources", storage_source, "ast"]
val storage_contracts =
  artifact_part storage_fixture ["contracts", storage_source]

(* The first variable declaration is the state variable total. A public
 * one needs its getter's selector. *)
val () = import_error_with Malformed storage_contracts "public state variable without a selector"
  (edit_first "VariableDeclaration"
     (set_field "visibility" (JSON.STRING "public")) storage_ast)
val () = import_error_with Unsupported storage_contracts "overriding state variable"
  (edit_first "VariableDeclaration"
     (fn v => case drop_field "overrides" v of
                JSON.OBJECT kvs =>
                  JSON.OBJECT (("overrides",
                    JSON.OBJECT [("nodeType", JSON.STRING "OverrideSpecifier"),
                                 ("id", JSON.INT 100000),
                                 ("overrides", JSON.ARRAY [])]) :: kvs)
              | v' => v')
     storage_ast)
val () = import_error_with Malformed storage_contracts "constant without a value"
  (edit_first "VariableDeclaration" (set_field "constant" (JSON.BOOL true))
     storage_ast)
(* An immutable is imported apart from the state variables. *)
val () =
  let
    val tm = import_source_unit []
      (edit_first "VariableDeclaration"
         (set_field "mutability" (JSON.STRING "immutable")) storage_ast)
      storage_contracts
    fun field name t = Lib.assoc name (snd (TypeBase.dest_record t))
    fun names t =
      map (stringSyntax.fromHOLstring o field "var_name")
        (fst (listSyntax.dest_list t))
    val c = hd (fst (listSyntax.dest_list (field "unit_contracts" tm)))
    val immutables = names (field "contract_immutables" c)
  in
    if length immutables = 1 andalso
       not (List.exists (fn n => n = hd immutables)
              (names (field "contract_state_variables" c)))
    then () else raise Fail "immutable state variable: not imported apart"
  end
val () = import_error_with Malformed (JSON.OBJECT []) "missing storage layout" storage_ast

(* The contracts output with an edit to the layout entries; the first is
 * total's. *)
fun edit_layout f =
  case storage_contracts of
    JSON.OBJECT [(name, contract)] =>
      let
        val layout = JSONUtil.lookupField contract "storageLayout"
        val entries =
          JSON.ARRAY (f (JSONUtil.arrayMap I (JSONUtil.lookupField layout "storage")))
      in
        JSON.OBJECT [(name, set_field "storageLayout"
                              (set_field "storage" entries layout) contract)]
      end
  | _ => raise Fail "expected one contract"

fun edit_first_entry f = edit_layout (fn e :: es => f e :: es | [] => [])

val () = edited_unit_with
  (edit_first_entry (set_field "type" (JSON.STRING "t_uint8")))
  "layout_type_mismatch" storage_ast
val () = edited_unit_with
  (edit_first_entry (set_field "astId" (JSON.INT 999999)))
  "layout_id_mismatch" storage_ast
val () = edited_unit_with (edit_layout tl) "layout_missing_entry" storage_ast
val () = edited_unit_with (edit_layout (fn e :: es => es @ [e] | [] => []))
  "layout_reordered" storage_ast

(* The first function is setTotal, which writes total. *)
val () = edited_unit_with storage_contracts "pure_writes_state"
  (edit_first "FunctionDefinition"
     (set_field "stateMutability" (JSON.STRING "pure")) storage_ast)
val () = edited_unit_with storage_contracts "payable_function"
  (edit_first "FunctionDefinition"
     (set_field "stateMutability" (JSON.STRING "payable")) storage_ast)
val () = edited_unit_with storage_contracts "unknown_mutability"
  (edit_first "FunctionDefinition"
     (set_field "stateMutability" (JSON.STRING "constant")) storage_ast)

Theorem layout_type_mismatch_rejected:
  ¬valid_src_unit layout_type_mismatch
Proof
  CONV_TAC cv_eval
QED

Theorem layout_id_mismatch_rejected:
  ¬valid_src_unit layout_id_mismatch
Proof
  CONV_TAC cv_eval
QED

Theorem layout_missing_entry_rejected:
  ¬valid_src_unit layout_missing_entry
Proof
  CONV_TAC cv_eval
QED

Theorem layout_reordered_rejected:
  ¬valid_src_unit layout_reordered
Proof
  CONV_TAC cv_eval
QED

Theorem payable_function_valid:
  valid_src_unit payable_function
Proof
  CONV_TAC cv_eval
QED

Theorem unknown_mutability_rejected:
  ¬valid_src_unit unknown_mutability
Proof
  CONV_TAC cv_eval
QED


(* Mapping AST and layout identifiers have different encodings. Both must
 * agree with the normalized key/value types, including nested declarations.
 *)
val mapping_fixture = "../testdata/differential/expected/mappings.json"
val mapping_source = "testdata/differential/mappings.sol"
val mapping_ast = artifact_part mapping_fixture ["sources", mapping_source, "ast"]
val mapping_contracts = artifact_part mapping_fixture ["contracts", mapping_source]

Definition mapping_unit_def:
  mapping_unit = ^(import_artifact mapping_fixture mapping_source)
End

val () = cv_auto_trans mapping_unit_def;

val () = edited_unit_with mapping_contracts "mapping_key_metadata_mismatch"
  (edit_first "VariableDeclaration"
     (type_identifier "t_mapping$_t_int256_$_t_uint8_$") mapping_ast)

val () = edited_unit_with mapping_contracts "mapping_leaf_metadata_mismatch"
  (edit_first "IndexAccess" (type_identifier "t_uint256") mapping_ast)

Theorem mapping_key_metadata_rejected:
  ¬valid_src_unit mapping_key_metadata_mismatch
Proof
  CONV_TAC cv_eval
QED

(* The compiler uses different array encodings in AST types and storageLayout;
 * changing only the resolved dimension or the indexed leaf must be rejected. *)
val array_fixture = "../testdata/differential/expected/storage_arrays.json"
val array_source = "testdata/differential/storage_arrays.sol"
val array_ast = artifact_part array_fixture ["sources", array_source, "ast"]
val array_contracts = artifact_part array_fixture ["contracts", array_source]

(* A null index is a valid array type expression, not malformed compiler JSON. *)
val () =
  case import_rejection []
         (edit_first "IndexAccess" (set_field "indexExpression" JSON.NULL) array_ast)
         array_contracts of
    NONE => raise Fail "array type expression imported"
  | SOME (Malformed, msg) =>
      raise Fail ("array type expression: malformed input: " ^ msg)
  | SOME _ => ();

Definition array_unit_def:
  array_unit = ^(import_artifact array_fixture array_source)
End
val () = cv_auto_trans array_unit_def;

val () = edited_unit_with array_contracts "array_dynamic_dimension_mismatch"
  (edit_first "ArrayTypeName" (set_field "length" JSON.NULL) array_ast)

Theorem array_dynamic_dimension_metadata_rejected:
  ¬valid_src_unit array_dynamic_dimension_mismatch
Proof
  CONV_TAC cv_eval
QED

val () = import_error_with Unsupported array_contracts "malformed resolved array dimension"
  (edit_first "ArrayTypeName"
     (fn v => set_field "length"
       (type_identifier "t_rational_35x_by_1" (JSONUtil.lookupField v "length")) v)
     array_ast)

val () = edited_unit_with array_contracts "array_dimension_mismatch"
  (edit_first "ArrayTypeName"
     (fn v => set_field "length"
       (type_identifier "t_rational_34_by_1" (JSONUtil.lookupField v "length")) v)
     array_ast)

Theorem array_dimension_metadata_rejected:
  ¬valid_src_unit array_dimension_mismatch
Proof
  CONV_TAC cv_eval
QED

val () = edited_unit_with array_contracts "array_leaf_mismatch"
  (edit_first "IndexAccess" (type_identifier "t_uint16") array_ast)

Definition dynamic_array_unit_def:
  dynamic_array_unit =
    ^(import_artifact "../testdata/differential/expected/dynamic_storage_arrays.json"
                      "testdata/differential/dynamic_storage_arrays.sol")
End
val () = cv_auto_trans dynamic_array_unit_def;

(* Builtin identity is solc's declaration reference; spelling is diagnostic. *)
val builtins_fixture = "../testdata/differential/expected/builtins.json"
val builtins_source = "testdata/differential/builtins.sol"
val builtins_ast = artifact_part builtins_fixture ["sources", builtins_source, "ast"]
val builtins_contracts = artifact_part builtins_fixture ["contracts", builtins_source]

Definition builtins_unit_def:
  builtins_unit = ^(import_artifact builtins_fixture builtins_source)
End

val () = cv_auto_trans builtins_unit_def;

fun edit_callee f = edit_first "FunctionCall" (fn call =>
  set_field "expression" (f (JSONUtil.lookupField call "expression")) call)

val () = edited_unit_with builtins_contracts "renamed_builtin"
  (edit_callee (set_field "name" (JSON.STRING "assert")) builtins_ast)

Theorem renamed_builtin_valid:
  valid_src_unit renamed_builtin
Proof
  CONV_TAC cv_eval
QED

val () = import_error_with UnsupportedFunction builtins_contracts "unknown builtin declaration"
  (edit_callee (set_field "referencedDeclaration" (JSON.INT ~999)) builtins_ast)

(* A nonliteral message must not be silently ignored on success. *)
val () = edited_unit_with builtins_contracts "nonliteral_builtin_message"
  (edit_first "FunctionCall" (fn call =>
     set_field "arguments" (JSON.ARRAY
       [hd (JSONUtil.arrayMap I (JSONUtil.lookupField call "arguments")),
        set_field "id" (JSON.INT 999999)
          (hd (JSONUtil.arrayMap I (JSONUtil.lookupField call "arguments")))]) call)
     builtins_ast)

val struct_fixture = "../testdata/differential/expected/storage_structs.json"
val struct_source = "testdata/differential/storage_structs.sol"
val struct_ast = artifact_part struct_fixture ["sources", struct_source, "ast"]
val struct_contracts = artifact_part struct_fixture ["contracts", struct_source]

Definition struct_unit_def:
  struct_unit = ^(import_artifact struct_fixture struct_source)
End
val () = cv_auto_trans struct_unit_def;

val () = edited_unit_with struct_contracts "struct_type_identity_mismatch"
  (edit_first "UserDefinedTypeName"
    (set_field "referencedDeclaration" (JSON.INT 999999)) struct_ast)

val () = edited_unit_with struct_contracts "struct_field_identity_mismatch"
  (edit_first "MemberAccess"
    (set_field "referencedDeclaration" (JSON.INT 999999)) struct_ast)

val () = edited_unit_with struct_contracts "struct_field_type_mismatch"
  (edit_first "MemberAccess" (type_identifier "t_uint16") struct_ast)

Theorem struct_type_identity_checked:
  ¬valid_src_unit struct_type_identity_mismatch
Proof
  CONV_TAC cv_eval
QED

(* A public struct has a getter when each member it returns is a value or a
 * byte sequence: item's members are values, nested's include a struct. *)
fun public_state_variable name selector =
  edit_first_where
    (fn v => is_node "VariableDeclaration" v andalso
             JSONUtil.testField "name" (fn JSON.STRING s => s = name | _ => false) v)
    ("state variable " ^ name)
    (fn v => case set_field "visibility" (JSON.STRING "public") v of
                JSON.OBJECT kvs =>
                  JSON.OBJECT (kvs @ [("functionSelector", JSON.STRING selector)])
              | v' => v')

val () = edited_unit_with struct_contracts "struct_getter"
  (public_state_variable "item" "f2a4a82e" struct_ast)
val () = edited_unit_with struct_contracts "nested_struct_getter"
  (public_state_variable "nested" "4ce2d543" struct_ast)

Theorem nested_struct_getter_rejected:
  valid_src_unit struct_getter ∧ ¬valid_src_unit nested_struct_getter
Proof
  CONV_TAC cv_eval
QED

val () = import_error_with Malformed struct_contracts "missing field identity"
  (edit_first "MemberAccess" (drop_field "referencedDeclaration") struct_ast)

val () = import_error_with Malformed struct_contracts "missing struct type identity"
  (edit_first "UserDefinedTypeName" (drop_field "referencedDeclaration") struct_ast)

(* Inheritance: only the deployable contract is imported, flattened along its
 * linearization; calls through the bases reach the most derived overrides. *)

val inheritance_fixture = "../testdata/differential/expected/inheritance.json"
val inheritance_source = "testdata/differential/inheritance.sol"

Definition inheritance_unit_def:
  inheritance_unit = ^(import_artifact inheritance_fixture inheritance_source)
End

val () = cv_auto_trans inheritance_unit_def;

(* Counter._scale has no body and is left out; Counter.peek, Counter._sender
 * and Context._sender are overridden. *)
Theorem inheritance_unit_flattened:
  MAP (λc. c.contract_name) inheritance_unit.unit_contracts = ["Doubling"] ∧
  MAP (λf. f.fn_name)
    (HD inheritance_unit.unit_contracts).contract_functions =
  ["peek"; "_scale"; "_sender"; "bump"; "peek"; "_sender"; "_update";
   "_sender"; "_who"] ∧
  MAP (λf. f.fn_name)
    (live_functions (HD inheritance_unit.unit_contracts).contract_functions) =
  ["peek"; "_scale"; "_sender"; "bump"; "_update"; "_who"] ∧
  MAP (λv. v.var_name)
    (HD inheritance_unit.unit_contracts).contract_state_variables =
  ["total"; "counts"; "calls"]
Proof
  EVAL_TAC
QED

(* Every _sender, Context's too, resolves to Doubling's. *)
Theorem inheritance_overrides_resolve:
  EVERY (λf. f.fn_name = "_sender" ⇒
             OPTION_MAP (λg. g.fn_scope)
               (ALOOKUP (call_table
                  (HD inheritance_unit.unit_contracts).contract_functions)
                  f.fn_info.node_id) =
             SOME (HD inheritance_unit.unit_contracts).contract_info.node_id)
    (HD inheritance_unit.unit_contracts).contract_functions
Proof
  EVAL_TAC
QED

val inheritance_ast =
  artifact_part inheritance_fixture ["sources", inheritance_source, "ast"]
val inheritance_contracts =
  artifact_part inheritance_fixture ["contracts", inheritance_source]

fun map_nodes f (JSON.OBJECT kvs) =
      f (JSON.OBJECT (map (fn (k, x) => (k, map_nodes f x)) kvs))
  | map_nodes f (JSON.ARRAY vs) = JSON.ARRAY (map (map_nodes f) vs)
  | map_nodes _ v = v

(* Without Doubling._scale's baseFunctions, Counter.bump's call of the
 * unimplemented Counter._scale reaches no function. *)
val () = edited_unit_with inheritance_contracts "unresolved_override"
  (map_nodes
     (fn v => if is_node "FunctionDefinition" v andalso
                 JSONUtil.asString (JSONUtil.lookupField v "name") = "_scale"
              then drop_field "baseFunctions" v else v)
     inheritance_ast)

(* Imports: the contract's base, the interface it implements and calls
 * through, their event and the struct it stores all come from
 * imports_base.sol, and resolve by id across the compilation. *)

val imports_fixture = "../testdata/differential/expected/imports.json"
val imports_source = "testdata/differential/imports.sol"

Definition imports_unit_def:
  imports_unit = ^(import_artifact imports_fixture imports_source)
End

val () = cv_auto_trans imports_unit_def;

(* Counter.bump is overridden; ICounter.count has no body. Only Point, of
 * imports_base.sol's two structs, is referred to. *)
Theorem imports_unit_resolved:
  LENGTH imports_unit.unit_sources = 2 ∧
  MAP (λc. c.contract_name) imports_unit.unit_contracts = ["Imports"] ∧
  LENGTH (HD imports_unit.unit_contracts).contract_bases = 3 ∧
  MAP (λf. f.fn_name) (HD imports_unit.unit_contracts).contract_functions =
  ["count"; "bump"; "lastSum"; "countOf"; "bump"] ∧
  LENGTH (HD imports_unit.unit_contracts).contract_events = 1 ∧
  EVERY (λs. s.struct_scope ≠ imports_unit.unit_info.node_id ∧
             MEM s.struct_scope imports_unit.unit_sources)
    (HD imports_unit.unit_contracts).contract_structs ∧
  LENGTH (HD imports_unit.unit_contracts).contract_structs = 1
Proof
  EVAL_TAC
QED

(* Without the other file, the base is out of reach. *)
val () = import_error_with Unsupported
  (artifact_part imports_fixture ["contracts", imports_source])
  "imports without the imported file"
  (artifact_part imports_fixture ["sources", imports_source, "ast"])

(* Custom errors: each revert carries the selector and parameters of the
 * error it names, wherever that is declared: at file level or in an
 * interface base, both in errors_base.sol, or in the contract. *)

val errors_fixture = "../testdata/differential/expected/errors.json"
val errors_source = "testdata/differential/errors.sol"

Definition errors_unit_def:
  errors_unit = ^(import_artifact errors_fixture errors_source)
End

val () = cv_auto_trans errors_unit_def;

(* The errors a body reverts with, in order: selector, parameter count and
 * argument count. *)
Definition revert_errors_def:
  (revert_errors (SrcBlock _ ss) = revert_errors_list ss) ∧
  (revert_errors (SrcIfStatement _ _ t NONE) = revert_errors t) ∧
  (revert_errors (SrcRevertError _ err args _) =
    [(err.error_selector, LENGTH err.error_parameters, LENGTH args)]) ∧
  (revert_errors _ = []) ∧
  (revert_errors_list [] = []) ∧
  (revert_errors_list (s :: ss) = revert_errors s ++ revert_errors_list ss)
End

Theorem errors_reverts_resolved:
  FLAT (MAP (λf. revert_errors f.fn_body)
          (HD errors_unit.unit_contracts).contract_functions) =
  [([0xdbw; 0x42w; 0x14w; 0x4dw], 3, 3); ([0x8ew; 0x4aw; 0x23w; 0xd6w], 1, 1);
   ([0x3dw; 0xb2w; 0xa1w; 0x2aw], 0, 0); ([0x05w; 0x6ew; 0xe4w; 0xfaw], 3, 3)]
Proof
  EVAL_TAC
QED

(* type(T).max and type(T).min: integer types only. *)

Definition type_bounds_unit_def:
  type_bounds_unit = ^(import_artifact
    "../testdata/differential/expected/type_bounds.json"
    "testdata/differential/type_bounds.sol")
End

val () = cv_auto_trans type_bounds_unit_def;

Theorem type_bound_values:
  type_bound "min" (UintT 8) = SOME 0 ∧
  type_bound "max" (UintT 8) = SOME 255 ∧
  type_bound "min" (IntT 8) = SOME (-128) ∧
  type_bound "max" (IntT 8) = SOME 127 ∧
  type_bound "max" (UintT 256) = SOME (&(2 ** 256) - 1) ∧
  type_bound "min" (IntT 256) = SOME (-&(2 ** 255)) ∧
  type_bound "max" BoolT = NONE ∧
  type_bound "interfaceId" (UintT 8) = NONE
Proof
  EVAL_TAC
QED

(* Libraries: only internal functions, attached through a library name, with a
 * receiver that is not copied, are imported; library functions are plain
 * functions.
 *)

val using_fixture = "../testdata/differential/expected/using_for.json"
val using_source = "testdata/differential/using_for.sol"
val using_ast = artifact_part using_fixture ["sources", using_source, "ast"]
val using_contracts = artifact_part using_fixture ["contracts", using_source]

(* A virtual modifier rejects the unit, like a function header would: only a
 * modifier's body failing import is confined to the functions using it. *)
val () =
  (import_source_unit []
     (edit_first "ModifierDefinition" (set_field "virtual" (JSON.BOOL true))
        using_ast)
     using_contracts;
   raise Fail "virtual modifier: imported")
  handle ImportError _ => ()

(* A modifier whose body fails import keeps its header, so the source check
 * still sees it (here a parameter's scope); the functions invoking it are
 * unsupported. *)
fun failed_modifier_body v =
  edit_first "ModifierDefinition"
    (edit_first "ExpressionStatement"
       (set_field "nodeType" (JSON.STRING "UnknownStatement"))) v
val () = edited_unit_with using_contracts "modifier_failed_body"
  (failed_modifier_body using_ast)
val () = edited_unit_with using_contracts "modifier_failed_body_wrong_scope"
  (failed_modifier_body
     (edit_first "ModifierDefinition"
        (edit_first "VariableDeclaration"
           (set_field "scope" (JSON.INT 999999))) using_ast))

Definition using_unit_def:
  using_unit = ^(import_artifact using_fixture using_source)
End

val () = cv_auto_trans using_unit_def;

(* The library functions the contract reaches, and only those: Arith.triple,
 * which only a super call past an interface's declaration reaches, but not
 * Linked's public identity, which only the overridden Hooked.hook calls. *)
Theorem using_unit_library_functions:
  MAP (λc. (c.contract_name, LENGTH c.contract_library_functions))
    using_unit.unit_contracts = [("UsingFor", 10)]
Proof
  EVAL_TAC
QED

(* Contracts of a unit may share library functions and constants, and so
 * their node ids. *)
Definition shared_library_unit_def:
  shared_library_unit =
    using_unit with unit_contracts :=
      using_unit.unit_contracts ++ using_unit.unit_contracts
End

val () = cv_auto_trans shared_library_unit_def;

fun named ty name v =
  is_node ty v andalso
  JSONUtil.testField "name" (fn JSON.STRING s => s = name | _ => false) v

val () = import_error_with Unsupported using_contracts "public library function"
  (edit_first_where (named "FunctionDefinition" "addBonus") "addBonus"
     (set_field "visibility" (JSON.STRING "public")) using_ast)
val () = import_error_with Unsupported using_contracts "file-level using with functions"
  (edit_first "UsingForDirective" (drop_field "libraryName") using_ast)
val () = import_error_with Unsupported using_contracts "contract using with functions"
  (edit_first_where
     (fn v => is_node "UsingForDirective" v andalso
              JSONUtil.testField "libraryName" (named "IdentifierPath" "Arrays") v)
     "using Arrays" (drop_field "libraryName") using_ast)
(* A compilation of two files: the library Arith moves to a file of its own,
 * whose file-level directives the contract reaches through Arith. *)
fun using_unit_split directives =
  case using_ast of
    JSON.OBJECT kvs =>
      let
        val ns = JSONUtil.arrayMap I (JSONUtil.lookupField using_ast "nodes")
        val (arith, rest) = List.partition (named "ContractDefinition" "Arith") ns
      in
        (JSON.OBJECT
           [("nodeType", JSON.STRING "SourceUnit"), ("id", JSON.INT 999990),
            ("src", JSON.STRING "0:0:1"), ("absolutePath", JSON.STRING "arith.sol"),
            ("nodes", JSON.ARRAY (arith @ directives))],
         JSON.OBJECT
           (map (fn ("nodes", _) => ("nodes", JSON.ARRAY rest) | kv => kv) kvs))
      end
  | _ => raise Fail "using_ast: not an object"

val using_functions_directive =
  JSON.OBJECT [("nodeType", JSON.STRING "UsingForDirective"),
               ("id", JSON.INT 999998), ("src", JSON.STRING "0:0:1"),
               ("functionList", JSON.ARRAY []), ("global", JSON.BOOL false)]

val _ =
  let val (arith_unit, rest) = using_unit_split []
  in import_source_unit [arith_unit] rest using_contracts end

val () =
  let val (arith_unit, rest) = using_unit_split [using_functions_directive]
  in
    import_units_error_with Unsupported [arith_unit] using_contracts
      "using with functions in another file" rest
  end

val () = import_error_with Unsupported using_contracts "reached library using functions"
  (edit_first_where (named "ContractDefinition" "Arith") "Arith"
     (fn JSON.OBJECT kvs =>
           JSON.OBJECT
             (map (fn ("nodes", JSON.ARRAY ns) =>
                        ("nodes",
                         JSON.ARRAY
                           (ns @ [JSON.OBJECT
                                    [("nodeType", JSON.STRING "UsingForDirective"),
                                     ("id", JSON.INT 999998),
                                     ("src", JSON.STRING "0:0:0"),
                                     ("functionList", JSON.ARRAY []),
                                     ("global", JSON.BOOL false)]]))
                    | kv => kv) kvs)
       | v => v)
     using_ast)
val () = import_error_with UnsupportedFunction using_contracts "receiver copied to memory"
  (edit_first_where
     (fn v => is_node "MemberAccess" v andalso
              JSONUtil.testField "memberName" (fn JSON.STRING s => s = "fill" | _ => false) v)
     "xs.fill"
     (fn m => set_field "expression"
                (type_identifier "t_array$_t_uint256_$dyn_storage_ptr"
                   (JSONUtil.lookupField m "expression")) m)
     using_ast)

val () = edited_unit_with using_contracts "library_receive"
  (edit_first_where (named "FunctionDefinition" "addBonus") "addBonus"
     (set_field "kind" (JSON.STRING "receive")) using_ast)

Theorem library_receive_rejected:
  ¬valid_src_unit library_receive
Proof
  CONV_TAC cv_eval
QED

(* Contract types are read as address, so overloads that differ only in them
 * are rejected: here balanceVia(address) and a renamed same(IToken). *)

val contracts_fixture = "../testdata/differential/expected/contract_types.json"
val contracts_source = "testdata/differential/contract_types.sol"
val contracts_ast = artifact_part contracts_fixture ["sources", contracts_source, "ast"]
val contracts_contracts = artifact_part contracts_fixture ["contracts", contracts_source]

val () = import_error_with Unsupported contracts_contracts "overloads differing only in contract types"
  (edit_first_where (named "FunctionDefinition" "same") "same"
     (set_field "name" (JSON.STRING "balanceVia")) contracts_ast)

(* Selectors: only names the compiler does not evaluate may be receivers, and
 * a state variable's selector is its getter's only through this. *)

val hashes_fixture = "../testdata/differential/expected/hashes.json"
val hashes_source = "testdata/differential/hashes.sol"
val hashes_ast = artifact_part hashes_fixture ["sources", hashes_source, "ast"]
val hashes_base = artifact_part hashes_fixture ["sources", "testdata/differential/hashes_base.sol", "ast"]
val hashes_contracts = artifact_part hashes_fixture ["contracts", hashes_source]

fun member name v =
  is_node "MemberAccess" v andalso
  JSONUtil.testField "memberName" (fn JSON.STRING s => s = name | _ => false) v

fun declaration_id ty name v =
  let
    fun find v =
      if named ty name v then SOME (JSONUtil.lookupField v "id")
      else case v of
             JSON.OBJECT kvs => List.foldl (fn ((_, x), r) => if isSome r then r else find x) NONE kvs
           | JSON.ARRAY vs => List.foldl (fn (x, r) => if isSome r then r else find x) NONE vs
           | _ => NONE
  in
    valOf (find v)
  end

fun hashes_error name v = import_units_error_with UnsupportedFunction [hashes_base] hashes_contracts name v

val _ = import_source_unit [hashes_base] hashes_ast hashes_contracts

val () = hashes_error "selector through a contract-typed value"
  (edit_first_where (named "Identifier" "IReceiver") "IReceiver"
     (type_identifier "t_contract$_IReceiver_$1") hashes_ast)

val () = hashes_error "selector of a state variable through a contract name"
  (edit_first_where (member "total") "this.total"
     (fn m => set_field "expression"
                (type_identifier "t_type$_t_contract$_Hashes_$1"
                   (set_field "referencedDeclaration" (JSON.INT 1)
                      (JSONUtil.lookupField m "expression"))) m) hashes_ast)

val () = hashes_error "selector of a state variable by name"
  (edit_first_where (named "Identifier" "Denied") "Denied"
     (set_field "referencedDeclaration"
        (declaration_id "VariableDeclaration" "total" hashes_ast)) hashes_ast)

(* Conditionals: the checker takes one whose type is a value or a memory
 * reference. The first conditional is c ? 1 : 300, typed uint16. *)

val conditionals_fixture = "../testdata/differential/expected/conditionals.json"
val conditionals_source = "testdata/differential/conditionals.sol"
val conditionals_ast = artifact_part conditionals_fixture ["sources", conditionals_source, "ast"]
val conditionals_contracts = artifact_part conditionals_fixture ["contracts", conditionals_source]

Definition conditionals_unit_def:
  conditionals_unit = ^(import_artifact conditionals_fixture conditionals_source)
End

val () = cv_auto_trans conditionals_unit_def;

val () = edited_unit_with conditionals_contracts "storage_conditional"
  (edit_first "Conditional" (type_identifier "t_bytes_storage_ptr") conditionals_ast)

(* a storage bytes variable's own type, which decodes unlocated *)
val () = edited_unit_with conditionals_contracts "stored_bytes_conditional"
  (edit_first "Conditional" (type_identifier "t_bytes_storage") conditionals_ast)

val () = edited_unit_with conditionals_contracts "tuple_conditional"
  (edit_first "Conditional" (type_identifier "t_tuple$_t_uint16_$_t_uint16_$") conditionals_ast)

val () = edited_unit_with conditionals_contracts "calldata_conditional"
  (edit_first "Conditional" (type_identifier "t_bytes_calldata_ptr") conditionals_ast)

val () = edited_unit_with conditionals_contracts "function_conditional"
  (edit_first "Conditional" (type_identifier "t_function_internal_pure$__$returns$__$") conditionals_ast)

(* abi.encodeCall leaves out its receiver's read, which a constant's would
 * not be: the compiler evaluates its initializer, which may fail. So a
 * function encoding a call through a constant receiver is unsupported. *)

val encode_calls_fixture = "../testdata/differential/expected/encode_calls.json"
val encode_calls_source = "testdata/differential/encode_calls.sol"
val encode_calls_ast = artifact_part encode_calls_fixture ["sources", encode_calls_source, "ast"]
val encode_calls_contracts = artifact_part encode_calls_fixture ["contracts", encode_calls_source]

val _ = import_source_unit [] encode_calls_ast encode_calls_contracts

(* token made a constant, initialized by a literal of the fixture. *)
val encode_calls_literal =
  let
    val found = ref NONE
    val _ = edit_first_where (is_node "Literal") "Literal"
              (fn v => (found := SOME v; v)) encode_calls_ast
  in
    valOf (!found)
  end

fun make_constant (JSON.OBJECT kvs) =
      set_field "constant" (JSON.BOOL true)
        (JSON.OBJECT (kvs @ [("value", encode_calls_literal)]))
  | make_constant v = v

val () =
  case import_rejection []
         (edit_first_where (named "VariableDeclaration" "token") "token"
            make_constant encode_calls_ast)
         encode_calls_contracts of
    NONE => raise Fail "encodeCall through a constant: imported"
  | SOME (UnsupportedFunction, msg) =>
      if String.isSubstring "constant receiver" msg then ()
      else raise Fail ("encodeCall through a constant: " ^ msg)
  | SOME (actual, msg) =>
      raise Fail ("encodeCall through a constant: expected unsupported " ^
                  "function, got " ^ failure_name actual ^ ": " ^ msg)

(* Constants: a number literal initializes a bytes32 constant. *)

val bytes_constants_fixture = "../testdata/differential/expected/bytes_constants.json"
val bytes_constants_source = "testdata/differential/bytes_constants.sol"
val bytes_constants_ast =
  artifact_part bytes_constants_fixture ["sources", bytes_constants_source, "ast"]
val bytes_constants_contracts =
  artifact_part bytes_constants_fixture ["contracts", bytes_constants_source]

Definition bytes_constants_unit_def:
  bytes_constants_unit = ^(import_artifact bytes_constants_fixture bytes_constants_source)
End

val () = cv_auto_trans bytes_constants_unit_def;

