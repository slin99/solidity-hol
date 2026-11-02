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
  "../testdata/differential/expected/inheritance.json"
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
  normalize_type_name (SrcElementaryTypeName i "bytes" NONE) = NONE ∧
  normalize_type_name (SrcElementaryTypeName i "string" NONE) = NONE ∧
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
  decode_type_identifier "t_address_payable" =
    SOME (SrcType (AddressT PayableAddress)) ∧
  decode_type_identifier "t_uint7" = NONE ∧
  decode_type_identifier "t_uint" = NONE ∧
  decode_type_identifier "t_string_memory_ptr" = NONE ∧
  decode_type_identifier "t_bytes_memory_ptr" = NONE
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

fun edit_first ty f v =
  let
    val edited = ref false
    fun go v =
      if !edited then v
      else case v of
             JSON.OBJECT kvs =>
               if is_node ty v then (edited := true; f v)
               else JSON.OBJECT (map (fn (k, x) => (k, go x)) kvs)
           | JSON.ARRAY vs => JSON.ARRAY (map go vs)
           | _ => v
    val result = go v
  in
    if !edited then result else raise Fail ("no " ^ ty ^ " node")
  end

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

datatype import_failure = Unsupported | Malformed

fun import_error_with expected contracts name v =
  (import_source_unit v contracts; raise Fail (name ^ ": imported"))
  handle ImportError _ =>
           if expected = Unsupported then () else raise Fail (name ^ ": expected malformed input")
       | MalformedInput _ =>
           if expected = Malformed then () else raise Fail (name ^ ": expected unsupported input")

val import_error = import_error_with Unsupported contracts
val malformed_input = import_error_with Malformed contracts

(* An edited unit that imports, as a cv-translated constant. *)
fun edited_unit_with contracts name v =
  let
    val tm = import_source_unit v contracts
    val def = new_definition (name ^ "_def", mk_eq (mk_var (name, type_of tm), tm))
  in
    cv_auto_trans def
  end

val edited_unit = edited_unit_with contracts

(* Unknown forms, missing annotations and unsupported features fail import. *)

val () = import_error "unknown statement"
  (edit_first "Break" (set_field "nodeType" (JSON.STRING "InlineAssembly")) ast)
val () = import_error "unknown expression"
  (edit_first "Literal" (set_field "nodeType" (JSON.STRING "Conditional")) ast)
val () = malformed_input "missing type annotation"
  (edit_first "Identifier" (drop_field "typeDescriptions") ast)
val () = malformed_input "missing declaration reference"
  (edit_first "Identifier" (drop_field "referencedDeclaration") ast)
val () = malformed_input "missing common type"
  (edit_first "BinaryOperation" (drop_field "commonType") ast)
val () = malformed_input "function as state variable"
  (edit_first "FunctionDefinition"
     (set_field "nodeType" (JSON.STRING "VariableDeclaration")) ast)
val () = import_error "modifier"
  (edit_first "FunctionDefinition"
     (set_field "modifiers"
        (JSON.ARRAY [JSON.OBJECT [("kind", JSON.STRING "modifierInvocation")]]))
     ast)
val () = import_error "named arguments"
  (edit_first "FunctionCall"
     (set_field "names" (JSON.ARRAY [JSON.STRING "n"])) ast)
val () = import_error "base outside the unit"
  (edit_first "ContractDefinition"
     (fn c => set_field "linearizedBaseContracts"
                (JSON.ARRAY [JSONUtil.lookupField c "id", JSON.INT 999999]) c)
     ast)

(* Builtin references outside call position remain unsupported; the rejection
 * names the identifier's node.
 *)
val () =
  (import_source_unit
     (edit_first "Identifier"
        (set_field "referencedDeclaration" (JSON.INT ~18)) ast) contracts;
   raise Fail "built-in: imported")
  handle ImportError msg =>
    if String.isPrefix "Identifier " msg andalso
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

(* The first call is fact(n - 1). *)
val () = edited_unit "call_arity"
  (edit_first "FunctionCall" (set_field "arguments" (JSON.ARRAY [])) ast)

Theorem duplicate_id_rejected:
  ¬valid_src_unit duplicate_id
Proof
  CONV_TAC cv_eval
QED

Theorem dangling_reference_rejected:
  ¬valid_src_unit dangling_reference
Proof
  CONV_TAC cv_eval
QED

Theorem identifier_type_mismatch_rejected:
  ¬valid_src_unit identifier_type_mismatch
Proof
  CONV_TAC cv_eval
QED

Theorem function_as_value_rejected:
  ¬valid_src_unit function_as_value
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

Theorem unlinked_declaration_rejected:
  ¬valid_src_unit unlinked_declaration
Proof
  CONV_TAC cv_eval
QED

Theorem call_arity_rejected:
  ¬valid_src_unit call_arity
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

Theorem storage_unit_valid:
  valid_src_unit storage_unit
Proof
  CONV_TAC cv_eval
QED

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

(* The first variable declaration is the state variable total. *)
val () = import_error_with Unsupported storage_contracts "public state variable"
  (edit_first "VariableDeclaration"
     (set_field "visibility" (JSON.STRING "public")) storage_ast)
val () = import_error_with Unsupported storage_contracts "constant state variable"
  (edit_first "VariableDeclaration" (set_field "constant" (JSON.BOOL true))
     storage_ast)
val () = import_error_with Unsupported storage_contracts "immutable state variable"
  (edit_first "VariableDeclaration"
     (set_field "mutability" (JSON.STRING "immutable")) storage_ast)
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

Theorem pure_writes_state_rejected:
  ¬valid_src_unit pure_writes_state
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

Theorem mapping_unit_valid:
  valid_src_unit mapping_unit
Proof
  CONV_TAC cv_eval
QED

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

Theorem mapping_leaf_metadata_rejected:
  ¬valid_src_unit mapping_leaf_metadata_mismatch
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
  (import_source_unit
     (edit_first "IndexAccess" (set_field "indexExpression" JSON.NULL) array_ast)
     array_contracts;
   raise Fail "array type expression imported")
  handle ImportError _ => ();

Definition array_unit_def:
  array_unit = ^(import_artifact array_fixture array_source)
End
val () = cv_auto_trans array_unit_def;

Theorem array_unit_valid:
  valid_src_unit array_unit
Proof
  CONV_TAC cv_eval
QED

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

Theorem array_leaf_metadata_rejected:
  ¬valid_src_unit array_leaf_mismatch
Proof
  CONV_TAC cv_eval
QED

Definition dynamic_array_unit_def:
  dynamic_array_unit =
    ^(import_artifact "../testdata/differential/expected/dynamic_storage_arrays.json"
                      "testdata/differential/dynamic_storage_arrays.sol")
End
val () = cv_auto_trans dynamic_array_unit_def;

Theorem dynamic_array_unit_valid:
  valid_src_unit dynamic_array_unit
Proof
  CONV_TAC cv_eval
QED

(* Builtin identity is solc's declaration reference; spelling is diagnostic. *)
val builtins_fixture = "../testdata/differential/expected/builtins.json"
val builtins_source = "testdata/differential/builtins.sol"
val builtins_ast = artifact_part builtins_fixture ["sources", builtins_source, "ast"]
val builtins_contracts = artifact_part builtins_fixture ["contracts", builtins_source]

Definition builtins_unit_def:
  builtins_unit = ^(import_artifact builtins_fixture builtins_source)
End

val () = cv_auto_trans builtins_unit_def;

Theorem builtins_unit_valid:
  valid_src_unit builtins_unit
Proof
  CONV_TAC cv_eval
QED

fun edit_callee f = edit_first "FunctionCall" (fn call =>
  set_field "expression" (f (JSONUtil.lookupField call "expression")) call)

val () = edited_unit_with builtins_contracts "renamed_builtin"
  (edit_callee (set_field "name" (JSON.STRING "assert")) builtins_ast)

Theorem renamed_builtin_valid:
  valid_src_unit renamed_builtin
Proof
  CONV_TAC cv_eval
QED

val () = import_error_with Unsupported builtins_contracts "unknown builtin declaration"
  (edit_callee (set_field "referencedDeclaration" (JSON.INT ~999)) builtins_ast)

(* A nonliteral message must not be silently ignored on success. *)
val () = edited_unit_with builtins_contracts "nonliteral_builtin_message"
  (edit_first "FunctionCall" (fn call =>
     set_field "arguments" (JSON.ARRAY
       [hd (JSONUtil.arrayMap I (JSONUtil.lookupField call "arguments")),
        set_field "id" (JSON.INT 999999)
          (hd (JSONUtil.arrayMap I (JSONUtil.lookupField call "arguments")))]) call)
     builtins_ast)

Theorem nonliteral_builtin_message_rejected:
  ¬valid_src_unit nonliteral_builtin_message
Proof
  CONV_TAC cv_eval
QED

val struct_fixture = "../testdata/differential/expected/storage_structs.json"
val struct_source = "testdata/differential/storage_structs.sol"
val struct_ast = artifact_part struct_fixture ["sources", struct_source, "ast"]
val struct_contracts = artifact_part struct_fixture ["contracts", struct_source]

Definition struct_unit_def:
  struct_unit = ^(import_artifact struct_fixture struct_source)
End
val () = cv_auto_trans struct_unit_def;

Theorem struct_unit_valid:
  valid_src_unit struct_unit
Proof
  CONV_TAC cv_eval
QED

val () = edited_unit_with struct_contracts "struct_type_identity_mismatch"
  (edit_first "UserDefinedTypeName"
    (set_field "referencedDeclaration" (JSON.INT 999999)) struct_ast)

val () = edited_unit_with struct_contracts "struct_field_identity_mismatch"
  (edit_first "MemberAccess"
    (set_field "referencedDeclaration" (JSON.INT 999999)) struct_ast)

val () = edited_unit_with struct_contracts "struct_field_type_mismatch"
  (edit_first "MemberAccess" (type_identifier "t_uint16") struct_ast)

Theorem struct_identities_checked:
  ¬valid_src_unit struct_type_identity_mismatch ∧
  ¬valid_src_unit struct_field_identity_mismatch ∧
  ¬valid_src_unit struct_field_type_mismatch
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

Theorem inheritance_unit_valid:
  valid_src_unit inheritance_unit
Proof
  CONV_TAC cv_eval
QED

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

Theorem unresolved_override_rejected:
  ¬valid_src_unit unresolved_override
Proof
  CONV_TAC cv_eval
QED
