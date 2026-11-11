structure solidityImportLib :> solidityImportLib =
struct

open HolKernel boolLib solidityImportTheory

exception ImportError of string
exception MalformedInput of string

fun fail msg = raise ImportError msg

(* JSON access, with JSONUtil errors reported against the enclosing node. *)

val field = JSONUtil.lookupField
fun string_field v k = JSONUtil.asString (field v k)
fun bool_field v k = JSONUtil.asBool (field v k)
fun int_field v k = JSONUtil.asIntInf (field v k)
fun object (JSON.OBJECT fields) = fields
  | object v = raise JSONUtil.JSONError (JSONUtil.NotObject, v)

(* An optional field: absent or null. *)
fun optional_field v k =
  case JSONUtil.findField v k of
    NONE => NONE
  | SOME JSON.NULL => NONE
  | SOME x => SOME x

fun node_type v = string_field v "nodeType"

fun describe v =
  (node_type v handle _ => "node") ^
  (case JSONUtil.findField v "id" handle _ => NONE of
     SOME (JSON.INT i) => " " ^ IntInf.toString i
   | _ => "")

fun within v f =
  f v
  handle ImportError msg => raise ImportError msg
       | e as JSONUtil.JSONError _ => raise MalformedInput (describe v ^ ": " ^ JSONUtil.exnMessage e)
       | e as JSONUtil.FieldNotFound _ => raise MalformedInput (describe v ^ ": " ^ JSONUtil.exnMessage e)
       | e as JSONUtil.NotObject => raise MalformedInput (describe v ^ ": " ^ JSONUtil.exnMessage e)
       | e as JSONUtil.NotArray => raise MalformedInput (describe v ^ ": " ^ JSONUtil.exnMessage e)

fun require v cond msg = if cond then () else fail (describe v ^ ": " ^ msg)

fun expect v ty = require v (node_type v = ty) ("expected " ^ ty)

(* Blockers: the reasons, one per line, of the nodes the importer cannot
 * represent, of the function or modifier being imported, or else of the
 * unit. Each line names its node ("Literal 12: why"); a reason that does not
 * is put after the name of the node it was raised for. *)
val blockers : string list ref = ref []

(* Record the reason msg, raised for v, and return it as recorded. *)
fun note v msg =
  let
    val lines =
      map (fn l => if String.isSubstring ": " l then l else describe v ^ ": " ^ l)
        (String.fields (fn c => c = #"\n") msg)
  in
    blockers := !blockers @ lines;
    String.concatWith "\n" lines
  end

(* f (), with an ImportError it raises recorded against v. *)
fun recover v f = f () handle ImportError msg => ignore (note v msg)

(* f v, or NONE with the ImportError recorded: an item the importer cannot
 * represent is left out. *)
fun keep f v = SOME (f v) handle ImportError msg => (ignore (note v msg); NONE)
fun keep_all f vs = List.mapPartial (keep f) vs

(* f () and the blockers it records, apart from the current ones. Should f
 * raise, its blockers join the current ones. *)
fun with_blockers f =
  let val outer = !blockers in
    (blockers := [];
     (f (), !blockers) before blockers := outer)
    handle e => (blockers := outer @ !blockers; raise e)
  end

(* Terms *)

fun mk_num i =
  if i < 0 then fail ("negative number " ^ IntInf.toString i)
  else numSyntax.mk_numeral (Arbnum.fromString (IntInf.toString i))

val mk_str = stringSyntax.fromMLstring

fun mk_opt ty NONE = optionSyntax.mk_none ty
  | mk_opt _ (SOME tm) = optionSyntax.mk_some tm

fun import_type name = mk_thy_type {Thy = "solidityImport", Tyop = name, Args = []}
val expr_ty = import_type "src_expr"
val type_name_ty = import_type "src_type_name"
val stmt_ty = import_type "src_stmt"
val variable_ty = import_type "src_variable"
val function_ty = import_type "src_function"
val contract_ty = import_type "src_contract"
val struct_ty = import_type "src_struct"
val storage_entry_ty = import_type "src_storage_entry"
val event_ty = import_type "src_event"

fun con name args =
  list_mk_comb (prim_mk_const {Thy = "solidityImport", Name = name}, args)

fun record name fields = TypeBase.mk_record (import_type name, fields)

fun mk_bool b = if b then T else F

(* The constant table gives the compiler's string s, read as what. *)
fun decode v what table s =
  case List.find (fn (k, _) => k = s) table of
    SOME (_, tm) => tm
  | NONE => fail (describe v ^ ": unsupported " ^ what ^ " " ^ s)

fun constants thy table =
  map (fn (s, name) => (s, prim_mk_const {Thy = thy, Name = name})) table

val mutabilities = constants "solidityAST"
  [("pure", "PureMut"), ("view", "ViewMut"), ("nonpayable", "NonpayableMut"),
   ("payable", "PayableMut")]

val payabilities = constants "solidityAST"
  [("nonpayable", "NonpayableAddress"), ("payable", "PayableAddress")]

val locations = constants "solidityAST"
  [("storage", "StorageLoc"), ("memory", "MemoryLoc"), ("calldata", "CalldataLoc")]

val function_kinds = constants "solidityImport"
  [("function", "FunctionKind"), ("freeFunction", "FunctionKind"),
   ("constructor", "ConstructorKind"),
   ("receive", "ReceiveKind"), ("fallback", "FallbackKind")]

val visibilities = constants "solidityImport"
  [("public", "PublicVisibility"), ("external", "ExternalVisibility"),
   ("internal", "InternalVisibility"), ("private", "PrivateVisibility")]

val literal_kinds = constants "solidityImport"
  [("number", "NumberLiteral"), ("bool", "BoolLiteral"), ("string", "StringLiteral"),
   ("unicodeString", "UnicodeStringLiteral"), ("hexString", "HexStringLiteral")]

val unary_operators = constants "solidityImport"
  [("++", "SrcIncrement"), ("--", "SrcDecrement"), ("-", "SrcNegate"), ("!", "SrcNot"),
   ("~", "SrcBitNot"), ("delete", "SrcDelete")]

val binary_operators = constants "solidityImport"
  [("+", "SrcAdd"), ("-", "SrcSub"), ("*", "SrcMul"), ("/", "SrcDiv"), ("%", "SrcMod"),
   ("**", "SrcExp"), ("<<", "SrcShl"), (">>", "SrcShr"), ("&", "SrcBitAnd"),
   ("|", "SrcBitOr"), ("^", "SrcBitXor"), ("==", "SrcEq"), ("!=", "SrcNe"),
   ("<", "SrcLt"), ("<=", "SrcLe"), (">", "SrcGt"), (">=", "SrcGe"), ("&&", "SrcAnd"),
   ("||", "SrcOr")]

val binary_operator_ty = import_type "src_binary_operator"

(* "=" or a compound assignment "op=" *)
val assignment_operators =
  ("=", optionSyntax.mk_none binary_operator_ty) ::
  map (fn (s, tm) => (s ^ "=", optionSyntax.mk_some tm))
      (List.filter (fn (s, _) => List.exists (fn k => k = s)
                      ["+", "-", "*", "/", "%", "<<", ">>", "&", "|", "^"])
         binary_operators)

(* The declaration ids the pinned compiler gives its built-ins. *)
val abi_id : IntInf.int = ~1
val addmod_id : IntInf.int = ~2
val assert_id : IntInf.int = ~3
val block_id : IntInf.int = ~4
val ecrecover_id : IntInf.int = ~6
val keccak256_id : IntInf.int = ~8
val msg_id : IntInf.int = ~15
val mulmod_id : IntInf.int = ~16
val require_id : IntInf.int = ~18
val revert_id : IntInf.int = ~19
val tx_id : IntInf.int = ~26
val this_id : IntInf.int = ~28

(* The bytes of a hex string without prefix. *)
fun hex_bytes v hex =
  let
    fun digit c =
      if c >= #"0" andalso c <= #"9" then Char.ord c - 48
      else if c >= #"a" andalso c <= #"f" then Char.ord c - 87
      else if c >= #"A" andalso c <= #"F" then Char.ord c - 55
      else fail (describe v ^ ": invalid hex string " ^ hex)
    val () = require v (size hex mod 2 = 0) ("odd hex string length " ^ hex)
  in
    List.tabulate (size hex div 2, fn i =>
      16 * digit (String.sub (hex, 2*i)) + digit (String.sub (hex, 2*i+1)))
  end

fun mk_bytes v hex =
  listSyntax.mk_list
    (map (fn b => wordsSyntax.mk_wordii (b, 8)) (hex_bytes v hex),
     wordsSyntax.mk_int_word_type 8)

(* The members of msg, tx and block, by the built-in declaration ids of the
 * pinned compiler. *)
fun environment_field v base member =
  let
    val fields =
      [((msg_id, "sender"), "MsgSender"), ((msg_id, "value"), "MsgValue"),
       ((msg_id, "data"), "MsgData"), ((tx_id, "origin"), "TxOrigin"),
       ((tx_id, "gasprice"), "TxGasPrice"), ((block_id, "number"), "BlockNumber"),
       ((block_id, "timestamp"), "BlockTimestamp"), ((block_id, "chainid"), "BlockChainId"),
       ((block_id, "coinbase"), "BlockCoinbase"), ((block_id, "basefee"), "BlockBaseFee"),
       ((block_id, "gaslimit"), "BlockGasLimit")]
  in
    case List.find (fn (k, _) => k = (base, member)) fields of
      SOME (_, name) => prim_mk_const {Thy = "solidityCore", Name = name}
    | NONE => fail (describe v ^ ": unsupported built-in member " ^ member)
  end

fun builtin_identifier v id =
  node_type v = "Identifier" andalso int_field v "referencedDeclaration" = id

(* "start:length:source" *)
fun location v =
  case String.fields (fn c => c = #":") (string_field v "src") of
    [s, l, f] =>
      (case (IntInf.fromString s, IntInf.fromString l, IntInf.fromString f) of
         (SOME s, SOME l, SOME f) =>
           record "src_location"
             [("loc_start", mk_num s), ("loc_length", mk_num l),
              ("loc_source", mk_num f)]
       | _ => fail (describe v ^ ": malformed src"))
  | _ => fail (describe v ^ ": malformed src")

fun info v =
  record "node_info"
    [("node_id", mk_num (int_field v "id")), ("node_location", location v)]

val compilation_max_id : IntInf.int ref = ref 0

fun greatest_node_id (JSON.OBJECT fields) =
      List.foldl (fn (("id", JSON.INT i), n) => IntInf.max (i, n)
                   | ((_, v), n) => IntInf.max (greatest_node_id v, n)) 0 fields
  | greatest_node_id (JSON.ARRAY vs) =
      List.foldl (fn (v, n) => IntInf.max (greatest_node_id v, n)) 0 vs
  | greatest_node_id _ = 0

(* Placeholders. The expressions and statements imported directly under the
 * node being imported, kept by its placeholder if it turns out unsupported:
 * a node imports its children before its own checks, so that their blockers
 * are recorded too. *)
datatype child = ExprChild of term | StmtChild of term
val children : child list ref = ref []

(* import v, or, when it raises ImportError, v's placeholder with the
 * recorded reason and the children imported so far; wrap says what the
 * result is as a child of v's parent. *)
fun guarded wrap placeholder import v =
  let val outer = !children in
    (children := [];
     let
       val result =
         import v handle ImportError msg => placeholder v (note v msg) (!children)
     in
       children := outer @ wrap result; result
     end)
    handle e => (children := outer; raise e)
  end

fun child_exprs cs =
  listSyntax.mk_list
    (List.mapPartial (fn ExprChild e => SOME e | _ => NONE) cs, expr_ty)

fun child_stmts cs =
  listSyntax.mk_list
    (List.mapPartial (fn StmtChild st => SOME st | _ => NONE) cs, stmt_ty)

fun unsupported_type_name v reason _ =
  con "SrcUnsupportedTypeName" [info v, mk_str reason]
fun unsupported_expr v reason cs =
  con "SrcUnsupportedExpr" [info v, mk_str reason, child_exprs cs]
fun unsupported_stmt v reason cs =
  con "SrcUnsupportedStmt" [info v, mk_str reason, child_exprs cs, child_stmts cs]

val value_type_declarations : (IntInf.int * JSON.value) list ref = ref []

fun value_type_underlying id =
  case List.find (fn (i, _) => i = id) (!value_type_declarations) of
    SOME (_, d) => field d "underlyingType"
  | NONE => fail ("unknown user-defined value type " ^ IntInf.toString id)

fun raw_type_id v = string_field (field v "typeDescriptions") "typeIdentifier"

(* Use a declaration's elementary type at the use's own source node. *)
fun type_at v ty =
  JSON.OBJECT (map (fn ("id", _) => ("id", field v "id")
                    | ("src", _) => ("src", field v "src")
                    | kv => kv) (object ty))

(* A contract or interface type is an address at run time, stored and ABI
 * encoded as one: its type identifier, t_contract$_C_$n in the AST and
 * t_contract(C)n in a storage layout, is read as t_address. An enum's,
 * t_enum$_E_$n or t_enum(E)n, is read as t_enum_n, which names the enum by
 * its id alone. UDVTs are their elementary underlying types, including
 * inside array, mapping and tuple identifiers. *)
fun normalize_type_id s =
  let
    val n = size s
    fun at i p = String.isPrefix p (String.extract (s, i, NONE))
    fun digits i =
      if i < n andalso Char.isDigit (String.sub (s, i)) then digits (i + 1) else i
    (* The id ending "C_$n", where a "$" in C is escaped as "$$$". *)
    fun name_id i =
      if i + 2 >= n then fail ("malformed type identifier " ^ s)
      else if at i "_$" andalso Char.isDigit (String.sub (s, i + 2))
      then (i + 2, digits (i + 2))
      else name_id (i + 1)
    fun paren_id i =
      if i >= n then fail ("malformed type identifier " ^ s)
      else if String.sub (s, i) = #")" then (i + 1, digits (i + 1))
      else paren_id (i + 1)
    fun id (start, stop) = String.substring (s, start, stop - start)
    fun underlying r =
      case IntInf.fromString (id r) of
        SOME i => raw_type_id (value_type_underlying i)
      | NONE => fail ("malformed type identifier " ^ s)
    fun go i acc =
      if i >= n then String.concat (rev acc)
      else if at i "t_contract$_" then go (#2 (name_id (i + 12))) ("t_address" :: acc)
      else if at i "t_contract(" then go (#2 (paren_id (i + 11))) ("t_address" :: acc)
      else if at i "t_enum$_" then
        let val r = name_id (i + 8) in go (#2 r) (("t_enum_" ^ id r) :: acc) end
      else if at i "t_enum(" then
        let val r = paren_id (i + 7) in go (#2 r) (("t_enum_" ^ id r) :: acc) end
      else if at i "t_userDefinedValueType$_" then
        let val r = name_id (i + 24) in go (#2 r) (underlying r :: acc) end
      else if at i "t_userDefinedValueType(" then
        let val r = paren_id (i + 23) in go (#2 r) (underlying r :: acc) end
      else if at i "_calldata_ptr_slice" then go (i + 19) ("_calldata_ptr" :: acc)
      else go (i + 1) (String.str (String.sub (s, i)) :: acc)
  in
    go 0 []
  end

fun type_id v = mk_str (normalize_type_id (raw_type_id v))

fun address_type_name v =
  con "SrcElementaryTypeName"
    [info v, mk_str "address",
     optionSyntax.mk_some (decode v "address mutability" payabilities "nonpayable")]

(* Type names *)

fun type_name v = guarded (fn _ => []) unsupported_type_name (fn v => within v (fn v =>
  case node_type v of
    "UserDefinedTypeName" =>
      let
        val declaration = int_field v "referencedDeclaration"
        val tid = raw_type_id v
      in
        if String.isPrefix "t_contract$_" tid then address_type_name v
        else if String.isPrefix "t_enum$_" tid then
          con "SrcEnumTypeName" [info v, mk_num declaration]
        else if String.isPrefix "t_userDefinedValueType$_" tid then
          let val ty = value_type_underlying declaration in
            require v (String.isSuffix ("_$" ^ IntInf.toString declaration) tid)
              "user-defined value type annotation mismatch";
            type_name (type_at v ty)
          end
        else
          (require v (declaration >= 0 andalso String.isPrefix "t_struct$_" tid)
             "only struct user-defined types are supported";
           con "SrcStructTypeName" [info v, mk_num declaration, mk_str tid])
      end
  | "Mapping" => con "SrcMappingTypeName"
      [info v, type_name (field v "keyType"), type_name (field v "valueType")]
  | "ElementaryTypeName" =>
      let
        val name = string_field v "name"
        (* solc omits this on address keys and conversion type names. *)
        val mutability =
          case optional_field v "stateMutability" of
            SOME m => SOME (JSONUtil.asString m)
          | NONE => if name = "address" then SOME "nonpayable" else NONE
      in
        con "SrcElementaryTypeName"
          [info v, mk_str name,
           mk_opt (mk_thy_type {Thy = "solidityAST", Tyop = "address_payability", Args = []})
             (Option.map (decode v "address mutability" payabilities) mutability)]
      end
  | "ArrayTypeName" =>
      (case optional_field v "length" of
         NONE => con "SrcDynamicArrayTypeName" [info v, type_name (field v "baseType")]
       | SOME length => let
        val base = type_name (field v "baseType")
        val dimension =
          case String.fields (fn c => c = #"_")
                 (string_field (field length "typeDescriptions") "typeIdentifier") of
            ["t", "rational", n, "by", "1"] =>
              if size n > 0 andalso CharVector.all Char.isDigit n
              then IntInf.fromString n else NONE
          | _ => NONE
        val n = case dimension of
                  SOME n => if n > 0 then n else fail "nonpositive array length"
                | NONE => fail (describe v ^ ": array length is not a positive integer constant")
      in
        con "SrcArrayTypeName" [info v, base, mk_num n]
      end)
  | other => fail (describe v ^ ": unsupported type name " ^ other))) v

(* Declarations *)

fun variable_record v =
  record "src_variable"
    [("var_info", info v), ("var_name", mk_str (string_field v "name")),
     ("var_scope", mk_num (int_field v "scope")),
     ("var_type_name", type_name (field v "typeName")),
     ("var_type_id", type_id v),
     ("var_location",
      case string_field v "storageLocation" of
        "default" => mk_opt (mk_thy_type {Thy = "solidityAST", Tyop = "data_location", Args = []}) NONE
      | l => optionSyntax.mk_some (decode v "storage location" locations l))]

(* A local, parameter or return variable, or, given state, a state variable
 * or an immutable. *)
fun declaration state v = within v (fn v =>
  let
    val () = expect v "VariableDeclaration"
    val imported = variable_record v
  in
    recover v (fn () =>
      (require v (not (bool_field v "constant")) "constants are not supported";
       require v (bool_field v "stateVariable" = state)
         (if state then "expected a state variable"
          else "expected a local variable");
       require v (string_field v "mutability" = "mutable" orelse
                  state andalso string_field v "mutability" = "immutable")
         "immutable variables are not supported";
       require v (state orelse not (isSome (optional_field v "value")))
         "declaration values are not supported";
       require v (not (isSome (optional_field v "overrides")))
         "overriding state variables are not supported"));
    imported
  end)

val variable = declaration false


fun parameter_list v = within v (fn v =>
  (expect v "ParameterList";
   (mk_num (int_field v "id"),
    listSyntax.mk_list
      (JSONUtil.arrayMap variable (field v "parameters"), variable_ty))))

(* The function declarations of the compilation, by id: the targets
 * of high-level calls. *)
val function_declarations : (IntInf.int * JSON.value) list ref = ref []

fun function_declaration v id =
  case List.find (fn (i, _) => i = id) (!function_declarations) of
    SOME (_, d) => d
  | NONE => fail (describe v ^ ": calls only functions declared in the compilation")

(* The error declarations of the compilation, by id: the errors revert
 * statements name. *)
val error_declarations : (IntInf.int * JSON.value) list ref = ref []

(* The error a revert statement names. *)
fun error_declaration v id =
  case List.find (fn (i, _) => i = id) (!error_declarations) of
    SOME (_, d) =>
      within d (fn d =>
        record "src_error"
          [("error_selector", mk_bytes d (string_field d "errorSelector")),
           ("error_parameters", #2 (parameter_list (field d "parameters")))])
  | NONE => fail (describe v ^ ": reverts only with errors declared in the compilation")

(* A call of an external function of a contract or interface value. *)
fun is_external_call callee =
  node_type callee = "MemberAccess" andalso
  String.isPrefix "t_function_external_"
    (string_field (field callee "typeDescriptions") "typeIdentifier")

(* a.call, a.staticcall or a.delegatecall, as a callee: the address member,
 * not a function attached to addresses by using for. Its low_level_kind. *)
fun low_level_kind callee =
  if node_type callee = "MemberAccess" andalso
     not (isSome (optional_field callee "referencedDeclaration")) andalso
     List.exists (fn t => t = raw_type_id (field callee "expression"))
       ["t_address", "t_address_payable"]
  then
    case string_field callee "memberName" of
      "call" => SOME "LowLevelCall"
    | "staticcall" => SOME "LowLevelStaticCall"
    | "delegatecall" => SOME "LowLevelDelegateCall"
    | _ => NONE
  else NONE

(* The function a callee with call options {...} applies them to. *)
fun options_target callee =
  if node_type callee = "FunctionCallOptions" then field callee "expression"
  else callee

val call_option_ty = import_type "call_option"

(* bytes.concat or string.concat, as a callee: kind is "bytes" or "string". *)
fun is_concat kind callee =
  node_type callee = "MemberAccess" andalso
  String.isPrefix ("t_function_" ^ kind ^ "concat_")
    (string_field (field callee "typeDescriptions") "typeIdentifier")

(* The compiler reads address.code.length directly, without allocating bytes. *)
fun is_address_code v =
  node_type v = "MemberAccess" andalso
  not (isSome (optional_field v "referencedDeclaration")) andalso
  string_field v "memberName" = "code" andalso
  List.exists (fn ty => ty = normalize_type_id
    (string_field (field (field v "expression") "typeDescriptions") "typeIdentifier"))
    ["t_address", "t_address_payable"]

(* super.f, as a callee. *)
fun is_super_member callee =
  node_type callee = "MemberAccess" andalso
  (let val base = field callee "expression" in
     node_type base = "Identifier" andalso
     String.isPrefix "t_type$_t_super"
       (string_field (field base "typeDescriptions") "typeIdentifier")
   end)

(* The declarations the super calls of the function being imported name,
 * and whether one is being imported: super calls are admitted only in a
 * function's body and its modifier invocations' arguments. *)
val super_calls = ref ([] : IntInf.int list)
val in_function = ref false

(* The enums of the compilation, wherever declared: their ids and member
 * counts, and each member's id with its enum's id and its index. *)
val enum_declarations : (IntInf.int * int) list ref = ref []
val enum_values : (IntInf.int * (IntInf.int * int)) list ref = ref []

fun enum_value id = List.find (fn (i, _) => i = id) (!enum_values)

(* The functions, events, errors and state variables of the compilation, by
 * id, for the selectors their member accesses name. *)
val selector_declarations : (IntInf.int * JSON.value) list ref = ref []

(* The contracts of the compilation, by id, for type(I).interfaceId. *)
val contract_declarations : (IntInf.int * JSON.value) list ref = ref []

(* type(I).interfaceId: the XOR of the selectors of the functions the interface
 * declares itself, not those it inherits, nor its fallback or receive. *)
fun interface_id v id =
  let
    val c =
      case List.find (fn (i, _) => i = id) (!contract_declarations) of
        SOME (_, c) => c
      | NONE => fail (describe v ^ ": unsupported type(…) member")
    val () = require v (string_field c "contractKind" = "interface")
               "interfaceId of a non-interface"
    val selectors =
      List.mapPartial
        (fn m => if node_type m = "FunctionDefinition" andalso
                    string_field m "kind" = "function"
                 then SOME (hex_bytes m (string_field m "functionSelector"))
                 else NONE)
        (JSONUtil.arrayMap I (field c "nodes"))
    val xor = ListPair.map (fn (a, b) =>
                Word.toInt (Word.xorb (Word.fromInt a, Word.fromInt b)))
  in
    listSyntax.mk_list
      (map (fn b => wordsSyntax.mk_wordii (b, 8)) (foldl xor [0, 0, 0, 0] selectors),
       wordsSyntax.mk_int_word_type 8)
  end

(* A call's parameter order: for each parameter of the declaration id, the
 * index of the argument the call names for it; [] for a call without names.
 * The first skip parameters (a bound call's receiver) are passed
 * positionally, before the named arguments, so they keep their indices.
 * The arguments stay in the call's order, the order they are evaluated in. *)
fun argument_order call id skip =
  case JSONUtil.arrayMap JSONUtil.asString (field call "names") of
    [] => listSyntax.mk_nil numSyntax.num
  | names =>
      let
        val d = case List.find (fn (i, _) => i = id) (!selector_declarations) of
                  SOME (_, d) => d
                | NONE => fail (describe call ^
                                ": named arguments of a declaration outside the compilation")
        val params =
          List.drop
            (JSONUtil.arrayMap (fn p => string_field p "name")
               (field (field d "parameters") "parameters"), skip)
        val indexed = ListPair.zip (List.tabulate (length names, fn i => i), names)
        fun index p =
          case List.find (fn (_, n) => n = p) indexed of
            SOME (i, _) => mk_num (IntInf.fromInt (skip + i))
          | NONE => fail (describe call ^ ": no argument named " ^ p)
      in
        require call (length params = length names) "named arguments must name every parameter";
        listSyntax.mk_list
          (List.tabulate (skip, fn i => mk_num (IntInf.fromInt i)) @ map index params,
           numSyntax.num)
      end

(* Whether a node is f.selector, a member the compiler declares. *)
fun is_selector v =
  let fun is k x = case optional_field v k of SOME (JSON.STRING y) => x = y | _ => false
  in is "nodeType" "MemberAccess" andalso is "memberName" "selector" andalso
     not (isSome (optional_field v "referencedDeclaration"))
  end

(* Whether a receiver is this or a name the compiler does not evaluate: a
 * contract, interface or library name, or an imported module's, possibly
 * qualified by a module. *)
fun unevaluated_receiver r =
  let val named = String.isPrefix "t_type$_t_contract$_" (raw_type_id r) orelse
                  String.isPrefix "t_module_" (raw_type_id r)
  in
    case node_type r of
      "Identifier" => int_field r "referencedDeclaration" = this_id orelse named
    | "MemberAccess" => named andalso unevaluated_receiver (field r "expression")
    | _ => false
  end

(* f.selector, E.selector, this.f.selector, I.f.selector, this.x.selector for a
 * public state variable: the selector the compiler records on the declaration
 * the base names. In a member base, the receiver must be one the compiler does
 * not evaluate. *)
fun selector_bytes v base =
  let
    val id =
      case node_type base of
        "Identifier" => int_field base "referencedDeclaration"
      | "MemberAccess" =>
          (require v (unevaluated_receiver (field base "expression"))
             "selectors of computed values are not supported";
           case optional_field base "referencedDeclaration" of
             SOME d => JSONUtil.asIntInf d
           | NONE => fail (describe v ^ ": unsupported selector"))
      | _ => fail (describe v ^ ": selectors of computed values are not supported")
    val d =
      case List.find (fn (i, _) => i = id) (!selector_declarations) of
        SOME (_, d) => d
      | NONE => fail (describe v ^ ": unsupported selector")
    (* x.selector and C.x.selector for a variable x are the selector of the
     * function value it holds; only this.x names x's getter *)
    val () = require v (node_type d <> "VariableDeclaration" orelse
                        (node_type base = "MemberAccess" andalso
                         node_type (field base "expression") = "Identifier" andalso
                         int_field (field base "expression") "referencedDeclaration" = this_id))
               "selectors of function values are not supported"
    val key =
      case node_type d of
        "EventDefinition" => "eventSelector"
      | "ErrorDefinition" => "errorSelector"
      | _ => "functionSelector"
  in
    case optional_field d key of
      SOME _ => mk_bytes d (string_field d key)
    | NONE => fail (describe v ^ ": unsupported selector")
  end

(* The members of the libraries of the compilation, by id: their internal
 * functions and constants are imported with the contracts that use them. *)
val library_members : (IntInf.int * JSON.value) list ref = ref []

(* The using directives of the libraries of the compilation, by library id. *)
val library_directives : (IntInf.int * JSON.value) list ref = ref []

fun check_using d = within d (fn d =>
  require d (isSome (optional_field d "libraryName") orelse
             (case optional_field d "functionList" of
                SOME fs => not (null (JSONUtil.arrayMap I fs))
              | NONE => false))
    "using directive has no library or nonempty function list")

(* A named UDVT used as a type-valued expression. *)
fun value_type_expression v =
  let val tid = raw_type_id v in
    if not (String.isPrefix "t_type$_t_userDefinedValueType$_" tid) then NONE
    else
      let
        val () = require v (node_type v = "Identifier" orelse
                    (node_type v = "MemberAccess" andalso
                     unevaluated_receiver (field v "expression")))
                   "unsupported user-defined value type name"
        val id = int_field v "referencedDeclaration"
        val () = require v (String.isSuffix ("_$" ^ IntInf.toString id ^ "_$") tid)
                   "user-defined value type annotation mismatch"
      in
        SOME (String.substring (tid, 8, size tid - 10), value_type_underlying id)
      end
  end

(* The compiler resolves an overloaded operator to a pure free function.
 * Its synthetic callee has a fresh id, above every compiler node id. *)
fun operator_call v args =
  let
    val id = int_field v "function"
    val f = function_declaration v id
    val () = require v (string_field f "kind" = "freeFunction" andalso
                        string_field f "stateMutability" = "pure")
               "an overloaded operator must name a pure free function"
    fun types key = JSONUtil.arrayMap raw_type_id
      (field (field f key) "parameters")
    val tid = "t_function_internal_pure$_" ^ String.concatWith "_$_" (types "parameters") ^
              "_$returns$_" ^ String.concatWith "_$_" (types "returnParameters") ^ "_$"
    val callee_info = record "node_info"
      [("node_id", mk_num (!compilation_max_id + int_field v "id" + 1)),
       ("node_location", location v)]
  in
    con "SrcFunctionCall"
      [info v, con "SrcIdentifier"
         [callee_info, mk_str (string_field f "name"), mk_num id,
          mk_str (normalize_type_id tid)],
       listSyntax.mk_list (args, expr_ty), listSyntax.mk_nil numSyntax.num, type_id v]
  end

(* L.f or L.c, or x.f with f attached to the type of x by a using directive,
 * naming a member of library L. *)
fun is_library_member v =
  node_type v = "MemberAccess" andalso
  (case optional_field v "referencedDeclaration" of
     SOME d =>
       List.exists (fn (i, _) => i = JSONUtil.asIntInf d) (!library_members)
   | NONE => false)

fun is_attached v =
  String.isSubstring "$attached_to$"
    (string_field (field v "typeDescriptions") "typeIdentifier")

(* Whether x.f converts x from storage or calldata to memory. *)
fun copies_receiver v =
  let
    val receiver =
      string_field (field (field v "expression") "typeDescriptions") "typeIdentifier"
    val f =
      case List.find (fn (i, _) => i = int_field v "referencedDeclaration")
             (!library_members) of
        SOME (_, f) => f
      | NONE => fail (describe v ^ ": unknown library member")
    val parameter =
      case JSONUtil.arrayMap I (field (field f "parameters") "parameters") of
        p :: _ => string_field (field p "typeDescriptions") "typeIdentifier"
      | [] => fail (describe v ^ ": an attached function takes a parameter")
  in
    (List.exists (fn l => String.isSuffix l receiver)
       ["_storage", "_storage_ptr", "_calldata", "_calldata_ptr"]) andalso
    String.isSuffix "_memory_ptr" parameter
  end

(* Expressions *)

(* The kinds of expression node, whose children an unknown one imports. *)
val expression_kinds =
  ["Identifier", "MemberAccess", "Literal", "UnaryOperation", "BinaryOperation",
   "Conditional", "Assignment", "IndexAccess", "IndexRangeAccess",
   "TupleExpression", "FunctionCall"]

fun is_expression v =
  List.exists (fn k => k = node_type v) expression_kinds handle _ => false

fun expr v = guarded (fn e => [ExprChild e]) unsupported_expr (fn v => within v (fn v =>
  case node_type v of
    "Identifier" =>
      if builtin_identifier v this_id then
        (* this, the contract's own address *)
        con "SrcEnvironment"
          [info v, prim_mk_const {Thy = "solidityCore", Name = "SelfAddress"},
           type_id v]
      else
      let val declaration = int_field v "referencedDeclaration" in
        require v (declaration >= 0)
          ("built-in " ^ string_field v "name" ^ " is not supported");
        con "SrcIdentifier"
          [info v, mk_str (string_field v "name"), mk_num declaration,
           type_id v]
      end
  | "MemberAccess" =>
      (case optional_field v "referencedDeclaration" of
         SOME declaration =>
           (case enum_value (JSONUtil.asIntInf declaration) of
              SOME (_, (enum, index)) =>
                (* E.A, the enum's member at index *)
                con "SrcEnumValue"
                  [info v, con "SrcEnumTypeName" [info (field v "expression"), mk_num enum],
                   mk_num (IntInf.fromInt index), type_id v]
            | NONE =>
           if is_library_member v then
             (if is_attached v then
                (ignore (expr (field v "expression"));
                 fail (describe v ^ ": an attached function is supported only as a callee"))
              else ();
              con "SrcIdentifier"
                [info v, mk_str (string_field v "memberName"),
                 mk_num (JSONUtil.asIntInf declaration), type_id v])
           else
           con "SrcMemberAccess"
             [info v, expr (field v "expression"),
              mk_num (JSONUtil.asIntInf declaration), type_id v])
       | NONE =>
           let val base = field v "expression" in
           if node_type base = "Identifier" andalso
              int_field base "referencedDeclaration" < 0 then
             con "SrcEnvironment"
               [info v,
                environment_field v (int_field base "referencedDeclaration")
                  (string_field v "memberName"),
                type_id v]
           else if node_type base = "FunctionCall" andalso
                   node_type (field base "expression") = "Identifier" andalso
                   string_field (field base "expression") "name" = "type" andalso
                   int_field (field base "expression") "referencedDeclaration" < 0
           then
             (case JSONUtil.arrayMap I (field base "arguments") of
                [arg] =>
                  if node_type arg = "Identifier" andalso
                     string_field v "memberName" = "interfaceId" then
                    con "SrcSelector"
                      [info v, interface_id v (int_field arg "referencedDeclaration"),
                       type_id v]
                  else if String.isPrefix "t_type$_t_enum$_" (raw_type_id arg) then
                    let
                      val declaration = int_field arg "referencedDeclaration"
                      val member = string_field v "memberName"
                      val () = require v (member = "min" orelse member = "max")
                                 "unsupported enum type member"
                      val members =
                        case List.find (fn (id, _) => id = declaration) (!enum_declarations) of
                          SOME (_, n) => n
                        | NONE => fail (describe arg ^ ": unknown enum declaration")
                      val () = require v (0 < members) "empty enum declaration"
                    in
                      con "SrcEnumValue"
                        [info v, con "SrcEnumTypeName" [info arg, mk_num declaration],
                         mk_num (IntInf.fromInt (if member = "min" then 0 else members - 1)),
                         type_id v]
                    end
                  else
                  (within arg (fn a => expect a "ElementaryTypeNameExpression");
                   con "SrcTypeMember"
                     [info v, mk_str (string_field v "memberName"),
                      type_name (field arg "typeName"), type_id v])
              | _ => fail (describe v ^ ": type takes one argument"))
           else if String.isPrefix "t_struct$_"
                 (string_field (field (field v "expression") "typeDescriptions") "typeIdentifier")
            then raise MalformedInput (describe v ^ ": missing struct field declaration")
            else if string_field v "memberName" = "selector" then
              con "SrcSelector"
                [info v,
                 (* a base that is not admitted is imported for its blockers *)
                 (selector_bytes v base
                  handle ImportError msg => (ignore (expr base); raise ImportError msg)),
                 type_id v]
            else case string_field v "memberName" of
              "length" =>
                if is_address_code base then
                  con "SrcAddressCodeLength"
                    [info v, info base, expr (field base "expression"), type_id v]
                else con "SrcArrayLength" [info v, expr base, type_id v]
            | member =>
                let val receiver = expr (field v "expression") in
                  require v (member = "push" orelse member = "pop")
                    "unsupported built-in member";
                  con "SrcArrayMember" [info v, mk_str member, receiver, type_id v]
                end
           end)
  | "Literal" =>
      let
        val kind = string_field v "kind"
        val tid = raw_type_id v
        val () = case optional_field v "subdenomination" of
          NONE => ()
        | SOME unit =>
            require v (kind = "number" andalso String.isPrefix "t_rational_" tid andalso
                       List.exists (fn u => u = JSONUtil.asString unit)
                         ["wei", "gwei", "ether", "seconds", "minutes", "hours", "days", "weeks"])
              "unsupported literal subdenomination"
        val value =
          if kind = "number" andalso tid = "t_address" then
            let
              val s = string_field v "value"
              val () = require v (size s = 42 andalso String.isPrefix "0x" s)
                         "invalid address literal"
            in
              IntInf.toString
                (foldl (fn (b, n) => 256 * n + IntInf.fromInt b) 0
                  (hex_bytes v (String.extract (s, 2, NONE))))
            end
          else if List.exists (fn k => k = kind)
                       ["string", "unicodeString", "hexString"] then
            String.implode (map Char.chr (hex_bytes v (string_field v "hexValue")))
          else string_field v "value"
      in
        con "SrcLiteral"
          [info v, decode v "literal kind" literal_kinds kind, mk_str value, type_id v]
      end
  | "UnaryOperation" =>
      let val operand = expr (field v "subExpression") in
        if isSome (optional_field v "function") then operator_call v [operand]
        else con "SrcUnaryOperation"
          [info v, decode v "unary operator" unary_operators (string_field v "operator"),
           (if bool_field v "prefix" then T else F), operand, type_id v]
      end
  | "BinaryOperation" =>
      let
        val left = expr (field v "leftExpression")
        val right = expr (field v "rightExpression")
      in
        if isSome (optional_field v "function") then operator_call v [left, right]
        else con "SrcBinaryOperation"
          [info v, decode v "binary operator" binary_operators (string_field v "operator"),
           left, right,
           mk_str (normalize_type_id (string_field (field v "commonType") "typeIdentifier")),
           type_id v]
      end
  | "Conditional" =>
      con "SrcConditional"
        [info v, expr (field v "condition"), expr (field v "trueExpression"),
         expr (field v "falseExpression"), type_id v]
  | "Assignment" =>
      let
        val left = expr (field v "leftHandSide")
        val right = expr (field v "rightHandSide")
      in
        con "SrcAssignment"
          [info v, decode v "assignment operator" assignment_operators (string_field v "operator"),
           left, right, type_id v]
      end
  | "IndexAccess" =>
      let val base = expr (field v "baseExpression") in
        require v (isSome (optional_field v "indexExpression"))
          "array type expressions are not supported";
        con "SrcIndexAccess"
          [info v, base, expr (field v "indexExpression"), type_id v]
      end
  | "IndexRangeAccess" =>
      con "SrcIndexRangeAccess"
        [info v, expr (field v "baseExpression"),
         mk_opt expr_ty (Option.map expr (optional_field v "startExpression")),
         mk_opt expr_ty (Option.map expr (optional_field v "endExpression")), type_id v]
  | "TupleExpression" =>
      let
        val components =
          JSONUtil.arrayMap
            (fn JSON.NULL => optionSyntax.mk_none expr_ty
              | c => optionSyntax.mk_some (expr c))
            (field v "components")
      in
        require v (not (bool_field v "isInlineArray"))
          "inline arrays are not supported";
        con "SrcTupleExpression"
          [info v, listSyntax.mk_list (components, optionSyntax.mk_option expr_ty),
           type_id v]
      end
  | "FunctionCall" =>
      let
        val callee = field v "expression"
        val abi_member =
          node_type callee = "MemberAccess" andalso
          node_type (field callee "expression") = "Identifier" andalso
          int_field (field callee "expression") "referencedDeclaration" = abi_id
        val abi_decode = abi_member andalso string_field callee "memberName" = "decode"
        (* abi.decode's second argument names types, which abi_decode reads;
         * abi.encodeCall reads its arguments itself *)
        val args =
          case (abi_decode, JSONUtil.arrayMap I (field v "arguments")) of
            (true, data :: _) => [expr data]
          | (_, raw) =>
              if abi_member andalso string_field callee "memberName" = "encodeCall" then []
              else map expr raw
        val no_names = null (JSONUtil.arrayMap I (field v "names"))
        fun positional () = require v no_names "named arguments are not supported here"
      in
        require v (not (bool_field v "tryCall")) "try calls are not supported";
        case string_field v "kind" of
          "functionCall" =>
            if isSome (low_level_kind (options_target callee)) then
              (positional (); low_level_call v callee args)
            else if node_type callee = "MemberAccess" andalso
               (String.isPrefix "t_function_wrap_" (raw_type_id callee) orelse
                String.isPrefix "t_function_unwrap_" (raw_type_id callee)) then
              (positional (); wrap_call v callee args)
            else if is_external_call callee orelse
               node_type callee = "FunctionCallOptions" then
              external_call v callee args
            else if node_type callee = "Identifier" andalso
               int_field callee "referencedDeclaration" = keccak256_id then
              (positional ();
               require v (length args = 1) "keccak256 takes one argument";
               con "SrcKeccak256" [info v, info callee, hd args, type_id v])
            else if node_type callee = "Identifier" andalso
               int_field callee "referencedDeclaration" = ecrecover_id then
              (positional ();
               require v (length args = 4) "ecrecover takes four arguments";
               con "SrcEcrecover"
                 [info v, info callee, listSyntax.mk_list (args, expr_ty), type_id v])
            else if abi_decode then
              (positional (); abi_decode_call v callee args)
            else if node_type callee = "Identifier" andalso
               (int_field callee "referencedDeclaration" = addmod_id orelse
                int_field callee "referencedDeclaration" = mulmod_id) then
              (positional ();
               require v (length args = 3) "addmod and mulmod take three arguments";
               con "SrcModular"
                 [info v, info callee,
                  prim_mk_const
                    {Thy = "solidityCore",
                     Name = if int_field callee "referencedDeclaration" = addmod_id
                            then "AddModOp" else "MulModOp"},
                  listSyntax.mk_list (args, expr_ty), type_id v])
            else if is_concat "bytes" callee orelse is_concat "string" callee then
              (* bytes.concat is abi.encodePacked; string.concat is too, as a string *)
              (positional ();
               con "SrcAbiEncode"
                 [info v, info callee,
                  con (if is_concat "string" callee then "AbiStringConcat" else "AbiPacked") [],
                  listSyntax.mk_list (args, expr_ty), type_id v])
            else if abi_member then
              (positional (); abi_encode v callee args)
            else if node_type callee = "Identifier" andalso
               int_field callee "referencedDeclaration" < 0 then
              let
                val () = positional ()
                val id = int_field callee "referencedDeclaration"
                val builtin = if id = require_id then "RequireBuiltin"
                              else if id = assert_id then "AssertBuiltin"
                              else if id = revert_id then "RevertBuiltin"
                              else fail (describe callee ^ ": unsupported built-in declaration " ^
                                         IntInf.toString id)
                val (condition, message) =
                  case (builtin, args) of
                    ("AssertBuiltin", [c]) => (SOME c, NONE)
                  | ("RequireBuiltin", [c]) => (SOME c, NONE)
                  | ("RequireBuiltin", [c, m]) => (SOME c, SOME m)
                  | ("RevertBuiltin", []) => (NONE, NONE)
                  | ("RevertBuiltin", [m]) => (NONE, SOME m)
                  | _ => fail (describe v ^ ": unsupported built-in arguments")
              in
                con "SrcBuiltinCall" [info v, info callee, con builtin [],
                  mk_opt expr_ty condition, mk_opt expr_ty message, type_id v]
              end
            else if node_type callee = "NewExpression" then
              (positional ();
               require v (node_type (field callee "typeName") <> "UserDefinedTypeName")
                 "contract creation (new C) is not supported";
               require v (length args = 1) "new takes one argument";
               con "SrcNew"
                 [info v, type_name (field callee "typeName"), hd args,
                  type_id v])
            else if is_super_member callee then
              let
                val () = require v (!in_function)
                           "super outside a function body is not supported"
                val r = int_field callee "referencedDeclaration"
              in
                if List.exists (fn x => x = r) (!super_calls) then ()
                else super_calls := !super_calls @ [r];
                con "SrcSuperCall"
                  [info v, mk_num r, listSyntax.mk_list (args, expr_ty),
                   argument_order v r 0, type_id v]
              end
            else if is_library_member callee andalso is_attached callee then
              (* x.f(args) calls f with x as its first argument; the compiler
               * converts x before evaluating args, and elaboration after, so
               * a conversion that copies x (from storage or calldata to
               * memory) is not supported *)
              let val receiver = expr (field callee "expression") in
                require v (not (copies_receiver callee))
                  "a bound call copying its receiver to memory is not supported";
                con "SrcFunctionCall"
                  [info v,
                   con "SrcIdentifier"
                     [info callee, mk_str (string_field callee "memberName"),
                      mk_num (int_field callee "referencedDeclaration"),
                      type_id callee],
                   listSyntax.mk_list (receiver :: args, expr_ty),
                   argument_order v (int_field callee "referencedDeclaration") 1,
                   type_id v]
              end
            else con "SrcFunctionCall"
              [info v, expr callee, listSyntax.mk_list (args, expr_ty),
               case optional_field callee "referencedDeclaration" of
                 SOME _ => argument_order v (int_field callee "referencedDeclaration") 0
               | NONE => (positional (); listSyntax.mk_nil numSyntax.num),
               type_id v]
        | "typeConversion" =>
            (positional ();
             require v (length args = 1) "a conversion takes one argument";
             if String.isPrefix "t_type$_t_contract$_" (raw_type_id callee) then
               (* I(a), a conversion to a contract type *)
               con "SrcTypeConversion" [info v, address_type_name callee, hd args, type_id v]
             else if String.isPrefix "t_type$_t_enum$_" (raw_type_id callee) then
               (* E(x), with E named by an identifier or a member access *)
               con "SrcTypeConversion"
                 [info v,
                  con "SrcEnumTypeName"
                    [info callee, mk_num (int_field callee "referencedDeclaration")],
                  hd args, type_id v]
             else
               (within callee (fn c => expect c "ElementaryTypeNameExpression");
                con "SrcTypeConversion"
                  [info v, type_name (field callee "typeName"), hd args,
                   type_id v]))
        | kind => fail (describe v ^ ": unsupported call kind " ^ kind)
      end
  | other =>
      (List.app (fn (_, c) => if is_expression c then ignore (expr c) else ())
         (object v);
       fail (describe v ^ ": unsupported expression " ^ other)))) v

and wrap_call v callee args =
  let
    val (nominal, ty) =
      case value_type_expression (field callee "expression") of
        SOME pair => pair
      | NONE => fail (describe v ^ ": wrap/unwrap requires a user-defined value type")
    val member = string_field callee "memberName"
    val () = require v (member = "wrap" orelse member = "unwrap")
               "unsupported user-defined value type member"
    val underlying = raw_type_id ty
    val (input, output) = if member = "wrap" then (underlying, nominal)
                          else (nominal, underlying)
    val expected = "t_function_" ^ member ^ "_pure$_" ^ input ^
                   "_$returns$_" ^ output ^ "_$"
  in
    require v (length args = 1) "wrap/unwrap takes one argument";
    require v (raw_type_id callee = expected andalso raw_type_id v = output)
      "wrap/unwrap type annotation mismatch";
    con "SrcTypeConversion"
      [info v, type_name (type_at callee ty), hd args, type_id v]
  end

(* abi.encode, abi.encodePacked, abi.encodeWithSelector and
 * abi.encodeWithSignature of a literal signature; the signature's bytes are
 * taken from the literal, which is not kept as an argument. *)
and abi_encode v callee args =
  if string_field callee "memberName" = "encodeCall" then abi_encode_call v callee else
  let
    val form =
      case string_field callee "memberName" of
        "encode" => con "AbiPlain" []
      | "encodePacked" => con "AbiPacked" []
      | "encodeWithSelector" => con "AbiWithSelector" []
      | "encodeWithSignature" =>
          let
            val sig_node = hd (JSONUtil.arrayMap I (field v "arguments"))
              handle Empty => fail (describe v ^ ": encodeWithSignature takes a signature")
          in
            require v (node_type sig_node = "Literal" andalso
                       string_field sig_node "kind" = "string")
              "abi.encodeWithSignature of a non-literal signature is not supported";
            con "AbiWithSignature" [mk_bytes sig_node (string_field sig_node "hexValue")]
          end
      | member => fail (describe v ^ ": unsupported abi." ^ member)
    val args =
      if string_field callee "memberName" = "encodeWithSignature" then tl args else args
  in
    con "SrcAbiEncode"
      [info v, info callee, form, listSyntax.mk_list (args, expr_ty), type_id v]
  end

(* abi.decode(data, (T1, ..., Tk)) of elementary types; the parenthesised
 * types are a tuple expression even for one type. *)
and abi_decode_call v callee args =
  let
    val components =
      case JSONUtil.arrayMap I (field v "arguments") of
        [_, types] =>
          if node_type types = "TupleExpression" andalso
             not (bool_field types "isInlineArray")
          then JSONUtil.arrayMap I (field types "components")
          else [types]
      | _ => fail (describe v ^ ": abi.decode takes data and a list of types")
    fun decoded_type c =
      case c of
        JSON.NULL => NONE
      | _ => if node_type c = "ElementaryTypeNameExpression"
             then SOME (type_name (field c "typeName"))
             else Option.map (fn (_, ty) => type_name (type_at c ty))
                    (value_type_expression c)
    val types = map decoded_type components
  in
    require v (List.all isSome types)
      "abi.decode of a non-elementary type is not supported";
    con "SrcAbiDecode"
      [info v, info callee, hd args,
       listSyntax.mk_list (map valOf types, type_name_ty), type_id v]
  end

(* abi.encodeCall(f, (a, b)): f's selector, then the arguments, which the
 * elaborator converts to the types of f's parameters, given by their type
 * identifiers. A single argument may stand without parentheses. f's receiver
 * is one the compiler does not evaluate, or a variable other than a
 * constant, whose read has no effect and is left out (a constant's
 * initializer is evaluated, and may fail). *)
and abi_encode_call v callee =
  let
    val (f, values) =
      case JSONUtil.arrayMap I (field v "arguments") of
        [f, values] => (f, values)
      | _ => fail (describe v ^ ": encodeCall takes a function and its arguments")
    val arguments =
      if node_type values = "TupleExpression" andalso not (bool_field values "isInlineArray")
      then JSONUtil.arrayMap I (field values "components")
      else [values]
    val imported = map expr arguments
    val () = require v (node_type f = "MemberAccess") "abi.encodeCall of an unnamed function"
    val receiver = field f "expression"
    val () =
      if unevaluated_receiver receiver orelse
         (node_type receiver = "Identifier" andalso
          int_field receiver "referencedDeclaration" > 0) then ()
      else (ignore (expr receiver);
            fail (describe v ^ ": abi.encodeCall through a computed receiver is not supported"))
    val () =
      require v (unevaluated_receiver receiver orelse
                 (case List.find (fn (i, _) => i = int_field receiver "referencedDeclaration")
                                 (!selector_declarations) of
                    SOME (_, rdecl) => not (bool_field rdecl "constant")
                  | NONE => true))
        "abi.encodeCall through a constant receiver is not supported"
    val d =
      case optional_field f "referencedDeclaration" of
        SOME id =>
          (case List.find (fn (i, _) => i = JSONUtil.asIntInf id) (!selector_declarations) of
             SOME (_, d) => d
           | NONE => fail (describe v ^ ": encodeCall of a function outside the compilation"))
      | NONE => fail (describe v ^ ": unsupported encodeCall function")
    val () = require v (node_type d = "FunctionDefinition") "abi.encodeCall of a getter is not supported"
    val selector =
      con "SrcSelector" [info f, mk_bytes d (string_field d "functionSelector"), mk_str "t_bytes4"]
    val parameters = JSONUtil.arrayMap I (field (field d "parameters") "parameters")
    val () = require v (length arguments = length parameters)
               "abi.encodeCall takes one argument per parameter"
  in
    con "SrcAbiEncode"
      [info v, info callee,
       con "AbiCall" [listSyntax.mk_list (map type_id parameters, stringSyntax.string_ty)],
       listSyntax.mk_list (selector :: imported, expr_ty), type_id v]
  end

(* A callee's call options {value: v, gas: g}, in source order. Their
 * expressions are imported before their names are checked, so an unsupported
 * option does not hide the blockers of its value. *)
and call_options callee =
  if node_type callee = "FunctionCallOptions" then
    within callee (fn opts =>
      let
        val values = JSONUtil.arrayMap expr (field opts "options")
        val names = JSONUtil.arrayMap JSONUtil.asString (field opts "names")
        fun distinct [] = true
          | distinct (n :: ns) = not (List.exists (fn m => m = n) ns) andalso distinct ns
        val () = require opts (distinct names) "duplicate call options"
      in
        ListPair.zipEq
          (map (fn "value" => con "ValueOption" []
                 | "gas" => con "GasOption" []
                 | _ => fail (describe opts ^ ": unsupported call options"))
             names,
           values)
      end)
  else []

(* a.call{value: v, gas: g}(data), a.staticcall{gas: g}(data) or
 * a.delegatecall{gas: g}(data), with a of an address type. *)
and low_level_call v callee args =
  let
    val member = options_target callee
    val target = expr (field member "expression")
    val options = call_options callee
    val () = require v (length args = 1)
               (string_field member "memberName" ^ " takes one argument")
  in
    con "SrcLowLevelCall"
      [info v, info member, con (valOf (low_level_kind member)) [],
       listSyntax.mk_list (map #1 options, call_option_ty),
       listSyntax.mk_list (target :: map #2 options @ args, expr_ty),
       type_id v]
  end

(* c.f{value: v, gas: g}(args), with c of a contract type. *)
and external_call v callee args =
  let
    val member = options_target callee
    val target = Option.map expr (optional_field member "expression")
    val options = call_options callee
    val () = require member (is_external_call member)
               "unsupported call options"
    val () =
      within (field member "expression") (fn b =>
        require b (String.isPrefix "t_contract$_" (raw_type_id b))
          "external calls only on contract-typed values")
  in
    con "SrcExternalCall"
      [info v,
       external_function
         (function_declaration member (int_field member "referencedDeclaration")),
       listSyntax.mk_list (map #1 options, call_option_ty),
       listSyntax.mk_list (valOf target :: map #2 options @ args, expr_ty),
       argument_order v (int_field member "referencedDeclaration") 0,
       type_id v]
  end

(* The declaration a high-level call refers to. *)
and external_function v = within v (fn v =>
  (expect v "FunctionDefinition";
   record "src_external"
     [("ext_selector", mk_bytes v (string_field v "functionSelector")),
      ("ext_mutability", decode v "state mutability" mutabilities (string_field v "stateMutability")),
      ("ext_parameters", #2 (parameter_list (field v "parameters"))),
      ("ext_returns", #2 (parameter_list (field v "returnParameters")))]))

fun optional_expr v k =
  mk_opt expr_ty (Option.map expr (optional_field v k))

(* Statements *)

(* An inline assembly block's code, and the Solidity variables it names. The
 * compiler lists each use of one in externalReferences, by the source range
 * of the identifier naming it, so the name comes from the identifier at that
 * range. A suffix other than slot and offset (length, address, selector) is
 * a reference this semantics does not read.
 *)
fun yul_identifiers v =
  case v of
    JSON.OBJECT fields =>
      (if node_type v = "YulIdentifier" handle _ => false then
         [(string_field v "src", string_field v "name")]
       else []) @ List.concat (map (yul_identifiers o #2) fields)
  | JSON.ARRAY vs => List.concat (map yul_identifiers vs)
  | _ => []

val assembly_reference_ty = import_type "src_assembly_reference"

(* Every Yul node the semantics does not read is a line of the block's
 * reason, and so is a reference it does not. *)
fun inline_assembly v =
  let
    val ast = field v "AST"
    val (code, yul_failures) =
      (SOME (yulImportLib.import_code ast), [])
      handle yulImportLib.ImportError msg =>
               (NONE, map (fn l => describe v ^ ": " ^ l)
                        (String.fields (fn c => c = #"\n") msg))
           | yulImportLib.MalformedInput msg =>
               raise MalformedInput (describe v ^ ": " ^ msg)
    val names = yul_identifiers ast
    fun reference r =
      let
        val decl = mk_num (int_field r "declaration")
        val src = string_field r "src"
        val name =
          case List.find (fn (s, _) => s = src) names of
            SOME (_, n) => n
          | NONE => fail (describe v ^ ": no identifier at " ^ src)
        val kind =
          case optional_field r "suffix" of
            NONE => "SrcAssemblyValue"
          | SOME (JSON.STRING "slot") => "SrcAssemblySlot"
          | SOME (JSON.STRING "offset") => "SrcAssemblyOffset"
          | SOME _ => fail (describe v ^ ": unsupported reference " ^ name)
      in
        (name, con kind [decl])
      end
    (* one entry per name, however often the code uses it *)
    fun add (name, r) refs =
      case List.find (fn (n, _) => n = name) refs of
        NONE => refs @ [(name, r)]
      | SOME (_, r') =>
          if aconv r r' then refs
          else fail (describe v ^ ": " ^ name ^ " names two declarations")
    (* each reference is read whatever the others' blockers, a reason once
     * however often the code repeats it *)
    val (refs, reference_failures) =
      foldl (fn (r, (refs, fs)) =>
               (add (reference r) refs, fs)
               handle ImportError msg =>
                 (refs, if List.exists (fn f => f = msg) fs then fs else fs @ [msg]))
        ([], []) (JSONUtil.arrayMap I (field v "externalReferences"))
    val failures = yul_failures @ reference_failures
  in
    case (code, failures) of
      (SOME code, []) =>
        con "SrcInlineAssembly"
          [info v, code,
           listSyntax.mk_list
             (map (fn (n, r) => pairSyntax.mk_pair (mk_str n, r)) refs,
              pairSyntax.mk_prod (stringSyntax.string_ty, assembly_reference_ty))]
    | _ => fail (String.concatWith "\n" failures)
  end

fun stmt v = guarded (fn st => [StmtChild st]) unsupported_stmt (fn v => within v (fn v =>
  case node_type v of
    "Block" => con "SrcBlock" [info v, stmts (field v "statements")]
  | "UncheckedBlock" =>
      con "SrcUncheckedBlock" [info v, stmts (field v "statements")]
  | "ExpressionStatement" =>
      con "SrcExpressionStatement" [info v, expr (field v "expression")]
  | "VariableDeclarationStatement" =>
      con "SrcVariableDeclarationStatement"
        [info v,
         listSyntax.mk_list
           (JSONUtil.arrayMap
              (fn JSON.NULL => optionSyntax.mk_none numSyntax.num
                | i => optionSyntax.mk_some (mk_num (JSONUtil.asIntInf i)))
              (field v "assignments"),
            optionSyntax.mk_option numSyntax.num),
         listSyntax.mk_list
           (JSONUtil.arrayMap
              (fn JSON.NULL => optionSyntax.mk_none variable_ty
                | d => optionSyntax.mk_some (variable d))
              (field v "declarations"),
            optionSyntax.mk_option variable_ty),
         optional_expr v "initialValue"]
  | "IfStatement" =>
      con "SrcIfStatement"
        [info v, expr (field v "condition"), stmt (field v "trueBody"),
         optional_stmt v "falseBody"]
  | "WhileStatement" =>
      con "SrcWhileStatement"
        [info v, expr (field v "condition"), stmt (field v "body")]
  | "DoWhileStatement" =>
      con "SrcDoWhileStatement"
        [info v, stmt (field v "body"), expr (field v "condition")]
  | "ForStatement" =>
      con "SrcForStatement"
        [info v, optional_stmt v "initializationExpression",
         optional_expr v "condition", optional_stmt v "loopExpression",
         stmt (field v "body")]
  | "InlineAssembly" => inline_assembly v
  | "TryStatement" =>
      let
        val call = field v "externalCall"
        val clauses = JSONUtil.arrayMap I (field v "clauses")
        val args = case optional_field call "arguments" of
                     SOME args => JSONUtil.arrayMap expr args
                   | NONE => []
        (* each part is imported whatever the others' blockers, and the
         * checks on the clauses come after *)
        fun attempt f = (SOME (f ()), []) handle ImportError msg => (NONE, [msg])
        val (try_call, kind_failure) = attempt (fn () =>
          require call
            (node_type call = "FunctionCall" andalso
             string_field call "kind" = "functionCall" andalso bool_field call "tryCall")
            "try supports only external function calls")
        val (imported, call_failure) =
          if isSome try_call
          then attempt (fn () => external_call call (field call "expression") args)
          else (NONE, [])
        fun clause_parameters c =
          case optional_field c "parameters" of
            SOME ps => JSONUtil.arrayMap variable (field ps "parameters")
          | NONE => []
        val parameters = map (fn c => attempt (fn () => clause_parameters c)) clauses
        val blocks = map (fn c => stmt (field c "block")) clauses
        val (_, clause_failure) = attempt (fn () =>
          (require v (length clauses = 2) "try requires one catch(bytes memory) clause";
           require v (List.all (fn c => string_field c "errorName" = "") clauses)
             "typed catch clauses are not supported";
           case parameters of
             [_, (SOME [_], _)] => ()
           | [_, (NONE, _)] => ()
           | _ => fail (describe (List.nth (clauses, 1)) ^
                        ": catch requires one bytes parameter")))
        val failures =
          kind_failure @ call_failure @ List.concat (map #2 parameters) @ clause_failure
      in
        case (failures, imported, parameters, blocks, clauses) of
          ([], SOME imported, [(SOME returns, _), (SOME [reason], _)],
           [ok_block, err_block], [ok, err]) =>
            con "SrcTryStatement"
              [info v, imported, info ok, listSyntax.mk_list (returns, variable_ty),
               ok_block, info err, reason, err_block]
        | _ => fail (String.concatWith "\n" failures)
      end
  | "Break" => con "SrcBreak" [info v]
  | "Continue" => con "SrcContinue" [info v]
  | "Return" =>
      (* a return in a modifier has no return parameters *)
      con "SrcReturn"
        [info v,
         mk_num (case optional_field v "functionReturnParameters" of
                   SOME x => JSONUtil.asIntInf x
                 | NONE => 0),
         optional_expr v "expression"]
  | "PlaceholderStatement" => con "SrcPlaceholder" [info v]
  | "EmitStatement" =>
      let val call = field v "eventCall" in
        within call (fn call =>
          let
            val args = JSONUtil.arrayMap expr (field call "arguments")
            val ev = int_field (field call "expression") "referencedDeclaration"
          in
            within (field call "expression") (fn e => expect e "Identifier");
            con "SrcEmit"
              [info v, mk_num ev, listSyntax.mk_list (args, expr_ty),
               argument_order call ev 0]
          end)
      end
  | "RevertStatement" =>
      let val call = field v "errorCall" in
        within call (fn call =>
          let
            val args = JSONUtil.arrayMap expr (field call "arguments")
            val err = int_field (field call "expression") "referencedDeclaration"
          in
            (* E, or a qualified I.E, which names a declaration only *)
            within (field call "expression") (fn e =>
              require e (node_type e = "Identifier" orelse
                         node_type e = "MemberAccess")
                "unsupported error name");
            con "SrcRevertError"
              [info v, error_declaration call err, listSyntax.mk_list (args, expr_ty),
               argument_order call err 0]
          end)
      end
  | other => fail (describe v ^ ": unsupported statement " ^ other))) v
and stmts v = listSyntax.mk_list (JSONUtil.arrayMap stmt v, stmt_ty)
and optional_stmt v k = mk_opt stmt_ty (Option.map stmt (optional_field v k))

(* Functions, contracts and source units *)

(* The declarations a function overrides: those it names, and those they
 * override in turn, so that a call naming a declaration without a body
 * reaches the function implementing it however many declarations lie
 * between them. *)
fun overridden v =
  let
    fun direct d =
      case optional_field d "baseFunctions" of
        SOME ids => JSONUtil.arrayMap JSONUtil.asIntInf ids
      | NONE => []
    fun close [] = []
      | close (id :: ids) = id :: close (direct (function_declaration v id) @ ids)
  in
    close (direct v)
  end

(* The modifiers whose bodies have blockers, with those, which make a
 * function invoking one unsupported. *)
val failed_modifiers : (IntInf.int * string list) list ref = ref []

(* A function is imported whole: header, modifier invocations and body, with
 * placeholders for what the importer cannot represent. One with blockers, or
 * invoking a modifier with some, is unsupported, with the blockers as its
 * reason: it keeps its place, so that calls, overrides and super calls
 * resolve to it. Blockers in its header reject the unit too, and so does a
 * header the importer cannot represent at all. A fallback with parameters or
 * returns is unsupported likewise: the core's fallback takes neither. *)
fun function modifier_target v = within v (fn v =>
  let
    val () = super_calls := []
    val ((params_id, params, returns_id, returns), header) = with_blockers (fn () =>
      let
        val (params_id, params) = parameter_list (field v "parameters")
        val (returns_id, returns) = parameter_list (field v "returnParameters")
      in
        (params_id, params, returns_id, returns)
      end)
    (* the modifier invocations; base constructor arguments are imported with
     * the contract *)
    fun invocation m = within m (fn m =>
      if string_field m "kind" = "baseConstructorSpecifier" then NONE
      else
        let
          val () = require m (string_field m "kind" = "modifierInvocation")
                     ("unsupported modifier invocation kind " ^ string_field m "kind")
          val id = modifier_target (field m "modifierName")
          val args = case optional_field m "arguments" of
                       SOME args => JSONUtil.arrayMap expr args
                     | NONE => []
        in
          case List.find (fn (i, _) => i = id) (!failed_modifiers) of
            SOME (_, lines) => blockers := !blockers @ lines
          | NONE => ();
          SOME (pairSyntax.mk_pair (mk_num id, listSyntax.mk_list (args, expr_ty)))
        end)
    val ((modifiers, body), lines) = with_blockers (fn () =>
      (in_function := true;
       (List.mapPartial I (keep_all invocation (JSONUtil.arrayMap I (field v "modifiers"))),
        stmt (field v "body"))
       before in_function := false)
      handle e => (in_function := false; raise e))
    val () = blockers := !blockers @ header
    val fallback =
      if string_field v "kind" = "fallback" andalso
         not (listSyntax.is_nil params andalso listSyntax.is_nil returns)
      then [describe v ^ ": fallback with parameters or returns"] else []
    val reasons = header @ lines @ fallback
    val supers = !super_calls
  in
    (expect v "FunctionDefinition";
    record "src_function"
      [("fn_info", info v), ("fn_name", mk_str (string_field v "name")),
       ("fn_scope", mk_num (int_field v "scope")),
       ("fn_kind", decode v "function kind" function_kinds (string_field v "kind")),
       ("fn_visibility", decode v "visibility" visibilities (string_field v "visibility")),
       ("fn_mutability", decode v "state mutability" mutabilities (string_field v "stateMutability")),
       ("fn_selector",
        mk_opt (listSyntax.mk_list_type (wordsSyntax.mk_int_word_type 8))
          (Option.map (mk_bytes v o JSONUtil.asString)
             (optional_field v "functionSelector"))),
       ("fn_base_functions",
        listSyntax.mk_list (map mk_num (overridden v), numSyntax.num)),
       ("fn_parameters_id", params_id), ("fn_parameters", params),
       ("fn_nominal_parameters", listSyntax.mk_list
          (JSONUtil.arrayMap (mk_str o raw_type_id)
             (field (field v "parameters") "parameters"), stringSyntax.string_ty)),
       ("fn_returns_id", returns_id), ("fn_returns", returns),
       ("fn_modifiers", listSyntax.mk_list
          (modifiers, pairSyntax.mk_prod
                        (numSyntax.num, listSyntax.mk_list_type expr_ty))),
       ("fn_super_calls", listSyntax.mk_list (map mk_num supers, numSyntax.num)),
       ("fn_body", body),
       ("fn_unsupported",
        mk_opt stringSyntax.string_ty
          (if null reasons then NONE
           else SOME (mk_str (String.concatWith "\n" reasons))))])
    (* a function that cannot be represented is left out, with its blockers *)
    handle ImportError msg => (blockers := !blockers @ lines; raise ImportError msg)
  end)

(* Only invoked implementations are imported. A failed body makes the
 * functions invoking it unsupported; parameter blockers reject the unit. *)
fun modifier v = within v (fn v =>
  let
    val (params_id, params) = parameter_list (field v "parameters")
    val () = expect v "ModifierDefinition"
    val (body, lines) = with_blockers (fn () =>
      case optional_field v "body" of
        SOME b => stmt b
      | NONE => unsupported_stmt v (note v "modifier without a body") [])
    val () =
      if null lines then ()
      else failed_modifiers := !failed_modifiers @ [(int_field v "id", lines)]
  in
    record "src_modifier"
      [("modifier_info", info v), ("modifier_parameters_id", params_id),
       ("modifier_parameters", params), ("modifier_body", body)]
  end)

fun modifiers ms = (failed_modifiers := []; keep_all modifier ms)

fun event v = within v (fn v =>
  (expect v "EventDefinition";
   record "src_event"
     [("event_info", info v),
      ("event_anonymous", mk_bool (bool_field v "anonymous")),
      ("event_selector", mk_bytes v (string_field v "eventSelector")),
      ("event_parameters", listSyntax.mk_list
         (JSONUtil.arrayMap
            (fn p => pairSyntax.mk_pair (variable p, mk_bool (bool_field p "indexed")))
            (field (field v "parameters") "parameters"),
          pairSyntax.mk_prod (variable_ty, bool)))]))

(* An entry of a contract's storageLayout. *)
fun storage_entry v = within v (fn v =>
  record "src_storage_entry"
    [("storage_id", mk_num (int_field v "astId")),
     ("storage_slot",
      case IntInf.fromString (string_field v "slot") of
        SOME i => mk_num i
      | NONE => fail "malformed storage slot"),
     ("storage_offset", mk_num (int_field v "offset")),
     ("storage_type_id", mk_str (normalize_type_id (string_field v "type")))])

fun struct_declaration types v = within v (fn v =>
  let
    val () = expect v "StructDefinition"
    val members = JSONUtil.arrayMap (declaration false) (field v "members")
    val key = "t_struct(" ^ string_field v "name" ^ ")" ^
              IntInf.toString (int_field v "id") ^ "_storage"
    val layout =
      case (case types of JSON.NULL => NONE | _ => JSONUtil.findField types key) of
        NONE => NONE
      | SOME desc =>
          (require v (string_field desc "encoding" = "inplace")
             "struct layout encoding must be inplace";
           SOME (pairSyntax.mk_pair
             (case IntInf.fromString (string_field desc "numberOfBytes") of
                SOME bytes => mk_num bytes
              | NONE => fail "malformed struct layout size",
              listSyntax.mk_list
                (JSONUtil.arrayMap storage_entry (field desc "members"),
                 storage_entry_ty))))
  in
    record "src_struct"
      [("struct_info", info v),
       ("struct_scope", mk_num (int_field v "scope")),
       ("struct_members", listSyntax.mk_list (members, variable_ty)),
       ("struct_layout", mk_opt
         (pairSyntax.mk_prod (numSyntax.num, listSyntax.mk_list_type storage_entry_ty))
         layout)]
  end)

(* The super.f member accesses within a JSON value. *)
fun super_members (v as JSON.OBJECT fields) =
      (if List.exists (fn (k, _) => k = "nodeType") fields andalso
          is_super_member v then [v] else []) @
      List.concat (map (super_members o #2) fields)
  | super_members (JSON.ARRAY vs) = List.concat (map super_members vs)
  | super_members _ = []

(* The declarations the nodes of v refer to. *)
fun references (v as JSON.OBJECT fields) =
      (* Selectors and using declarations do not execute their references. *)
      if is_selector v orelse
         JSONUtil.testField "nodeType"
           (fn JSON.STRING s => s = "UsingForDirective" | _ => false) v
      then [] else
      List.concat
        (map (fn ("referencedDeclaration", JSON.INT i) => [i]
               (* an inline assembly block's reference *)
               | ("declaration", JSON.INT i) => [i]
               | ("function", JSON.INT i) => [i]
               | (_, w) => references w) fields)
  | references (JSON.ARRAY vs) = List.concat (map references vs)
  | references _ = []

(* A contract's constant with its value. *)
fun constant_declaration v = within v (fn v =>
  let
    val () = expect v "VariableDeclaration"
    val () = require v (bool_field v "constant")
               "expected a constant"
    val imported = variable_record v
    val value = expr (field v "value")
  in
    recover v (fn () =>
      (require v (not (isSome (optional_field v "overrides")))
         "overriding state variables are not supported";
       require v (not (String.isPrefix "t_enum$_" (raw_type_id v)))
         "enum constants are not supported"));
    pairSyntax.mk_pair (imported, value)
  end)

(* A deployable contract, flattened along its linearization (most derived
 * first), whose contracts declared lists by id: the implemented functions of
 * its bases, most derived first, their events and structs, their state
 * variables base first, the order of the storage layout, their immutables,
 * the initializers of both in declaration order, base first, their constants
 * with their values, and the base
 * constructor arguments each base gives, most derived base first. The
 * file-level structs it refers to come first, and the layout also describes
 * those referenced by its state variables. The library functions and
 * constants it refers to, also through each other, come with it, the
 * constants after its own.
 *)
fun contract external_structs contracts declared v = within v (fn v =>
  let
    val name = string_field v "name"
    val linearization =
      JSONUtil.arrayMap JSONUtil.asIntInf (field v "linearizedBaseContracts")
    val () =
      recover v (fn () =>
        require v (case linearization of
                     id :: _ => id = int_field v "id"
                   | [] => false)
          "the linearization does not start with the contract itself")
    val bases =
      map (fn id =>
             case List.find (fn (i, _) => i = id) declared of
               SOME (_, c) => c
             | NONE => fail (describe v ^ ": base contract " ^
                             IntInf.toString id ^ " is not in the compilation"))
        linearization
    fun nodes c = JSONUtil.arrayMap I (field c "nodes")
    fun members_of ty cs =
      List.concat
        (map (fn c => List.filter (fn m => node_type m = ty) (nodes c)) cs)
    (* The bases without what calls cannot reach: the functions another
     * function of the bases overrides, unless a super call runs them, and the
     * modifiers no reachable function invokes. A super call runs the first
     * implemented function, along the bases after the caller's, with the name
     * and parameter types of the declaration it names (super_target in
     * solidityImport). Modifier targets are resolved below before selecting
     * their bodies for library discovery and import. *)
    val functions = members_of "FunctionDefinition" bases
    val overriders = List.concat (map overridden functions)
    fun same_id f g = int_field f "id" = int_field g "id"
    fun is_overridden f = List.exists (fn i => i = int_field f "id") overriders
    fun parameter_types f =
      JSONUtil.arrayMap
        (fn p => string_field (field p "typeDescriptions") "typeIdentifier")
        (field (field f "parameters") "parameters")
    fun after f =
      let
        fun go [] = []
          | go (c :: cs) = if int_field c "id" = int_field f "scope" then cs else go cs
      in go bases end
    fun super_targets f =
      List.mapPartial
        (fn m =>
           let
             val d = function_declaration m (int_field m "referencedDeclaration")
             val later = after f
           in
             List.find
               (fn g => List.exists (fn c => int_field c "id" = int_field g "scope") later andalso
                        bool_field g "implemented" andalso
                        string_field g "kind" = "function" andalso
                        string_field g "name" = string_field d "name" andalso
                        parameter_types g = parameter_types d)
               functions
           end)
        (super_members f)
    fun close live [] = live
      | close live (f :: fs) =
          let
            val new = List.foldl
                        (fn (g, acc) =>
                           if List.exists (same_id g) (live @ acc) then acc else acc @ [g])
                        [] (super_targets f)
          in close (live @ new) (fs @ new) end
    val live =
      let val start = List.filter (not o is_overridden) functions
      in close start start end
    val modifier_definitions = members_of "ModifierDefinition" bases
    fun overridden_modifiers m =
      case optional_field m "baseModifiers" of
        NONE => []
      | SOME ids =>
          List.concat (map (fn id =>
            id :: (case List.find (fn d => int_field d "id" = id) modifier_definitions of
                     SOME d => overridden_modifiers d
                   | NONE => []))
            (JSONUtil.arrayMap JSONUtil.asIntInf ids))
    val modifier_targets =
      List.concat (map (fn m =>
        map (fn id => (id, int_field m "id"))
          (int_field m "id" :: overridden_modifiers m)) modifier_definitions)
    fun modifier_target m =
      let val id = int_field m "referencedDeclaration" in
        if String.isSubstring "." (string_field m "name") then id
        else case List.find (fn (i, _) => i = id) modifier_targets of
               SOME (_, target) => target
             | NONE => id
      end
    val invoked =
      List.concat
        (map (fn f => List.mapPartial
                        (fn i => case optional_field i "kind" of
                                   SOME (JSON.STRING "modifierInvocation") =>
                                     SOME (modifier_target (field i "modifierName"))
                                 | _ => NONE)
                        (JSONUtil.arrayMap I (field f "modifiers")))
           live)
    fun reachable n =
      case node_type n of
        "FunctionDefinition" => List.exists (same_id n) live
      | "ModifierDefinition" =>
          List.exists (fn i => i = int_field n "id") invoked
      | _ => true
    val reachable_bases =
      map (fn JSON.OBJECT kvs =>
                JSON.OBJECT
                  (map (fn ("nodes", JSON.ARRAY ns) =>
                             ("nodes", JSON.ARRAY (List.filter reachable ns))
                         | kv => kv) kvs)
            | c => c) bases
    (* The library members those bases refer to, also through other library
     * members. *)
    fun reached picked =
      let
        val ids = List.concat (map references (reachable_bases @ picked))
        val picked' =
          map #2 (List.filter (fn (i, _) => List.exists (fn j => j = i) ids)
                    (!library_members))
      in
        if length picked' = length picked then picked else reached picked'
      end
    val used_members = reached []
    val library_functions =
      List.filter (fn m => node_type m = "FunctionDefinition") used_members
    val () =
      List.app (fn m => recover m (fn () => within m (fn m =>
        case node_type m of
          "FunctionDefinition" =>
            require m (string_field m "visibility" = "internal" orelse
                       string_field m "visibility" = "private")
              "only internal library functions are supported"
        | "VariableDeclaration" =>
            require m (bool_field m "constant")
              "library variables are not supported"
        | "ModifierDefinition" => ()
        | "ErrorDefinition" => ()
        | "EnumDefinition" => ()
        | "UserDefinedValueTypeDefinition" => ()
        | other => fail (describe m ^ ": unsupported library member " ^ other))))
        used_members
    val () =
      List.app (fn (l, d) =>
                  if List.exists (fn f => int_field f "scope" = l) library_functions
                  then recover d (fn () => check_using d)
                  else ())
        (!library_directives)
    val libraries =
      List.foldr (fn (m, ls) =>
                    if List.exists (fn l => l = int_field m "scope") ls then ls
                    else int_field m "scope" :: ls)
        [] (List.filter (fn m => node_type m = "FunctionDefinition" orelse
                                 node_type m = "VariableDeclaration") used_members)
    (* The file-level structs the bases refer to, also through other structs. *)
    fun used picked =
      let
        val ids = List.concat (map references (bases @ used_members @ picked))
        val picked' =
          List.filter (fn s => List.exists (fn i => i = int_field s "id") ids)
            external_structs
      in
        if length picked' = length picked then picked else used picked'
      end
    val () =
      List.app (fn c => within c (fn c =>
        (recover c (fn () =>
           require c (string_field c "contractKind" = "contract" orelse
                      string_field c "contractKind" = "interface")
             ("unsupported contract kind " ^ string_field c "contractKind"));
         List.app (fn m => recover m (fn () => within m (fn m =>
                    (require m (node_type m = "FunctionDefinition" orelse
                                node_type m = "VariableDeclaration" orelse
                                node_type m = "StructDefinition" orelse
                                node_type m = "UserDefinedValueTypeDefinition" orelse
                                node_type m = "EnumDefinition" orelse
                                node_type m = "EventDefinition" orelse
                                node_type m = "ErrorDefinition" orelse
                                node_type m = "ModifierDefinition" orelse
                                node_type m = "UsingForDirective")
                       "unsupported contract member";
                     if node_type m = "UsingForDirective" then check_using m
                     else ()))))
           (nodes c))))
        bases
    val layout =
      JSONUtil.get (contracts,
        [JSONUtil.SEL name, JSONUtil.SEL "storageLayout"])
    val variables = members_of "VariableDeclaration" (rev bases)
    (* The state variables and immutables, in declaration order, base first. *)
    val assigned =
      List.filter (fn d => not (bool_field d "constant")) variables
    fun immutable d = string_field d "mutability" = "immutable"
    val state_variables = List.filter (not o immutable) assigned
    (* The base constructor arguments base x gives: those of its inheritance
     * specifiers and its constructor's base constructor specifiers, in the
     * order of x's own linearization. *)
    fun base_arguments x =
      let
        val specifiers =
          map (fn b => (field b "baseName", optional_field b "arguments"))
            (JSONUtil.arrayMap I (field x "baseContracts")) @
          List.concat
            (map (fn f =>
                    if string_field f "kind" = "constructor" then
                      map (fn m => (field m "modifierName",
                                    optional_field m "arguments"))
                        (JSONUtil.arrayMap I (field f "modifiers"))
                    else [])
               (members_of "FunctionDefinition" [x]))
        val given =
          List.mapPartial
            (fn (n, SOME args) => SOME (int_field n "referencedDeclaration", args)
              | (_, NONE) => NONE)
            specifiers
      in
        List.mapPartial
          (fn b => case List.find (fn (i, _) => i = b) given of
                     SOME (_, args) =>
                       SOME (pairSyntax.list_mk_pair
                         [mk_num (int_field x "id"), mk_num b,
                          listSyntax.mk_list (JSONUtil.arrayMap expr args, expr_ty)])
                   | NONE => NONE)
          (JSONUtil.arrayMap JSONUtil.asIntInf (field x "linearizedBaseContracts"))
      end
    (* before the functions, which need the modifiers that failed *)
    val imported_modifiers =
      modifiers (List.filter reachable modifier_definitions @
                 List.filter (fn m => node_type m = "ModifierDefinition")
                   used_members)
  in
    recover v (fn () => expect v "ContractDefinition");
    record "src_contract"
      [("contract_info", info v),
       ("contract_name", mk_str name),
       ("contract_scope", mk_num (int_field v "scope")),
       ("contract_bases", listSyntax.mk_list
          (JSONUtil.arrayMap (mk_num o JSONUtil.asIntInf)
             (field v "linearizedBaseContracts"), numSyntax.num)),
       ("contract_state_variables",
        listSyntax.mk_list (keep_all (declaration true) state_variables, variable_ty)),
       ("contract_immutables",
        listSyntax.mk_list
          (keep_all (declaration true) (List.filter immutable assigned), variable_ty)),
       ("contract_initializers", listSyntax.mk_list
          (List.mapPartial
             (fn d => Option.map (fn e => pairSyntax.mk_pair
                                    (mk_num (int_field d "id"), expr e))
                        (optional_field d "value"))
             assigned,
           pairSyntax.mk_prod (numSyntax.num, expr_ty))),
       ("contract_libraries", listSyntax.mk_list
          (map mk_num libraries, numSyntax.num)),
       ("contract_constants", listSyntax.mk_list
          (keep_all constant_declaration
             (List.filter (fn d => bool_field d "constant") variables @
              List.filter (fn d => node_type d = "VariableDeclaration")
                used_members),
           pairSyntax.mk_prod (variable_ty, expr_ty))),
       ("contract_base_arguments", listSyntax.mk_list
          (List.concat (map base_arguments bases),
           pairSyntax.list_mk_prod
             [numSyntax.num, numSyntax.num, listSyntax.mk_list_type expr_ty])),
       ("contract_storage",
        listSyntax.mk_list
          (keep_all storage_entry (JSONUtil.arrayMap I (field layout "storage")),
           storage_entry_ty)),
       ("contract_structs", listSyntax.mk_list
          (keep_all (struct_declaration (field layout "types"))
             (used [] @ members_of "StructDefinition" (rev bases)),
           struct_ty)),
       ("contract_enums", listSyntax.mk_list
          (map (fn (i, k) => pairSyntax.mk_pair (mk_num i, mk_num (IntInf.fromInt k)))
             (!enum_declarations),
           pairSyntax.mk_prod (numSyntax.num, numSyntax.num))),
       ("contract_events", listSyntax.mk_list
          (keep_all event (members_of "EventDefinition" bases), event_ty)),
       ("contract_modifiers", listSyntax.mk_list
          (imported_modifiers, import_type "src_modifier")),
       ("contract_functions",
        listSyntax.mk_list
          (keep_all (function modifier_target)
             (List.filter (fn f => bool_field f "implemented")
                (members_of "FunctionDefinition" bases)),
           function_ty)),
       ("contract_library_functions",
        listSyntax.mk_list (keep_all (function modifier_target) library_functions, function_ty)),
       ("contract_getters", listSyntax.mk_list
          (List.mapPartial
             (fn d => if string_field d "visibility" = "public" then
                        keep (fn d => pairSyntax.mk_pair
                          (mk_num (int_field d "id"),
                           mk_bytes d (string_field d "functionSelector"))) d
                      else NONE)
             variables,
           pairSyntax.mk_prod (numSyntax.num,
             listSyntax.mk_list_type (wordsSyntax.mk_int_word_type 8))))]
  end)

(* File-level structs, of any source unit of the compilation, accompany each
 * contract that refers to them, and revert statements carry the errors
 * they name; pragmas and import directives carry no semantics for the pinned
 * profile, since declarations are referred to by id.
 * Interfaces, abstract contracts and the bases of other contracts of the unit
 * are imported only as bases, which may come from any unit.
 *)
fun import_unit units v contracts = within v (fn v =>
  let
    val units = v :: List.filter (fn u => int_field u "id" <> int_field v "id") units
    val members = JSONUtil.arrayMap I (field v "nodes")
    fun all_members ty =
      List.concat
        (map (fn u => List.filter (fn m => node_type m = ty)
                        (JSONUtil.arrayMap I (field u "nodes"))) units)
    val () = compilation_max_id := greatest_node_id (JSON.ARRAY units)
    val structs = all_members "StructDefinition"
    val declared =
      map (fn c => (int_field c "id", c)) (all_members "ContractDefinition")
    val () = value_type_declarations :=
      map (fn d => (int_field d "id", d))
        (all_members "UserDefinedValueTypeDefinition" @
         List.concat (map (fn (_, c) =>
           List.filter (fn m => node_type m = "UserDefinedValueTypeDefinition")
             (JSONUtil.arrayMap I (field c "nodes"))) declared))
    val enums =
      all_members "EnumDefinition" @
      List.concat
        (map (fn (_, c) =>
                List.filter (fn m => node_type m = "EnumDefinition")
                  (JSONUtil.arrayMap I (field c "nodes")))
           declared)
    val () =
      enum_declarations :=
        map (fn e => (int_field e "id", length (JSONUtil.arrayMap I (field e "members"))))
          enums
    val () =
      enum_values :=
        List.concat
          (map (fn e =>
                  ListPair.zip
                    (JSONUtil.arrayMap (fn m => int_field m "id") (field e "members"),
                     List.tabulate (length (JSONUtil.arrayMap I (field e "members")),
                                    fn i => (int_field e "id", i))))
             enums)
    val () = contract_declarations := declared
    val () =
      selector_declarations :=
        List.mapPartial
          (fn d => if List.exists (fn k => k = node_type d)
                        ["FunctionDefinition", "EventDefinition", "ErrorDefinition",
                         "VariableDeclaration"]
                   then SOME (int_field d "id", d) else NONE)
          (List.concat (map (fn u => JSONUtil.arrayMap I (field u "nodes")) units) @
           List.concat (map (fn (_, c) => JSONUtil.arrayMap I (field c "nodes")) declared))
    val () =
      function_declarations :=
        map (fn f => (int_field f "id", f)) (all_members "FunctionDefinition") @
        List.concat
          (map (fn (_, c) =>
                  List.mapPartial
                    (fn f => if node_type f = "FunctionDefinition"
                             then SOME (int_field f "id", f) else NONE)
                    (JSONUtil.arrayMap I (field c "nodes")))
             declared)
    val () =
      library_members :=
        map (fn f => (int_field f "id", f))
          (all_members "FunctionDefinition" @ all_members "VariableDeclaration") @
        List.concat
          (map (fn (_, c) =>
                  if string_field c "contractKind" = "library" then
                    map (fn m => (int_field m "id", m))
                      (JSONUtil.arrayMap I (field c "nodes"))
                  else [])
             declared)
    val () =
      library_directives :=
        List.concat
          (map (fn (_, c) =>
                  if string_field c "contractKind" = "library" then
                    map (fn m => (int_field c "id", m))
                      (List.filter (fn m => node_type m = "UsingForDirective")
                         (JSONUtil.arrayMap I (field c "nodes")))
                  else [])
             declared)
    val () =
      error_declarations :=
        map (fn e => (int_field e "id", e))
          (all_members "ErrorDefinition" @
           List.concat
             (map (fn (_, c) =>
                     List.filter (fn m => node_type m = "ErrorDefinition")
                       (JSONUtil.arrayMap I (field c "nodes")))
                declared))
    val inherited =
      List.concat
        (map (fn c =>
                case JSONUtil.arrayMap JSONUtil.asIntInf
                       (field c "linearizedBaseContracts") of
                  _ :: bases => bases
                | [] => [])
           (List.filter (fn m => node_type m = "ContractDefinition") members))
    (* A file-level directive applies to the code of its own file, which the
     * contracts may reach through any unit of the compilation. *)
    val () =
      List.app (fn d => recover d (fn () => check_using d))
        (all_members "UsingForDirective")
    fun member m =
      case node_type m of
        "PragmaDirective" => NONE
      | "ImportDirective" => NONE
      | "StructDefinition" => NONE
      | "UserDefinedValueTypeDefinition" => NONE
      | "FunctionDefinition" => NONE
      | "VariableDeclaration" => NONE
      | "EnumDefinition" => NONE
      | "ErrorDefinition" => NONE
      | "UsingForDirective" => NONE
      | "ContractDefinition" =>
          if string_field m "contractKind" = "interface" orelse
             string_field m "contractKind" = "library" then NONE
          else
            (recover m (fn () =>
               require m (string_field m "contractKind" = "contract")
                 ("unsupported contract kind " ^ string_field m "contractKind"));
             if bool_field m "abstract" orelse
                List.exists (fn i => i = int_field m "id") inherited
             then NONE
             else keep (contract structs contracts declared) m)
      | other => (ignore (note m ("unsupported source unit member " ^ other)); NONE)
    val contracts = List.mapPartial (fn m => within m member) members
  in
    recover v (fn () => expect v "SourceUnit");
    record "src_unit"
      [("unit_info", info v),
       ("unit_path", mk_str (string_field v "absolutePath")),
       ("unit_sources", listSyntax.mk_list
          (map (fn u => mk_num (int_field u "id")) units, numSyntax.num)),
       ("unit_contracts", listSyntax.mk_list (contracts, contract_ty))]
  end)

(* The unit, and the blockers outside its functions and modifiers, which
 * reject it. *)
fun import_source_unit_blockers units v contracts =
  (blockers := [];
   children := [];
   (import_unit units v contracts, !blockers))

fun import_source_unit units v contracts =
  case import_source_unit_blockers units v contracts of
    (unit, []) => unit
  | (_, lines) => fail (String.concatWith "\n" lines)

fun read_artifact path =
  let
    val artifact = JSONParser.parseFile path
      handle e => fail (path ^ ": " ^ General.exnMessage e)
    val format = string_field artifact "format"
      handle e => fail (path ^ ": " ^ JSONUtil.exnMessage e)
  in
    if format <> "solidity-hol-solc-artifact-v1" then
      fail (path ^ ": unsupported artifact format " ^ format)
    else artifact
  end

fun artifact_deployed_bytecode path source contract =
  JSONUtil.asString
    (JSONUtil.get (read_artifact path,
       [JSONUtil.SEL "output", JSONUtil.SEL "contracts", JSONUtil.SEL source,
        JSONUtil.SEL contract, JSONUtil.SEL "evm",
        JSONUtil.SEL "deployedBytecode", JSONUtil.SEL "object"]))
  handle ImportError msg => raise ImportError msg
       | e => fail (path ^ ": no deployed bytecode for " ^ contract ^ ": " ^
                    JSONUtil.exnMessage e)

fun import_artifact path source =
  let
    val artifact = read_artifact path
    fun get keys what =
      JSONUtil.get (artifact, map JSONUtil.SEL keys)
      handle e => fail (path ^ ": no " ^ what ^ " for " ^ source ^ ": " ^
                        JSONUtil.exnMessage e)
  in
    import_source_unit
      (map (fn (_, s) => field s "ast") (object (get ["output", "sources"] "sources")))
      (get ["output", "sources", source, "ast"] "AST")
      (get ["output", "contracts", source] "contracts")
  end

end
