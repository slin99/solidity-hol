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

(* Terms *)

fun mk_num i =
  if i < 0 then fail ("negative number " ^ IntInf.toString i)
  else numSyntax.mk_numeral (Arbnum.fromString (IntInf.toString i))

val mk_str = stringSyntax.fromMLstring

fun mk_opt ty NONE = optionSyntax.mk_none ty
  | mk_opt _ (SOME tm) = optionSyntax.mk_some tm

fun import_type name = mk_thy_type {Thy = "solidityImport", Tyop = name, Args = []}
val expr_ty = import_type "src_expr"
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
    val name =
      case (IntInf.toInt base, member) of
        (~15, "sender") => "MsgSender"
      | (~15, "value") => "MsgValue"
      | (~15, "data") => "MsgData"
      | (~26, "origin") => "TxOrigin"
      | (~26, "gasprice") => "TxGasPrice"
      | (~4, "number") => "BlockNumber"
      | (~4, "timestamp") => "BlockTimestamp"
      | (~4, "chainid") => "BlockChainId"
      | (~4, "coinbase") => "BlockCoinbase"
      | (~4, "basefee") => "BlockBaseFee"
      | (~4, "gaslimit") => "BlockGasLimit"
      | _ => fail (describe v ^ ": unsupported built-in member " ^ member)
  in
    prim_mk_const {Thy = "solidityCore", Name = name}
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

(* A contract or interface type is an address at run time, stored and ABI
 * encoded as one: its type identifier, t_contract$_C_$n in the AST and
 * t_contract(C)n in a storage layout, is read as t_address. An enum's,
 * t_enum$_E_$n or t_enum(E)n, is read as t_enum_n, which names the enum by
 * its id alone. *)
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
    fun go i acc =
      if i >= n then String.concat (rev acc)
      else if at i "t_contract$_" then go (#2 (name_id (i + 12))) ("t_address" :: acc)
      else if at i "t_contract(" then go (#2 (paren_id (i + 11))) ("t_address" :: acc)
      else if at i "t_enum$_" then
        let val r = name_id (i + 8) in go (#2 r) (("t_enum_" ^ id r) :: acc) end
      else if at i "t_enum(" then
        let val r = paren_id (i + 7) in go (#2 r) (("t_enum_" ^ id r) :: acc) end
      else go (i + 1) (String.str (String.sub (s, i)) :: acc)
  in
    go 0 []
  end

fun raw_type_id v = string_field (field v "typeDescriptions") "typeIdentifier"
fun type_id v = mk_str (normalize_type_id (raw_type_id v))

fun address_type_name v =
  con "SrcElementaryTypeName"
    [info v, mk_str "address", mk_opt stringSyntax.string_ty (SOME (mk_str "nonpayable"))]

(* Type names *)

fun type_name v = within v (fn v =>
  case node_type v of
    "UserDefinedTypeName" =>
      let
        val declaration = int_field v "referencedDeclaration"
        val tid = raw_type_id v
      in
        if String.isPrefix "t_contract$_" tid then address_type_name v
        else if String.isPrefix "t_enum$_" tid then
          con "SrcEnumTypeName" [info v, mk_num declaration]
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
          [info v, mk_str name, mk_opt stringSyntax.string_ty (Option.map mk_str mutability)]
      end
  | "ArrayTypeName" =>
      (case optional_field v "length" of
         NONE => con "SrcDynamicArrayTypeName" [info v, type_name (field v "baseType")]
       | SOME length => let
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
        con "SrcArrayTypeName" [info v, type_name (field v "baseType"), mk_num n]
      end)
  | other => fail (describe v ^ ": unsupported type name " ^ other))

(* Declarations *)

fun variable_record v =
  record "src_variable"
    [("var_info", info v), ("var_name", mk_str (string_field v "name")),
     ("var_scope", mk_num (int_field v "scope")),
     ("var_type_name", type_name (field v "typeName")),
     ("var_type_id", type_id v),
     ("var_location", mk_str (string_field v "storageLocation"))]

(* A local, parameter or return variable, or, given state, a state variable
 * or an immutable. *)
fun declaration state v = within v (fn v =>
  (expect v "VariableDeclaration";
   require v (not (bool_field v "constant")) "constants are not supported";
   require v (bool_field v "stateVariable" = state)
     (if state then "expected a state variable"
      else "expected a local variable");
   require v (string_field v "mutability" = "mutable" orelse
              state andalso string_field v "mutability" = "immutable")
     "immutable variables are not supported";
   require v (state orelse not (isSome (optional_field v "value")))
     "declaration values are not supported";
   require v (not (isSome (optional_field v "overrides")))
     "overriding state variables are not supported";
   variable_record v))

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
      "Identifier" => int_field r "referencedDeclaration" = ~28 orelse named
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
                         int_field (field base "expression") "referencedDeclaration" = ~28))
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

(* The using directives of the libraries of the compilation, by library id:
 * those of a library whose functions a contract reaches must name a library,
 * as the contract's own must. *)
val library_directives : (IntInf.int * JSON.value) list ref = ref []

(* A using directive is admitted only when it names a library: one with a
 * function list (`using {f, ...} for T`) attaches free functions or defines
 * operators. *)
fun check_using d = within d (fn d =>
  require d (isSome (optional_field d "libraryName"))
    "using directives attaching functions are not supported")

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

fun expr v = within v (fn v =>
  case node_type v of
    "Identifier" =>
      if builtin_identifier v ~28 then
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
             (require v (not (is_attached v))
                "an attached function is supported only as a callee";
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
              con "SrcSelector" [info v, selector_bytes v base, type_id v]
            else case string_field v "memberName" of
              "length" =>
                if is_address_code base then
                  con "SrcAddressCodeLength"
                    [info v, info base, expr (field base "expression"), type_id v]
                else con "SrcArrayLength" [info v, expr base, type_id v]
            | member =>
                (require v (member = "push" orelse member = "pop")
                   "unsupported built-in member";
                 con "SrcArrayMember"
                   [info v, mk_str member, expr (field v "expression"), type_id v])
           end)
  | "Literal" =>
      (require v (not (isSome (optional_field v "subdenomination")))
         "literal subdenominations are not supported";
       con "SrcLiteral"
         [info v, mk_str (string_field v "kind"),
          mk_str (if List.exists (fn k => k = string_field v "kind")
                       ["string", "unicodeString", "hexString"] then
                    String.implode
                      (map Char.chr (hex_bytes v (string_field v "hexValue")))
                  else string_field v "value"), type_id v])
  | "UnaryOperation" =>
      con "SrcUnaryOperation"
        [info v, mk_str (string_field v "operator"),
         (if bool_field v "prefix" then T else F),
         expr (field v "subExpression"), type_id v]
  | "BinaryOperation" =>
      con "SrcBinaryOperation"
        [info v, mk_str (string_field v "operator"),
         expr (field v "leftExpression"), expr (field v "rightExpression"),
         mk_str (normalize_type_id (string_field (field v "commonType") "typeIdentifier")),
         type_id v]
  | "Conditional" =>
      con "SrcConditional"
        [info v, expr (field v "condition"), expr (field v "trueExpression"),
         expr (field v "falseExpression"), type_id v]
  | "Assignment" =>
      con "SrcAssignment"
        [info v, mk_str (string_field v "operator"),
         expr (field v "leftHandSide"), expr (field v "rightHandSide"),
         type_id v]
  | "IndexAccess" =>
      (require v (isSome (optional_field v "indexExpression"))
         "array type expressions are not supported";
       con "SrcIndexAccess"
         [info v, expr (field v "baseExpression"),
          expr (field v "indexExpression"), type_id v])
  | "TupleExpression" =>
      (require v (not (bool_field v "isInlineArray"))
         "inline arrays are not supported";
       con "SrcTupleExpression"
         [info v,
          listSyntax.mk_list
            (JSONUtil.arrayMap
               (fn JSON.NULL => optionSyntax.mk_none expr_ty
                 | c => optionSyntax.mk_some (expr c))
               (field v "components"),
             optionSyntax.mk_option expr_ty),
          type_id v])
  | "FunctionCall" =>
      let
        val args = JSONUtil.arrayMap expr (field v "arguments")
        val callee = field v "expression"
        val no_names = null (JSONUtil.arrayMap I (field v "names"))
        fun positional () = require v no_names "named arguments are not supported here"
      in
        require v (not (bool_field v "tryCall")) "try calls are not supported";
        case string_field v "kind" of
          "functionCall" =>
            if is_external_call callee orelse
               node_type callee = "FunctionCallOptions" then
              external_call v callee args
            else if node_type callee = "Identifier" andalso
               int_field callee "referencedDeclaration" = ~8 then
              (positional ();
               require v (length args = 1) "keccak256 takes one argument";
               con "SrcKeccak256" [info v, info callee, hd args, type_id v])
            else if node_type callee = "Identifier" andalso
               int_field callee "referencedDeclaration" = ~6 then
              (positional ();
               require v (length args = 4) "ecrecover takes four arguments";
               con "SrcEcrecover"
                 [info v, info callee, listSyntax.mk_list (args, expr_ty), type_id v])
            else if is_concat "bytes" callee orelse is_concat "string" callee then
              (* bytes.concat is abi.encodePacked; string.concat is too, as a string *)
              (positional ();
               con "SrcAbiEncode"
                 [info v, info callee,
                  con (if is_concat "string" callee then "AbiStringConcat" else "AbiPacked") [],
                  listSyntax.mk_list (args, expr_ty), type_id v])
            else if node_type callee = "MemberAccess" andalso
               node_type (field callee "expression") = "Identifier" andalso
               int_field (field callee "expression") "referencedDeclaration" = ~1 then
              (positional (); abi_encode v callee args)
            else if node_type callee = "Identifier" andalso
               int_field callee "referencedDeclaration" < 0 then
              let
                val () = positional ()
                val id = int_field callee "referencedDeclaration"
                val builtin = if id = ~18 then "RequireBuiltin"
                              else if id = ~3 then "AssertBuiltin"
                              else if id = ~19 then "RevertBuiltin"
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
              (require v (not (copies_receiver callee))
                 "a bound call copying its receiver to memory is not supported";
              con "SrcFunctionCall"
                [info v,
                 con "SrcIdentifier"
                   [info callee, mk_str (string_field callee "memberName"),
                    mk_num (int_field callee "referencedDeclaration"),
                    type_id callee],
                 listSyntax.mk_list (expr (field callee "expression") :: args,
                                     expr_ty),
                 argument_order v (int_field callee "referencedDeclaration") 1,
                 type_id v])
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
  | other => fail (describe v ^ ": unsupported expression " ^ other))

(* abi.encode, abi.encodePacked, abi.encodeWithSelector and
 * abi.encodeWithSignature of a literal signature; the signature's bytes are
 * taken from the literal, which is not kept as an argument. *)
and abi_encode v callee args =
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

(* c.f{value: v}(args), with c of a contract type. *)
and external_call v callee args =
  let
    val (member, value) =
      if node_type callee = "FunctionCallOptions" then
        within callee (fn opts =>
          (require opts
             (JSONUtil.arrayMap JSONUtil.asString (field opts "names") =
              ["value"])
             "only the value call option is supported";
           (field opts "expression",
            SOME (expr (hd (JSONUtil.arrayMap I (field opts "options")))))))
      else (callee, NONE)
    val () = require member (is_external_call member)
               "unsupported call options"
    val base = field member "expression"
    val () =
      within base (fn b =>
        require b (String.isPrefix "t_contract$_" (raw_type_id b))
          "external calls only on contract-typed values")
    val target = expr base
  in
    con "SrcExternalCall"
      [info v,
       external_function
         (function_declaration member (int_field member "referencedDeclaration")),
       mk_bool (isSome value),
       listSyntax.mk_list (target :: (case value of SOME x => [x] | NONE => []) @ args,
                           expr_ty),
       argument_order v (int_field member "referencedDeclaration") 0,
       type_id v]
  end

(* The declaration a high-level call refers to. *)
and external_function v = within v (fn v =>
  (expect v "FunctionDefinition";
   record "src_external"
     [("ext_selector", mk_bytes v (string_field v "functionSelector")),
      ("ext_mutability", mk_str (string_field v "stateMutability")),
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

fun inline_assembly v =
  let
    val ast = field v "AST"
    val code = yulImportLib.import_code ast
      handle yulImportLib.ImportError msg => fail (describe v ^ ": " ^ msg)
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
    val refs = foldl (fn (r, refs) => add (reference r) refs) []
                 (JSONUtil.arrayMap I (field v "externalReferences"))
  in
    con "SrcInlineAssembly"
      [info v, code,
       listSyntax.mk_list
         (map (fn (n, r) => pairSyntax.mk_pair (mk_str n, r)) refs,
          pairSyntax.mk_prod (stringSyntax.string_ty, assembly_reference_ty))]
  end

fun stmt v = within v (fn v =>
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
        val () = require call
          (node_type call = "FunctionCall" andalso
           string_field call "kind" = "functionCall" andalso bool_field call "tryCall")
          "try supports only external function calls"
        val (ok, err) = case JSONUtil.arrayMap I (field v "clauses") of
          [ok, err] => (ok, err)
        | _ => fail (describe v ^ ": try requires one catch(bytes memory) clause")
        val () = require v
          (string_field ok "errorName" = "" andalso string_field err "errorName" = "")
          "typed catch clauses are not supported"
        val reason = case optional_field err "parameters" of
          SOME ps => (case JSONUtil.arrayMap variable (field ps "parameters") of
                        [p] => p
                      | _ => fail (describe err ^ ": catch requires one bytes parameter"))
        | NONE => fail (describe err ^ ": catch requires one bytes parameter")
        val imported = external_call call (field call "expression")
          (JSONUtil.arrayMap expr (field call "arguments"))
        val parameters = case optional_field ok "parameters" of
          SOME ps => #2 (parameter_list ps)
        | NONE => listSyntax.mk_list ([], variable_ty)
      in
        con "SrcTryStatement"
          [info v, imported, info ok, parameters,
           stmt (field ok "block"), info err, reason, stmt (field err "block")]
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
            val ev = int_field (field call "expression") "referencedDeclaration"
          in
            within (field call "expression") (fn e => expect e "Identifier");
            con "SrcEmit"
              [info v, mk_num ev,
               listSyntax.mk_list
                 (JSONUtil.arrayMap expr (field call "arguments"), expr_ty),
               argument_order call ev 0]
          end)
      end
  | "RevertStatement" =>
      let val call = field v "errorCall" in
        within call (fn call =>
          let
            val err = int_field (field call "expression") "referencedDeclaration"
          in
            (* E, or a qualified I.E, which names a declaration only *)
            within (field call "expression") (fn e =>
              require e (node_type e = "Identifier" orelse
                         node_type e = "MemberAccess")
                "unsupported error name");
            con "SrcRevertError"
              [info v, error_declaration call err,
               listSyntax.mk_list
                 (JSONUtil.arrayMap expr (field call "arguments"), expr_ty),
               argument_order call err 0]
          end)
      end
  | other => fail (describe v ^ ": unsupported statement " ^ other))
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

fun function v = within v (fn v =>
  let
    val () = super_calls := []
    val (params_id, params) = parameter_list (field v "parameters")
    val (returns_id, returns) = parameter_list (field v "returnParameters")
    val () = in_function := true
    (* the modifier invocations; base constructor arguments are imported
     * with the contract *)
    val modifiers =
      List.mapPartial (fn m => within m (fn m =>
        if string_field m "kind" = "baseConstructorSpecifier" then NONE
        else
          (require m (string_field m "kind" = "modifierInvocation")
             ("unsupported modifier invocation kind " ^ string_field m "kind");
           SOME (pairSyntax.mk_pair
             (mk_num (int_field (field m "modifierName") "referencedDeclaration"),
              listSyntax.mk_list
                (case optional_field m "arguments" of
                   SOME args => JSONUtil.arrayMap expr args
                 | NONE => [],
                 expr_ty))))))
      (JSONUtil.arrayMap I (field v "modifiers"))
      handle e => (in_function := false; raise e)
    val body = stmt (field v "body") handle e => (in_function := false; raise e)
    val () = in_function := false
    val supers = !super_calls
  in
    expect v "FunctionDefinition";
    require v (List.exists (fn k => k = string_field v "kind")
                 ["function", "receive", "fallback", "constructor"])
      ("unsupported function kind " ^ string_field v "kind");
    record "src_function"
      [("fn_info", info v), ("fn_name", mk_str (string_field v "name")),
       ("fn_scope", mk_num (int_field v "scope")),
       ("fn_kind", mk_str (string_field v "kind")),
       ("fn_visibility", mk_str (string_field v "visibility")),
       ("fn_mutability", mk_str (string_field v "stateMutability")),
       ("fn_selector",
        mk_opt (listSyntax.mk_list_type (wordsSyntax.mk_int_word_type 8))
          (Option.map (mk_bytes v o JSONUtil.asString)
             (optional_field v "functionSelector"))),
       ("fn_base_functions",
        listSyntax.mk_list (map mk_num (overridden v), numSyntax.num)),
       ("fn_parameters_id", params_id), ("fn_parameters", params),
       ("fn_returns_id", returns_id), ("fn_returns", returns),
       ("fn_modifiers", listSyntax.mk_list
          (modifiers, pairSyntax.mk_prod
                        (numSyntax.num, listSyntax.mk_list_type expr_ty))),
       ("fn_super_calls", listSyntax.mk_list (map mk_num supers, numSyntax.num)),
       ("fn_body", body)]
  end)

(* A modifier invocation runs the modifier it names, so one that could be
 * overridden is not supported. *)
fun modifier v = within v (fn v =>
  let
    val (params_id, params) = parameter_list (field v "parameters")
  in
    expect v "ModifierDefinition";
    require v (not (bool_field v "virtual") andalso
               not (isSome (optional_field v "overrides")))
      "virtual modifiers are not supported";
    record "src_modifier"
      [("modifier_info", info v), ("modifier_parameters_id", params_id),
       ("modifier_parameters", params),
       ("modifier_body", stmt (field v "body"))]
  end)

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
       ("struct_members", listSyntax.mk_list
         (JSONUtil.arrayMap (declaration false) (field v "members"), variable_ty)),
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
      (* a selector's base is not imported *)
      if is_selector v then [] else
      List.concat
        (map (fn ("referencedDeclaration", JSON.INT i) => [i]
               (* an inline assembly block's reference *)
               | ("declaration", JSON.INT i) => [i]
               | (_, w) => references w) fields)
  | references (JSON.ARRAY vs) = List.concat (map references vs)
  | references _ = []

(* A contract's constant with its value. *)
fun constant_declaration v = within v (fn v =>
  (expect v "VariableDeclaration";
   require v (bool_field v "constant" andalso bool_field v "stateVariable")
     "expected a contract constant";
   require v (not (isSome (optional_field v "overrides")))
     "overriding state variables are not supported";
   require v (not (String.isPrefix "t_enum$_" (raw_type_id v)))
     "enum constants are not supported";
   pairSyntax.mk_pair (variable_record v, expr (field v "value"))))

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
      require v (case linearization of
                   id :: _ => id = int_field v "id"
                 | [] => false)
        "the linearization does not start with the contract itself"
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
     * solidityImport); an invocation runs the modifier it names, since
     * modifiers that could be overridden are not supported. *)
    val functions = members_of "FunctionDefinition" bases
    val overriders = List.concat (map overridden functions)
    fun same_id f g = int_field f "id" = int_field g "id"
    fun is_overridden f = List.exists (fn i => i = int_field f "id") overriders
    fun parameter_types f =
      JSONUtil.arrayMap
        (fn p => string_field (field p "typeDescriptions") "typeIdentifier")
        (field (field f "parameters") "parameters")
    (* Contract types are read as address, so implemented functions that
     * differ only in contract-typed parameters could not be told apart where
     * they are matched by parameter types, as super targets are. *)
    val overloadable =
      List.filter (fn f => string_field f "kind" = "function" andalso bool_field f "implemented")
        functions
    val () =
      List.app (fn f => List.app (fn g =>
        if string_field f "name" = string_field g "name" andalso
           parameter_types f <> parameter_types g andalso
           map normalize_type_id (parameter_types f) = map normalize_type_id (parameter_types g)
        then fail (describe g ^ ": overloads differing only in contract types are not supported")
        else ()) overloadable) overloadable
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
    val invoked =
      List.concat
        (map (fn f => List.mapPartial
                        (fn i => case optional_field i "kind" of
                                   SOME (JSON.STRING "modifierInvocation") =>
                                     SOME (int_field (field i "modifierName")
                                             "referencedDeclaration")
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
      List.app (fn m => within m (fn m =>
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
        | other => fail (describe m ^ ": unsupported library member " ^ other)))
        used_members
    val () =
      List.app (fn (l, d) =>
                  if List.exists (fn f => int_field f "scope" = l) library_functions
                  then check_using d
                  else ())
        (!library_directives)
    val libraries =
      List.foldr (fn (m, ls) =>
                    if List.exists (fn l => l = int_field m "scope") ls then ls
                    else int_field m "scope" :: ls)
        [] (List.filter (fn m => node_type m <> "ErrorDefinition" andalso
                                 node_type m <> "ModifierDefinition" andalso
                                 node_type m <> "EnumDefinition") used_members)
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
        (require c (string_field c "contractKind" = "contract" orelse
                    string_field c "contractKind" = "interface")
           ("unsupported contract kind " ^ string_field c "contractKind");
         List.app (fn m => within m (fn m =>
                    (require m (node_type m = "FunctionDefinition" orelse
                                node_type m = "VariableDeclaration" orelse
                                node_type m = "StructDefinition" orelse
                                node_type m = "EnumDefinition" orelse
                                node_type m = "EventDefinition" orelse
                                node_type m = "ErrorDefinition" orelse
                                node_type m = "ModifierDefinition" orelse
                                node_type m = "UsingForDirective")
                       "unsupported contract member";
                     if node_type m = "UsingForDirective" then check_using m
                     else ())))
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
  in
    expect v "ContractDefinition";
    record "src_contract"
      [("contract_info", info v),
       ("contract_name", mk_str name),
       ("contract_scope", mk_num (int_field v "scope")),
       ("contract_bases", listSyntax.mk_list
          (JSONUtil.arrayMap (mk_num o JSONUtil.asIntInf)
             (field v "linearizedBaseContracts"), numSyntax.num)),
       ("contract_state_variables",
        listSyntax.mk_list (map (declaration true) state_variables, variable_ty)),
       ("contract_immutables",
        listSyntax.mk_list
          (map (declaration true) (List.filter immutable assigned), variable_ty)),
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
          (map constant_declaration
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
          (JSONUtil.arrayMap storage_entry (field layout "storage"), storage_entry_ty)),
       ("contract_structs", listSyntax.mk_list
          (map (struct_declaration (field layout "types"))
             (used [] @ members_of "StructDefinition" (rev bases)),
           struct_ty)),
       ("contract_enums", listSyntax.mk_list
          (map (fn (i, k) => pairSyntax.mk_pair (mk_num i, mk_num (IntInf.fromInt k)))
             (!enum_declarations),
           pairSyntax.mk_prod (numSyntax.num, numSyntax.num))),
       ("contract_events", listSyntax.mk_list
          (map event (members_of "EventDefinition" bases), event_ty)),
       ("contract_modifiers", listSyntax.mk_list
          (map modifier (members_of "ModifierDefinition" bases @
                         List.filter (fn m => node_type m = "ModifierDefinition")
                           used_members),
           import_type "src_modifier")),
       ("contract_functions",
        listSyntax.mk_list
          (map function
             (List.filter (fn f => bool_field f "implemented")
                (members_of "FunctionDefinition" bases)),
           function_ty)),
       ("contract_library_functions",
        listSyntax.mk_list (map function library_functions, function_ty)),
       ("contract_getters", listSyntax.mk_list
          (List.mapPartial
             (fn d => if string_field d "visibility" = "public" then
                        SOME (pairSyntax.mk_pair
                          (mk_num (int_field d "id"),
                           mk_bytes d (string_field d "functionSelector")))
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
fun import_source_unit units v contracts = within v (fn v =>
  let
    val units = v :: List.filter (fn u => int_field u "id" <> int_field v "id") units
    val members = JSONUtil.arrayMap I (field v "nodes")
    fun all_members ty =
      List.concat
        (map (fn u => List.filter (fn m => node_type m = ty)
                        (JSONUtil.arrayMap I (field u "nodes"))) units)
    val structs = all_members "StructDefinition"
    val declared =
      map (fn c => (int_field c "id", c)) (all_members "ContractDefinition")
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
        List.concat
          (map (fn (_, c) =>
                  List.mapPartial
                    (fn f => if node_type f = "FunctionDefinition"
                             then SOME (int_field f "id", f) else NONE)
                    (JSONUtil.arrayMap I (field c "nodes")))
             declared)
    val () =
      library_members :=
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
    val () = List.app check_using (all_members "UsingForDirective")
    fun member m acc =
      case node_type m of
        "PragmaDirective" => acc
      | "ImportDirective" => acc
      | "StructDefinition" => acc
      | "EnumDefinition" => acc
      | "ErrorDefinition" => acc
      | "UsingForDirective" => acc
      | "ContractDefinition" =>
          if string_field m "contractKind" = "interface" orelse
             string_field m "contractKind" = "library" then acc
          else
            (require m (string_field m "contractKind" = "contract")
               ("unsupported contract kind " ^ string_field m "contractKind");
             if bool_field m "abstract" orelse
                List.exists (fn i => i = int_field m "id") inherited
             then acc
             else contract structs contracts declared m :: acc)
      | other => fail (describe m ^ ": unsupported source unit member " ^ other)
    val contracts =
      List.foldr (fn (m, acc) => within m (fn m => member m acc)) []
        members
  in
    expect v "SourceUnit";
    record "src_unit"
      [("unit_info", info v),
       ("unit_path", mk_str (string_field v "absolutePath")),
       ("unit_sources", listSyntax.mk_list
          (map (fn u => mk_num (int_field u "id")) units, numSyntax.num)),
       ("unit_contracts", listSyntax.mk_list (contracts, contract_ty))]
  end)

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
