structure solidityBytecodeLib =
struct

open HolKernel boolLib bossLib solidityBytecodeTheory cv_transLib intLib wordsLib

val ERR = mk_HOL_ERR "solidityBytecodeLib"

exception CorpusError of string

fun fail msg = raise CorpusError msg

(* Result lines, read by tools/run_differential.py *)

fun json_string s =
  let
    fun escape #"\"" = "\\\""
      | escape #"\\" = "\\\\"
      | escape #"\n" = "\\n"
      | escape c =
          if Char.isPrint c then String.str c
          else "\\u" ^ StringCvt.padLeft #"0" 4 (Int.fmt StringCvt.HEX (ord c))
  in
    "\"" ^ String.translate escape s ^ "\""
  end

fun json_object fields =
  "{" ^ String.concatWith ","
          (map (fn (k, v) => json_string k ^ ":" ^ v) fields) ^ "}"

fun json_array vs = "[" ^ String.concatWith "," vs ^ "]"

fun emit fields = print ("differential-result: " ^ json_object fields ^ "\n")

(* Corpus input *)

val field = JSONUtil.lookupField
fun object (JSON.OBJECT fields) = fields
  | object _ = fail "expected a JSON object"
fun string_field v k = JSONUtil.asString (field v k)
fun array_field v k = Vector.foldr (op ::) [] (JSONUtil.asArray (field v k))

fun identifier s =
  size s > 0 andalso Char.isAlpha (String.sub (s, 0)) andalso
  CharVector.all (fn c => Char.isAlphaNum c orelse c = #"_") s

fun name_field v k =
  let val s = string_field v k in
    if identifier s then s else fail ("not an identifier: " ^ s)
  end

fun hex_digit c =
  if Char.isDigit c then ord c - ord #"0"
  else if #"a" <= c andalso c <= #"f" then ord c - ord #"a" + 10
  else if #"A" <= c andalso c <= #"F" then ord c - ord #"A" + 10
  else fail ("not a hex digit: " ^ String.str c)

(* "0x" followed by an even number of hex digits *)
fun hex_bytes s =
  let
    val digits =
      if String.isPrefix "0x" s then String.extract (s, 2, NONE)
      else fail ("expected 0x-prefixed hex: " ^ s)
    fun go [] = []
      | go (h :: l :: rest) = (16 * hex_digit h + hex_digit l) :: go rest
      | go [_] = fail ("odd number of hex digits: " ^ s)
  in
    go (explode digits)
  end

fun is_hex s = String.isPrefix "0x" s

fun decimal s =
  let
    val (negative, digits) =
      if String.isPrefix "-" s then (true, String.extract (s, 1, NONE))
      else (false, s)
  in
    if size digits > 0 andalso CharVector.all Char.isDigit digits then
      (if negative then ~1 else 1) * valOf (IntInf.fromString digits)
    else fail ("not an integer: " ^ s)
  end

fun integer (JSON.INT i) = i
  | integer (JSON.STRING s) =
      if is_hex s then
        List.foldl (fn (b, acc) => acc * 256 + IntInf.fromInt b) 0 (hex_bytes s)
      else decimal s
  | integer _ = fail "expected an integer"

(* Terms *)

fun con name args =
  list_mk_comb (prim_mk_const {Thy = "solidityBytecode", Name = name}, args)

fun num_term i = numSyntax.mk_numeral (Arbnum.fromString (IntInf.toString i))

fun int_term i =
  if i < 0 then intSyntax.mk_negated (intSyntax.mk_injected (num_term (~i)))
  else intSyntax.mk_injected (num_term i)

val byte_ty = wordsSyntax.mk_int_word_type 8

fun bytes_term bs =
  listSyntax.mk_list (map (fn b => wordsSyntax.mk_wordii (b, 8)) bs, byte_ty)

val argument_ty =
  mk_thy_type {Thy = "solidityBytecode", Tyop = "argument", Args = []}

fun argument (JSON.BOOL b) = con "BoolArg" [if b then T else F]
  | argument (JSON.INT i) = con "IntArg" [int_term i]
  | argument (JSON.STRING s) =
      if is_hex s then con "BytesArg" [bytes_term (hex_bytes s)]
      else con "IntArg" [int_term (decimal s)]
  | argument _ = fail "an argument is an integer, a boolean or a 0x string"

fun arguments vs = listSyntax.mk_list (map argument vs, argument_ty)

fun expectation v =
  case v of
    JSON.OBJECT [("return", JSON.ARRAY vs)] => con "ExpectReturn" [arguments vs]
  | JSON.OBJECT [("returned", JSON.STRING s)] =>
      con "ExpectRawReturn" [bytes_term (hex_bytes s)]
  | JSON.OBJECT [("panic", code)] => con "ExpectPanic" [num_term (integer code)]
  | JSON.OBJECT [("revert", JSON.STRING s)] =>
      con "ExpectRevert" [bytes_term (hex_bytes s)]
  | _ => fail "expect is one of {\"return\": [...]}, {\"returned\": \"0x...\"}, {\"panic\": code}, \
              \{\"revert\": \"0x...\"}"

(* An object from slot to value, both 256-bit words. *)
fun storage v =
  let
    fun word i =
      if 0 <= i andalso i < IntInf.pow (2, 256) then num_term i
      else fail ("not a 256-bit word: " ^ IntInf.toString i)
    fun entry (k, x) = pairSyntax.mk_pair (word (integer (JSON.STRING k)), word (integer x))
  in
    case v of
      NONE => listSyntax.mk_list ([], “:num # num”)
    | SOME (JSON.OBJECT kvs) => listSyntax.mk_list (map entry kvs, “:num # num”)
    | SOME _ => fail "storage is an object from slot to value"
  end

fun word_term bits i =
  if 0 <= i andalso i < IntInf.pow (2, bits) then
    wordsSyntax.mk_wordi (Arbnum.fromString (IntInf.toString i), bits)
  else fail ("not a " ^ Int.toString bits ^ "-bit word: " ^ IntInf.toString i)

(* Calldata as 0x hex, a named function and its arguments, or a creation
 * ("deploy": true) from the suite's initcode with the constructor's arguments
 * or, as calldata, their raw encoding. *)
fun call_input initcode c =
  case (JSONUtil.findField c "calldata", JSONUtil.findField c "function",
        JSONUtil.findField c "deploy") of
    (SOME (JSON.STRING s), NONE, NONE) => con "RawCall" [bytes_term (hex_bytes s)]
  | (NONE, SOME (JSON.STRING f), NONE) =>
      con "NamedCall"
        [stringSyntax.fromMLstring f, arguments (array_field c "args")]
  | (NONE, NONE, SOME (JSON.BOOL true)) =>
      con "Deploy" [initcode (),
                    sumSyntax.mk_inl (arguments (array_field c "args"),
                                      listSyntax.mk_list_type byte_ty)]
  | (SOME (JSON.STRING s), NONE, SOME (JSON.BOOL true)) =>
      con "Deploy" [initcode (),
                    sumSyntax.mk_inr (bytes_term (hex_bytes s),
                                      listSyntax.mk_list_type argument_ty)]
  | _ => fail "a case has either calldata, a function and its arguments, \
              \or deploy and the constructor's arguments or calldata"

(* Logs as a list of {"logger": address, "topics": [...], "data": "0x..."},
 * the logger the contract by default. *)
fun logs v =
  let
    val bytes32 = wordsSyntax.mk_int_word_type 256
    fun log l =
      pairSyntax.list_mk_pair
        [word_term 160 (case JSONUtil.findField l "logger" of
                          SOME a => integer a
                        | NONE => 0x1000),
         listSyntax.mk_list
           (map (word_term 256 o integer) (array_field l "topics"), bytes32),
         bytes_term (hex_bytes (string_field l "data"))]
  in
    listSyntax.mk_list
      (map log (case v of NONE => [] | SOME (JSON.ARRAY ls) => ls
                        | SOME _ => fail "logs is a list"),
       pairSyntax.list_mk_prod
         [wordsSyntax.mk_int_word_type 160, listSyntax.mk_list_type bytes32,
          listSyntax.mk_list_type byte_ty])
  end

(* Outcomes as JSON *)

fun hex_of_bytes tm =
  "0x" ^ String.concat
    (map (fn b =>
            StringCvt.padLeft #"0" 2
              (String.map Char.toLower
                 (Arbnum.toHexString (wordsSyntax.dest_word_literal b))))
         (fst (listSyntax.dest_list tm)))

fun outcome_json tm =
  let val (f, args) = strip_comb tm in
    case (fst (dest_const f), args) of
      ("Returned", [bs]) => json_object [("returned", json_string (hex_of_bytes bs))]
    | ("Reverted", [bs]) => json_object [("reverted", json_string (hex_of_bytes bs))]
    | ("Diagnostic", [d]) =>
        json_object [("diagnostic", json_string (fst (dest_const d)))]
    | _ => json_string (term_to_string tm)
  end

fun logs_json tm =
  json_array
    (map (fn e =>
            let val (_, fields) = TypeBase.dest_record e in
              json_object
                [("logger", json_string ("0x" ^ String.map Char.toLower
                    (Arbnum.toHexString
                       (wordsSyntax.dest_word_literal (Lib.assoc "logger" fields))))),
                 ("topics", json_array
                    (map (fn t => json_string ("0x" ^ String.map Char.toLower
                                    (Arbnum.toHexString (wordsSyntax.dest_word_literal t))))
                       (fst (listSyntax.dest_list
                               (Lib.assoc "topics" fields))))),
                 ("data", json_string (hex_of_bytes (Lib.assoc "data" fields)))]
            end)
         (fst (listSyntax.dest_list tm)))

fun storage_json tm =
  json_object
    (map (fn p =>
            let val (k, v) = pairSyntax.dest_pair p in
              (Arbnum.toString (numSyntax.dest_numeral k),
               json_string ("0x" ^ String.map Char.toLower
                                     (Arbnum.toHexString (numSyntax.dest_numeral v))))
            end)
         (fst (listSyntax.dest_list tm)))

(* Definitions made by the corpus *)

fun define name tm =
  new_definition (name ^ "_def", mk_eq (mk_var (name, type_of tm), tm))


fun code_definition name hex =
  let
    val def = define name
                “REVERSE $ hex_to_rev_bytes [] ^(stringSyntax.fromMLstring hex)”
    val () = cv_trans_deep_embedding EVAL def
  in
    lhs (concl def)
  end

(* The deployed code ("deployedBytecode") or initcode ("bytecode"). *)
fun code_constant name kind artifact source contract =
  let
    val hex = JSONUtil.asString (JSONUtil.get (artifact,
      map JSONUtil.SEL ["output", "contracts", source, contract, "evm",
                        kind, "object"]))
      handle e as JSONUtil.JSONError _ => fail (JSONUtil.exnMessage e)
           | e as JSONUtil.FieldNotFound _ => fail (JSONUtil.exnMessage e)
  in
    code_definition name hex
  end

fun read_bytecode_artifact path =
  let
    val artifact = JSONParser.parseFile path
    val format = string_field artifact "format"
  in
    if format = "solidity-hol-solc-artifact-v1" then artifact
    else fail (path ^ ": expected solidity-hol-solc-artifact-v1, got " ^ format)
  end

(* The peer's code, from its own artifact; no code without a peer. *)
fun peer_code root prefix s =
  case JSONUtil.findField s "peer" of
    NONE => listSyntax.mk_nil byte_ty
  | SOME p =>
      code_constant (prefix ^ "_peer_code") "deployedBytecode"
        (read_bytecode_artifact (root ^ "/" ^ string_field p "artifact"))
        (string_field p "source") (string_field p "contract")


fun record_field name tm = Lib.assoc name (snd (TypeBase.dest_record tm))

(* Cases *)

fun is_con name tm =
  let val f = fst (strip_comb tm) in
    is_const f andalso fst (dest_const f) = name
  end

(* The values a call case gives the immutables, by name ("immutables": an
 * object from name to argument), as their declarations; names is the
 * contract's immutables, by name. *)
fun case_immutables names c =
  case JSONUtil.findField c "immutables" of
    NONE => listSyntax.mk_list ([], “:num # argument”)
  | SOME (JSON.OBJECT kvs) =>
      listSyntax.mk_list
        (map (fn (k, v) =>
                case List.find (fn (n, _) => n = k) names of
                  SOME (_, id) => pairSyntax.mk_pair (num_term id, argument v)
                | NONE => fail ("no immutable named " ^ k))
           kvs,
         “:num # argument”)
  | SOME _ => fail "immutables is an object from name to value"

(* A corpus case as solidityBytecode's differential_case record, which is
 * what both the bytecode run and the Yul run are given. peer is the peer
 * contract's code, empty for a suite that declares no peer; immutables
 * gives the contract's immutables, by name, and refs the offsets of those
 * its deployed code reads.
 *)
fun case_term peer (immutables : {names : (string * IntInf.int) list,
                                  refs : term}) input c =
  TypeBase.mk_record
    (mk_thy_type {Thy = "solidityBytecode", Tyop = "differential_case",
                  Args = []},
     [("case_sender",
       word_term 160 (case JSONUtil.findField c "sender" of
                        SOME v => integer v
                      | NONE => 0x2000)),
      ("case_value",
       num_term (case JSONUtil.findField c "value" of
                   SOME v => integer v
                 | NONE => 0)),
      ("case_input", input),
      ("case_immutables", case_immutables (#names immutables) c),
      ("case_immutable_refs", #refs immutables),
      ("case_storage", storage (JSONUtil.findField c "storage")),
      ("case_peer_code", peer),
      ("case_peer_storage", storage (JSONUtil.findField c "peer_storage")),
      ("case_expect", expectation (field c "expect")),
      ("case_final", storage (JSONUtil.findField c "final_storage")),
      ("case_logs", logs (JSONUtil.findField c "logs"))])

(* ABI types come from the compiler artifact, independently of source import. *)
fun abi_type v = contractABISyntax.parse_abi_type (string_field v "type")

fun abi_value ty v =
  let
    val (kind, _) = strip_comb ty
    fun abi name args = list_mk_comb
      (prim_mk_const {Thy = "contractABI", Name = name}, args)
  in
    case fst (dest_const kind) of
      "Bool" =>
        (case v of JSON.BOOL b => abi "NumV" [num_term (if b then 1 else 0)]
         | _ => fail "a bool ABI argument must be a boolean")
    | "Int" => abi "IntV" [int_term (integer v)]
    | "Uint" => abi "NumV" [num_term (integer v)]
    | "Address" => abi "NumV" [num_term (integer v)]
    | "Bytes" => abi "BytesV" [bytes_term (hex_bytes (JSONUtil.asString v))]
    | "String" => abi "BytesV" [bytes_term (hex_bytes (JSONUtil.asString v))]
    | _ => fail "aggregate arguments require raw calldata/return bytes"
  end

fun encode types values =
  let
    val () = if length types = length values then ()
             else fail "ABI argument count differs from the artifact"
    val vs = map (fn (ty, v) => abi_value ty v) (ListPair.zip (types, values))
    val tys = listSyntax.mk_list (types, “:abi_type”)
    val vs = listSyntax.mk_list (vs, “:abi_value”)
    val typed = cv_eval “has_types ^tys ^vs”
    val () = if rhs (concl typed) ~~ T then ()
             else fail "ABI value does not have its declared type"
  in
    rhs (concl (cv_eval “enc (Tuple ^tys) (ListV ^vs)”))
  end

fun artifact_contract artifact source contract =
  JSONUtil.get (artifact, map JSONUtil.SEL ["output", "contracts", source, contract])

fun named_abi artifact name =
  case List.filter
    (fn f => string_field f "type" = "function" andalso string_field f "name" = name)
    (array_field artifact "abi") of
    [f] => f
  | [] => fail ("no ABI function named " ^ name)
  | _ => fail ("ambiguous ABI function " ^ name ^ "; use raw calldata")

fun constructor_abi artifact =
  case List.filter (fn f => string_field f "type" = "constructor")
         (array_field artifact "abi") of
    [] => []
  | [f] => map abi_type (array_field f "inputs")
  | _ => fail "more than one constructor in ABI"

fun abi_call artifact c =
  case JSONUtil.findField c "calldata" of
    SOME v => (bytes_term (hex_bytes (JSONUtil.asString v)), [])
  | NONE =>
      if JSONUtil.hasField "deploy" c then
        (encode (constructor_abi artifact) (array_field c "args"), [])
      else
        let
          val name = string_field c "function"
          val f = named_abi artifact name
          val inputs = array_field f "inputs"
          val selector_name = name ^ "(" ^
            String.concatWith "," (map (fn t => string_field t "type") inputs) ^ ")"
          val selector = JSONUtil.asString (JSONUtil.get (artifact,
            map JSONUtil.SEL ["evm", "methodIdentifiers", selector_name]))
          val data = encode (map abi_type inputs) (array_field c "args")
        in
          (listSyntax.mk_append (bytes_term (hex_bytes ("0x" ^ selector)), data),
           map abi_type (array_field f "outputs"))
        end

(* Only the selected contract and its bases supply immutable declarations. *)
fun artifact_immutables artifact source contract =
  let
    val sources = object (field (field artifact "output") "sources")
    val contracts = List.concat (map (fn (_, s) =>
      List.filter (fn n => string_field n "nodeType" = "ContractDefinition")
        (array_field (field s "ast") "nodes")) sources)
    val root_nodes = array_field
      (JSONUtil.get (artifact, map JSONUtil.SEL ["output", "sources", source, "ast"])) "nodes"
    val selected = case List.find (fn n =>
      string_field n "nodeType" = "ContractDefinition" andalso
      string_field n "name" = contract) root_nodes of
        SOME n => n | NONE => fail ("missing AST contract " ^ contract)
    val bases = map integer (array_field selected "linearizedBaseContracts")
    val declarations = List.concat (map (fn c => array_field c "nodes")
      (List.filter (fn c => List.exists (fn id => id = integer (field c "id")) bases)
         contracts))
    val imms = List.filter (fn v =>
      string_field v "nodeType" = "VariableDeclaration" andalso
      string_field v "mutability" = "immutable") declarations
    fun immutable v =
      let
        val name = string_field v "name"
        val text = string_field (field v "typeDescriptions") "typeString"
        val ty = if String.isPrefix "contract " text orelse text = "address payable"
                 then contractABISyntax.parse_abi_type "address"
                 else if String.isPrefix "enum " text then “Uint 8”
                 else contractABISyntax.parse_abi_type text
      in (name, integer (field v "id"), ty) end
    val target = artifact_contract artifact source contract
    val refs = case JSONUtil.findField (field (field target "evm") "deployedBytecode")
                                  "immutableReferences" of
        NONE => []
      | SOME v => object v
    fun reference (id, rs) = pairSyntax.mk_pair (num_term (decimal id),
      listSyntax.mk_list (map (fn r => num_term (integer (field r "start")))
        (Vector.foldr (op ::) [] (JSONUtil.asArray rs)), numSyntax.num))
  in
    (map immutable imms, listSyntax.mk_list (map reference refs, “:num # num list”))
  end

fun immutable_words declarations c =
  let
    val values = case JSONUtil.findField c "immutables" of
        NONE => [] | SOME v => object v
    fun entry (name, value) =
      case List.find (fn (n, _, _) => n = name) declarations of
        NONE => fail ("no immutable named " ^ name)
      | SOME (_, id, ty) =>
          pairSyntax.list_mk_pair [num_term id, F, encode [ty] [value]]
  in
    listSyntax.mk_list (map entry values,
      pairSyntax.list_mk_prod [numSyntax.num, bool, listSyntax.mk_list_type byte_ty])
  end

fun raw_expectation outputs c =
  case field c "expect" of
    JSON.OBJECT [("return", JSON.ARRAY values)] =>
      con "Returned" [encode outputs values]
  | JSON.OBJECT [("returned", JSON.STRING value)] =>
      con "Returned" [bytes_term (hex_bytes value)]
  | JSON.OBJECT [("panic", value)] =>
      let val data = encode [“Uint 256”] [value]
      in con "Reverted" [listSyntax.mk_append
           (bytes_term [0x4e, 0x48, 0x7b, 0x71], data)] end
  | JSON.OBJECT [("revert", JSON.STRING value)] =>
      con "Reverted" [bytes_term (hex_bytes value)]
  | _ => fail "unsupported expectation"

fun run_bytecode_case {suite, artifact, code, initcode, peer, declarations, refs} c =
  let
    val name = name_field c "name"
    val prefix = "bytecode_" ^ suite ^ "_" ^ name
    val (data, outputs) = abi_call artifact c
    val input = call_input initcode c
    val imms = {names = map (fn (name, id, _) => (name, id)) declarations, refs = refs}
    val case_tm = case_term peer imms input c
    val words = immutable_words declarations c
    val accounts = “case_accounts (patch_immutables ^refs ^words ^code)
                      (^case_tm).case_storage (^case_tm).case_sender
                      (^case_tm).case_peer_code (^case_tm).case_peer_storage”
    val tx = “case_tx ^case_tm ^data”
    val input_def = define (prefix ^ "_input")
      (pairSyntax.list_mk_pair [accounts, tx, refs])
    val () = cv_auto_trans input_def
    val input_constant = lhs (concl input_def)
    val expected = raw_expectation outputs c
    val expected_store = listSyntax.mk_append
      (storage (JSONUtil.findField c "final_storage"), storage (JSONUtil.findField c "storage"))
    val expected_events = logs (JSONUtil.findField c "logs")
    val expected_run =
      “(^expected, SOME (seed_storage ^expected_store), expected_logs ^expected_events)”
    val equality = mk_eq (“bytecode_execution ^input_constant”, expected_run)
    val evaluated = cv_eval equality
    val () = if rhs (concl evaluated) ~~ T then ()
             else fail (suite ^ "." ^ name ^ ": bytecode differs from the expectation")
    val _ = save_thm (prefix, EQT_ELIM evaluated)
  in
    emit [("kind", json_string "case"), ("suite", json_string suite),
          ("case", json_string name), ("side", json_string "bytecode"),
          ("status", json_string "agree"), ("theorem", json_string prefix)];
    true
  end
  handle e =>
    (emit [("kind", json_string "case"), ("suite", json_string suite),
           ("case", json_string (string_field c "name")),
           ("side", json_string "bytecode"), ("status", json_string "error"),
           ("message", json_string (General.exnMessage e))];
     false)

(* Prove complete bytecode observations without loading the Solidity frontend. *)
fun run_suite_file {root, suite_file} =
  let
    val s = JSONParser.parseFile (root ^ "/" ^ suite_file)
    val suite = name_field s "name"
    val source = string_field s "source"
    val contract = string_field s "contract"
    val artifact = read_bytecode_artifact (root ^ "/" ^ string_field s "artifact")
    val target = artifact_contract artifact source contract
    val prefix = "bytecode_" ^ suite
    val code = code_constant (prefix ^ "_code") "deployedBytecode" artifact source contract
    val peer = peer_code root prefix s
    val init = ref NONE
    fun initcode () = case !init of
      SOME code => code
    | NONE => let val code = code_constant (prefix ^ "_initcode") "bytecode" artifact source contract
              in init := SOME code; code end
    val (declarations, refs) = artifact_immutables artifact source contract
    val env =
      {suite = suite, artifact = target, code = code, initcode = initcode,
       peer = peer, declarations = declarations, refs = refs}
    val ok = List.foldl (fn (c, ok) => run_bytecode_case env c andalso ok)
               true (array_field s "cases")
  in
    if ok then () else fail (suite ^ ": bytecode suite failed")
  end

end
