structure solidityPrepareLib :> solidityPrepareLib =
struct

open HolKernel boolLib solidityElaborateTheory solidityCoreWfTheory cv_transLib

(* cv_eval sizes word literals (selectors, assembly numbers) with the rules
 * wordsLib adds to the compset when it loads; without it, it fails with
 * "non-cv constant: (:256)". *)
val _ = wordsLib.WORD_CONV

datatype failure = MalformedInput | UnsupportedImport | UnsupportedLowering
                   | SourceRejected | InvalidCore
exception PreparationError of failure * string

fun failure_name MalformedInput = "malformed-input"
  | failure_name UnsupportedImport = "unsupported-import"
  | failure_name UnsupportedLowering = "unsupported-lowering"
  | failure_name SourceRejected = "source-rejected"
  | failure_name InvalidCore = "invalid-core"

fun reject kind message = raise PreparationError (kind, message)

val field = JSONUtil.lookupField
fun string_field value key = JSONUtil.asString (field value key)
fun object (JSON.OBJECT fields) = fields
  | object value = raise JSONUtil.JSONError (JSONUtil.NotObject, value)

(* Object order is immaterial; duplicate keys are not an exact contract. *)
fun json_equal (JSON.OBJECT xs, JSON.OBJECT ys) =
      length xs = length ys andalso
      List.all (fn (key, value) =>
        length (List.filter (fn (k, _) => k = key) xs) = 1 andalso
        case List.filter (fn (k, _) => k = key) ys of
          [(_, other)] => json_equal (value, other)
        | _ => false) xs
  | json_equal (JSON.ARRAY xs, JSON.ARRAY ys) =
      length xs = length ys andalso ListPair.allEq json_equal (xs, ys)
  | json_equal (JSON.STRING x, JSON.STRING y) = x = y
  | json_equal (JSON.INT x, JSON.INT y) = x = y
  | json_equal (JSON.BOOL x, JSON.BOOL y) = x = y
  | json_equal (JSON.NULL, JSON.NULL) = true
  | json_equal _ = false

fun json_input work =
  work ()
  handle e as JSONUtil.JSONError _ => reject MalformedInput (JSONUtil.exnMessage e)
       | e as JSONUtil.FieldNotFound _ => reject MalformedInput (JSONUtil.exnMessage e)
       | e as JSONUtil.NotObject => reject MalformedInput (JSONUtil.exnMessage e)
       | e as JSONUtil.NotArray => reject MalformedInput (JSONUtil.exnMessage e)

fun read_json path =
  JSONParser.parseFile path
  handle Fail message => reject MalformedInput (path ^ ": " ^ message)
       | IO.Io {name, function, cause} =>
           reject MalformedInput (path ^ ": " ^ function ^ " " ^ name ^ ": " ^
                                  General.exnMessage cause)

fun read_pin root =
  let
    val stream = TextIO.openIn (OS.Path.concat (root, "SOLIDITY_PIN"))
    val text = TextIO.inputAll stream
    val () = TextIO.closeIn stream
  in
    String.concat (String.tokens Char.isSpace text)
  end

val output_selection = JSON.OBJECT [("*", JSON.OBJECT [
  ("", JSON.ARRAY [JSON.STRING "ast"]),
  ("*", JSON.ARRAY (map JSON.STRING ["abi", "storageLayout", "transientStorageLayout",
    "evm.bytecode.object", "evm.deployedBytecode.object",
    "evm.deployedBytecode.immutableReferences", "evm.methodIdentifiers"]))])]

fun read_artifact {root, path} = json_input (fn () =>
  let
    val artifact = read_json path
    val profile = read_json (OS.Path.concat (root, "profiles/solc-0.8.37-via-ir-osaka.json"))
    val pin = read_pin root
    fun require condition message =
      if condition then () else reject MalformedInput (path ^ ": " ^ message)
    val format = string_field artifact "format"
    val () = require (format = "solidity-hol-solc-artifact-v1")
      ("artifact format " ^ format ^ "; expected solidity-hol-solc-artifact-v1")
    val compiler = field artifact "compiler"
    val () = require (string_field compiler "pin" = pin) "compiler pin differs from SOLIDITY_PIN"
    val prefix = string_field profile "compilerVersion" ^ "+commit."
    fun identity token =
      String.isPrefix prefix token andalso
      let
        val suffix = String.extract (token, size prefix, NONE)
        val commit = hd (String.fields (fn c => c = #".") suffix)
      in
        size commit >= 8 andalso String.isPrefix (String.map Char.toLower commit) (String.map Char.toLower pin)
      end
    fun reported_identity ("Version:" :: version :: rest) =
          identity version orelse reported_identity rest
      | reported_identity (_ :: rest) = reported_identity rest
      | reported_identity [] = false
    val () = require (reported_identity
      (String.tokens Char.isSpace (string_field compiler "reportedVersion")))
      "reported compiler version/commit differs from pinned profile"
    val () = require (json_equal (field artifact "profile", profile))
      "recorded profile differs from pinned profile"
    val settings = object (field profile "settings")
    val input = field artifact "input"
    val () = require (string_field input "language" = "Solidity") "input language must be Solidity"
    val () = require (json_equal (field input "settings",
      JSON.OBJECT (settings @ [("outputSelection", output_selection)])))
      "input settings differ from pinned profile/output selection"
    val _ = object (field input "sources")
    val output = field artifact "output"
    val () = require (not (null (object (field output "sources"))))
      "artifact has no source units"
    val () = case JSONUtil.findField output "errors" of
      NONE => ()
    | SOME errors => List.app (fn error =>
        require (string_field error "severity" <> "error") "artifact contains compiler errors")
        (JSONUtil.asArray errors |> Vector.foldr (op ::) [])
  in
    artifact
  end)

type function_outcome = {id : int, name : string, reason : string option}
type prepared = {unit : term, program : term, source_valid : thm,
                 elaborates : thm, core_wf : thm,
                 functions : function_outcome list}

(* A predicate evaluated to T, or a rejection with the message rejection
 * computes. *)
fun checked_predicate kind rejection tm =
  let val evaluated = cv_eval tm in
    if rhs (concl evaluated) ~~ T then EQT_ELIM evaluated
    else if rhs (concl evaluated) ~~ F then reject kind (rejection ())
    else raise mk_HOL_ERR "solidityPrepareLib" "checked_predicate" "non-boolean cv result"
  end

val elaborate_unit_tm = prim_mk_const {Thy = "solidityElaborate", Name = "elaborate_unit"}
fun import_const name = prim_mk_const {Thy = "solidityImport", Name = name}

fun cv_value tm = rhs (concl (cv_eval tm))

fun dedup xs = rev (List.foldl (fn (x, seen) => if mem x seen then seen else x :: seen) [] xs)

(* A blocker (id, reason) as a line: the importer's reasons already name
 * their node ("<node type> <id>: ..."), HOL's tags don't contain ": ". *)
fun blocker_line t =
  case pairSyntax.strip_pair t of
    [id, reason] =>
      let val reason = stringSyntax.fromHOLstring reason in
        if String.isSubstring ": " reason then reason
        else Arbnum.toString (numSyntax.dest_numeral id) ^ ": " ^ reason
      end
  | _ => raise mk_HOL_ERR "solidityPrepareLib" "blocker_line" "bad blocker"

fun record_field r name =
  snd (valOf (List.find (fn (n, _) => n = name) (#2 (TypeBase.dest_record r))))

fun function_id f =
  numSyntax.int_of_term (record_field (record_field f "fn_info") "node_id")

fun unit_record unit =
  if TypeBase.is_record unit then unit else rhs (concl (computeLib.EVAL_CONV unit))

(* The functions and library functions of a unit's contracts. *)
fun unit_function_terms unit =
  List.concat (map (fn c =>
      List.concat (map (fn name => #1 (listSyntax.dest_list (record_field c name)))
        ["contract_functions", "contract_library_functions"]))
    (#1 (listSyntax.dest_list (record_field (unit_record unit) "unit_contracts"))))

(* The unit with the functions of the given ids marked unsupported, each
 * with its reason. *)
fun mark_unsupported reasons unit0 =
  let
    val unit = unit_record unit0
    fun mark_function f =
      case List.find (fn (x, _) => function_id f = x) reasons of
        NONE => f
      | SOME (_, reason) =>
          TypeBase.mk_record (type_of f,
            map (fn ("fn_unsupported", _) =>
                      ("fn_unsupported", optionSyntax.mk_some (stringSyntax.fromMLstring reason))
                  | field => field) (#2 (TypeBase.dest_record f)))
    fun mark_list tm =
      listSyntax.mk_list (map mark_function (listSyntax.dest_list tm |> #1),
                          listSyntax.dest_list tm |> #2)
    fun mark_contract c =
      TypeBase.mk_record (type_of c,
        map (fn (name, value) =>
               if name = "contract_functions" orelse name = "contract_library_functions"
               then (name, mark_list value) else (name, value))
          (#2 (TypeBase.dest_record c)))
  in
    TypeBase.mk_record (type_of unit,
      map (fn ("unit_contracts", cs) =>
                ("unit_contracts",
                 listSyntax.mk_list (map mark_contract (#1 (listSyntax.dest_list cs)),
                                     #2 (listSyntax.dest_list cs)))
            | field => field) (#2 (TypeBase.dest_record unit)))
  end

(* What fails to elaborate, by function id (or the id of the contract for
 * what isn't in a function), with its blocker lines, elaborated strictly
 * (as elaborate_unit does) or not (calls may reach unsupported functions). *)
fun elaboration_failures strict unit =
  map (fn t =>
         case pairSyntax.strip_pair t of
           [x, blockers] =>
             (numSyntax.int_of_term x,
              map blocker_line (#1 (listSyntax.dest_list blockers)))
         | _ => raise mk_HOL_ERR "solidityPrepareLib" "elaboration_failures" "bad entry")
    (#1 (listSyntax.dest_list
      (cv_value (list_mk_comb (prim_mk_const
         {Thy = "solidityElaborate", Name = "unit_elaboration_failures"},
         [if strict then T else F, unit])))))

(* Mark unsupported the supported functions that fail to elaborate, with
 * their blockers, also because they call an unsupported function, until
 * none does. Each round marks at least one function or ends. *)
fun mark_failures unit =
  let
    val supported = List.mapPartial (fn f =>
        if optionSyntax.is_none (record_field f "fn_unsupported")
        then SOME (function_id f) else NONE) (unit_function_terms unit)
  in
    case List.filter (fn (x, _) => mem x supported) (elaboration_failures true unit) of
      [] => unit
    | failing =>
        let
          val loose = elaboration_failures false unit
          fun reason x =
            case List.find (fn (y, _) => x = y) loose of
              NONE => "calls an unsupported function"
            | SOME (_, []) => "uses an unsupported declaration"
            | SOME (_, blockers) => String.concatWith "\n" blockers
        in
          mark_failures
            (mark_unsupported (map (fn (x, _) => (x, reason x)) failing) unit)
        end
  end

(* Every blocker of a unit that is rejected: the whole-unit checks', the
 * importer's in its functions, and what fails to elaborate. *)
fun rejection_lines unit =
  dedup
    (map blocker_line (#1 (listSyntax.dest_list
       (cv_value (mk_comb (import_const "unit_rejections", unit))))) @
     List.concat (map (fn f =>
         let val reason = record_field f "fn_unsupported" in
           if optionSyntax.is_none reason then []
           else String.fields (fn c => c = #"\n")
                  (stringSyntax.fromHOLstring (optionSyntax.dest_some reason))
         end) (unit_function_terms unit)) @
     List.concat (map #2 (elaboration_failures false unit)))

fun rejection_message fallback unit () =
  case rejection_lines unit of
    [] => fallback
  | lines => String.concatWith "\n" lines

fun function_outcomes unit =
  map (fn t =>
         case pairSyntax.strip_pair t of
           [x, name, reason] =>
             {id = numSyntax.int_of_term x,
              name = stringSyntax.fromHOLstring name,
              reason = if optionSyntax.is_some reason
                       then SOME (stringSyntax.fromHOLstring (optionSyntax.dest_some reason))
                       else NONE}
         | _ => raise mk_HOL_ERR "solidityPrepareLib" "function_outcomes" "bad entry")
    (#1 (listSyntax.dest_list
      (cv_value (mk_comb (import_const "unit_functions", unit)))))

fun prepare_unit imported =
  let
    val unit = mark_failures imported
    val source_valid = checked_predicate SourceRejected
      (rejection_message "valid_src_unit failed (source validation/subset restriction)" imported)
      (mk_comb (import_const "valid_src_unit", unit))
    val elaborates = (REWRITE_CONV [elaborate_unit_def, source_valid] THENC cv_eval)
      (mk_comb (elaborate_unit_tm, unit))
    val result = rhs (concl elaborates)
    val program = if optionSyntax.is_none result then
      reject UnsupportedLowering
        (rejection_message "elaborate_unit returned NONE (unsupported lowering)" imported ())
      else optionSyntax.dest_some result
    val core_wf = checked_predicate InvalidCore
      (fn () => "generated program fails wf_core_program")
      “wf_core_program (core_program_environment ^program) ^program”
  in
    {unit = unit, program = program, source_valid = source_valid,
     elaborates = elaborates, core_wf = core_wf,
     functions = function_outcomes unit}
  end

(* A source of an artifact already checked by read_artifact, imported, with
 * the blockers outside its functions. *)
fun import_unit_blockers artifact source =
  json_input (fn () =>
    let
      val output = field artifact "output"
      val contracts = case JSONUtil.findField output "contracts" of
        NONE => JSON.OBJECT []
      | SOME all => (case JSONUtil.findField all source of
                      NONE => JSON.OBJECT [] | SOME contracts => contracts)
    in
      solidityImportLib.import_source_unit_blockers
        (map (fn (_, s) => field s "ast") (object (field output "sources")))
        (JSONUtil.get (output, map JSONUtil.SEL ["sources", source, "ast"])) contracts
    end)
  handle solidityImportLib.MalformedInput message => reject MalformedInput message

fun import_unit artifact source =
  (case import_unit_blockers artifact source of
     (unit, []) => unit
   | (_, blockers) => reject UnsupportedImport (String.concatWith "\n" blockers))
  handle PreparationError (kind, message) => reject kind (source ^ ": " ^ message)

fun prepare_source artifact source =
  case import_unit_blockers artifact source of
    (unit, []) => prepare_unit unit
  | (unit, blockers) =>
      reject UnsupportedImport (String.concatWith "\n" (dedup (blockers @ rejection_lines unit)))

fun prepare_artifact {root, path, source} =
  let
    val artifact = read_artifact {root = root, path = path}
    val prepared = prepare_source artifact source
      handle PreparationError (kind, message) => reject kind (source ^ ": " ^ message)
  in
    {artifact = artifact, prepared = prepared}
  end

end

end
