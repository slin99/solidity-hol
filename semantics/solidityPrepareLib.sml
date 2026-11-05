structure solidityPrepareLib :> solidityPrepareLib =
struct

open HolKernel boolLib solidityElaborateTheory solidityCoreWfTheory cv_transLib

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
    "evm.deployedBytecode.immutableReferences", "evm.methodIdentifiers",
    "ir", "irOptimized"]))])]

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

type prepared = {unit : term, program : term, source_valid : thm,
                 elaborates : thm, core_wf : thm}

fun checked_predicate kind message tm =
  let val evaluated = cv_eval tm in
    if rhs (concl evaluated) ~~ T then EQT_ELIM evaluated
    else if rhs (concl evaluated) ~~ F then reject kind message
    else raise mk_HOL_ERR "solidityPrepareLib" "checked_predicate" "non-boolean cv result"
  end

val elaborate_unit_tm = prim_mk_const {Thy = "solidityElaborate", Name = "elaborate_unit"}

fun prepare_unit unit =
  let
    val source_valid = checked_predicate SourceRejected
      "valid_src_unit failed (source validation/subset restriction)"
      (mk_comb (prim_mk_const {Thy = "solidityImport", Name = "valid_src_unit"}, unit))
    val elaborates = (REWRITE_CONV [elaborate_unit_def, source_valid] THENC cv_eval)
      (mk_comb (elaborate_unit_tm, unit))
    val result = rhs (concl elaborates)
    val program = if optionSyntax.is_none result then
      reject UnsupportedLowering "elaborate_unit returned NONE (unsupported lowering)"
      else optionSyntax.dest_some result
    val core_wf = checked_predicate InvalidCore
      "generated program fails wf_core_program"
      “wf_core_program (core_program_environment ^program) ^program”
  in
    {unit = unit, program = program, source_valid = source_valid,
     elaborates = elaborates, core_wf = core_wf}
  end


(* Import from an artifact already checked by read_artifact. *)
fun import_unit artifact source =
  (json_input (fn () =>
    let
      val output = field artifact "output"
      val contracts = case JSONUtil.findField output "contracts" of
        NONE => JSON.OBJECT []
      | SOME all => (case JSONUtil.findField all source of
                      NONE => JSON.OBJECT [] | SOME contracts => contracts)
    in
      solidityImportLib.import_source_unit
        (map (fn (_, s) => field s "ast") (object (field output "sources")))
        (JSONUtil.get (output, map JSONUtil.SEL ["sources", source, "ast"])) contracts
    end)
    handle solidityImportLib.ImportError message => reject UnsupportedImport message
         | solidityImportLib.MalformedInput message => reject MalformedInput message)
  handle PreparationError (kind, message) => reject kind (source ^ ": " ^ message)

fun prepare_artifact {root, path, source} =
  let
    val artifact = read_artifact {root = root, path = path}
    val unit = import_unit artifact source
    val prepared = prepare_unit unit
      handle PreparationError (kind, message) => reject kind (source ^ ": " ^ message)
  in
    {artifact = artifact, prepared = prepared}
  end

end
