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
    val default_profile = read_json
      (OS.Path.concat (root, "profiles/solc-0.8.37-via-ir-osaka.json"))
    val profile = field artifact "profile"
    val pin = read_pin root
    fun require condition message =
      if condition then () else reject MalformedInput (path ^ ": " ^ message)
    val format = string_field artifact "format"
    val () = require (format = "solidity-hol-solc-artifact-v1")
      ("artifact format " ^ format ^ "; expected solidity-hol-solc-artifact-v1")
    val compiler = field artifact "compiler"
    val () = require (string_field compiler "pin" = pin) "compiler pin differs from SOLIDITY_PIN"
    val prefix = string_field default_profile "compilerVersion" ^ "+commit."
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
    val () =
      if json_equal (profile, default_profile) then
        require (not (Option.isSome (JSONUtil.findField artifact "unoptimizedFailure")))
          "unoptimized profile must not record a fallback"
      else
        let
          val optimized_profile = read_json
            (OS.Path.concat (root, "profiles/solc-0.8.37-via-ir-osaka-optimized.json"))
          val () = require (json_equal (profile, optimized_profile))
            "recorded profile differs from pinned profiles"
          val failure = field artifact "unoptimizedFailure"
          val () = require (json_equal (field failure "profile", default_profile))
            "fallback did not start with the pinned unoptimized profile"
          fun stack_depth_error error =
            let
              val kind = string_field error "type"
              val message = String.map Char.toLower (string_field error "message")
            in
              string_field error "severity" = "error" andalso
              (kind = "YulException" orelse kind = "CompilerError") andalso
              (String.isSubstring "stack too deep" message orelse
               String.isSubstring "too deep in the stack" message)
            end
          val errors = JSONUtil.asArray (field failure "errors") |> Vector.foldr (op ::) []
        in
          require (not (null errors) andalso List.all stack_depth_error errors)
            "optimized profile requires unoptimized stack-depth errors only"
        end
    val settings = object (field profile "settings")
    val input = field artifact "input"
    val () = require (string_field input "language" = "Solidity") "input language must be Solidity"
    val (libraries, ordinary_settings) = List.partition
      (fn (key, _) => key = "libraries") (object (field input "settings"))
    val () = require (case libraries of
        [] => true
      | [(_, links)] => json_equal (links, solidityLinkLib.settings (field artifact "output"))
      | _ => false)
      "input libraries differ from the deterministic link assignment"
    val (remappings, input_settings) = List.partition
      (fn (key, _) => key = "remappings") ordinary_settings
    val () = require (case remappings of
        [] => true
      | [(_, JSON.ARRAY entries)] => List.all
          (fn JSON.STRING entry => String.isSubstring "=" entry | _ => false) entries
      | _ => false)
      "input remappings must be a single array of strings containing '='"
    val () = require (json_equal (JSON.OBJECT input_settings,
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

(* A record literal, as TypeBase.mk_record builds it (an update of every
 * field, in the caller's order, over ARB), equals its constructor applied to
 * the values. One equation per type and field order, proved on first use;
 * NONE for an update that isn't such a literal. *)
val literal_equations = ref ([] : (string * thm option) list)
fun literal_equation lit =
  let
    val (ty, fields) = TypeBase.dest_record lit
    val key = type_to_string ty ^ String.concatWith "," (map #1 fields)
  in
    case List.find (fn (k, _) => k = key) (!literal_equations) of
      SOME (_, th) => th
    | NONE =>
        let
          val generic = TypeBase.mk_record (ty,
            map (fn (name, v) => (name, mk_var ("v_" ^ name, type_of v))) fields)
          val cases = ISPEC (mk_arb ty) (TypeBase.nchotomy_of ty)
          val updates = combinTheory.K_THM :: TypeBase.updates_of ty
          val constructed = rhs (concl ((PURE_ONCE_REWRITE_CONV
              [ASSUME (snd (strip_exists (concl cases)))] THENC
            PURE_REWRITE_CONV updates) generic))
          val th = SOME (TAC_PROOF (([], mk_eq (generic, constructed)),
              STRUCT_CASES_TAC cases THEN PURE_REWRITE_TAC updates THEN REFL_TAC))
            handle HOL_ERR _ => NONE
        in
          literal_equations := (key, th) :: !literal_equations; th
        end
  end
  handle HOL_ERR _ => NONE

fun is_update tm =
  is_comb tm andalso
  let val (head, args) = strip_comb tm in
    length args = 2 andalso is_const head andalso
    String.isSuffix "_fupd" (#1 (dest_const head))
  end

(* tm with its record literals replaced by constructor applications, outside
 * in, so that EVAL can take them apart. cv_eval would instead prove two
 * lemmas per literal on every evaluation. *)
fun literals_conv tm =
  case if is_update tm then literal_equation tm else NONE of
    SOME eq => (REWR_CONV eq THENC SUB_CONV literals_conv) tm
  | NONE => SUB_CONV literals_conv tm

(* from_<ty> v = its cv form, when v is built from constructors and the
 * constants with the given cv equations (from_<ty> c = c_cv (Num 0)): EVAL
 * with integers' rules, then those equations and b2c's on literals, which
 * EVAL leaves in place. v's record literals are taken apart first. This is
 * much cheaper than cv_eval's own translation, which proves a cv_rep theorem
 * per node. *)
fun cv_form_conv cv_thms =
  let
    val compset =
      intReduce.add_int_compset (computeLib.copy (computeLib.the_compset ()))
  in
    RAND_CONV literals_conv THENC computeLib.CBV_CONV compset THENC
    PURE_REWRITE_CONV (cv_primTheory.cv_rep_T :: cv_primTheory.cv_rep_F :: cv_thms)
  end

(* A fresh constant defined as tm, deep-embedded with conv computing its cv
 * form, so that cv_eval reads that form from one equation instead of
 * translating tm node by node. *)
val embedding_counters = ref ([] : (string * int) list)
fun embed name conv tm =
  let
    val n = case List.find (fn (k, _) => k = name) (!embedding_counters) of
              SOME (_, n) => n | NONE => 0
    val () = embedding_counters :=
      (name, n + 1) :: List.filter (fn (k, _) => k <> name) (!embedding_counters)
    val name = name ^ "_" ^ Int.toString n
    val def = new_definition (name ^ "_def", mk_eq (mk_var (name, type_of tm), tm))
    val () = cv_trans_deep_embedding conv def
  in
    def
  end

(* The cv equation (from_<ty> c = c_cv (Num 0)) of the constant embed
 * defined by def. *)
fun cv_thm def =
  DB.fetch "-" (#1 (dest_const (lhs (concl def))) ^ "_cv_thm")

(* th with the embedded constant of def, at the position conv selects,
 * replaced by its definition. *)
fun unembed conv def = CONV_RULE (conv (REWR_CONV def))

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
              List.concat (map (String.fields (fn c => c = #"\n") o blocker_line)
                (#1 (listSyntax.dest_list blockers))))
         | _ => raise mk_HOL_ERR "solidityPrepareLib" "elaboration_failures" "bad entry")
    (#1 (listSyntax.dest_list
      (cv_value (list_mk_comb (prim_mk_const
         {Thy = "solidityElaborate", Name = "unit_elaboration_failures"},
         [if strict then T else F, unit])))))

(* Mark unsupported the supported functions that fail to elaborate, with
 * their blockers, also because they call an unsupported function, until
 * none does. Each round marks at least one function or ends. The unit comes
 * with the definition of its embedded constant, and so does the result.
 * loose is what fails to elaborate non-strictly in the imported unit: a
 * function's non-strict blockers don't depend on what is marked. *)
fun mark_failures embed_unit loose (unit, def) =
  let
    val supported = List.mapPartial (fn f =>
        if optionSyntax.is_none (record_field f "fn_unsupported")
        then SOME (function_id f) else NONE) (unit_function_terms unit)
  in
    case List.filter (fn (x, _) => mem x supported)
           (elaboration_failures true (lhs (concl def))) of
      [] => (unit, def)
    | failing =>
        let
          fun reason x =
            case List.find (fn (y, _) => x = y) (loose ()) of
              NONE => "calls an unsupported function"
            | SOME (_, []) => "uses an unsupported declaration"
            | SOME (_, blockers) => String.concatWith "\n" blockers
          val marked = mark_unsupported (map (fn (x, _) => (x, reason x)) failing) unit
        in
          mark_failures embed_unit loose (marked, embed_unit marked)
        end
  end

(* The elaboration blockers to add to the reasons of the functions the
 * importer marked unsupported, so a reason lists every blocker of its
 * function: the new reasons, by function id. *)
fun elaboration_reasons loose unit =
  let
    val marked = List.mapPartial (fn f =>
        let val r = record_field f "fn_unsupported" in
          if optionSyntax.is_none r then NONE
          else SOME (function_id f,
                     String.fields (fn c => c = #"\n")
                       (stringSyntax.fromHOLstring (optionSyntax.dest_some r)))
        end) (unit_function_terms unit)
    val loose = if null marked then [] else loose ()
  in
    List.mapPartial (fn (x, lines) =>
        case List.find (fn (y, _) => x = y) loose of
          NONE => NONE
        | SOME (_, bs) =>
            let val all = dedup (lines @ bs) in
              if length all = length lines then NONE
              else SOME (x, String.concatWith "\n" all)
            end) marked
  end

(* What elaborate_unit_reason reports for the unit as a whole when it
 * rejects it (no contract, say), as lines. *)
fun unit_reason_lines unit =
  let
    val result = cv_value (mk_comb (prim_mk_const
      {Thy = "solidityElaborate", Name = "elaborate_unit_reason"}, unit))
  in
    if sumSyntax.is_inr result then
      List.concat (map (String.fields (fn c => c = #"\n") o blocker_line)
        (#1 (listSyntax.dest_list (#1 (sumSyntax.dest_inr result)))))
    else []
  end

(* Every blocker of a unit that is rejected: the whole-unit checks', the
 * importer's in its functions, what fails to elaborate, and the unit's own
 * elaboration blockers. The unit comes with its embedded constant and its
 * non-strict failures. *)
fun rejection_lines (unit, constant, loose) =
  dedup
    (map blocker_line (#1 (listSyntax.dest_list
       (cv_value (mk_comb (import_const "unit_rejections", constant))))) @
     List.concat (map (fn f =>
         let val reason = record_field f "fn_unsupported" in
           if optionSyntax.is_none reason then []
           else String.fields (fn c => c = #"\n")
                  (stringSyntax.fromHOLstring (optionSyntax.dest_some reason))
         end) (unit_function_terms unit)) @
     List.concat (map #2 loose) @
     unit_reason_lines constant)

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

(* The creation code byte lists of a unit and its byte-sequence literals of
 * at least long_literal bytes (type(C).creationCode) as constants, so that
 * the certificates keep them folded: input abbreviates the unit, whose
 * elaboration has the literals' byte lists, which output folds back. *)
val long_literal = 1024
fun creation_code_definitions unit =
  let
    fun applications name arity tm =
      let val (head, args) = strip_comb tm in
        head ~~ import_const name andalso length args = arity
      end
    fun code tm = record_field (List.nth (#2 (strip_comb tm), 1)) "create_bytecode"
    val literals = List.filter (fn s => size (stringSyntax.fromHOLstring s) >= long_literal)
      (map (fn tm => List.nth (#2 (strip_comb tm), 2))
         (find_terms (applications "SrcLiteral" 4) unit))
    fun bytes s =
      listSyntax.mk_list
        (map (fn c => wordsSyntax.mk_wordii (Char.ord c, 8))
           (String.explode (stringSyntax.fromHOLstring s)),
         wordsSyntax.mk_int_word_type 8)
    fun distinct tms = List.foldl (fn (tm, seen) =>
        if List.exists (aconv tm) seen then seen else tm :: seen) [] tms
    val byte_defs = map (embed "embedded_creation_code" computeLib.EVAL_CONV)
      (distinct (map code (find_terms (applications "SrcCreate" 6) unit) @
                 map bytes literals))
    val literal_defs = map (embed "embedded_literal" computeLib.EVAL_CONV)
      (distinct literals)
  in
    {input = byte_defs @ literal_defs, output = byte_defs}
  end

(* The unit with its large literals abbreviated, the definitions that do it
 * and those that fold them back into its elaboration. *)
fun abbreviate_literals imported =
  let val {input, output} = creation_code_definitions imported in
    (subst (map (fn def => rhs (concl def) |-> lhs (concl def)) input) imported,
     input, output)
  end

(* A computation done at most once, when first asked for. *)
fun once f =
  let val result = ref NONE in
    fn () => case !result of
               SOME x => x
             | NONE => let val x = f () in result := SOME x; x end
  end

(* Why the program has no procedure for the creation (elaborate_contract
 * lists it unsupported) when every constructor is supported, whose reasons
 * would say why: the contracts' own blockers in loose, which include the
 * creation's. A creation that fails only strictly, by calling an unsupported
 * function, has none there and gets its contract's id alone. *)
fun creation_blockers unit program loose =
  let
    val creation = record_field program "creation_procedure"
    val unsupported =
      #1 (listSyntax.dest_list (record_field program "unsupported_procedures"))
    val contracts =
      #1 (listSyntax.dest_list (record_field (unit_record unit) "unit_contracts"))
    val ids = map (fn c =>
        numSyntax.int_of_term (record_field (record_field c "contract_info") "node_id"))
      contracts
    val constructor_unsupported = List.exists (fn f =>
        optionSyntax.is_some (record_field f "fn_unsupported") andalso
        term_eq (record_field f "fn_kind")
          (import_const "ConstructorKind"))
      (unit_function_terms unit)
  in
    if optionSyntax.is_none creation orelse constructor_unsupported orelse
       not (List.exists (term_eq (#1 (pairSyntax.dest_pair
                                       (optionSyntax.dest_some creation))))
              unsupported)
    then []
    else
      case List.concat (map #2 (List.filter (fn (x, _) => mem x ids) (loose ()))) of
        [] => map (fn x => Int.toString x ^ ": creation calls an unsupported function") ids
      | lines => dedup lines
  end

fun prepare_unit imported =
  let
    val (imported, literal_defs, code_defs) = abbreviate_literals (unit_record imported)
    val cv_form_conv = cv_form_conv (map cv_thm literal_defs)
    val embed_unit = embed "embedded_unit" cv_form_conv
    val imported_def = once (fn () => embed_unit imported)
    val imported_constant = lhs o concl o imported_def
    val loose = once (fn () => elaboration_failures false (imported_constant ()))
    fun rejection_message fallback () =
      case rejection_lines (imported, imported_constant (), loose ()) of
        [] => fallback
      | lines => String.concatWith "\n" lines
    val (unit, unit_def) = mark_failures embed_unit loose
      (case elaboration_reasons loose imported of
         [] => (imported, imported_def ())
       | reasons => let val unit = mark_unsupported reasons imported in
                      (unit, embed_unit unit)
                    end)
    val constant = lhs (concl unit_def)
    val source_valid = checked_predicate SourceRejected
      (rejection_message "valid_src_unit failed (source validation/subset restriction)")
      (mk_comb (import_const "valid_src_unit", constant))
    val elaborates = (REWRITE_CONV [elaborate_unit_def, source_valid] THENC cv_eval)
      (mk_comb (elaborate_unit_tm, constant))
    val elaborates = PURE_REWRITE_RULE (map SYM code_defs) elaborates
    val result = rhs (concl elaborates)
    val program = if optionSyntax.is_none result then
      reject UnsupportedLowering
        (rejection_message "elaborate_unit returned NONE (unsupported lowering)" ())
      else optionSyntax.dest_some result
    val program_def = embed "embedded_program" cv_form_conv program
    val embedded_program = lhs (concl program_def)
    val core_wf = checked_predicate InvalidCore
      (fn () => "generated program fails wf_core_program")
      “wf_core_program (core_program_environment ^embedded_program) ^embedded_program”
  in
    {unit = unit, program = program,
     source_valid = unembed RAND_CONV unit_def source_valid,
     elaborates = unembed (LAND_CONV o RAND_CONV) unit_def elaborates,
     core_wf = unembed (fn c => RAND_CONV c THENC LAND_CONV (RAND_CONV c))
                 program_def core_wf,
     functions = function_outcomes constant,
     creation = creation_blockers unit program loose}
  end

(* A source of an artifact already checked by read_artifact, imported, with
 * the blockers outside its functions. *)
fun import_unit_blockers artifact source contract =
  json_input (fn () =>
    solidityImportLib.import_contract_artifact_unit_blockers artifact source contract)
  handle solidityImportLib.ImportError message => reject UnsupportedImport message
       | solidityImportLib.MalformedInput message => reject MalformedInput message

fun import_unit artifact source =
  (case import_unit_blockers artifact source NONE of
     (unit, []) => unit
   | (_, blockers) => reject UnsupportedImport (String.concatWith "\n" blockers))
  handle PreparationError (kind, message) => reject kind (source ^ ": " ^ message)

fun prepare_contract_source artifact source contract =
  case import_unit_blockers artifact source contract of
    (unit, []) => prepare_unit unit
  | (unit, blockers) =>
      let
        val (unit, literal_defs, _) = abbreviate_literals (unit_record unit)
        val constant = lhs (concl (embed "embedded_unit"
          (cv_form_conv (map cv_thm literal_defs)) unit))
      in
        reject UnsupportedImport (String.concatWith "\n" (dedup (blockers @
          rejection_lines (unit, constant, elaboration_failures false constant))))
      end

fun prepare_source artifact source = prepare_contract_source artifact source NONE

fun prepare_contract_artifact {root, path, source, contract} =
  let
    val artifact = read_artifact {root = root, path = path}
    val prepared = prepare_contract_source artifact source contract
      handle PreparationError (kind, message) => reject kind (source ^ ": " ^ message)
  in
    {artifact = artifact, prepared = prepared}
  end

fun prepare_artifact {root, path, source} =
  prepare_contract_artifact {root = root, path = path, source = source, contract = NONE}

end
