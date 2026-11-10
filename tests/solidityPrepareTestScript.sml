(* The checked consumer boundary, including the generated-layout failure
 * previously hidden by elaborate_unit returning NONE.
 *)
Theory solidityPrepareTest
Ancestors
  solidityElaborate solidityImportTest
Libs
  solidityPrepareLib cv_transLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps [
  "../SOLIDITY_PIN", "../profiles/solc-0.8.37-via-ir-osaka.json",
  "../testdata/frontend/expected/pure_core.json",
  "../profiles/solc-0.8.37-via-ir-osaka-optimized.json",
  "../testdata/frontend/expected/stack_depth.json"
]

val checked_artifact = solidityPrepareLib.prepare_artifact
  {root = "..", path = "../testdata/frontend/expected/pure_core.json",
   source = "testdata/frontend/pure_core.sol"};
val prepared = #prepared checked_artifact;

Definition prepared_program_def:
  prepared_program = ^(#program prepared)
End

val () = cv_auto_trans prepared_program_def;

Theorem prepared_program_checked:
  wf_core_program (core_program_environment prepared_program) prepared_program
Proof
  CONV_TAC cv_eval
QED

fun rejects expected work =
  (work (); raise Fail "preparation unexpectedly accepted input")
  handle solidityPrepareLib.PreparationError (actual, _) =>
    if actual = expected then () else raise Fail "wrong preparation failure category";

(* The source layout contract validates slot identity/type alignment but the
 * complete core checker must reject a uint256 at nonzero byte offset.
 *)
val invalid_layout = rhs (concl (EVAL
  “storage_unit with unit_contracts :=
      [HD storage_unit.unit_contracts with contract_storage :=
        (HD (HD storage_unit.unit_contracts).contract_storage with storage_offset := 1) ::
        TL (HD storage_unit.unit_contracts).contract_storage]”));

Definition invalid_generated_layout_def:
  invalid_generated_layout = ^invalid_layout
End

val () = cv_auto_trans invalid_generated_layout_def;

Theorem invalid_layout_source_still_valid:
  valid_src_unit invalid_generated_layout
Proof
  CONV_TAC cv_eval
QED

val () = rejects solidityPrepareLib.InvalidCore
  (fn () => ignore (solidityPrepareLib.prepare_unit “invalid_generated_layout”));

(* A unit with no contract is refused as a whole, with that reason. *)
val () =
  (ignore (solidityPrepareLib.prepare_unit
     “pure_core with unit_contracts := []”);
   raise Fail "preparation unexpectedly accepted input")
  handle solidityPrepareLib.PreparationError
           (solidityPrepareLib.UnsupportedLowering, msg) =>
    if String.isSubstring ": no contract" msg then ()
    else raise Fail ("unit-level reason missing: " ^ msg);

(* A function header the source check rejects (here a parameter's scope or
 * type) rejects the unit: only a body is confined to its function. *)
fun edited_unit name =
  rhs (concl (DB.fetch "solidityImportTest" (name ^ "_def")));
val () = rejects solidityPrepareLib.SourceRejected
  (fn () => ignore (solidityPrepareLib.prepare_unit (edited_unit "wrong_scope")));
val () = rejects solidityPrepareLib.SourceRejected
  (fn () => ignore (solidityPrepareLib.prepare_unit
                      (edited_unit "declaration_type_mismatch")));

(* A modifier whose body fails import makes its invokers unsupported, but its
 * header is still checked with the unit. *)
val modifier_failed = solidityPrepareLib.prepare_unit
  (edited_unit "modifier_failed_body");
val () =
  case List.find (fn {name, ...} => name = "inverse")
         (#functions modifier_failed) of
    SOME {reason = SOME _, ...} => ()
  | _ => raise Fail "inverse: not marked unsupported";
val () = rejects solidityPrepareLib.SourceRejected
  (fn () => ignore (solidityPrepareLib.prepare_unit
                      (edited_unit "modifier_failed_body_wrong_scope")));

val bad_artifact_path = OS.FileSys.tmpName ();
val bad_artifact_stream = TextIO.openOut bad_artifact_path;
val () = TextIO.output (bad_artifact_stream,
  "{\"format\":\"solidity-hol-solc-artifact-v1\",\"compiler\":{\"pin\":\"wrong\"}}");
val () = TextIO.closeOut bad_artifact_stream;
val () = (rejects solidityPrepareLib.MalformedInput
  (fn () => ignore (solidityPrepareLib.read_artifact
    {root = "..", path = bad_artifact_path})))
  handle e => (OS.FileSys.remove bad_artifact_path; raise e);
val () = OS.FileSys.remove bad_artifact_path;

val artifact_stream = TextIO.openIn "../testdata/frontend/expected/pure_core.json";
val artifact_text = TextIO.inputAll artifact_stream;
val () = TextIO.closeIn artifact_stream;
(* The sorted fixture's first settings object is input.settings. *)
val settings_marker = "\"settings\": {";
val (settings_prefix, settings_suffix) =
  Substring.position settings_marker (Substring.full artifact_text);
val () = if Substring.isEmpty settings_suffix then raise Fail "missing settings" else ();

fun with_extra_settings extra check =
  let
    val path = OS.FileSys.tmpName ()
    val stream = TextIO.openOut path
    val () = TextIO.output (stream,
      Substring.string settings_prefix ^ settings_marker ^ extra ^
      Substring.string (Substring.triml (size settings_marker) settings_suffix))
    val () = TextIO.closeOut stream
    val () = check (fn () => solidityPrepareLib.read_artifact {root = "..", path = path})
      handle e => (OS.FileSys.remove path; raise e)
  in
    OS.FileSys.remove path
  end;

val () = with_extra_settings "\"remappings\": [\"a/=b/\"],"
  (fn read =>
    case JSONUtil.get (read (), [JSONUtil.SEL "input", JSONUtil.SEL "settings",
                                 JSONUtil.SEL "remappings"]) of
      JSON.ARRAY [JSON.STRING "a/=b/"] => ()
    | _ => raise Fail "remappings not retained");
val () = with_extra_settings "\"remappings\": []," (fn read => ignore (read ()));
val () = List.app (fn extra => with_extra_settings extra
  (fn read => rejects solidityPrepareLib.MalformedInput (fn () => ignore (read ()))))
  ["\"remappings\": \"a/=b/\",",
   "\"remappings\": [1],",
   "\"remappings\": [\"a/b/\"],",
   "\"remappings\": [], \"remappings\": [],",
   "\"remappings\": [\"a/=b/\"], \"unknownSetting\": true,",
   "\"remappings\": [\"a/=b/\"], \"viaIR\": false,"];

(* The source exporter reached this profile only after solc's unoptimized
 * 17-argument ABI/code generator failed with a stack-depth diagnostic. *)
val fallback_path = "../testdata/frontend/expected/stack_depth.json";
val fallback = solidityPrepareLib.prepare_artifact
  {root = "..", path = fallback_path, source = "testdata/frontend/stack_depth.sol"};
val () = case #functions (#prepared fallback) of
    [{name = "sum", reason = NONE, ...}] => ()
  | _ => raise Fail "stack-depth fallback did not admit sum";
val () = case JSONUtil.get (#artifact fallback,
    map JSONUtil.SEL ["profile", "settings", "optimizer", "enabled"]) of
    JSON.BOOL true => ()
  | _ => raise Fail "fallback did not retain its optimized profile";

fun with_artifact_text text check =
  let
    val path = OS.FileSys.tmpName ()
    val stream = TextIO.openOut path
    val () = TextIO.output (stream, text)
    val () = TextIO.closeOut stream
    val () = check (fn () => solidityPrepareLib.read_artifact {root = "..", path = path})
      handle e => (OS.FileSys.remove path; raise e)
  in
    OS.FileSys.remove path
  end;

fun replace_text old replacement text =
  let val (prefix, suffix) = Substring.position old (Substring.full text) in
    if Substring.isEmpty suffix then text
    else Substring.string prefix ^ replacement ^
         replace_text old replacement
           (Substring.string (Substring.triml (size old) suffix))
  end;

(* A normally compilable source cannot opt into optimization without a
 * recorded stack-depth failure. *)
val () = with_artifact_text
  (replace_text "\"enabled\": false" "\"enabled\": true" artifact_text)
  (fn read => rejects solidityPrepareLib.MalformedInput (fn () => ignore (read ())));

val fallback_stream = TextIO.openIn fallback_path;
val fallback_text = TextIO.inputAll fallback_stream;
val () = TextIO.closeIn fallback_stream;
val (without_failure, _) = Substring.position ",\n  \"unoptimizedFailure\""
  (Substring.full fallback_text);
val () = List.app (fn text => with_artifact_text text
    (fn read => rejects solidityPrepareLib.MalformedInput (fn () => ignore (read ()))))
  [Substring.string without_failure ^ "\n}\n",
   replace_text "\"type\": \"YulException\"" "\"type\": \"ParserError\"" fallback_text,
   replace_text "too deep in the stack" "unrelated compilation error" fallback_text];
