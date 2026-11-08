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
  "../testdata/frontend/expected/pure_core.json"
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
