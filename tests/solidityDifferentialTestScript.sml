(* The comparison itself: deliberately altered expectations and a mismatching
 * fixture are detected, and diagnostics are never agreement. The corpus
 * witnesses are in the per-suite solidityDifferentialCorpus theories.
 *)
Theory solidityDifferentialTest
Ancestors
  solidityDifferential solidityBytecode
  solidityDifferentialCorpus_pure_core solidityDifferentialCorpus_storage
  solidityDifferentialCorpus_mappings solidityDifferentialCorpus_token
  solidityDifferentialCorpus_transient_values
Libs
  solidityImportLib solidityDifferentialLib cv_transLib wordsLib intLib

(* Read by holbuild's dependency scanner, which stages the fixture. *)
fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps [
  "../testdata/differential/expected/mutant.json",
  "../testdata/differential/negative/bridge.json",
  "../testdata/differential/expected/storage.json",
  "../testdata/differential/storage.sol", "../SOLIDITY_PIN",
  "../profiles/solc-0.8.37-via-ir-osaka.json"]

(* testdata/differential/mutant.sol: PureCore.add, but wrapping. *)
Definition mutant_code_def:
  mutant_code = REVERSE $ hex_to_rev_bytes [] $
    ^(stringSyntax.fromMLstring
        (artifact_deployed_bytecode
           "../testdata/differential/expected/mutant.json"
           "testdata/differential/mutant.sol" "Mutant"))
End

val () = cv_trans_deep_embedding EVAL mutant_code_def;

(* testdata/differential/mutant.sol: Token.mint, logging a different Transfer. *)
Definition log_mutant_code_def:
  log_mutant_code = REVERSE $ hex_to_rev_bytes [] $
    ^(stringSyntax.fromMLstring
        (artifact_deployed_bytecode
           "../testdata/differential/expected/mutant.json"
           "testdata/differential/mutant.sol" "LogMutant"))
End

val () = cv_trans_deep_embedding EVAL log_mutant_code_def;

(* A call of a named function from the default sender, without value, that
 * logs nothing. *)
Definition named_call_def:
  named_call name args storage expect final =
    <| case_sender := 0x2000w; case_value := 0; case_input := NamedCall name args;
       case_storage := storage; case_peer_code := []; case_peer_storage := [];
       case_expect := expect; case_final := final; case_logs := [];
       case_immutables := []; case_immutable_refs := [] |>
End

val () = cv_auto_trans named_call_def;

(* Evaluates the one call of the named function, so that the bytecode run,
 * the evaluator run and the comparison are separate proof steps.
 *)
fun cv_eval_call name =
  ONCE_DEPTH_CONV (fn t =>
    let val (f, _) = strip_comb t in
      if is_const f andalso fst (dest_const f) = name then cv_eval t
      else NO_CONV t
    end)

Theorem altered_expectation_detected:
  differential_verdict corpus_pure_core_code corpus_pure_core_unit
    corpus_pure_core_program 1000 (named_call "add" [IntArg 2; IntArg 3] []
    (ExpectReturn [IntArg 6]) []) =
  Unexpected (returned [Uint 8] [NumV 5]) (returned [Uint 8] [NumV 6])
Proof
  simp_tac std_ss [differential_verdict_def, LET_THM] >>
  CONV_TAC (cv_eval_call "observed_slots") >>
  CONV_TAC cv_eval
QED

Theorem altered_panic_code_detected:
  differential_verdict corpus_pure_core_code corpus_pure_core_unit
    corpus_pure_core_program 1000 (named_call "add" [IntArg 200; IntArg 100] []
    (ExpectPanic 0x12) []) =
  Unexpected (Reverted (panic_data 0x11)) (Reverted (panic_data 0x12))
Proof
  simp_tac std_ss [differential_verdict_def, LET_THM] >>
  CONV_TAC (cv_eval_call "observed_slots") >>
  CONV_TAC cv_eval
QED

Theorem altered_final_storage_detected:
  differential_verdict corpus_storage_code corpus_storage_unit
    corpus_storage_program 1000 (named_call "setTotal" [IntArg 7] []
    (ExpectReturn []) [(0, 8)]) =
  StorageUnexpected [(1, 0); (2, 0); (3, 0); (0, 7)]
    [(1, 0); (2, 0); (3, 0); (0, 8)]
Proof
  simp_tac std_ss [differential_verdict_def, LET_THM] >>
  CONV_TAC (cv_eval_call "observed_slots") >>
  CONV_TAC cv_eval
QED

Theorem mismatching_fixture_detected:
  differential_verdict mutant_code corpus_pure_core_unit
    corpus_pure_core_program 1000 (named_call "add" [IntArg 200; IntArg 100] []
    (ExpectPanic 0x11) []) =
  Mismatch (returned [Uint 8] [NumV 44]) (Reverted (panic_data 0x11))
Proof
  simp_tac std_ss [differential_verdict_def, LET_THM] >>
  CONV_TAC (cv_eval_call "observed_slots") >>
  CONV_TAC cv_eval
QED

(* The mutant agrees where it behaves like the source. *)
Theorem mismatching_fixture_agrees_in_range:
  differential_agrees mutant_code corpus_pure_core_unit
    corpus_pure_core_program 1000 (named_call "add" [IntArg 2; IntArg 3] []
    (ExpectReturn [IntArg 5]) [])
Proof
  simp_tac std_ss [differential_agrees_def, differential_verdict_def, LET_THM] >>
  CONV_TAC (cv_eval_call "observed_slots") >>
  CONV_TAC cv_eval
QED

Theorem fuel_exhaustion_inconclusive:
  differential_verdict corpus_pure_core_code corpus_pure_core_unit
    corpus_pure_core_program 1 (named_call "fact" [IntArg 5] []
    (ExpectReturn [IntArg 120]) []) =
  Inconclusive (returned [Uint 256] [NumV 120]) (Diagnostic OutOfFuel)
Proof
  simp_tac std_ss [differential_verdict_def, LET_THM] >>
  CONV_TAC (cv_eval_call "observed_slots") >>
  CONV_TAC cv_eval
QED

(* Equal diagnostics on both sides are still not agreement. *)
Theorem unknown_function_inconclusive:
  differential_verdict corpus_pure_core_code corpus_pure_core_unit
    corpus_pure_core_program 1000 (named_call "missing" [] [] (ExpectReturn []) []) =
  Inconclusive (Diagnostic UnknownFunction) (Diagnostic UnknownFunction)
Proof
  simp_tac std_ss [differential_verdict_def, LET_THM] >>
  CONV_TAC (cv_eval_call "observed_slots") >>
  CONV_TAC cv_eval
QED

Theorem argument_out_of_range_inconclusive:
  differential_verdict corpus_pure_core_code corpus_pure_core_unit
    corpus_pure_core_program 1000 (named_call "add" [IntArg 256; IntArg 0] []
    (ExpectReturn [IntArg 0]) []) =
  Inconclusive (Diagnostic UnencodableArguments)
    (Diagnostic UnencodableArguments)
Proof
  simp_tac std_ss [differential_verdict_def, LET_THM] >>
  CONV_TAC (cv_eval_call "observed_slots") >>
  CONV_TAC cv_eval
QED

(* The source-only mutant writes an unlisted mapping key. Both runs return zero
 * and agree on every old observed slot; their complete storage differs.
 *)
val unlisted_write = rhs (concl (EVAL
  “corpus_mappings_program with procedures :=
    MAP (λproc. if proc.procedure_id = AstId 41 then
      proc with body :=
        [DefineStmt (AstId 900000) (ReferenceType (MappingT (UintT 256) (UintT 8)))
           (StateReferenceOperation (AstId 5));
         DefineStmt (AstId 900001) (ReferenceType (UintT 8))
           (NavigateOperation (UintT 8) (BoundAtom (AstId 900000))
             (IndexNavigation (ConstantAtom (IntegerValue 987654321))));
         CaptureValueStmt (AstId 900002) (BoundAtom (AstId 900001));
         WriteScalarStmt (AstId 900002) (UintT 8)
           (ConstantAtom (IntegerValue 17))] ++ proc.body
      else proc) corpus_mappings_program.procedures”));

Definition unlisted_write_program_def:
  unlisted_write_program = ^unlisted_write
End

val () = cv_auto_trans unlisted_write_program_def;

Theorem unlisted_write_program_wf:
  wf_core_program (core_program_environment unlisted_write_program) unlisted_write_program
Proof
  CONV_TAC cv_eval
QED

Theorem unlisted_mapping_write_escaped_slot_projection:
  evm_observation corpus_mappings_code corpus_mappings_unit
      (named_call "read" [IntArg 0] [] (ExpectReturn [IntArg 0]) [])
      (observed_slots unlisted_write_program [] []) =
  source_observation corpus_mappings_code corpus_mappings_unit
      unlisted_write_program 1000
      (named_call "read" [IntArg 0] [] (ExpectReturn [IntArg 0]) [])
      (observed_slots unlisted_write_program [] [])
Proof
  CONV_TAC (cv_eval_call "observed_slots") >>
  CONV_TAC (cv_eval_call "evm_observation") >>
  CONV_TAC (cv_eval_call "source_observation") >> REFL_TAC
QED

Theorem unlisted_mapping_write_old_comparison_agrees:
  compare_observations
    (expected_outcome corpus_mappings_unit (NamedCall "read" [IntArg 0]) (ExpectReturn [IntArg 0]), [(0,0); (1,0); (2,0); (3,0); (4,0); (5,0); (6,0)])
    (evm_observation corpus_mappings_code corpus_mappings_unit
      (named_call "read" [IntArg 0] [] (ExpectReturn [IntArg 0]) [])
      (observed_slots unlisted_write_program [] []))
    (source_observation corpus_mappings_code corpus_mappings_unit
      unlisted_write_program 1000
      (named_call "read" [IntArg 0] [] (ExpectReturn [IntArg 0]) [])
      (observed_slots unlisted_write_program [] [])) = Agree (expected_outcome corpus_mappings_unit (NamedCall "read" [IntArg 0]) (ExpectReturn [IntArg 0]))
Proof
  CONV_TAC (cv_eval_call "observed_slots") >>
  CONV_TAC (cv_eval_call "evm_observation") >>
  CONV_TAC (cv_eval_call "source_observation") >> CONV_TAC cv_eval
QED

Theorem unlisted_mapping_write_detected:
  differential_verdict corpus_mappings_code corpus_mappings_unit
    unlisted_write_program 1000 (named_call "read" [IntArg 0] []
    (ExpectReturn [IntArg 0]) []) =
  StorageMismatch [(0,0); (1,0); (2,0); (3,0); (4,0); (5,0); (6,0)]
                  [(0,0); (1,0); (2,0); (3,0); (4,0); (5,0); (6,0)]
Proof
  simp_tac std_ss [differential_verdict_def, LET_THM] >>
  CONV_TAC (cv_eval_call "observed_slots") >>
  CONV_TAC cv_eval
QED

(* Logs: a call that agrees on outcome and storage but logs differently is a
 * mismatch, and logs other than the case expects are unexpected. mint(0x3000,
 * 5) writes the supply (slot 2) and balances[0x3000] (keccak256 of the key and
 * slot 0).
 *)
Definition mint_call_def:
  mint_call logs =
    <| case_sender := 0x2000w; case_value := 0;
       case_input := NamedCall "mint" [IntArg 0x3000; IntArg 5];
       case_storage := []; case_peer_code := []; case_peer_storage := [];
       case_expect := ExpectReturn [];
       case_final :=
         [(2, 5);
          (68113724183316182233052564790125915752421945217496801851705428207216635038832,
           5)];
       case_logs := logs; case_immutables := []; case_immutable_refs := [] |>
End

val () = cv_auto_trans mint_call_def;

Definition is_log_mismatch_def:
  is_log_mismatch v = case v of LogMismatch _ _ => T | _ => F
End

Definition is_log_unexpected_def:
  is_log_unexpected v = case v of LogUnexpected _ _ => T | _ => F
End

val () = cv_auto_trans is_log_mismatch_def;
val () = cv_auto_trans is_log_unexpected_def;

Theorem different_logs_detected:
  is_log_mismatch (differential_verdict log_mutant_code corpus_token_unit
    corpus_token_program 1000 (mint_call []))
Proof
  simp_tac std_ss [differential_verdict_def, LET_THM] >>
  CONV_TAC (cv_eval_call "observed_slots") >>
  CONV_TAC cv_eval
QED

Theorem unexpected_logs_detected:
  is_log_unexpected (differential_verdict corpus_token_code corpus_token_unit
    corpus_token_program 1000 (mint_call []))
Proof
  simp_tac std_ss [differential_verdict_def, LET_THM] >>
  CONV_TAC (cv_eval_call "observed_slots") >>
  CONV_TAC cv_eval
QED

(* Exercise the runner, including its reported diagnostics, rather than only
 * differential_verdict: these paths previously hid an input mismatch or
 * replaced UnknownFunction with a generic bridge error. *)
local
  val path = OS.FileSys.tmpName ()
  val output = TextIO.openOut path
  val saved = TextIO.getOutstream TextIO.stdOut
  val () = TextIO.flushOut TextIO.stdOut
  val () = TextIO.setOutstream (TextIO.stdOut, TextIO.getOutstream output)
  val rejected =
    ((solidityDifferentialLib.run_suite_file
        {root = "..", suite_file = "testdata/differential/negative/bridge.json",
         fuel = 1000, bytecode_theory = "solidityBytecodeCorpus_storage"}; false)
     handle HOL_ERR _ => true)
    handle e => (TextIO.setOutstream (TextIO.stdOut, saved);
                 TextIO.closeOut output; OS.FileSys.remove path; raise e)
  val () = TextIO.flushOut TextIO.stdOut
  val () = TextIO.setOutstream (TextIO.stdOut, saved)
  val () = TextIO.closeOut output
  val input = TextIO.openIn path
  val report = TextIO.inputAll input
  val () = TextIO.closeIn input
  val () = OS.FileSys.remove path
  val cases = List.filter (String.isPrefix "differential-result: " )
                (String.tokens (fn c => c = #"\n") report)
  fun reported fields = List.exists
    (fn line => List.all (fn field => String.isSubstring field line) fields) cases
in
  val () = if rejected andalso
      reported ["\"case\":\"set_total\"", "\"status\":\"error\"",
                "prepared EVM input differs", "transaction"] andalso
      reported ["\"case\":\"get_total_reads_storage\"",
                "\"status\":\"inconclusive\"", "UnknownFunction"]
    then () else raise Fail ("bridge regression: " ^ report)
end

(* call_contract is a frame entry. The transaction driver supplies a fresh
 * transient map, while another call in the same transaction keeps it. *)
Definition enter_transient_guard_def:
  enter_transient_guard world =
    case input_call corpus_transient_values_unit (NamedCall "enter" []) of
      INR (data, _) => call_contract 1000 corpus_transient_values_program FEMPTY
        (differential_frame 0x2000w 0 data) world
    | INL _ => ContractInvalid "test calldata"
End

val () = cv_auto_trans enter_transient_guard_def;

Theorem transient_guard_lives_for_one_transaction:
  case enter_transient_guard (differential_world empty_accounts) of
    ContractReturned data world =>
      data = num_to_bytes 32 11 ∧
      (case enter_transient_guard world of
         ContractReverted [] _ => T | _ => F) ∧
      (case enter_transient_guard (differential_world world.accounts) of
         ContractReturned next _ => next = data | _ => F)
  | _ => F
Proof
  CONV_TAC cv_eval
QED
