(* Running the pinned compiler's own Yul on the differential corpus, and
 * comparing what it does with what the corpus already establishes.
 *
 * The corpus theory (solidityDifferentialCorpus) holds the elaborated core and
 * verifereum's EVM, on the compiled bytecode, to each case's committed
 * expectation: the outcome it declares, the storage it lists and the logs it
 * expects. This theory holds the Yul semantics to the same expectation, on the
 * Yul the same compiler emitted for the same source, at the three stages the
 * design separates (docs/roadmap.md, milestone 2): irAst, the code generator's
 * own output; irOptimizedAst with the optimizer off, after the transformations
 * solc runs then; and irOptimizedAst with the optimizer on, which is what a
 * production build hands to the backend.
 *
 * A run is a frame, as at the EVM boundary: the contract account at
 * contract_address holding the case's initial storage, the case's sender
 * funded for the value it sends, and the case's calldata, call value and
 * transaction parameters -- the same ones the bytecode run is given, so that
 * caller, callvalue, origin, chainid and the rest read the same values on both
 * sides. Its observation is the outcome the EVM sees (a return of ABI-encoded
 * data, a revert, or a diagnostic), the contract's committed storage and the
 * log the frame wrote; a revert takes the initial world back, as
 * finish_yul_frame says. The calldata is built by the same input_call the
 * bytecode run uses, so a named call and raw calldata are called identically
 * on both sides, and the verdict is solidityDifferential's own, with the Yul
 * run standing where the core run stands: a Mismatch is the bytecode run and
 * the Yul run disagreeing on the outcome, an Unexpected is both agreeing on
 * something the case does not declare, Inconclusive is either side being a
 * diagnostic, the storage verdicts compare complete committed storage, and the
 * log verdicts compare the log the frame wrote with the one the case expects.
 *)
Theory yulDifferential
Ancestors
  solidityDifferential yulAST yulState yulEvaluator
Libs
  cv_transLib wordsLib intLib

(* The frame the corpus's cases run in: the contract account at
 * contract_address holding the case's initial storage, the case's sender
 * funded for the value it sends, the peer contract the case's suite declares
 * (whose code is bytecode the Yul side never runs: the corpus's external-call
 * cases reach it through builtins the dialect does not have, so their stages
 * are not admitted), the case's calldata and call value, and the
 * transaction and block the bytecode run is given -- its own frame's
 * transaction parameters, so that origin, gasprice, chainid and the block
 * builtins read on both sides what the corpus's transaction says, rather than
 * a second copy of it that could drift from the corpus's. There are no
 * immutables to load: no corpus suite is compiled with any.
 *)
Definition yul_differential_machine_def:
  yul_differential_machine c data =
    <| accounts :=
         case_accounts [] c.case_storage c.case_sender c.case_peer_code
           c.case_peer_storage;
       logs := [];
       self_address := contract_address;
       caller_address := c.case_sender;
       call_value := n2w c.case_value;
       call_data := data;
       immutables := (FEMPTY : string |-> bytes32);
       memory := (FEMPTY : num |-> word8);
       memory_size := 0;
       scopes := ([] : (string |-> bytes32) list);
       transaction_parameters :=
         initial_tx_params differential_chain_id [] differential_block
           (differential_tx c.case_sender c.case_value data) 0 |>
End

(* What the frame's caller sees, as finish_yul_frame decides it: the same
 * shape contract_observation gives the bytecode run.
 *)
Definition yul_frame_observation_def:
  yul_frame_observation frames =
    case frames of
      YulFrameSuccess data w =>
        (Returned data,
         SOME (lookup_account contract_address w.accounts).storage, w.logs)
    | YulFrameRevert data w =>
        (Reverted data,
         SOME (lookup_account contract_address w.accounts).storage, w.logs)
    | YulFrameInvalid _ => (Diagnostic InvalidCompletion, NONE, [])
    | YulFrameResourceLimit => (Diagnostic OutOfFuel, NONE, [])
End

(* A case's call: the same calldata the bytecode run is given, so an
 * unencodable argument or an unknown function is the same diagnostic on both
 * sides.
 *)
Definition yul_case_execution_def:
  yul_case_execution code u c fuel =
    case input_call u c.case_input of
      INL d => (Diagnostic d, NONE, [])
    | INR (data, _) =>
        let m = yul_differential_machine c data in
        let r = run_yul fuel code m in
        yul_frame_observation (finish_yul_frame m r.machine r.completion)
End

Definition yul_observation_def:
  yul_observation code u c fuel slots =
    project_observation slots (yul_case_execution code u c fuel)
End

(* The verdict on one case at one stage, as differential_verdict decides it
 * with the Yul run standing where the core run stands.
 *)
Definition yul_case_verdict_def:
  yul_case_verdict code u prog c yfuel ycode =
    let slots = observed_slots prog c.case_storage c.case_final in
    let evm_run = evm_execution code u c in
    let yul_run = yul_case_execution ycode u c yfuel in
    let evm = project_observation slots evm_run in
    let yul = project_observation slots yul_run in
    case compare_observations
      (expected_outcome u c.case_input c.case_expect,
       expected_storage c.case_storage c.case_final slots) evm yul of
      Agree outcome =>
        if FST (SND evm_run) ≠ FST (SND yul_run) then
          StorageMismatch (SND evm) (SND yul)
        else if FST (SND evm_run) ≠
                SOME (seed_storage (c.case_final ++ c.case_storage)) then
          StorageUnexpected (SND evm)
            (expected_storage c.case_storage c.case_final slots)
        else if SND (SND evm_run) ≠ SND (SND yul_run) then
          LogMismatch (SND (SND evm_run)) (SND (SND yul_run))
        else if SND (SND evm_run) ≠ expected_logs c.case_logs then
          LogUnexpected (SND (SND evm_run)) (expected_logs c.case_logs)
        else Agree outcome
    | other => other
End

Definition yul_agrees_def:
  yul_agrees code u prog c yfuel ycode ⇔
    is_agreement (yul_case_verdict code u prog c yfuel ycode)
End

(* The complete-storage and complete-log checks of yul_case_verdict cannot
 * turn an agreement into a disagreement: what holds when compare_observations
 * agrees is what the verdict's own checks leave alone.
 *)
Theorem complete_check_agreement[local]:
  is_agreement
    (case verdict of
       Agree outcome =>
         if b1 then StorageMismatch s1 s2
         else if b2 then StorageUnexpected s3 s4
         else if b3 then LogMismatch l1 l2
         else if b4 then LogUnexpected l3 l4
         else Agree outcome
     | other => other) ⇒
  is_agreement verdict
Proof
  Cases_on ‘verdict’ >> simp[is_agreement_def] >>
  rpt IF_CASES_TAC >> simp[is_agreement_def]
QED

(* What an agreement establishes: the Yul run returns or reverts what the case
 * expects, and it is never a diagnostic. The bytecode run's side is
 * solidityDifferential's differential_agrees_outcomes.
 *)
Theorem yul_agrees_outcomes:
  yul_agrees code u prog c yfuel ycode ∧
  slots = observed_slots prog c.case_storage c.case_final ⇒
  ¬is_diagnostic (expected_outcome u c.case_input c.case_expect) ∧
  yul_observation ycode u c yfuel slots =
    (expected_outcome u c.case_input c.case_expect,
     expected_storage c.case_storage c.case_final slots)
Proof
  rw[yul_agrees_def, yul_case_verdict_def, yul_observation_def] >>
  drule complete_check_agreement >> strip_tac >>
  drule compare_observations_agree >> simp[]
QED

(* And it is at the complete storage the case expects, not just the slots it
 * lists: the whole committed storage, as the bytecode run's agreement is.
 *)
Theorem yul_agrees_storage:
  yul_agrees code u prog c yfuel ycode ⇒
  FST (SND (yul_case_execution ycode u c yfuel)) =
    SOME (seed_storage (c.case_final ++ c.case_storage))
Proof
  rw[yul_agrees_def, yul_case_verdict_def] >>
  BasicProvers.every_case_tac >> gvs[is_agreement_def]
QED

(* And the log it wrote is the one the case expects. *)
Theorem yul_agrees_logs:
  yul_agrees code u prog c yfuel ycode ⇒
  SND (SND (yul_case_execution ycode u c yfuel)) = expected_logs c.case_logs
Proof
  rw[yul_agrees_def, yul_case_verdict_def] >>
  BasicProvers.every_case_tac >> gvs[is_agreement_def]
QED

val () = cv_auto_trans yul_differential_machine_def;
val () = cv_auto_trans yul_frame_observation_def;
val () = cv_auto_trans yul_case_execution_def;
val () = cv_auto_trans yul_observation_def;
val () = cv_auto_trans yul_case_verdict_def;
val () = cv_auto_trans yul_agrees_def;
