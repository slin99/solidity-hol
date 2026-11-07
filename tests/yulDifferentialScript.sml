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

(* Each stage's actual object layout, alongside its creation code. *)
Datatype:
  yul_creation_program = <|
    creation_body : yul_stmt list;
    creation_name : string;
    deployed_name : string;
    creation_bytes : byte list;
    deployed_bytes : byte list;
    creation_refs : (num # num list) list
  |>
End

(* The frame the corpus's cases run in: the contract account at
 * contract_address holding the case's initial storage, its deployed bytecode
 * and the case's value, the case's sender funded for it, the peer contract the
 * case's suite declares (reached through a call builtin, whose callee is
 * always an account's bytecode, run by Verifereum, never the imported Yul),
 * the case's calldata
 * and call value, and the
 * transaction and block the bytecode run is given -- its own frame's
 * transaction parameters, so that origin, gasprice, chainid and the block
 * builtins read on both sides what the corpus's transaction says, rather than
 * a second copy of it that could drift from the corpus's. The immutables are
 * the ones the case gives, and zero for the others the code loads, by the
 * names the compiler's Yul loads them by (their declarations' ids); the
 * deployed code holds the same values, as in the bytecode run. The frame's gas
 * limit is that transaction's own -- the number the bytecode run starts with --
 * so a callee of the Yul frame gets the same order of budget as the bytecode
 * run's, and the return data buffer and transient storage start empty as a
 * fresh transaction's do.
 *)
Definition yul_differential_machine_def:
  yul_differential_machine code imm c data =
    <| accounts :=
         (* the same world the source run starts from: the case's value has
          * already moved to the contract, so a call the frame makes with part
          * of it can pay.
          * The contract's own deployed code is there for the call that comes
          * back to its address -- Caller.bumpSelf's ISelf(address(this)) -- so
          * that such a call runs the bytecode the real transaction would.
          *)
         transfer_value c.case_sender contract_address c.case_value
           (case_accounts (patch_immutables c.case_immutable_refs imm code)
              c.case_storage c.case_sender c.case_peer_code
              c.case_peer_storage);
       transient := empty_transient_storage;
       logs := [];
       self_address := contract_address;
       caller_address := c.case_sender;
       call_value := n2w c.case_value;
       call_data := data;
       return_data := [];
       code := patch_immutables c.case_immutable_refs imm code;
       objects := FEMPTY; immutable_offsets := FEMPTY;
       (* the compiler's Yul names an immutable by its declaration's id *)
       immutables :=
         FEMPTY |++ MAP (λ(x, _). (toString x, 0w : bytes32)) c.case_immutable_refs
                |++ MAP (λ(x, _, w). (toString x, n2w (num_of_be_bytes w) : bytes32))
                      imm;
       memory := (FEMPTY : num |-> word8);
       memory_size := 0;
       gas_limit := (differential_tx c.case_sender c.case_value data).gasLimit;
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

(* The creation frame has empty calldata; arguments follow its initcode. *)
Definition yul_creation_machine_def:
  yul_creation_machine p c data =
    (yul_differential_machine [] ([] : (num # scalar # byte list) list) c []) with
      <| accounts := transfer_value c.case_sender (case_address c) c.case_value
           (case_accounts [] c.case_storage c.case_sender
              c.case_peer_code c.case_peer_storage);
         self_address := case_address c;
         code := p.creation_bytes ++ data;
         objects := FEMPTY |+ (p.creation_name, (0, LENGTH p.creation_bytes))
           |+ (p.deployed_name,
                (LENGTH p.creation_bytes - LENGTH p.deployed_bytes,
                 LENGTH p.deployed_bytes));
         immutables := FEMPTY;
         immutable_offsets := FEMPTY |++
           MAP (λ(x, offsets). (toString x, offsets)) p.creation_refs;
         transaction_parameters := initial_tx_params differential_chain_id []
           differential_block (case_tx c data) 0 |>
End

(* Compare the bytes actually returned, including immutable patches. *)
Definition yul_created_code_def:
  yul_created_code p imm =
    FOLDL (λcode (x, offsets).
      FOLDL (patch_word (word_to_bytes_be
        (case FLOOKUP imm (toString x) of NONE => (0w : bytes32) | SOME w => w)))
        code offsets) p.deployed_bytes p.creation_refs
End

Definition yul_creation_execution_def:
  yul_creation_execution p c data fuel =
    if LENGTH p.deployed_bytes > LENGTH p.creation_bytes ∨
       DROP (LENGTH p.creation_bytes - LENGTH p.deployed_bytes)
         p.creation_bytes ≠ p.deployed_bytes then
      (Diagnostic InvalidCompletion, NONE, [])
    else
      let m = yul_creation_machine p c data in
      let r = run_yul fuel p.creation_body m in
      case finish_yul_frame m r.machine r.completion of
        YulFrameSuccess out w =>
          if out = yul_created_code p r.machine.immutables then
            (Returned (code_immutable_words p.creation_refs out),
             SOME (lookup_account (case_address c) w.accounts).storage, w.logs)
          else (Diagnostic InvalidCompletion, NONE, [])
      | YulFrameRevert out w =>
          (Reverted out,
           SOME (lookup_account (case_address c) w.accounts).storage, w.logs)
      | YulFrameInvalid _ => (Diagnostic InvalidCompletion, NONE, [])
      | YulFrameResourceLimit => (Diagnostic OutOfFuel, NONE, [])
End

(* A case's call: the same calldata the bytecode run is given, so an
 * unencodable argument or an unknown function is the same diagnostic on both
 * sides.
 *)
Definition yul_case_execution_def:
  yul_case_execution evm_code ycode u c fuel =
    case (input_call u c.case_input, case_immutable_values u c.case_immutables) of
      (INL d, _) => (Diagnostic d, NONE, [])
    | (_, NONE) => (Diagnostic UnencodableArguments, NONE, [])
    | (INR (data, _), SOME imm) =>
        (case c.case_input of
           Deploy _ _ =>
             (case SND ycode of
                NONE => (Diagnostic InvalidCompletion, NONE, [])
              | SOME p => yul_creation_execution p c data fuel)
         | _ =>
             let m = yul_differential_machine evm_code imm c data in
             let r = run_yul fuel (FST ycode) m in
             yul_frame_observation (finish_yul_frame m r.machine r.completion))
End

Definition yul_observation_def:
  yul_observation evm_code ycode u c fuel slots =
    project_observation slots (yul_case_execution evm_code ycode u c fuel)
End

(* The verdict on one case at one stage, as differential_verdict decides it
 * with the Yul run standing where the core run stands.
 *)
Definition yul_case_verdict_def:
  yul_case_verdict code u prog c yfuel ycode =
    let slots = observed_slots prog c.case_storage c.case_final in
    let evm_run = evm_execution code u c in
    let yul_run = yul_case_execution code ycode u c yfuel in
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
  yul_observation code ycode u c yfuel slots =
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
  FST (SND (yul_case_execution code ycode u c yfuel)) =
    SOME (seed_storage (c.case_final ++ c.case_storage))
Proof
  rw[yul_agrees_def, yul_case_verdict_def] >>
  BasicProvers.every_case_tac >> gvs[is_agreement_def]
QED

(* And the log it wrote is the one the case expects. *)
Theorem yul_agrees_logs:
  yul_agrees code u prog c yfuel ycode ⇒
  SND (SND (yul_case_execution code ycode u c yfuel)) = expected_logs c.case_logs
Proof
  rw[yul_agrees_def, yul_case_verdict_def] >>
  BasicProvers.every_case_tac >> gvs[is_agreement_def]
QED

val () = cv_auto_trans yul_differential_machine_def;
val () = cv_auto_trans yul_frame_observation_def;
val () = cv_auto_trans yul_creation_machine_def;
val () = cv_auto_trans yul_created_code_def;
val () = cv_auto_trans yul_creation_execution_def;
val () = cv_auto_trans yul_case_execution_def;
val () = cv_auto_trans yul_observation_def;
val () = cv_auto_trans yul_case_verdict_def;
val () = cv_auto_trans yul_agrees_def;
