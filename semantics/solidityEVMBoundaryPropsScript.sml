(* Preservation at the concrete adapter seam. No source refinement is assumed. *)
Theory solidityEVMBoundaryProps
Ancestors
  solidityEVMCall vfmRunCall vfmTxParams vfmWfState vfmExecutionProp vfmExecution
  While pair list combin arithmetic

Theorem stepping_preserves_well_formedness:
  ∀n x. wf_state (SND x) ⇒
    wf_state (SND (FUNPOW (step o SND) n x))
Proof
  Induct
  \\ simp[FUNPOW]
  \\ rpt strip_tac
  \\ first_x_assum irule
  \\ simp[step_preserves_wf_state]
QED

Theorem boundary_preserves_well_formedness:
  wf_state es ∧ execute_boundary instruction es = SOME (result, final) ⇒
  wf_state final
Proof
  strip_tac
  \\ ‘wf_state (SND (step es))’ by metis_tac[step_preserves_wf_state]
  \\ Cases_on ‘step es’
  \\ rename1 ‘(entry_result, entered)’
  \\ Cases_on ‘entry_result’
  \\ fs[execute_boundary_def]
  \\ Cases_on ‘LENGTH entered.contexts > LENGTH es.contexts’
  \\ fs[]
  \\ metis_tac[run_call_preserves_wf_state]
QED

(* Transaction parameters are invariant even on semantic aborts. This uses the
 * unconditional upstream single-step law, not stronger storage hypotheses.
 *)
Theorem subtree_preserves_transaction_parameters:
  run_call es = SOME (result, final) ⇒ final.txParams = es.txParams
Proof
  strip_tac
  \\ fs[run_call_def]
  \\ qsuff_tac
    ‘∀x y. OWHILE
      (λ(r, s). ISL r ∧ LENGTH s.contexts ≥ LENGTH es.contexts)
      (step o SND) x = SOME y ⇒
      (SND y).txParams = (SND x).txParams’
  >- (disch_then drule \\ simp[])
  \\ ho_match_mp_tac OWHILE_IND
  \\ rw[]
  \\ Cases_on ‘step (SND x)’
  \\ fs[]
  \\ metis_tac[step_preserves_txParams, pairTheory.SND]
QED

Theorem boundary_preserves_transaction_parameters:
  execute_boundary instruction es = SOME (result, final) ⇒
  final.txParams = es.txParams
Proof
  strip_tac
  \\ ‘(SND (step es)).txParams = es.txParams’ by
       simp[step_preserves_txParams]
  \\ Cases_on ‘step es’
  \\ rename1 ‘(entry_result, entered)’
  \\ Cases_on ‘entry_result’
  \\ fs[execute_boundary_def]
  \\ Cases_on ‘LENGTH entered.contexts > LENGTH es.contexts’
  \\ fs[]
  \\ metis_tac[subtree_preserves_transaction_parameters]
QED

(* Storage preservation applies to the entered subtree, with precisely the
 * upstream checkpoint assumptions. In particular, saved accounts need not
 * equal current accounts, but their differing slots must be covered by accesses.
 * CREATE may clear an unaccessed slot in a nonce-zero, code-empty account.
 *)
Theorem boundary_subtree_preserves_unaccessed_storage:
  positioned_at_boundary instruction es ∧
  step es = (INL (), entered) ∧
  LENGTH entered.contexts > LENGTH es.contexts ∧
  wf_state entered ∧ (FST (HD entered.contexts)).jumpDest = NONE ∧
  EVERY (λrb. storage_slot_preserved rb entered.rollback)
    (MAP SND (TAKE 2 entered.contexts)) ∧
  execute_boundary instruction es = SOME (result, final) ⇒
  ∀a k. ¬fIN (SK a k) final.rollback.accesses.storageKeys ⇒
    lookup_storage k (lookup_account a final.rollback.accounts).storage =
    lookup_storage k (lookup_account a entered.rollback.accounts).storage ∨
    lookup_storage k (lookup_account a final.rollback.accounts).storage = 0w ∧
    ¬account_already_created (lookup_account a entered.rollback.accounts)
Proof
  rpt strip_tac
  \\ ‘run_call entered = SOME (result, final)’ by
    (qpat_x_assum ‘execute_boundary instruction es = _’ mp_tac
     \\ asm_simp_tac (srw_ss()) [execute_boundary_def])
  \\ metis_tac[run_call_preserves_storage_outside_accessed_slots]
QED
