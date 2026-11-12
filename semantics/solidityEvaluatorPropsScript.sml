(* Compositional evaluator equations and fuel stability: a result that is not fuel-truncated
 * is unchanged by more fuel. The environment and state are universally
 * quantified, so the statements carry over unchanged once external answers are
 * supplied through them.
 *)
Theory solidityEvaluatorProps
Ancestors
  solidityEvaluator yulEvaluatorProps

(* An inline assembly block runs the Yul evaluator with the same fuel. *)
Theorem eval_assembly_fuel_stable[local]:
  (eval_assembly n env code refs st gas).completion ≠ FuelExhausted ∧ n ≤ m ⇒
  eval_assembly m env code refs st gas = eval_assembly n env code refs st gas
Proof
  simp[eval_assembly_def] >> rw[] >>
  Cases_on ‘assembly_inputs env st refs’ >> gvs[] >>
  rename1 ‘SOME p’ >> PairCases_on ‘p’ >> gvs[] >>
  Cases_on ‘assembly_machine st p0’ >> gvs[] >>
  qmatch_goalsub_abbrev_tac ‘run_yul m c m0’ >>
  Cases_on ‘(run_yul n c m0).completion = YulOutOfFuel’
  >- gvs[assembly_result_def, abrupt_result_def] >>
  ‘run_yul m c m0 = run_yul n c m0’ by metis_tac[run_yul_fuel_stable] >>
  simp[]
QED

Theorem eval_fuel_stable[local]:
  (∀n env ss st gas m.
     (eval_block n env ss st gas).completion ≠ FuelExhausted ∧ n ≤ m ⇒
     eval_block m env ss st gas = eval_block n env ss st gas) ∧
  (∀n env s st gas m.
     (eval_stmt n env s st gas).completion ≠ FuelExhausted ∧ n ≤ m ⇒
     eval_stmt m env s st gas = eval_stmt n env s st gas) ∧
  (∀n env prelude c bd st gas m.
     (eval_loop n env prelude c bd st gas).completion ≠ FuelExhausted ∧
     n ≤ m ⇒
     eval_loop m env prelude c bd st gas =
     eval_loop n env prelude c bd st gas) ∧
  (∀n env f args st gas m.
     (invoke_source n env f args st gas).completion ≠ FuelExhausted ∧
     n ≤ m ⇒
     invoke_source m env f args st gas = invoke_source n env f args st gas)
Proof
  ho_match_mp_tac eval_block_ind >> rpt strip_tac >>
  qpat_x_assum ‘_.completion ≠ FuelExhausted’ mp_tac >>
  once_rewrite_tac[eval_block_def] >>
  (* statements without nested evaluation, and the empty block *)
  TRY (strip_tac >> REFL_TAC >> NO_TAC)
  >~ [‘eval_assembly’] >- metis_tac[eval_assembly_fuel_stable]
  >~ [‘eval_stmt _ _ _ _ _’] >-
   (strip_tac >> first_x_assum (qspec_then ‘m’ assume_tac) >>
    rename1 ‘eval_stmt _ _ s _ _’ >>
    Cases_on ‘(eval_stmt n env s st gas).completion = NormalCompletion’ >>
    gvs[])
  >~ [‘panic_zero_function’] >-
   (strip_tac >>
    Cases_on ‘eval_atom st.scopes g’ >> gvs[] >>
    rename1 ‘eval_atom _ _ = SOME gv’ >> Cases_on ‘gv’ >> gvs[] >>
    rename1 ‘eval_atom _ _ = SOME (ScalarValue gs)’ >> Cases_on ‘gs’ >> gvs[] >>
    rename1 ‘eval_atom _ _ = SOME (ScalarValue (InternalFunctionValue go))’ >>
    Cases_on ‘go’ >> Cases_on ‘eval_atoms st.scopes atoms’ >> gvs[] >>
    rename1 ‘invoke_source _ _ f vs _ _’ >>
    Cases_on ‘(invoke_source n env f vs st gas).completion = FuelExhausted’ >>
    gvs[bind_call_result_def])
  >~ [‘bind_call_result’] >-
   (strip_tac >> Cases_on ‘eval_atoms st.scopes atoms’ >> gvs[] >>
    rename1 ‘invoke_source _ _ f vs _ _’ >>
    Cases_on ‘(invoke_source n env f vs st gas).completion = FuelExhausted’ >>
    gvs[bind_call_result_def])
  >~ [‘loop_after_body’] >-
   (qpat_x_assum
      ‘∀m. (eval_block n env prelude _ _).completion ≠ _ ∧ _ ⇒ _’
      (qspec_then ‘m’ mp_tac) >>
    qabbrev_tac ‘r1 = eval_block n env prelude (push_scope st) gas’ >>
    Cases_on ‘r1.completion = FuelExhausted’
    >- gvs[LET_THM, pop_result_def] >>
    simp[] >> disch_then (fn th => simp[th, LET_THM]) >>
    Cases_on ‘r1.completion = NormalCompletion’ >> gvs[] >>
    Cases_on ‘branch_of r1.state c’ >> gvs[] >>
    rename1 ‘SOME b’ >> Cases_on ‘b’ >> gvs[] >>
    qabbrev_tac
      ‘r2 = eval_block n env bd r1.state r1.unused_gas_evidence’ >>
    Cases_on ‘r2.completion = FuelExhausted’
    >- gvs[pop_result_def, loop_after_body_def] >>
    gvs[] >>
    Cases_on ‘loop_after_body (pop_result r2).completion’ >> gvs[] >>
    Cases_on ‘n = 0’ >> gvs[])
  >~ [‘lookup_procedure’] >-
   (strip_tac >> Cases_on ‘n = 0’ >- gvs[abrupt_result_def] >>
    ‘m ≠ 0’ by decide_tac >> simp[] >>
    rename1 ‘lookup_procedure env f’ >>
    Cases_on ‘lookup_procedure env f’ >> gvs[] >>
    rename1 ‘lookup_procedure _ _ = SOME p’ >>
    Cases_on ‘entry_scope env p args’ >> gvs[] >>
    rename1 ‘entry_scope _ _ _ = SOME scope’ >>
    Cases_on ‘(eval_block (n - 1) env p.body (enter_procedure st scope)
                 gas).completion = FuelExhausted’ >>
    gvs[LET_THM, procedure_completion_def, abrupt_result_def])
  >~ [‘branch_of’] >-
   (strip_tac >> Cases_on ‘branch_of st c’ >> gvs[] >>
    rename1 ‘SOME b’ >> Cases_on ‘b’ >> gvs[pop_result_def])
  (* while statement *)
  >> strip_tac >> gvs[]
QED

Theorem eval_block_fuel_stable:
  eval_block n env ss st gas = r ∧ r.completion ≠ FuelExhausted ∧ n ≤ m ⇒
  eval_block m env ss st gas = r
Proof
  metis_tac[eval_fuel_stable]
QED

Theorem invoke_source_fuel_stable:
  invoke_source n env f args st gas = r ∧ r.completion ≠ FuelExhausted ∧
  n ≤ m ⇒
  invoke_source m env f args st gas = r
Proof
  metis_tac[eval_fuel_stable]
QED

(* The evaluator's equations with each intermediate result named by a
 * constant that unfolds only once that result is a record literal, so that
 * rewriting never duplicates an unevaluated eval_stmt. *)

Definition block_next_def:
  block_next n env ss (r : source_result) =
    if r.completion = NormalCompletion
    then eval_block n env ss r.state r.unused_gas_evidence
    else r
End

Definition call_finish_def:
  call_finish p st (r : source_result) =
    abrupt_result (procedure_completion p r) (restore_caller st r.state)
      r.unused_gas_evidence
End

Definition loop_body_def:
  loop_body n env prelude c bd (r2 : source_result) =
    case loop_after_body r2.completion of
      LoopExit => r2 with completion := NormalCompletion
    | LoopStop => r2
    | LoopNext =>
        if n = 0 then r2 with completion := FuelExhausted
        else eval_loop (n - 1) env prelude c bd r2.state
               r2.unused_gas_evidence
End

Definition loop_prelude_def:
  loop_prelude n env prelude c bd (r1 : source_result) =
    if r1.completion ≠ NormalCompletion then pop_result r1 else
    case branch_of r1.state c of
      NONE =>
        pop_result
          (r1 with completion := InvalidCompletion "non-boolean condition")
    | SOME b =>
        if ¬b then pop_result r1 else
        loop_body n env prelude c bd
          (pop_result (eval_block n env bd r1.state r1.unused_gas_evidence))
End

Theorem eval_block_cons:
  eval_block n env (stmt :: ss) st gas = block_next n env ss (eval_stmt n env stmt st gas)
Proof
  simp[Once eval_block_def, block_next_def]
QED

Theorem eval_loop_unfold:
  eval_loop n env prelude c bd st gas =
  loop_prelude n env prelude c bd (eval_block n env prelude (push_scope st) gas)
Proof
  simp[Once eval_block_def, loop_prelude_def, loop_body_def]
QED

Theorem invoke_source_unfold:
  invoke_source n env fid args st gas =
  if n = 0 then abrupt_result FuelExhausted st gas else
  case lookup_procedure env fid of
    NONE => abrupt_result (InvalidCompletion "unknown procedure") st gas
  | SOME p =>
      case entry_scope env p args of
        NONE => abrupt_result (InvalidCompletion "bad arguments") st gas
      | SOME scope =>
          call_finish p st
            (eval_block (n - 1) env p.body (enter_procedure st scope) gas)
Proof
  simp[Once eval_block_def, call_finish_def]
QED

Theorem result_literal_eqs:
  block_next n env ss <| completion := c; state := st'; unused_gas_evidence := g |> =
    (if c = NormalCompletion then eval_block n env ss st' g
     else <| completion := c; state := st'; unused_gas_evidence := g |>) ∧
  call_finish p st <| completion := c; state := st'; unused_gas_evidence := g |> =
    abrupt_result
      (procedure_completion p
         <| completion := c; state := st'; unused_gas_evidence := g |>)
      (restore_caller st st') g ∧
  loop_prelude n env prelude cnd bd
    <| completion := c; state := st'; unused_gas_evidence := g |> =
    (if c ≠ NormalCompletion
     then pop_result <| completion := c; state := st'; unused_gas_evidence := g |>
     else
       case branch_of st' cnd of
         NONE =>
           pop_result
             <| completion := InvalidCompletion "non-boolean condition";
                state := st'; unused_gas_evidence := g |>
       | SOME b =>
           if ¬b then
             pop_result <| completion := c; state := st'; unused_gas_evidence := g |>
           else
             loop_body n env prelude cnd bd
               (pop_result (eval_block n env bd st' g))) ∧
  loop_body n env prelude cnd bd
    <| completion := c; state := st'; unused_gas_evidence := g |> =
    (case loop_after_body c of
       LoopExit => <| completion := NormalCompletion; state := st';
                      unused_gas_evidence := g |>
     | LoopStop => <| completion := c; state := st'; unused_gas_evidence := g |>
     | LoopNext =>
         if n = 0 then
           <| completion := FuelExhausted; state := st'; unused_gas_evidence := g |>
         else eval_loop (n - 1) env prelude cnd bd st' g) ∧
  bind_call_result x ty
    <| completion := c; state := st'; unused_gas_evidence := g |> =
    (case c of
       ReturnCompletion vs =>
         normal_result (define_binding x ty (pack_results vs) st') g
     | _ => <| completion := c; state := st'; unused_gas_evidence := g |>) ∧
  pop_result <| completion := c; state := st'; unused_gas_evidence := g |> =
    <| completion := c; state := st' with scopes := pop_scopes st'.scopes;
       unused_gas_evidence := g |>
Proof
  rw[block_next_def, call_finish_def, loop_prelude_def, loop_body_def,
     bind_call_result_def, pop_result_def]
QED


(* Compose blocks without duplicating evaluation of the first block. All
 * completions, including invalid execution in a static frame, propagate.
 *)
Theorem eval_block_append:
  eval_block n env (xs ++ ys) st gas =
  block_next n env ys (eval_block n env xs st gas)
Proof
  qid_spec_tac ‘gas’ >> qid_spec_tac ‘st’ >> Induct_on ‘xs’
  >- simp[eval_block_def, block_next_def, normal_result_def] >>
  rpt gen_tac >>
  Cases_on ‘(eval_stmt n env h st gas).completion = NormalCompletion’ >>
  simp[eval_block_cons, block_next_def]
QED
