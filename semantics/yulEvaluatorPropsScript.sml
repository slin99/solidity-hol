(* Fuel stability for the Yul evaluator: a run that does not run out of fuel
 * is unchanged by more fuel.
 *
 * Fuel is only ever tested for zero, and is spent only where the recursion is
 * not structural -- a loop's back edge and a call's entry -- so a larger bound
 * can neither turn a real answer into out-of-fuel nor change one: it can only
 * replace YulOutOfFuel by the answer the run would have reached.
 *
 * Expressions return a yul_expr_result rather than a yul_result, so the "did
 * not stop for fuel" side condition is yul_running instead of a completion
 * test.  The conjuncts are in the definition's order: block, stmt, expr, args,
 * loop, cases, call.
 *)
Theory yulEvaluatorProps
Ancestors
  yulEvaluator

Definition yul_running_def:
  (yul_running (EvalValues vs m) ⇔ T) ∧
  (yul_running (EvalAbrupt c m) ⇔ c ≠ YulOutOfFuel)
End

Theorem yul_result_completion[simp]:
  (yul_normal m).completion = YulNormal /\
  (yul_abrupt c m).completion = c /\
  (yul_invalid reason m).completion = YulInvalid reason /\
  (yul_pop_result r).completion = r.completion
Proof
  simp[yul_normal_def, yul_abrupt_def, yul_invalid_def,
       yul_pop_result_def]
QED

Theorem yul_fuel_predecessor:
  (n:num) <= k /\ n <> 0 ==> k <> 0 /\ n - 1 <= k - 1
Proof
  decide_tac
QED

Theorem yul_fuel_block_nil[local]:
  !n fns m k.
    (eval_yul_block n fns [] m).completion <> YulOutOfFuel /\ n <= k ==>
    eval_yul_block k fns [] m = eval_yul_block n fns [] m
Proof
  once_rewrite_tac[eval_yul_block_def] >> simp[]
QED

Theorem yul_fuel_stmt_block[local]:
  !n fns ss m.
    (!k. (eval_yul_block n fns ss (yul_push_scope m)).completion <>
          YulOutOfFuel /\ n <= k ==>
         eval_yul_block k fns ss (yul_push_scope m) =
         eval_yul_block n fns ss (yul_push_scope m)) ==>
    !k. (eval_yul_stmt n fns (YulBlock ss) m).completion <>
         YulOutOfFuel /\ n <= k ==>
        eval_yul_stmt k fns (YulBlock ss) m =
        eval_yul_stmt n fns (YulBlock ss) m
Proof
  rpt gen_tac >> strip_tac >> gen_tac >>
  once_rewrite_tac[eval_yul_block_def] >> simp[] >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

Theorem yul_fuel_expr_base[local]:
  (!n fns l m k.
    yul_running (eval_yul_expr n fns (YulLit l) m) /\ n <= k ==>
    eval_yul_expr k fns (YulLit l) m = eval_yul_expr n fns (YulLit l) m) /\
  (!n fns x m k.
    yul_running (eval_yul_expr n fns (YulName x) m) /\ n <= k ==>
    eval_yul_expr k fns (YulName x) m = eval_yul_expr n fns (YulName x) m) /\
  (!n fns m k.
    yul_running (eval_yul_args n fns [] m) /\ n <= k ==>
    eval_yul_args k fns [] m = eval_yul_args n fns [] m)
Proof
  once_rewrite_tac[eval_yul_block_def] >> simp[]
QED

Theorem yul_fuel_expr_builtin[local]:
  !n fns op args m.
    (!k. yul_running (eval_yul_args n fns args m) /\ n <= k ==>
         eval_yul_args k fns args m = eval_yul_args n fns args m) ==>
    !k. yul_running (eval_yul_expr n fns (YulBuiltin op args) m) /\ n <= k ==>
        eval_yul_expr k fns (YulBuiltin op args) m =
        eval_yul_expr n fns (YulBuiltin op args) m
Proof
  rpt gen_tac >> strip_tac >> gen_tac >>
  once_rewrite_tac[eval_yul_block_def] >>
  Cases_on `eval_yul_args n fns args m` >> simp[yul_running_def] >>
  strip_tac >> first_x_assum (qspec_then `k` mp_tac) >>
  simp[yul_running_def] >> disch_then SUBST1_TAC >> simp[]
QED

Theorem yul_fuel_cases_nil[local]:
  !n fns v default m.
    (!k. (eval_yul_block n fns default (yul_push_scope m)).completion <>
          YulOutOfFuel /\ n <= k ==>
         eval_yul_block k fns default (yul_push_scope m) =
         eval_yul_block n fns default (yul_push_scope m)) ==>
    !k. (eval_yul_cases n fns v [] default m).completion <> YulOutOfFuel /\ n <= k ==>
        eval_yul_cases k fns v [] default m = eval_yul_cases n fns v [] default m
Proof
  rpt gen_tac >> strip_tac >> gen_tac >>
  once_rewrite_tac[eval_yul_block_def] >> simp[] >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

Theorem yul_fuel_cases_cons[local]:
  !n fns v lit body rest default m.
    (!w. yul_literal_value lit = SOME w /\ w <> v ==>
      !k. (eval_yul_cases n fns v rest default m).completion <> YulOutOfFuel /\ n <= k ==>
          eval_yul_cases k fns v rest default m = eval_yul_cases n fns v rest default m) /\
    (!w. yul_literal_value lit = SOME w /\ w = v ==>
      !k. (eval_yul_block n fns body (yul_push_scope m)).completion <> YulOutOfFuel /\ n <= k ==>
          eval_yul_block k fns body (yul_push_scope m) =
          eval_yul_block n fns body (yul_push_scope m)) ==>
    !k. (eval_yul_cases n fns v ((lit,body)::rest) default m).completion <> YulOutOfFuel /\ n <= k ==>
        eval_yul_cases k fns v ((lit,body)::rest) default m =
        eval_yul_cases n fns v ((lit,body)::rest) default m
Proof
  rpt gen_tac >> strip_tac >> gen_tac >>
  once_rewrite_tac[eval_yul_block_def] >>
  Cases_on `yul_literal_value lit` >> simp[] >>
  rename1 `yul_literal_value lit = SOME w` >>
  Cases_on `w = v` >> gvs[] >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

Theorem yul_fuel_args_cons[local]:
  !n fns a args m.
    (!vs m'. eval_yul_args n fns args m = EvalValues vs m' ==>
      !k. yul_running (eval_yul_expr n fns a m') /\ n <= k ==>
          eval_yul_expr k fns a m' = eval_yul_expr n fns a m') /\
    (!k. yul_running (eval_yul_args n fns args m) /\ n <= k ==>
         eval_yul_args k fns args m = eval_yul_args n fns args m) ==>
    !k. yul_running (eval_yul_args n fns (a::args) m) /\ n <= k ==>
        eval_yul_args k fns (a::args) m = eval_yul_args n fns (a::args) m
Proof
  rpt gen_tac >> strip_tac >> gen_tac >>
  once_rewrite_tac[eval_yul_block_def] >>
  Cases_on `eval_yul_args n fns args m` >> gvs[yul_running_def] >>
  strip_tac >> gvs[] >>
  rename1 `eval_yul_expr n fns a m'` >>
  Cases_on `eval_yul_expr n fns a m'` >> gvs[yul_running_def]
QED

Theorem yul_fuel_expr_apply[local]:
  !n fns f args m.
    (!vs m'. n <> 0 /\ eval_yul_args n fns args m = EvalValues vs m' ==>
      !k. yul_running (invoke_yul (n-1) fns f vs m') /\ n-1 <= k ==>
          invoke_yul k fns f vs m' = invoke_yul (n-1) fns f vs m') /\
    (n <> 0 ==>
      !k. yul_running (eval_yul_args n fns args m) /\ n <= k ==>
          eval_yul_args k fns args m = eval_yul_args n fns args m) ==>
    !k. yul_running (eval_yul_expr n fns (YulApply f args) m) /\ n <= k ==>
        eval_yul_expr k fns (YulApply f args) m =
        eval_yul_expr n fns (YulApply f args) m
Proof
  rpt gen_tac >> strip_tac >> gen_tac >>
  once_rewrite_tac[eval_yul_block_def] >>
  Cases_on `n = 0` >> gvs[yul_running_def] >>
  Cases_on `eval_yul_args n fns args m` >> gvs[yul_running_def] >>
  strip_tac >> drule_all yul_fuel_predecessor >> strip_tac >> gvs[]
QED

Theorem yul_fuel_block_cons[local]:
  !n fns s ss m.
    (!r. r = eval_yul_stmt n fns s m /\ r.completion = YulNormal ==>
      !k. (eval_yul_block n fns ss r.machine).completion <> YulOutOfFuel /\ n <= k ==>
          eval_yul_block k fns ss r.machine = eval_yul_block n fns ss r.machine) /\
    (!k. (eval_yul_stmt n fns s m).completion <> YulOutOfFuel /\ n <= k ==>
         eval_yul_stmt k fns s m = eval_yul_stmt n fns s m) ==>
    !k. (eval_yul_block n fns (s::ss) m).completion <> YulOutOfFuel /\ n <= k ==>
        eval_yul_block k fns (s::ss) m = eval_yul_block n fns (s::ss) m
Proof
  rpt gen_tac >> strip_tac >> gen_tac >>
  once_rewrite_tac[eval_yul_block_def] >> simp_tac (srw_ss()) [] >>
  Cases_on `(eval_yul_stmt n fns s m).completion = YulNormal` >> gvs[] >>
  strip_tac >> gvs[]
QED

Theorem yul_fuel_stmt_base[local]:
  (!n fns name params results body m k.
    (eval_yul_stmt n fns (YulFunction name params results body) m).completion <> YulOutOfFuel /\ n <= k ==>
    eval_yul_stmt k fns (YulFunction name params results body) m =
    eval_yul_stmt n fns (YulFunction name params results body) m) /\
  (!n fns m k. (eval_yul_stmt n fns YulBreak m).completion <> YulOutOfFuel /\ n <= k ==>
    eval_yul_stmt k fns YulBreak m = eval_yul_stmt n fns YulBreak m) /\
  (!n fns m k. (eval_yul_stmt n fns YulContinue m).completion <> YulOutOfFuel /\ n <= k ==>
    eval_yul_stmt k fns YulContinue m = eval_yul_stmt n fns YulContinue m) /\
  (!n fns m k. (eval_yul_stmt n fns YulLeave m).completion <> YulOutOfFuel /\ n <= k ==>
    eval_yul_stmt k fns YulLeave m = eval_yul_stmt n fns YulLeave m)
Proof
  once_rewrite_tac[eval_yul_block_def] >> simp[]
QED

Theorem yul_fuel_stmt_let[local]:
  !n fns names value m.
    (!e. value = SOME e ==>
      !k. yul_running (eval_yul_expr n fns e m) /\ n <= k ==>
          eval_yul_expr k fns e m = eval_yul_expr n fns e m) ==>
    !k. (eval_yul_stmt n fns (YulLet names value) m).completion <> YulOutOfFuel /\ n <= k ==>
        eval_yul_stmt k fns (YulLet names value) m = eval_yul_stmt n fns (YulLet names value) m
Proof
  rpt gen_tac >> strip_tac >> gen_tac >>
  once_rewrite_tac[eval_yul_block_def] >>
  Cases_on `value` >> gvs[] >> rename1 `eval_yul_expr n fns e m` >>
  Cases_on `eval_yul_expr n fns e m` >> gvs[yul_running_def] >> strip_tac >> gvs[]
QED

Theorem yul_fuel_stmt_assign[local]:
  !n fns names e m.
    (!k. yul_running (eval_yul_expr n fns e m) /\ n <= k ==>
         eval_yul_expr k fns e m = eval_yul_expr n fns e m) ==>
    !k. (eval_yul_stmt n fns (YulAssign names e) m).completion <> YulOutOfFuel /\ n <= k ==>
        eval_yul_stmt k fns (YulAssign names e) m = eval_yul_stmt n fns (YulAssign names e) m
Proof
  rpt gen_tac >> strip_tac >> gen_tac >>
  once_rewrite_tac[eval_yul_block_def] >>
  Cases_on `eval_yul_expr n fns e m` >> gvs[yul_running_def] >> strip_tac >> gvs[]
QED

Theorem yul_fuel_stmt_expr[local]:
  !n fns e m.
    (!k. yul_running (eval_yul_expr n fns e m) /\ n <= k ==>
         eval_yul_expr k fns e m = eval_yul_expr n fns e m) ==>
    !k. (eval_yul_stmt n fns (YulExprStmt e) m).completion <> YulOutOfFuel /\ n <= k ==>
        eval_yul_stmt k fns (YulExprStmt e) m = eval_yul_stmt n fns (YulExprStmt e) m
Proof
  rpt gen_tac >> strip_tac >> gen_tac >>
  once_rewrite_tac[eval_yul_block_def] >>
  Cases_on `eval_yul_expr n fns e m` >> gvs[yul_running_def] >> strip_tac >> gvs[]
QED

Theorem yul_fuel_stmt_if[local]:
  !n fns c body m.
    (!vs m' v tail. eval_yul_expr n fns c m = EvalValues vs m' /\
      vs = v::tail /\ tail = [] /\ v <> 0w ==>
      !k. (eval_yul_block n fns body (yul_push_scope m')).completion <> YulOutOfFuel /\ n <= k ==>
          eval_yul_block k fns body (yul_push_scope m') = eval_yul_block n fns body (yul_push_scope m')) /\
    (!k. yul_running (eval_yul_expr n fns c m) /\ n <= k ==>
         eval_yul_expr k fns c m = eval_yul_expr n fns c m) ==>
    !k. (eval_yul_stmt n fns (YulIf c body) m).completion <> YulOutOfFuel /\ n <= k ==>
        eval_yul_stmt k fns (YulIf c body) m = eval_yul_stmt n fns (YulIf c body) m
Proof
  rpt gen_tac >> strip_tac >> gen_tac >>
  once_rewrite_tac[eval_yul_block_def] >>
  Cases_on `eval_yul_expr n fns c m` >> gvs[yul_running_def] >>
  rename1 `EvalValues vs m'` >>
  Cases_on `vs` >> gvs[] >> rename1 `EvalValues (v::tail) m'` >>
  Cases_on `tail` >> gvs[] >> Cases_on `v = 0w` >> gvs[] >> strip_tac >> gvs[]
QED

Theorem yul_fuel_stmt_switch[local]:
  !n fns e cases default m.
    (!vs m' v tail. eval_yul_expr n fns e m = EvalValues vs m' /\
      vs = v::tail /\ tail = [] ==>
      !k. (eval_yul_cases n fns v cases default m').completion <> YulOutOfFuel /\ n <= k ==>
          eval_yul_cases k fns v cases default m' = eval_yul_cases n fns v cases default m') /\
    (!k. yul_running (eval_yul_expr n fns e m) /\ n <= k ==>
         eval_yul_expr k fns e m = eval_yul_expr n fns e m) ==>
    !k. (eval_yul_stmt n fns (YulSwitch e cases default) m).completion <> YulOutOfFuel /\ n <= k ==>
        eval_yul_stmt k fns (YulSwitch e cases default) m = eval_yul_stmt n fns (YulSwitch e cases default) m
Proof
  rpt gen_tac >> strip_tac >> gen_tac >>
  once_rewrite_tac[eval_yul_block_def] >>
  Cases_on `eval_yul_expr n fns e m` >> gvs[yul_running_def] >>
  rename1 `EvalValues vs m'` >>
  Cases_on `vs` >> gvs[] >> rename1 `EvalValues (v::tail) m'` >>
  Cases_on `tail` >> gvs[] >> strip_tac >> gvs[]
QED

Theorem yul_fuel_stmt_for[local]:
  !n fns init cond post body m.
    (!m1 r. m1 = yul_push_scope m /\ r = eval_yul_block n fns init m1 /\
      r.completion = YulNormal ==>
      !k. (eval_yul_loop n fns cond post body r.machine).completion <> YulOutOfFuel /\ n <= k ==>
          eval_yul_loop k fns cond post body r.machine = eval_yul_loop n fns cond post body r.machine) /\
    (!m1. m1 = yul_push_scope m ==>
      !k. (eval_yul_block n fns init m1).completion <> YulOutOfFuel /\ n <= k ==>
          eval_yul_block k fns init m1 = eval_yul_block n fns init m1) ==>
    !k. (eval_yul_stmt n fns (YulFor init cond post body) m).completion <> YulOutOfFuel /\ n <= k ==>
        eval_yul_stmt k fns (YulFor init cond post body) m = eval_yul_stmt n fns (YulFor init cond post body) m
Proof
  rpt gen_tac >> strip_tac >> gen_tac >>
  once_rewrite_tac[eval_yul_block_def] >> simp_tac (srw_ss()) [] >>
  Cases_on `(eval_yul_block n fns init (yul_push_scope m)).completion = YulNormal` >>
  gvs[] >> strip_tac >> gvs[]
QED

Theorem yul_fuel_invoke[local]:
  !n fns name args m.
    (!fd m1. n <> 0 /\ FLOOKUP fns name = SOME fd /\
      ~(LENGTH fd.function_params <> LENGTH args) /\
      m1 = yul_push_frame fd.function_params args fd.function_results m ==>
      !k. (eval_yul_block (n-1) fns fd.function_body m1).completion <> YulOutOfFuel /\ n-1 <= k ==>
          eval_yul_block k fns fd.function_body m1 = eval_yul_block (n-1) fns fd.function_body m1) ==>
    !k. yul_running (invoke_yul n fns name args m) /\ n <= k ==>
        invoke_yul k fns name args m = invoke_yul n fns name args m
Proof
  rpt gen_tac >> strip_tac >> gen_tac >>
  once_rewrite_tac[eval_yul_block_def] >>
  Cases_on `n = 0` >> gvs[yul_running_def] >>
  Cases_on `k = 0` >- simp[] >>
  Cases_on `FLOOKUP fns name` >> gvs[] >> rename1 `SOME fd` >>
  Cases_on `LENGTH fd.function_params = LENGTH args` >> gvs[] >>
  qmatch_goalsub_abbrev_tac `eval_yul_block (n-1) fns fd.function_body m1` >>
  Cases_on `(eval_yul_block (n-1) fns fd.function_body m1).completion = YulNormal \/
            (eval_yul_block (n-1) fns fd.function_body m1).completion = YulLeave` >>
  gvs[yul_running_def] >> strip_tac >>
  drule_all yul_fuel_predecessor >> strip_tac >> gvs[]
QED

Theorem yul_fuel_loop[local]:
  !n fns cond post body m.
    (!vs m' v tail rb rp.
      eval_yul_expr n fns cond m = EvalValues vs m' /\ vs = v::tail /\ tail = [] /\ v <> 0w /\
      rb = yul_pop_result (eval_yul_block n fns body (yul_push_scope m')) /\
      rb.completion <> YulBreak /\ ~(rb.completion <> YulNormal /\ rb.completion <> YulContinue) /\
      rp = yul_pop_result (eval_yul_block n fns post (yul_push_scope rb.machine)) /\
      ~(rp.completion = YulBreak \/ rp.completion = YulContinue) /\
      ~(rp.completion <> YulNormal) /\ n <> 0 ==>
      !k. (eval_yul_loop (n-1) fns cond post body rp.machine).completion <> YulOutOfFuel /\ n-1 <= k ==>
          eval_yul_loop k fns cond post body rp.machine = eval_yul_loop (n-1) fns cond post body rp.machine) /\
    (!vs m' v tail rb.
      eval_yul_expr n fns cond m = EvalValues vs m' /\ vs = v::tail /\ tail = [] /\ v <> 0w /\
      rb = yul_pop_result (eval_yul_block n fns body (yul_push_scope m')) /\
      rb.completion <> YulBreak /\ ~(rb.completion <> YulNormal /\ rb.completion <> YulContinue) ==>
      !k. (eval_yul_block n fns post (yul_push_scope rb.machine)).completion <> YulOutOfFuel /\ n <= k ==>
          eval_yul_block k fns post (yul_push_scope rb.machine) = eval_yul_block n fns post (yul_push_scope rb.machine)) /\
    (!vs m' v tail.
      eval_yul_expr n fns cond m = EvalValues vs m' /\ vs = v::tail /\ tail = [] /\ v <> 0w ==>
      !k. (eval_yul_block n fns body (yul_push_scope m')).completion <> YulOutOfFuel /\ n <= k ==>
          eval_yul_block k fns body (yul_push_scope m') = eval_yul_block n fns body (yul_push_scope m')) /\
    (!k. yul_running (eval_yul_expr n fns cond m) /\ n <= k ==>
         eval_yul_expr k fns cond m = eval_yul_expr n fns cond m) ==>
    !k. (eval_yul_loop n fns cond post body m).completion <> YulOutOfFuel /\ n <= k ==>
        eval_yul_loop k fns cond post body m = eval_yul_loop n fns cond post body m
Proof
  rpt gen_tac >> strip_tac >> gen_tac >>
  once_rewrite_tac[eval_yul_block_def] >>
  Cases_on `eval_yul_expr n fns cond m` >> gvs[yul_running_def] >>
  rename1 `EvalValues vs m'` >>
  Cases_on `vs` >> gvs[] >> rename1 `EvalValues (v::tail) m'` >>
  Cases_on `tail` >> gvs[] >> Cases_on `v = 0w` >> gvs[] >>
  qmatch_goalsub_abbrev_tac `B.completion = YulBreak` >>
  qmatch_goalsub_abbrev_tac `yul_pop_scope rb.machine` >>
  qabbrev_tac `P = eval_yul_block n fns post (yul_push_scope rb.machine)` >>
  qabbrev_tac `rp = yul_pop_result P` >>
  Cases_on `B.completion = YulBreak`
  >- (simp[] >> strip_tac >> simp[Abbr `rb`]) >>
  Cases_on `B.completion <> YulNormal /\ B.completion <> YulContinue`
  >- (simp[Abbr `rb`] >> strip_tac >> simp[]) >>
  `B.completion <> YulOutOfFuel` by
    (Cases_on `B.completion` >> gvs[]) >>
  strip_tac >>
  simp[] >>
  Cases_on `P.completion <> YulNormal`
  >- (`P.completion <> YulOutOfFuel` by (Cases_on `P.completion` >> gvs[Abbr `rp`]) >>
      gvs[Abbr `rp`]) >>
  Cases_on `n = 0` >> gvs[] >>
  drule_all yul_fuel_predecessor >> strip_tac >>
  simp[Abbr `rp`]
QED

Theorem eval_yul_fuel_stable[local]:
  (∀n fns ss m k.
     (eval_yul_block n fns ss m).completion ≠ YulOutOfFuel ∧ n ≤ k ⇒
     eval_yul_block k fns ss m = eval_yul_block n fns ss m) ∧
  (∀n fns s m k.
     (eval_yul_stmt n fns s m).completion ≠ YulOutOfFuel ∧ n ≤ k ⇒
     eval_yul_stmt k fns s m = eval_yul_stmt n fns s m) ∧
  (∀n fns e m k.
     yul_running (eval_yul_expr n fns e m) ∧ n ≤ k ⇒
     eval_yul_expr k fns e m = eval_yul_expr n fns e m) ∧
  (∀n fns es m k.
     yul_running (eval_yul_args n fns es m) ∧ n ≤ k ⇒
     eval_yul_args k fns es m = eval_yul_args n fns es m) ∧
  (∀n fns cond post body m k.
     (eval_yul_loop n fns cond post body m).completion ≠ YulOutOfFuel ∧
     n ≤ k ⇒
     eval_yul_loop k fns cond post body m =
     eval_yul_loop n fns cond post body m) ∧
  (∀n fns v cases default m k.
     (eval_yul_cases n fns v cases default m).completion ≠ YulOutOfFuel ∧
     n ≤ k ⇒
     eval_yul_cases k fns v cases default m =
     eval_yul_cases n fns v cases default m) ∧
  (∀n fns name args m k.
     yul_running (invoke_yul n fns name args m) ∧ n ≤ k ⇒
     invoke_yul k fns name args m = invoke_yul n fns name args m)
Proof
  ho_match_mp_tac eval_yul_block_ind >> rpt conj_tac
  >- MATCH_ACCEPT_TAC yul_fuel_block_nil
  >- MATCH_ACCEPT_TAC yul_fuel_block_cons
  >- MATCH_ACCEPT_TAC yul_fuel_stmt_block
  >- MATCH_ACCEPT_TAC (cj 1 yul_fuel_stmt_base)
  >- MATCH_ACCEPT_TAC yul_fuel_stmt_let
  >- MATCH_ACCEPT_TAC yul_fuel_stmt_assign
  >- MATCH_ACCEPT_TAC yul_fuel_stmt_if
  >- MATCH_ACCEPT_TAC yul_fuel_stmt_switch
  >- MATCH_ACCEPT_TAC yul_fuel_stmt_for
  >- MATCH_ACCEPT_TAC (cj 2 yul_fuel_stmt_base)
  >- MATCH_ACCEPT_TAC (cj 3 yul_fuel_stmt_base)
  >- MATCH_ACCEPT_TAC (cj 4 yul_fuel_stmt_base)
  >- MATCH_ACCEPT_TAC yul_fuel_stmt_expr
  >- MATCH_ACCEPT_TAC (cj 1 yul_fuel_expr_base)
  >- MATCH_ACCEPT_TAC (cj 2 yul_fuel_expr_base)
  >- MATCH_ACCEPT_TAC yul_fuel_expr_builtin
  >- MATCH_ACCEPT_TAC yul_fuel_expr_apply
  >- MATCH_ACCEPT_TAC (cj 3 yul_fuel_expr_base)
  >- MATCH_ACCEPT_TAC yul_fuel_args_cons
  >- MATCH_ACCEPT_TAC yul_fuel_loop
  >- MATCH_ACCEPT_TAC yul_fuel_cases_nil
  >- MATCH_ACCEPT_TAC yul_fuel_cases_cons
  >> MATCH_ACCEPT_TAC yul_fuel_invoke
QED

Theorem run_yul_fuel_stable:
  run_yul n code m = r ∧ r.completion ≠ YulOutOfFuel ∧ n ≤ k ⇒
  run_yul k code m = r
Proof
  rw[run_yul_def] >> metis_tac[eval_yul_fuel_stable]
QED
