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
    (!k. yul_running (eval_yul_args n fns (yul_builtin_value_args op args) m) /\ n <= k ==>
         eval_yul_args k fns (yul_builtin_value_args op args) m = eval_yul_args n fns (yul_builtin_value_args op args) m) ==>
    !k. yul_running (eval_yul_expr n fns (YulBuiltin op args) m) /\ n <= k ==>
        eval_yul_expr k fns (YulBuiltin op args) m =
        eval_yul_expr n fns (YulBuiltin op args) m
Proof
  rpt gen_tac >> strip_tac >> gen_tac >>
  once_rewrite_tac[eval_yul_block_def] >>
  Cases_on `eval_yul_args n fns (yul_builtin_value_args op args) m` >> simp[yul_running_def] >>
  strip_tac >> first_x_assum (qspec_then `k` mp_tac) >>
  simp[yul_running_def] >> disch_then SUBST1_TAC >> simp[]
QED

Theorem yul_fuel_expr_checked[local]:
  !n fns op args m.
    (!k. yul_running (eval_yul_args n fns (yul_builtin_value_args op args) m) /\ n <= k ==>
         eval_yul_args k fns (yul_builtin_value_args op args) m = eval_yul_args n fns (yul_builtin_value_args op args) m) ==>
    !k. yul_running (eval_yul_expr n fns (YulCheckedBuiltin op args) m) /\ n <= k ==>
        eval_yul_expr k fns (YulCheckedBuiltin op args) m =
        eval_yul_expr n fns (YulCheckedBuiltin op args) m
Proof
  rpt gen_tac >> strip_tac >> gen_tac >>
  once_rewrite_tac[eval_yul_block_def] >>
  Cases_on `eval_yul_args n fns (yul_builtin_value_args op args) m` >> simp[yul_running_def] >>
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
  >- MATCH_ACCEPT_TAC yul_fuel_expr_checked
  >- MATCH_ACCEPT_TAC yul_fuel_expr_apply
  >- MATCH_ACCEPT_TAC (cj 3 yul_fuel_expr_base)
  >- MATCH_ACCEPT_TAC yul_fuel_args_cons
  >- MATCH_ACCEPT_TAC yul_fuel_loop
  >- MATCH_ACCEPT_TAC yul_fuel_cases_nil
  >- MATCH_ACCEPT_TAC yul_fuel_cases_cons
  >> MATCH_ACCEPT_TAC yul_fuel_invoke
QED

(* One call's own form of the same fact, which is the shape a per-function
 * theorem's Yul side has: the run at a fuel large enough for it is the run at
 * any larger fuel.  A caller that has evaluated the body at a numeral fuel
 * has nothing left to say about the bound it chose. *)
Theorem invoke_yul_fuel_stable:
  ∀n fns name args m k. yul_running (invoke_yul n fns name args m) ∧ n ≤ k ⇒
  invoke_yul k fns name args m = invoke_yul n fns name args m
Proof
  MATCH_ACCEPT_TAC (List.last (CONJUNCTS eval_yul_fuel_stable))
QED

(* What a statement's result is handed on as: a block tests the result of one
 * statement and runs the rest of the body on it, and an expression's result is
 * what a statement branches on.  A body that has to be built once per outcome
 * rather than once per use of a bound name pushes the function it is being
 * handed to inside the case, which says the two are the same term.  The
 * distributions themselves are not stated here: `TypeBase.case_rand_of` has
 * them for every datatype, on the case the evaluator's own clauses leave
 * behind, and the conversion takes them from there. *)

(* A result the evaluator's own clauses do not decide, whose scrutinee is itself
 * a case: the outer case is pushed into the inner one, so that a branch the
 * inner case decides -- a lookup's NONE, which the evaluator answers with a
 * literal `YulInvalid` -- is decided here rather than left standing with the
 * rest of the body inside it.  Without this, a statement whose result is not
 * decided by one of its own equations leaves the body's continuation in the
 * branches of two nested cases, and neither branch is decided, so both survive
 * and a body of k such statements comes out at about 2^k times the size.
 *
 * The three inner cases are the ones the evaluator reaches: a lookup answers
 * with an `option`, `eval_yul_args` and the argument scanners case over a
 * `list`, and a statement over an expression's result cases on a
 * `yul_expr_result` again. *)
Theorem yul_expr_result_CASE_CASE:
  ∀X A B b1 b2.
    yul_expr_result_CASE (yul_expr_result_CASE X A B) b1 b2 =
    yul_expr_result_CASE X
      (λvs m. yul_expr_result_CASE (A vs m) b1 b2)
      (λc m. yul_expr_result_CASE (B c m) b1 b2)
Proof
  rw [] >> Cases_on `X` >> simp [yul_expr_result_case_def]
QED

Theorem yul_expr_result_CASE_option:
  ∀x n s b1 b2.
    yul_expr_result_CASE (option_CASE x n s) b1 b2 =
    option_CASE x (yul_expr_result_CASE n b1 b2)
      (λv. yul_expr_result_CASE (s v) b1 b2)
Proof
  rw [] >> Cases_on `x` >> simp [optionTheory.option_case_def]
QED

Theorem yul_expr_result_CASE_list:
  ∀l n c b1 b2.
    yul_expr_result_CASE (list_CASE l n c) b1 b2 =
    list_CASE l (yul_expr_result_CASE n b1 b2)
      (λh t. yul_expr_result_CASE (c h t) b1 b2)
Proof
  rw [] >> Cases_on `l` >> simp [listTheory.list_case_def]
QED

(* The case in a conditional's *test*, pushed in: the case comes to the top and
 * each of its branches carries the conditional, on what that branch holds.
 *
 * A statement whose own evaluation is a decision -- a guard the evaluator
 * cannot settle because the call in it is folded, `if <the call's value> then
 * <the invalid answer> else <the normal one>` -- leaves the case in the test,
 * which is the one place the continuation's push (`COND_RAND`) cannot reach:
 * the continuation goes into the conditional's two branches, both of which
 * keep it, and the branch the evaluator's own literal would have dropped is
 * only decided once the case is outside.  A body of k such guards is 2^k times
 * the size without this, and linear with it. *)
Theorem yul_expr_result_CASE_cond:
  ∀X b1 b2 t e.
    (if yul_expr_result_CASE X b1 b2 then t else e) =
    yul_expr_result_CASE X
      (λvs m. if b1 vs m then t else e)
      (λc m. if b2 c m then t else e)
Proof
  Cases_on `X` >> simp [yul_expr_result_case_def]
QED

(* A call that ends abruptly never ends `YulNormal`.  Read off the call's own
 * clause: the abrupt answers it can give are out of fuel, an unknown function,
 * a bad arity, and the callee's own completion, which it tests for `YulNormal`
 * (and for `YulLeave`) before it takes that branch. *)
Theorem invoke_yul_abrupt_neq_normal:
  invoke_yul n fns name args m = EvalAbrupt c m' ⇒ c ≠ YulNormal
Proof
  rw [eval_yul_block_def] >> BasicProvers.every_case_tac >> gvs []
QED

(* So the branch a caller's own continuation puts on a call's abrupt outcome is
 * dead, and a body handed to one -- `let r = <call> in if r.completion =
 * YulNormal then <the rest> else r` -- is just that outcome.  Stated on the
 * lifted case the block's clause leaves behind, with the continuation as a
 * function of the case's own variable and machine, which is the shape the
 * splitting conv hands it. *)
Theorem yul_expr_result_CASE_invoke_abrupt:
  ∀n fns name args m b1 T.
    yul_expr_result_CASE (invoke_yul n fns name args m) b1
      (λc m'. if (yul_abrupt c m').completion = YulNormal then T c m'
              else yul_abrupt c m') =
    yul_expr_result_CASE (invoke_yul n fns name args m) b1
      (λc m'. yul_abrupt c m')
Proof
  rw [] >> Cases_on `invoke_yul n fns name args m` >>
  imp_res_tac invoke_yul_abrupt_neq_normal >>
  gvs [yul_abrupt_def, yul_expr_result_case_def]
QED

(* The same, with the outcome written out as the record it is.  A compute set
 * that has the helper unfolded hands the branch the record itself, and the test
 * on it is still unreduced when the rule runs, so this is the shape the rule
 * sees for a call inside a converted body. *)
Theorem yul_expr_result_CASE_invoke_abrupt_lit:
  ∀n fns name args m b1 T.
    yul_expr_result_CASE (invoke_yul n fns name args m) b1
      (λc m'. if (<|completion := c; machine := m'|>).completion = YulNormal
              then T c m' else <|completion := c; machine := m'|>) =
    yul_expr_result_CASE (invoke_yul n fns name args m) b1
      (λc m'. <|completion := c; machine := m'|>)
Proof
  rw [] >> Cases_on `invoke_yul n fns name args m` >>
  imp_res_tac invoke_yul_abrupt_neq_normal >>
  gvs [yul_expr_result_case_def]
QED

(* The same again with the machine a function of the case's own variable and
 * machine rather than the branch's machine as it stands, which is what a branch
 * that has already written to it -- `yul_pop_result`, over a branch's block --
 * hands the record.  The test reads the completion alone, so the machine is
 * irrelevant to it and the branch is still the record itself; `_lit` is this
 * with `M` the second projection, kept as the statement a caller that has the
 * branch's own machine can rewrite with directly. *)
Theorem yul_expr_result_CASE_invoke_abrupt_record:
  ∀n fns name args m b1 T M.
    yul_expr_result_CASE (invoke_yul n fns name args m) b1
      (λc m'. if (<|completion := c; machine := M c m'|>).completion = YulNormal
              then T c m' else <|completion := c; machine := M c m'|>) =
    yul_expr_result_CASE (invoke_yul n fns name args m) b1
      (λc m'. <|completion := c; machine := M c m'|>)
Proof
  rw [] >> Cases_on `invoke_yul n fns name args m` >>
  imp_res_tac invoke_yul_abrupt_neq_normal >>
  gvs [yul_expr_result_case_def]
QED

(* The same again for a branch whose test is the completion alone, which is the
 * shape a case reaches once the field read above has taken the record apart. *)
Theorem yul_expr_result_CASE_invoke_abrupt_cond:
  ∀n fns name args m b1 T E.
    yul_expr_result_CASE (invoke_yul n fns name args m) b1
      (λc m'. if c = YulNormal then T c m' else E c m') =
    yul_expr_result_CASE (invoke_yul n fns name args m) b1
      (λc m'. E c m')
Proof
  rw [] >> Cases_on `invoke_yul n fns name args m` >>
  imp_res_tac invoke_yul_abrupt_neq_normal >>
  gvs [yul_expr_result_case_def]
QED

Theorem run_yul_fuel_stable:
  run_yul n code m = r ∧ r.completion ≠ YulOutOfFuel ∧ n ≤ k ⇒
  run_yul k code m = r
Proof
  rw[run_yul_def] >> metis_tac[eval_yul_fuel_stable]
QED

(* ---------------------------------------------------------------------------
   What a call hands back: the caller's own scope stack, and as many values as
   the callee declares results.

   A call's frame is the callee's alone, so the machine a call returns differs
   from the caller's only in the fields the callee itself wrote: its scope
   stack is the caller's, unchanged.  And the values it returns are the
   callee's result names read out of that frame, one apiece, so their number is
   the callee's -- known from the function table, and the reason a caller's
   binding of them can be resolved at all.
 ---------------------------------------------------------------------------*)

Theorem invoke_yul_scopes:
  (∀n fns name args m vals m'.
     invoke_yul n fns name args m = EvalValues vals m' ⇒ m'.scopes = m.scopes) ∧
  (∀n fns name args m c m'.
     invoke_yul n fns name args m = EvalAbrupt c m' ⇒ m'.scopes = m.scopes)
Proof
  conj_tac >> rpt gen_tac >> strip_tac >>
  pop_assum mp_tac >> simp [eval_yul_block_def] >>
  BasicProvers.every_case_tac >> rpt strip_tac >>
  gvs [yulStateTheory.yul_machine_accfupds]
QED

Theorem yul_lookup_names_length:
  ∀nms scopes vals. yul_lookup_names nms scopes = SOME vals ⇒
    LENGTH vals = LENGTH nms
Proof
  Induct_on `nms` >> rw [yul_lookup_names_def] >>
  rename1 `yul_lookup nm scopes` >>
  Cases_on `yul_lookup nm scopes` >> gvs [] >>
  Cases_on `yul_lookup_names nms scopes` >> gvs [] >> metis_tac []
QED

Theorem invoke_yul_values_length:
  ∀n fns name args m vals m' fd.
    FLOOKUP fns name = SOME fd ∧
    invoke_yul n fns name args m = EvalValues vals m' ⇒
    LENGTH vals = LENGTH fd.function_results
Proof
  rpt gen_tac >> strip_tac >>
  pop_assum mp_tac >> simp [eval_yul_block_def] >>
  BasicProvers.every_case_tac >> rpt strip_tac >>
  gvs [] >> imp_res_tac yul_lookup_names_length >> gvs []
QED

(* The spine a call's answer has, off the callee's own result names: a list of
 * a known length is still a variable, and `ZIP` and `list_CASE` match on `::`
 * and `[]`, so a caller binding the answer stays stuck on it however well its
 * length is known.  Taking the names' own shape turns the known length into
 * the constructors the match needs. *)
Definition yul_take_shape_def:
  (yul_take_shape ([] : string list) (vals : bytes32 list) = []) ∧
  (yul_take_shape (nm :: nms) vals = HD vals :: yul_take_shape nms (TL vals))
End

Theorem yul_take_shape_id:
  ∀nms vals. LENGTH nms = LENGTH vals ⇒ yul_take_shape nms vals = vals
Proof
  Induct_on `nms` >> rpt gen_tac >> Cases_on `vals` >>
  gvs [yul_take_shape_def]
QED

(* One rewrite that says both, on the case a caller's split leaves: a branch
 * that reads the answer's spine or the machine's scope stack sees the callee's
 * result names and the caller's own scopes instead.  The two antecedents are
 * what the caller can look up (the table's binding, and the arity the clause
 * itself tests), and the branch functions are arbitrary, so the rule reaches a
 * case wherever the continuation has been pushed into it. *)
(* Rewriting a machine's own scope stack back into it is the machine.  The
 * record package's own `_fupd` equations do the work; what this adds is the
 * single equation the conversion's rule below needs. *)
Theorem yul_machine_scopes_update_self:
  ∀m. m with scopes := m.scopes = m
Proof
  simp [yulStateTheory.yul_machine_component_equality,
        yulStateTheory.yul_machine_accfupds]
QED

Theorem yul_machine_scopes_update_eq:
  ∀m m'. m'.scopes = m.scopes ⇒ m' with scopes := m.scopes = m'
Proof
  rpt gen_tac >> strip_tac >>
  pop_assum (fn th => REWRITE_TAC [GSYM th]) >>
  simp [yul_machine_scopes_update_self]
QED

Theorem yul_expr_result_CASE_invoke_frame:
  ∀n fns name args m b1 b2 fd.
    FLOOKUP fns name = SOME fd ∧ LENGTH fd.function_params = LENGTH args ⇒
    yul_expr_result_CASE (invoke_yul n fns name args m) b1 b2 =
    yul_expr_result_CASE (invoke_yul n fns name args m)
      (λvals m'. b1 (yul_take_shape fd.function_results vals)
                   (m' with scopes := m.scopes))
      b2
Proof
  rw [] >> Cases_on `invoke_yul n fns name args m` >>
  imp_res_tac invoke_yul_values_length >> imp_res_tac invoke_yul_scopes >>
  gvs [yul_take_shape_id, yul_machine_scopes_update_eq]
QED


(* A memory write changes only the memory, whatever the bytes written.  Its
 * clauses recurse on the list, so a write of bytes the evaluator cannot list
 * -- the output a call returned, `TAKE n outcome.call_return` -- stays folded,
 * and these read the other fields through it. *)
Theorem yul_memory_write_fields:
  ∀bs m off.
    (yul_memory_write m off bs).accounts = m.accounts ∧
    (yul_memory_write m off bs).transient = m.transient ∧
    (yul_memory_write m off bs).logs = m.logs ∧
    (yul_memory_write m off bs).self_address = m.self_address ∧
    (yul_memory_write m off bs).caller_address = m.caller_address ∧
    (yul_memory_write m off bs).call_value = m.call_value ∧
    (yul_memory_write m off bs).call_data = m.call_data ∧
    (yul_memory_write m off bs).return_data = m.return_data ∧
    (yul_memory_write m off bs).immutables = m.immutables ∧
    (yul_memory_write m off bs).code = m.code ∧
    (yul_memory_write m off bs).objects = m.objects ∧
    (yul_memory_write m off bs).immutable_offsets = m.immutable_offsets ∧
    (yul_memory_write m off bs).memory_size = m.memory_size ∧
    (yul_memory_write m off bs).gas_limit = m.gas_limit ∧
    (yul_memory_write m off bs).scopes = m.scopes ∧
    (yul_memory_write m off bs).transaction_parameters = m.transaction_parameters
Proof
  Induct >> simp [yul_memory_write_def]
QED
