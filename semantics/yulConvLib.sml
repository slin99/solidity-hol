(* Unfolding one Yul call: the evaluator's own equations run over the body of
 * one function, with the calls it makes left standing.
 *
 * The Yul side of the translation-validation work has to be compared against
 * the bytecode's function, and the comparison needs the function's body
 * evaluated to a term over its arguments and its entry machine: not the
 * function table, which is the same table for every function, and not the
 * callees, which are proved separately.  The simplifier is the wrong tool for
 * it: the evaluator's equations are stated with `let`, and a simplifier that
 * expands a `let` before its bound term is a value copies the rest of the
 * evaluation into every branch.
 *
 * So the equations are run as compute rules, whose call-by-value order makes
 * a `let`'s bound term a value before it is substituted, and the three things
 * the compute rules cannot do themselves are done here:
 *
 *  - The scopes.  A scope is a chain of updates over the empty map, keyed by
 *    the names the compiler emitted, so `FLOOKUP` on one is decided by
 *    walking the chain: each update's key is a closed string, so the test
 *    `FLOOKUP_UPDATE` leaves is one the test set answers.  Nothing else has to
 *    know the names are literals.
 *
 *  - The call itself.  `invoke_yul`'s equation is deliberately not a compute
 *    rule, so a call the body makes stops there and is handed back to the
 *    caller as an `invoke_yul` application.  The one call that is unfolded is
 *    the one asked for, and its function is read out of the table by the same
 *    walk of the chain.
 *
 *  - The block, whose clause binds a statement's result and tests it.  A call
 *    leaves that result stuck, and evaluating the clause as it stands copies
 *    the rest of the body into every use of the bound name; the block is
 *    split on the statement's outcome instead.  That is the case tree the
 *    translation validation compares against, and it is the difference
 *    between a form of a few hundred constants and one of a few million.  See
 *    the section below.
 *
 * Reading the table is the only part that touches the compiler's whole
 * object, so it happens once per distinct table term and the table is left
 * alone in the form the caller gets: the body's calls name the table the
 * caller passed, not a copy of it.
 *)
structure yulConvLib :> yulConvLib =
struct

open HolKernel boolLib bossLib computeLib
open yulASTTheory yulEvaluatorTheory yulEvaluatorPropsTheory

(*---------------------------------------------------------------------------
   Finite maps.

   finite_mapSyntax is not built in the toolchain holbuild gives a project, so
   the FLOOKUP syntax comes from the kernel's own `syntax_fns2`, which also
   instantiates: the constant is polymorphic, and `list_mk_comb` will not
   instantiate it.
 ---------------------------------------------------------------------------*)

val (flookup_tm, mk_flookup, dest_flookup, is_flookup) =
  HolKernel.syntax_fns2 "finite_map" "FLOOKUP"

val invoke_c = prim_mk_const {Thy = "yulEvaluator", Name = "invoke_yul"}
val eval_yul_block_c = prim_mk_const {Thy = "yulEvaluator", Name = "eval_yul_block"}

(* The constants are recognised by theory and name, reading the record
 * `dest_term` leaves rather than making one to compare against. *)
fun is_const_named thy nm tm =
  case Lib.total dest_thy_const tm of
    SOME {Thy, Name, ...} => Thy = thy andalso Name = nm
  | NONE => false

fun head_const t = fst (strip_comb t)

fun is_fempty tm = is_const_named "finite_map" "FEMPTY" tm
fun is_update tm = is_const_named "finite_map" "FUPDATE" (head_const tm)
fun is_invoke tm = is_const_named "yulEvaluator" "invoke_yul" tm

(* `SOME v`, as opposed to NONE, which is not an application at all. *)
fun is_some tm = is_const_named "option" "SOME" (head_const tm)

(* A constant is keyed by theory and name, not by type: at any instance it is
 * still a step of the evaluation the form was supposed to have taken. *)
fun const_key (r : {Name : string, Thy : string, Ty : 'a}) = (#Thy r, #Name r)

fun consts_in tm =
  case dest_term tm of
    Term.VAR _ => []
  | Term.CONST r => [const_key r]
  | Term.LAMB (_, b) => consts_in b
  | Term.COMB (a, b) => consts_in a @ consts_in b

(* The two things a rule asks about a term before it copies one: does it hold a
 * call the conversion has left folded -- what copies a form is always the
 * scaffolding around one of these -- and does it hold a `word_exp`, which a
 * test's own reduction is kept off (see `eval_unsafe` below).  Both are
 * questions about the term alone, and the terms are the machines and statement
 * results the conversion is about, the same one asked about again and again as
 * a body's tail is handed from branch to branch, so the answer is remembered.
 * One walk settles both. *)
local
  val answers : (bool * bool) Termtab.table ref = ref Termtab.empty
in
  fun clear_answers () = answers := Termtab.empty

  fun scan tm =
    case Termtab.lookup (!answers) tm of
      SOME b => b
    | NONE =>
        let
          val ks = consts_in tm
          val b = (Lib.mem ("yulEvaluator", "invoke_yul") ks,
                   Lib.mem ("words", "word_exp") ks orelse
                   Lib.mem ("words", "word_exp_tailrec") ks)
        in
          answers := Termtab.update (tm, b) (!answers);
          b
        end
end

fun contains_invoke tm = #1 (scan tm)

(*---------------------------------------------------------------------------
   One scope lookup.

   `FLOOKUP f k` where f is FEMPTY or an update of one: the evaluator's own
   equation, whose test k' = k the test set decides, then one update in when
   the test is false.  Any other map -- a variable, or something no rule reads
   -- is left alone, so a lookup the conversion cannot decide shows up as a
   residue rather than as a wrong answer.

   The branch is taken by the two COND_CLAUSE theorems rather than by a
   simplifier: SIMP_CONV is TRY_CONV over the simplifier, and TRY_CONV catches
   only HOL_ERR, so a simplifier that makes no progress raises UNCHANGED
   straight through it.  `QCONV` is what turns a conversion that declines into
   the identity, which is what the two together are used as here.
 ---------------------------------------------------------------------------*)

val (cond_true, cond_false) = CONJ_PAIR (SPEC_ALL boolTheory.COND_CLAUSES)

(* `if T then t1 else t2` to t1, `if F then ...` to t2, and -- since QCONV
 * below only answers UNCHANGED -- nothing otherwise. *)
fun cond_conv tm =
  let val (test, _, _) = boolSyntax.dest_cond tm in
    if test ~~ boolSyntax.T then Conv.REWR_CONV cond_true tm
    else if test ~~ boolSyntax.F then Conv.REWR_CONV cond_false tm
    else raise Conv.UNCHANGED
  end
  handle HOL_ERR _ => raise Conv.UNCHANGED

(*---------------------------------------------------------------------------
   The set a test is reduced on.

   `EVAL` is not usable for this.  `wordsLib` adds the word library's rules to
   the *global* set when it is loaded (`computeLib.upd_compset
   (add_words_compset false)`), so `word_exp w v = word_exp_tailrec w v 1w` is
   there whatever set the caller built, and the tail recursion takes the
   exponent apart a bit at a time with no bottom on a symbolic one.  A test that
   holds a `word_exp` must therefore not be reduced on that set -- and it is not
   only a test that holds one: a test whose reduction *reaches* one does too.
   `FLOOKUP scope x = NONE`, the guard the evaluator's own lookup writes, is a
   lookup of a scope whose values hold what the body's calls returned, and the
   conditional `FLOOKUP_UPDATE` makes of it has those values in its branches,
   which a call-by-value reduction takes as well as the guard.  That is how
   `power := cleanup_uint8(exp(base, exponent))` -- one statement of one corpus
   function, its exponent symbolic -- stopped the conversion: nothing in the
   test named `word_exp`, so the scan that keeps `EVAL` off one did not fire,
   and the branches' `word_exp` unfolded the tail recursion on a symbolic
   exponent, which has no bottom.

   So the rules here reduce a test on a set of their own: the global one as it
   was when this file loaded, with the evaluator's own clause for `invoke_yul`
   and for the block taken out (a test's reduction must not unfold a callee
   either, and a scope's values are folded calls), and with the word library's
   exponentiation recursion taken out and the literal-only rule put back.
 ---------------------------------------------------------------------------*)
val word_exp_c = prim_mk_const {Thy = "words", Name = "word_exp"}
val word_exp_tailrec_c =
  prim_mk_const {Thy = "words", Name = "word_exp_tailrec"}

(* The literal case, on a set that has the word library's own rules: `n2w` of a
 * numeral is what makes `word_exp 2w 3w` a value rather than a term.  A copy,
 * because `add_words_compset` adds to the compset it is given and a compset's
 * per-constant entries are shared refs -- building it on `the_compset ()` would
 * put the word library into the global set, and with it `EVAL`. *)
val exp_compset =
  wordsLib.add_words_compset true (computeLib.copy (computeLib.the_compset ()))

(* Both arguments literal is the only case worth taking: with a symbolic base
 * the answer is `n2w (w2n base ** k)`, a longer term rather than a value, so a
 * symbolic exponentiation stays as the value it is. *)
fun word_exp_conv tm =
  case Lib.total (fn () => snd (strip_comb tm)) () of
    SOME [a, b] =>
      if wordsSyntax.is_word_literal a andalso wordsSyntax.is_word_literal b
      then computeLib.CBV_CONV exp_compset tm
      else raise Conv.UNCHANGED
  | _ => raise Conv.UNCHANGED

val test_compset =
  computeLib.add_conv (word_exp_c, 2, word_exp_conv)
    (List.foldl (fn (c, cs) => computeLib.scrub_const cs c)
       (computeLib.copy (computeLib.the_compset ()))
       [eval_yul_block_c, invoke_c, word_exp_c, word_exp_tailrec_c])

fun eval_test tm = computeLib.CBV_CONV test_compset tm

fun flookup_conv tm =
  let val (f, _) = dest_flookup tm in
    if is_fempty f then
      Conv.REWR_CONV finite_mapTheory.FLOOKUP_EMPTY tm
    else if not (is_update f) then raise Conv.UNCHANGED
    else
      let
        val update = Conv.REWR_CONV finite_mapTheory.FLOOKUP_UPDATE tm
        val (test, _, _) = boolSyntax.dest_cond (rhs (concl update))
        val test_thm = eval_test test
        val truth = rhs (concl test_thm)
        val is_true = truth ~~ boolSyntax.T
        val is_false = truth ~~ boolSyntax.F
      in
        if not (is_true orelse is_false) then raise Conv.UNCHANGED
        else
          let
            (* The test is rewritten in place, not by a rewriter over the
             * whole conditional: the `else` side is the rest of the chain,
             * which for a real object is the whole table, and a rewriter
             * asked to rewrite it walks all of it to change one subterm. *)
            val cond_tm = rhs (concl update)
            val (_, then_tm, else_tm) = boolSyntax.dest_cond cond_tm
            val cond_c = fst (strip_comb cond_tm)
            val cond_thm =
              Thm.AP_THM (Thm.AP_THM (Thm.AP_TERM cond_c test_thm)
                            then_tm)
                else_tm
            val branch = Conv.QCONV cond_conv (rhs (concl cond_thm))
            val sofar = Thm.TRANS update (Thm.TRANS cond_thm branch)
          in
            if is_false then Thm.TRANS sofar (flookup_conv (rhs (concl branch)))
            else sofar
          end
      end
  end

(*---------------------------------------------------------------------------
   The equations, and the compute set they run in.
 ---------------------------------------------------------------------------*)

(* Each clause of a `Definition` is universally quantified, so the head is
 * read off an instance: for the whole mutually recursive group -- the six
 * clauses that do the work, and invoke_yul, which is the one call the caller
 * gets to see and so is kept out of the compute set. *)
fun head_const_of th = head_const (lhs (concl (SPEC_ALL th)))

(* The head constants of every clause of a list of definitions, taken one
 * conjunct at a time: a definition of a non-recursive function over a list is
 * a conjunction rather than a quantified equation, and has no single head. *)
fun clause_heads ths =
  List.concat (List.map (fn th => List.map head_const_of (CONJUNCTS th)) ths)

val is_block_clause = fn th => is_const_named "yulEvaluator" "eval_yul_block"
                                   (head_const_of th)

val clauses = CONJUNCTS eval_yul_block_def

val invoke_clause =
  valOf (List.find (fn th => is_invoke (head_const_of th)) clauses)

(* What the compute set runs: everything but the call, which is folded, and the
 * block, whose clauses the rule below replaces with a split on the statement's
 * result. *)
val evaluator_clauses =
  List.filter (fn th => not (is_invoke (head_const_of th)) andalso
                        not (is_block_clause th)) clauses

(* What the equations reach on the way: the record readers, which build a
 * result out of a completion and a machine and never copy one. *)
val helper_defs = [
  yul_normal_def, yul_abrupt_def, yul_invalid_def,
  yul_literal_value_def, yul_sign_extend_def
]

(* The operations that read or build a machine, a scope, memory or storage, and
 * the builtin dispatch that reaches them.  `yul_bind` is the shape of them all:
 * it tests `m.scopes`, writes a scope back into `m` and hands `m` on, so
 * unfolding it over a machine that holds a folded call puts that call at each
 * of the three places `m` is used.  A body of k such steps then comes out at
 * about 3^k times the size whatever the block does with its statements, and it
 * is the machine -- the call's own scaffolding -- that is being tripled, not
 * the statement.
 *
 * So each of these unfolds only while its own term holds no folded call, and
 * stays folded otherwise.  That is exactly the boundary between the two kinds
 * of input: inside a statement's outcome -- the case the block splits on -- the
 * values and the machine are the case's bound variables, so a binding unfolds
 * there and resolves its scope, while a step whose input is a frame a call has
 * not returned yet stays the step the evaluator itself stops at.
 *
 * The scope readers are not in this list.  A reader's own case is `option` over
 * `FLOOKUP`, and its branches are the two the evaluator answers a lookup with
 * -- a value, or a literal `YulInvalid` -- so unfolding it is what lets the
 * block's split decide which one of them the body is in; that is worth the
 * copies of the map it reads, and without it every statement after a call
 * branches on a variable and the rest of the body stays in both branches.
 *)
val guarded_helper_defs = [
  yul_pop_result_def, yul_pop_scope_def, yul_push_scope_def, yul_push_frame_def,
  yul_bind_def, yul_bind_scope_def, yul_assign_def, yul_assign_list_def,
  yul_update_def,
  yul_memory_byte_def, yul_memory_read_def, yul_memory_write_def,
  yul_memory_touch_def, yul_memory_region_def, yul_mload_def, yul_mstore_def,
  yul_sload_def, yul_sstore_def, yul_call_def,
  yul_return_data_copy_def, yul_name_of_bytes_def,
  eval_yul_builtin_call_def
]

(* Each of them as its constant and its clauses, and the arity the compute set
 * keys a conversion on, off the clause's own left-hand side. *)
fun clauses_about th =
  let val eqs = CONJUNCTS th
      val clause = hd eqs
      val nhyp = List.length (snd (strip_comb (lhs (concl (SPEC_ALL clause)))))
  in
    (head_const_of clause, nhyp, eqs)
  end

val guarded_helpers = List.map clauses_about guarded_helper_defs

(* One clause of the operation, the first that matches: a clause set of a
 * recursive function over a list has a clause per constructor, and the argument
 * that matches none is the one the evaluator cannot take either. *)
fun guarded_unfold eqs tm =
  if contains_invoke tm then raise Conv.UNCHANGED
  else
    let
      fun first [] = raise Conv.UNCHANGED
        | first (eq :: rest) = Conv.REWR_CONV eq tm handle HOL_ERR _ => first rest
    in
      first eqs
    end

(*---------------------------------------------------------------------------
   Splitting a body on its statements' outcomes.

   A block hands each statement's result to the rest of the body as

     let r = eval_yul_stmt n fns s m in
       if r.completion = YulNormal then eval_yul_block n fns ss r.machine else r

   and a statement that makes a call leaves `r` stuck on a call the conversion
   keeps folded.  A conversion that just evaluates that `let` copies the rest
   of the body into every place `r` is used -- three of them -- and then
   evaluates each copy, so a body of k statements comes out at about 3^k times
   the size, and the copies carry the calls' own scaffolding with them: one
   real function of the corpus (five statements, four of them calls) reaches
   four million constants, and one of the ABI decoders on symbolic arguments
   needs 18GB of heap.

   So the statement's result is split out first:

     case eval_yul_stmt n fns s m of
       EvalAbrupt c m' => <the body's continuation on that completion>
     | EvalValues vs m' => <...>

   which is the case tree the Yul side of the translation validation is
   compared against.  A leaf is the body's remainder with the statement's
   outcome substituted -- `r.machine` becomes the branch's own machine, a
   variable -- so the copies are small, and the branching is a call's two
   outcomes rather than the three places `r` was used.

   The split has to happen before the `let` is taken, so it is a compute rule
   for `eval_yul_block` itself rather than a conversion run over the finished
   term: `eval_yul_block`'s own clauses are left out of the compute set and
   this conversion puts the statement's result in the case form the rest of
   the rule set can work with.
 ---------------------------------------------------------------------------*)

(* The evaluator's result type is the one a block's statements hand each other.
 * Its scrutinee comes first and a constructor's branch function is curried on
 * the constructor's arguments, so splitting means abstracting each branch onto
 * the continuation.  The branch's type is a parameter of its own: a statement
 * hands the block a `yul_result`, and an expression hands a statement a
 * `yul_expr_result`, so the case being split need not be the one `f` is on.
 *
 * `yul_expr_result_RAND` is the lemma, in yulEvaluatorProps: a theorem about
 * the evaluator's own equations belongs in the theory that proves them, and a
 * structure compiled as a library has no theory open to prove one into. *)

(* A case on the evaluator's expression result.  After the compute set has run
 * over a statement this is what being stuck looks like -- for a call, or for a
 * name that reads a machine a call returned -- and it is what the split needs
 * to see. *)
fun is_yul_case tm =
  is_const_named "yulEvaluator" "yul_expr_result_CASE" (head_const tm)

(* How often a variable is used, to see whether a substitution would copy. *)
fun occurrences v tm =
  if aconv tm v then 1
  else
    case dest_term tm of
      Term.LAMB (bv, body) => if aconv bv v then 0 else occurrences v body
    | Term.COMB (a, b) => occurrences v a + occurrences v b
    | _ => 0

(* Beta reduction, except where it would copy a folded call: substituting one
 * into a continuation puts the call -- and the scaffolding around it -- at
 * every place the bound name appears, and evaluating those copies is the
 * blowup this file exists to avoid.  This is what sees a block's own binding
 * (the clause is written as the redex, so it is a `let` of this shape), and
 * declining there is not enough on its own: the redex is left for the compute
 * set to take, which copies it anyway.  Taking the binding where what copies
 * can be avoided is `result_conv` below; this rule is what takes the branches
 * a case has been pushed into, which are applications of a lambda to the
 * branch's own small term. *)
fun beta_conv tm =
  case dest_term tm of
    Term.COMB (rator, arg) =>
      if is_abs rator then
        let val (bv, body) = dest_abs rator in
          if contains_invoke arg andalso occurrences bv body >= 2
          then raise Conv.UNCHANGED
          else Thm.BETA_CONV tm
        end
      else raise Conv.UNCHANGED
  | _ => raise Conv.UNCHANGED

(* A `let` binding, taken the same way and with the same exception as a beta
 * redex: the clause is written as one or the other -- a `Definition` quotation
 * turns `let x = e in b` into the redex, but the binding a case has been pushed
 * into is the `LET` constant, and taking it is what lets the rule that drops a
 * call's dead branch see the conditional it is stated on.  Without it the
 * binding is left for the compute set, which substitutes the bound term at
 * every use. *)
fun let_conv tm =
  let
    val unlet = Conv.REWR_CONV boolTheory.LET_THM tm
    val applied = rhs (concl unlet)
    val (bv, body) = dest_abs (rator applied)
  in
    if contains_invoke (rand applied) andalso occurrences bv body >= 2
    then raise Conv.UNCHANGED
    else Thm.TRANS unlet (Thm.BETA_CONV applied)
  end
  handle HOL_ERR _ => raise Conv.UNCHANGED

(* A case whose scrutinee is itself a case, pushed outward: the outer case
 * moves inside the inner one, which is what surfaces the branches the inner
 * case decides -- and those are the ones the whole split exists to prune.
 * Applied at the top only, repeatedly, since the pushed-out inner case is at
 * the top again and may itself be one.  The conditional is in the list for
 * the same reason: a guard the evaluator leaves undecided, because the call in
 * it is folded, leaves the case in the test, where nothing else reaches it. *)
val push_lemmas = [yul_expr_result_CASE_cond,
                   yul_expr_result_CASE_CASE,
                   yul_expr_result_CASE_option,
                   yul_expr_result_CASE_list]

fun push_conv tm =
  let
    fun try_lemmas [] = raise Conv.UNCHANGED
      | try_lemmas (lem :: rest) = Conv.REWR_CONV lem tm handle HOL_ERR _ => try_lemmas rest
  in
    try_lemmas push_lemmas
  end

fun push_all_conv tm =
  let
    fun go acc 0 = acc
      | go acc k =
          case Lib.total push_conv (rhs (concl acc)) of
            NONE => acc
          | SOME th => go (Thm.TRANS acc th) (k - 1)
  in
    go (Thm.REFL tm) 8
  end

(* A case on a call's own result: the branch the callee's abrupt completion
 * takes cannot be the body's continuation at all -- a call that ends abruptly
 * never ends `YulNormal`, so the continuation's test `c = YulNormal` is false
 * there and the branch is the result itself.  That is what keeps the rest of
 * the body out of that branch, and a body of k calls at 2^k times the size. *)
val prune_lemmas = [yul_expr_result_CASE_invoke_abrupt_lit,
                    yul_expr_result_CASE_invoke_abrupt]

(* The rule's continuation is a function of the case's own variable and
 * machine, `λc m'. T c m'`, and HOL's ordinary rewrite matching is first
 * order: `REWR_CONV` hands the pattern to the kernel's matcher, which can only
 * take `T c m'` apart when the body really is an application of a head to
 * those two variables, and fails on any other body -- so the rule never fires
 * and the branch it prunes stays.  `HO_REWR_CONV` matches a variable applied
 * to bound variables to whatever the body is, so it takes the rule's
 * `T` to be an abstraction and beta-reduces what it puts back. *)
fun prune_call_conv tm =
  let
    fun try_ho lem = Conv.HO_REWR_CONV lem tm handle HOL_ERR _ => raise Conv.UNCHANGED
    fun first [] = raise Conv.UNCHANGED
      | first (lem :: rest) =
          (Conv.REWR_CONV lem tm handle HOL_ERR _ => try_ho lem)
          handle Conv.UNCHANGED => first rest
  in
    first prune_lemmas
  end

fun prune_all_conv tm =
  let
    fun go acc 0 = acc
      | go acc k =
          case Lib.total prune_call_conv (rhs (concl acc)) of
            NONE => acc
          | SOME th => go (Thm.TRANS acc th) (k - 1)
  in
    go (Thm.REFL tm) 4
  end

(* Whether a test is worth handing to the set at all, which is not the case
 * while it holds either of the two things `scan` reports.  A folded call, and a
 * `word_exp`: both are things a form carries on purpose, and a test is decided
 * by the small terms in it rather than by evaluating those.  The set the test
 * is reduced on has both taken out, so this is a question of cost, not of
 * soundness -- reducing a test that holds a call's whole argument list to
 * decide an equality is work with no answer at the end of it. *)
fun eval_unsafe tm =
  let val (call, exp) = scan tm in call orelse exp end

(* `if <test> then t1 else t2` with a test the set can decide: a completion
 * carrying a message is told apart from YulNormal the same way a bare
 * constructor is, and one that is still a variable leaves the conditional
 * alone. *)
fun decide_conv tm =
  let
    val (test, t1, t2) = boolSyntax.dest_cond tm
    val test_thm = if eval_unsafe test then raise Conv.UNCHANGED
                   else eval_test test
    val truth = rhs (concl test_thm)
    val rule = if truth ~~ boolSyntax.T then cond_true
               else if truth ~~ boolSyntax.F then cond_false
               else raise Conv.UNCHANGED
    val tested = Thm.AP_THM
                   (Thm.AP_THM (Thm.AP_TERM (fst (strip_comb tm)) test_thm) t1)
                   t2
  in Thm.TRANS tested (Conv.REWR_CONV rule (rhs (concl tested))) end
  handle HOL_ERR _ => raise Conv.UNCHANGED

(* The two fields the block's clause reads off a statement's result, taken out
 * of the result itself.  The clause is
 *
 *   let r = eval_yul_stmt n fns s m in
 *     if r.completion = YulNormal then eval_yul_block n fns ss r.machine else r
 *
 * and the binding has three uses of `r`.  `beta_conv` above declines to take
 * it -- the bound term holds a folded call, as it does as soon as the body has
 * made one, and `r` is used twice or more -- so the compute set is what takes
 * it, and the term it substitutes at each use carries the machine and every
 * scope and memory write the body has built on it.  A straight-line body
 * therefore grew by about 2.4 per statement, call statements and plain
 * assignments alike; measured as constants in the block's normal form over
 * fun_widen's first four statements: 20 388, 62 676, 130 116, 306 660.
 *
 * The fields are taken out first, which leaves the machine once.  The clauses
 * of `yul_normal` and its siblings are rewrite rules of the compute set, so
 * what a block's clause reads its fields off is the record a statement reduced
 * to; the equations that read a field off one are the datatype's own, saved by
 * the record package (`RecordType.sml`'s `save_thm(typename^"_accessors", …)`)
 * as `yul_result_accessors`: one per field, `∀c m. sel (yul_result c m) = c`
 * and `= m`.  Those equations are not what reads a field here.  They are
 * stated on the constructor application, and a literal this evaluator builds
 * is a chain of updates over one rather than that application: the head of the
 * selector on a statement's result is a `_fupd` constant, the constructor is
 * nowhere in the term, and every `REWR_CONV` of an accessor equation on it
 * fails.  All that is taken from them is which constants are fields; the
 * reading itself is left to the compute set, whose own rules for the datatype
 * (`_accfupds`, saved by the record package with the accessors, and the
 * type's update equations) do know the chain.
 *
 * They are also quantified over the fields, so they are specialised before
 * anything is read off them: `lhs` on a theorem that is still a `∀` is a
 * `HOL_ERR`, and raised where the equations are read -- inside a `DEPTH_CONV`
 * -- it would come out as "nothing to take" rather than as the mistake it is. *)
val result_field_eqs =
  case List.map SPEC_ALL (CONJUNCTS yulStateTheory.yul_result_accessors) of
    [eq1, eq2] => [eq1, eq2]
  | _ => raise ERR "yulConvLib"
                "yul_result_accessors is not one equation per field"

fun eq_accessor eq = fst (strip_comb (lhs (concl eq)))

fun is_result_field c = List.exists (fn eq => same_const c (eq_accessor eq))
                                    result_field_eqs

(* The compute set with `block_conv` in it, closed over by the two conversions
 * that have to reduce a term which is part of one: reading a record's field,
 * and the statement rule below.  It has to be the set the rule is part of, so
 * that a block nested in what they reduce is taken the same way; the reference
 * closes that circle. *)
(* A block the conversion has already taken, remembered by its term.  What the
 * rule derives is a function of the term alone -- the compute set it runs on is
 * fixed for the whole of one call -- and a body's continuation is handed to the
 * branch of every decision above it, so the same `eval_yul_block n fns ss m`
 * is converted again and again as the body's own guarantees are split out.
 * Emptying the table whenever the set changes is what keeps the equations
 * valid: they hold for the set that produced them, and not for another.
 *
 * Terms are hash-consed, so `Term.compare`'s first test -- pointer equality --
 * settles the entry the lookup is after, and only the misses past it walk both
 * terms. *)
val blocks : thm Termtab.table ref = ref Termtab.empty

fun memo_blocks tm = Termtab.lookup (!blocks) tm

fun remember_block tm th = blocks := Termtab.update (tm, th) (!blocks)

local
  val cs_ref : compset option ref = ref NONE
in
  fun cs () =
    case !cs_ref of
      SOME c => c
    | NONE => raise ERR "yulConvLib" "the compute set is not set yet"

  fun set_block_compset c =
    (cs_ref := SOME c; blocks := Termtab.empty; clear_answers ())
end
(* A field, read off a record: `sel v` for a term whose selector is one of the
 * datatype's fields.  Anything else is left alone, which is what keeps this
 * out of the way of the rest of `step_conv`'s work. *)
fun reduce_field tm =
  case Lib.total dest_comb tm of
    SOME (acc, _) =>
      if not (is_result_field acc) then raise Conv.UNCHANGED
      else
        let val th = computeLib.CBV_CONV (cs ()) tm in
          if aconv tm (rhs (concl th)) then raise Conv.UNCHANGED else th
        end
  | NONE => raise Conv.UNCHANGED

fun result_field_conv v tm =
  let val (_, x) = dest_comb tm in
    if aconv x v then reduce_field tm else raise Conv.UNCHANGED
  end
  handle HOL_ERR _ => raise Conv.UNCHANGED

(* The binding, taken with its fields in hand.  A `let` in a definition is
 * either an application of `LET` or the beta redex itself -- this evaluator's
 * clause is the redex, `(λr. …) (eval_yul_stmt n fns s m)`, which is also why
 * `beta_conv` above sees it -- and the beta reduction is what takes it.  The
 * `LET` form is what the rule is stated on, and it is the only shape that
 * rewrite can take; the redex is left to the beta reduction below. *)
fun result_conv v tm =
  let
    val unlet =
      if is_const_named "bool" "LET" (head_const tm) then
        Conv.REWR_CONV boolTheory.LET_THM tm
      else Thm.REFL tm
    val beta = Thm.BETA_CONV (rhs (concl unlet))
    val body = rhs (concl beta)
    val proj = Conv.DEPTH_CONV (result_field_conv v) body
    val fields = rhs (concl proj)
    val taken = Conv.QCONV (Conv.DEPTH_CONV decide_conv) fields
  in Thm.TRANS unlet (Thm.TRANS beta (Thm.TRANS proj taken)) end

(* What the split exposed, taken.  The case the split builds has the block's
 * continuation in each of its branches, and a branch the evaluator has already
 * ended cannot use it: the statement answered with a completion, so the
 * clause's test `completion = YulNormal` is `F` there and the rest of the body
 * must not be built into it.  Two things say so.
 *
 * A case whose scrutinee is a value the evaluator built is that value's own
 * branch -- `yul_expr_result_CASE (EvalAbrupt (YulInvalid …) m) b1 b2` is
 * `b2 (YulInvalid …) m` -- so the branch that answers abruptly is reached and
 * its completion read off a literal.  And a field of a record is what the
 * record holds, so the test the clause wrote on the branch's own variable
 * becomes a test on a literal.  What is left is a conditional the test set
 * decides.
 *
 * Neither reduction is one of the evaluator's own clauses: the branches'
 * scrutinees are the case's bound variables, so no compute rule reaches them,
 * and they are what the two `_invoke_abrupt` lemmas do for a call by hand. *)

(* The function the block's clause hands on is the rest of the body, and an
 * applied function moves inside a decision its argument makes: `f (if g then a
 * else b)` is `if g then f a else f b`, and the same for the cases a statement's
 * result is built as.  Left above the statement's tree, the continuation reads
 * the completion and the machine off the whole tree -- the tree is copied at
 * every use of the bound name, and it holds every statement before this one --
 * so the machine the next statement is handed is a case expression over all of
 * them and a straight-line body grows by a factor per statement, even though
 * the continuation is one term.  Pushed in, each branch is handed what it holds:
 * a completion that can be read off a literal record, and a machine the next
 * statement's own lookups can be resolved against.
 *
 * Only a *binding* is pushed in -- the abstraction the clause is written as, or
 * the `LET` constant it turns into when something rewrites inside it.  A plain
 * application whose argument happens to be a decision, `eval_yul_block n fns ss
 * m` on a machine that is an `if`, is left where it is: nothing there is read
 * off the decision, and pushing would copy the rest of the body into both
 * branches of a decision the block's own clause does not branch on. *)
val distribute_lemmas = [boolTheory.COND_RAND,
                         yul_expr_result_RAND,
                         option_RAND]

fun is_binding tm =
  is_comb tm andalso
  (is_abs (rator tm) orelse is_const_named "bool" "LET" (fst (strip_comb tm)))

fun distribute_conv tm =
  if not (is_binding tm) then raise Conv.UNCHANGED
  else
    let
      fun first [] = raise Conv.UNCHANGED
        | first (lem :: rest) =
            Conv.REWR_CONV lem tm handle HOL_ERR _ => first rest
    in
      first distribute_lemmas
    end

(* The case equations of the types the evaluator's clauses case on: a
 * statement's result, and the `option` a value is looked up into and the
 * `list` its arguments are scanned from.  `CONJUNCTS` takes the two clauses of
 * each apart -- `CASE` on one constructor and on the other -- and leaves a
 * `_case_def` that is a single equation as itself. *)
val case_equations =
  CONJUNCTS yul_expr_result_case_def @
  CONJUNCTS optionTheory.option_case_def @
  CONJUNCTS listTheory.list_case_def

fun matching [] tm = raise Conv.UNCHANGED
  | matching (eq :: rest) tm =
      Conv.REWR_CONV eq tm handle HOL_ERR _ => matching rest tm

fun case_conv tm = matching case_equations tm

(* A binding, taken: the continuation is pushed inside whatever decision the
 * statement ended in, and what is left is an ordinary beta redex or `let`,
 * which the two rules below take with the exceptions they make for a term that
 * has to be kept once.  Distribution is tried before either, so that a decision
 * is never copied into the continuation's uses -- which is the copy the whole
 * pass exists to avoid. *)
fun binding_step_conv tm =
  if not (is_comb tm) then raise Conv.UNCHANGED
  else
    let
      val (c, _) = strip_comb tm
      val (rator, _) = dest_comb tm
      val is_beta = is_abs rator
    in
      if is_beta orelse is_const_named "bool" "LET" c then
        distribute_conv tm
        handle Conv.UNCHANGED =>
          (if is_beta then beta_conv tm else let_conv tm)
      else raise Conv.UNCHANGED
    end

(* One node of the pass, dispatched on what the node is.  A depth-first pass
 * reaches every node of the form, and most of them are neither a case on one
 * of these types nor a binding nor a field, so trying every rule at all of them
 * pays a failed match -- and an exception -- for every rule at every node: on
 * a body whose form is tens of thousands of nodes, and with the pass repeated
 * until it changes nothing, that is what a form costs seconds in.  The head
 * constant (or an abstraction where a function goes) is the test, and the rules
 * it dispatches to cannot overlap: a case's head is its own type's constant, a
 * binding's is `LET` or an abstraction, and a field's is a selector.
 *
 * Taking a case or a conditional apart can leave a beta redex in the node's
 * place -- the branch a case applies is written as a function even when it is
 * the abstraction it was pushed into -- so those two nodes hand on to the
 * binding rules, as the pass did when every rule was tried at every node. *)
fun after_binding th =
  let val t = rhs (concl th)
  in Thm.TRANS th (binding_step_conv t handle Conv.UNCHANGED => Thm.REFL t) end

fun step_conv tm =
  if not (is_comb tm) then raise Conv.UNCHANGED
  else
    let
      val (c, _) = strip_comb tm
      val (rator, _) = dest_comb tm
      val is_beta = is_abs rator
    in
      if is_const_named "yulEvaluator" "yul_expr_result_CASE" c orelse
         is_const_named "option" "option_CASE" c orelse
         is_const_named "list" "list_CASE" c
      then after_binding (case_conv tm)
      else if is_beta orelse is_const_named "bool" "LET" c
      then binding_step_conv tm
      else if is_const_named "bool" "COND" c then after_binding (decide_conv tm)
      else reduce_field tm
    end

(* `QCONV`: a pass that finds nothing to take is this conversion's way of
 * saying so, and it has to be the identity here rather than an exception --
 * `block_conv` is a compute rule, and one that raises `UNCHANGED` is read as a
 * rule that does not apply, which leaves the block standing in the form with
 * nothing said about it. *)
val expose_conv = Conv.QCONV (Conv.DEPTH_CONV step_conv)

(* Repeated, since taking a case apart exposes another one, and one pass of a
 * depth-first reduction does not return to what beta reduction has just put at
 * the top.  It is also where the case a scrutinee is itself a case is broken
 * up (`push_all_conv` above), which is what lets a literal branch a nested
 * case decides be reached at all. *)
fun expose_all_conv tm =
  let
    fun go acc 0 = acc
      | go acc k =
          let
            val pushed = push_all_conv (rhs (concl acc))
            val red = expose_conv (rhs (concl pushed))
            val next = Thm.TRANS acc (Thm.TRANS pushed red)
          in
            if aconv (rhs (concl next)) (rhs (concl acc)) then next
            else go next (k - 1)
          end
  in
    go (Thm.REFL tm) 6
  end

(* Taking the cases apart and dropping the dead ones, until neither has
 * anything left to do.  The order matters: a case that has just been pushed
 * out from inside a scrutinee is at the top and may be a call's, which the
 * prune is what drops -- and a branch the prune drops may leave a case that
 * has just become reducible behind it.  Doing all the taking apart first and
 * the pruning after leaves every call case the push surfaced unpruned, and a
 * body of k calls at 2^k times the size. *)
fun settle_conv tm =
  let
    fun go acc 0 = acc
      | go acc k =
          let
            val exposed = expose_all_conv (rhs (concl acc))
            val pruned = prune_all_conv (rhs (concl exposed))
            val next = Thm.TRANS acc (Thm.TRANS exposed pruned)
          in
            if aconv (rhs (concl next)) (rhs (concl acc)) then next
            else go next (k - 1)
          end
  in
    go (Thm.REFL tm) 3
  end

(* `(λr. CONT r) (case stmt of …)`: the continuation moves into the branches
 * (`yul_expr_result_RAND`), a call's own abrupt branch is dropped, and what
 * the case exposed is taken.  The branches' own bindings are taken here, before
 * the prune rather than after it: the prune is stated on the conditional the
 * clause wrote, and the field extraction below would have replaced its test
 * with the variable it is on. *)
fun split_conv tm =
  let
    val split = Conv.REWR_CONV yul_expr_result_RAND tm
    val betad = Conv.QCONV (Conv.DEPTH_CONV binding_step_conv)
                          (rhs (concl split))
    val out = settle_conv (rhs (concl betad))
  in
    Thm.TRANS split (Thm.TRANS betad out)
  end

(* `(λr. CONT r) v` where `v` is the record the clause reads its fields off:
 * the fields are taken out first, which leaves the machine once (see
 * `result_conv` above).  Not every statement's result is a record, though.  A
 * clause that ends in a test its own evaluation cannot decide -- `if NULL v
 * then <a binding into empty scopes> else <…>`, because the machine is a
 * variable a branch of the body handed it -- answers with a *decision*, and no
 * field is there to read: the binding is left to be copied at each of its
 * three uses, and the block in it is copied with the machine the body has not
 * resolved.  So the continuation goes inside the decision instead -- the same
 * push the split makes, over `COND_RAND` rather than the case's -- and each
 * branch is then handed a record to read, which is the shape the split's own
 * branches are in.  What neither rule recognises is left to the beta
 * reduction, as before; a decline from either has to end there rather than
 * escaping, since `block_conv` is a compute rule and a conv that raises is
 * read as one that does not apply. *)
fun value_conv v redex =
  result_conv v redex
  handle Conv.UNCHANGED =>
    (let
       val pushed = distribute_conv redex
       val recd = Conv.QCONV (Conv.DEPTH_CONV binding_step_conv)
                    (rhs (concl pushed))
       val out = settle_conv (rhs (concl recd))
     in
       Thm.TRANS pushed (Thm.TRANS recd out)
     end
     handle Conv.UNCHANGED => Conv.QCONV (Conv.DEPTH_CONV beta_conv) redex)
  | HOL_ERR _ => Conv.QCONV (Conv.DEPTH_CONV beta_conv) redex

(*---------------------------------------------------------------------------
   The compute rule for `eval_yul_block`.

   It takes one statement at a time: the evaluator's own clause for the
   statements, the statement's result evaluated on its own (a small term, since
   the rest of the body is not in it), and then the split.  On a result the
   evaluator decided -- a value, not a case -- there is nothing to split and
   the binding is taken as an ordinary `let`.
 ---------------------------------------------------------------------------*)

(* The two clauses of the block's definition, told apart by the statement list
 * they match: the empty one, and one statement and the rest. *)
val block_def_clauses = List.filter is_block_clause clauses

fun clause_is_nil th =
  let val tms = snd (strip_comb (lhs (concl (SPEC_ALL th))))
  in is_const_named "list" "NIL" (head_const (List.nth (tms, 2))) end

val block_nil_clause = valOf (List.find clause_is_nil block_def_clauses)
val block_cons_clause =
  valOf (List.find (fn th => not (clause_is_nil th)) block_def_clauses)

(* The statement rule, run as a compute rule (`add_conv` below): the clause is
 * instantiated, the statement is reduced with the compute set, and what the
 * statement reduced to is taken apart as `split_conv` or `value_conv` says. *)
fun block_conv_raw tm =
  let
    val (_, tms) = strip_comb tm
  in
    if List.length tms <> 4 then raise Conv.UNCHANGED
    else
      (* Only a literal statement list is taken here.  The clause matches
       * any list, but a body's list is a literal in the table the
       * conversion reads, and one that is not means the term is not a
       * form this rule can take apart. *)
      case Lib.total listSyntax.dest_list (List.nth (tms, 2)) of
        NONE => raise Conv.UNCHANGED
      | SOME (ss, _) =>
          let
            val clause = Conv.REWR_CONV
                           (if null ss then block_nil_clause
                            else block_cons_clause) tm
          in
            if null ss then clause
            else
              let
                val redex = rhs (concl clause)
                val (_, stmt) = dest_comb redex
                val ev = computeLib.CBV_CONV (cs ()) stmt
                val taken = Thm.TRANS clause
                              (Conv.RAND_CONV (fn _ => ev) redex)
                val redex' = rhs (concl taken)
              in
                (* A case at the top is the split; anything else is the
                 * statement's own result, and the binding is taken with
                 * whatever the result is (see `value_conv` above). *)
                let val ev_form = rhs (concl ev) in
                if is_yul_case ev_form
                then Thm.TRANS taken (split_conv redex')
                else Thm.TRANS taken (value_conv ev_form redex')
                end
              end
          end
  end

(* The rule itself: a block the table has is returned as the equation the
 * conversion derived for it, and one it does not have is converted and put
 * there.  A term the rule declines is not remembered -- `UNCHANGED` is the
 * set's way of saying the rule does not apply, not an answer about the term. *)
fun block_conv tm =
  case memo_blocks tm of
    SOME th => th
  | NONE =>
      let val th = block_conv_raw tm
      in
        remember_block tm th;
        th
      end

(* The base is EVAL's own compute set rather than the boolean one: an
 * evaluator clause is full of `case` over the Yul datatypes, and a datatype's
 * case equations are put where its definition registered them, not into the
 * boolean set.  The word library's own rules go on top of it, because the
 * evaluator reaches its memory through `w2n` of an address and EVAL's set
 * alone leaves `w2n 0w` standing, which is enough to strand every memory
 * operation -- the byte it would read never becomes a list to recurse on.
 * The word library's exponentiation recursion is taken back out, with the
 * literal-only rule for `word_exp` put in its place (see `test_compset`
 * above).
 *
 * On a copy of the global set: `add_words_compset` adds the word library's
 * rules to the compset it is given, and a compset's per-constant entries are
 * shared refs, so building this on `computeLib.the_compset ()` would change
 * what every later `EVAL` in the process reduces. *)
val eval_compset =
  let
    val base =
      computeLib.add_thms (evaluator_clauses @ helper_defs)
        (computeLib.add_conv (flookup_tm, 2, flookup_conv)
           (computeLib.add_conv (word_exp_c, 2, word_exp_conv)
              (computeLib.scrub_const
                 (computeLib.scrub_const
                    (wordsLib.add_words_compset true
                       (computeLib.scrub_const
                          (computeLib.scrub_const
                             (computeLib.copy (computeLib.the_compset ()))
                             eval_yul_block_c)
                          invoke_c))
                    word_exp_c)
                 word_exp_tailrec_c)))
    (* A guarded operation has no equation in the set at all -- the set's own
     * clause would run before any conversion and take the copy -- so its
     * clauses go on as this one rule, which declines on a term holding a call. *)
    fun guard ((c, nhyp, eqs), cs) =
      computeLib.add_conv (c, nhyp, guarded_unfold eqs)
        (computeLib.scrub_const cs c)
  in
    computeLib.add_conv (eval_yul_block_c, 4, block_conv)
      (List.foldl guard base guarded_helpers)
  end

(* The rule above reduces a statement with this compute set; it has to be the
 * one it is part of, or a block nested in a statement would be taken the old
 * way. *)
val () = set_block_compset eval_compset

(* The same with the table reader added: only reading the function out of the
 * object uses it, so the body's own evaluation never folds the object. *)
fun table_compset defs =
  computeLib.add_thms (yul_env_def :: defs) (computeLib.copy eval_compset)

(*---------------------------------------------------------------------------
   Reading the function table.

   Folded once per distinct table term, so that the per-function lookups walk
   a chain of the compiler's own definitions rather than rebuilding the object
   each time.
 ---------------------------------------------------------------------------*)

local
  (* A list, not a table: there is one table term per suite, and the whole
   * point of the memo is that the fold happens once. *)
  val chains : (term * thm) list ref = ref []
in
  fun table_chain defs fns =
    case List.find (fn (t, _) => aconv t fns) (!chains) of
      SOME (_, th) => th
    | NONE =>
        let val th = computeLib.CBV_CONV (table_compset defs) fns in
          chains := (fns, th) :: !chains; th
        end
end

(* `|- FLOOKUP fns name = SOME fd`, off the folded chain.  The chain is applied
 * to the lookup at the kernel level rather than by rewriting with it: a
 * rewriter walks the folded table it has just put in -- the compiler's whole
 * object, a million constants -- looking for further matches of the rule, and
 * that is 2.9s on every call however small the body is. *)
fun binding_thm defs fns name =
  let
    val chain = table_chain defs fns
    val flk = mk_flookup (fns, name)
    val flookup_c = fst (strip_comb flk)
    val ap = Thm.AP_THM (Thm.AP_TERM flookup_c chain) name
    val lk = flookup_conv (rhs (concl ap))
             handle Conv.UNCHANGED =>
               raise ERR "yulConvLib.binding_thm"
                 "the function table did not fold to one"
    val th = Thm.TRANS ap lk
  in
    if is_some (rhs (concl th)) then th
    else raise ERR "yulConvLib.binding_thm"
                 ("the function table does not bind " ^ term_to_string name)
  end

(*---------------------------------------------------------------------------
   Keeping the client's table out of the set the conversion runs on.

   HOL's compute set imports a theory's definitions as they are made
   (`computeLib.auto_import_definitions`), so a definition a client made before
   this library was loaded is already in `the_compset ()`, and `eval_compset` --
   built on a copy of it -- holds its equation.  A body that calls keeps the
   table as the folded call's own argument, so a set that unfolds it
   substitutes the compiler's whole object into the form -- `CBV_CONV` on the
   global set folds the corpus table to 414 885 nodes, against a statement's own
   evaluation in the tens -- and the machine every later statement is handed
   holds that copy, so the form is proportional to the object rather than to the
   body.

   A client whose fixture is defined *after* this library's load has none of it
   in the set to begin with, so the scrub below is a no-op there: on the corpus
   test, `CBV_CONV eval_compset` leaves both `scalars_function_table` and
   `yul_env scalars_object` standing, neither constant having an equation in the
   set, while the global set folds the table to 414 885 nodes.  What the scrub
   covers is the other order -- a fixture defined before this library loaded --
   and the literal table term a caller may pass instead of a name, whose
   constants do have equations in the set (`yul_env`'s, from `yulAST`).

   Nothing here wants the table unfolded.  The function the conversion was
   asked for is read off the folded chain at the kernel level (`binding_thm`),
   and a call the body makes is left as an `invoke_yul` application, so the
   table is only ever the constant the caller gave.  The client's own
   definitions are therefore scrubbed from the set, which leaves that constant
   alone -- in the form and in the set's own view of it.
 ---------------------------------------------------------------------------*)

val scrub_const = computeLib.scrub_const

fun scrub_defs cs defs =
  List.foldl (fn (th, cs) => scrub_const cs (head_const_of th)) cs defs

fun const_terms tm =
  case dest_term tm of
    Term.VAR _ => []
  | Term.CONST _ => [tm]
  | Term.LAMB (_, b) => const_terms b
  | Term.COMB (a, b) => const_terms a @ const_terms b

fun uniq_terms [] = []
  | uniq_terms (t :: ts) =
      t :: uniq_terms (List.filter (fn u => not (aconv t u)) ts)

(* The definitions the table needs *are* folded, deliberately, in
 * `table_compset`; this is the set the body's evaluation runs on. *)
fun body_set base defs table =
  List.foldl (fn (c, cs) => scrub_const cs c) (scrub_defs base defs)
    (uniq_terms (const_terms table))

(*---------------------------------------------------------------------------
   The conversion.
 ---------------------------------------------------------------------------*)

fun yul_invoke_conv defs tm =
  let
    val (f, tms) = strip_comb tm
    val _ = is_invoke f orelse
            raise ERR "yulConvLib.yul_invoke_conv"
                      "expected an invoke_yul application"
    val (fns, name) =
      case tms of
        [_, fns, name, _, _] => (fns, name)
      | _ => raise ERR "yulConvLib.yul_invoke_conv"
                       "expected an invoke_yul application"

    val bind = binding_thm defs fns name
    val step = Conv.REWR_CONV invoke_clause tm
    (* A copy: add_thms adds to the FLOOKUP entry in place, so a shared set
     * would collect one binding per call and get slower with each. *)
    val cs = computeLib.add_thms [bind]
               (body_set (computeLib.copy eval_compset) defs fns)
    (* The statement rule reduces the statement on the set the conversion is
     * running on, not on the one made at load time: same rules, with the
     * client's table scrubbed out of it. *)
    val () = set_block_compset cs
    val res = computeLib.CBV_CONV cs (rhs (concl step))
  in
    Thm.TRANS step res
  end

(*---------------------------------------------------------------------------
   Is a form the conversion produced closed?
 ---------------------------------------------------------------------------*)

(* What the conversion is meant to have removed: the equations it runs, the
 * scope and binding operations, and FLOOKUP itself, which is the way a scope
 * that did not come out is seen -- a lookup left standing means some name was
 * not read, which the caller would take for a form over its arguments.
 * invoke_yul is not among them -- a call the body made is exactly what the
 * form is allowed to carry. *)
val eliminated =
  List.map (const_key o dest_thy_const)
    (flookup_tm :: clause_heads (evaluator_clauses @ helper_defs @ block_def_clauses))

fun residues tm =
  Lib.mk_set (List.filter (fn k => Lib.mem k eliminated) (consts_in tm))

(* What a form may still contain: the call it left folded, and the evaluator's
 * own operations on a frame or on memory -- the ones under `helper_defs`.
 * What is *not* in here is the evaluation itself, the block, the statements
 * and the expressions, so a form with one of those in it is a form whose body
 * evaluation stopped early, which a test can say by asking a residue to be one
 * of these.
 *
 * A helper is in a form because its input is a value nobody has: after a call
 * the frame is the callee's; memory is a map to words, so a read of a word
 * written from a symbolic value is decided only when that value is; a scope
 * whose map came out of such a word is the same.  None of that is a step the
 * conversion could have taken.
 *)
val permitted_residues =
  ("yulEvaluator", "invoke_yul")
  :: List.map (const_key o dest_thy_const)
       (flookup_tm :: clause_heads helper_defs)

fun is_closed_form tm = null (residues tm)

(* The other half of what "closed" means, and the stronger half: the
 * conversion's own rules make no progress on the form, so nothing in it is a
 * step the conversion could still have taken.  A name list can only say which
 * constants are gone; this says there is nothing left for them to do, and it
 * catches a residue whose map or argument the conversion did not reach as
 * well as one it did.  The table reader is not in the set, so the function a
 * form names is not read again here. *)
fun is_fixed_point defs tm =
  aconv tm (rhs (concl (computeLib.CBV_CONV (scrub_defs eval_compset defs) tm)))

end
