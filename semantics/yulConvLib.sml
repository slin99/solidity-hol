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
val eval_yul_loop_c = prim_mk_const {Thy = "yulEvaluator", Name = "eval_yul_loop"}
val eval_yul_builtin_c =
  prim_mk_const {Thy = "yulEvaluator", Name = "eval_yul_builtin"}
(* The scope readers.  They are definitions of their own, outside the recursive
 * group `eval_yul_block_def` holds, so their clauses are not among the ones the
 * conversion is built from -- but the base set carries them, and a read of a
 * scope a callee has not returned yet comes out of the conversion standing. *)
val yul_lookup_c = prim_mk_const {Thy = "yulEvaluator", Name = "yul_lookup"}
val yul_lookup_names_c =
  prim_mk_const {Thy = "yulEvaluator", Name = "yul_lookup_names"}


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

(* Whether a machine is one a folded loop handed on.  The rest of a body after
 * a loop is left unevaluated over it: every scope read would be undecided, and
 * the client substitutes the loop's outcome and evaluates the rest then. *)
fun contains_loop tm = can (find_term (same_const eval_yul_loop_c)) tm

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
       [eval_yul_block_c, invoke_c, eval_yul_loop_c, word_exp_c,
        word_exp_tailrec_c])

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

fun is_loop_clause th = same_const eval_yul_loop_c (head_const_of th)

(* A loop is folded the way a call is: its run is a recursion with no closed
 * form, so the evaluation stops at it and a client proves it by induction on
 * the fuel, one iteration at a time (`yul_loop_conv`).  Unfolded,
 * it repeats the body once per unit of fuel with every iteration's guard
 * undecided, which no fuel big enough for the body's calls survives. *)
val loop_clause = valOf (List.find is_loop_clause clauses)

(* What the compute set runs: everything but the call and the loop, which are
 * folded, and the block, whose clauses the rule below replaces with a split on
 * the statement's result. *)
val evaluator_clauses =
  List.filter (fn th => not (is_invoke (head_const_of th)) andalso
                        not (is_loop_clause th) andalso
                        not (is_block_clause th)) clauses

(* What the equations reach on the way: the record readers, which build a
 * result out of a completion and a machine and never copy one. *)
val helper_defs = [
  yul_normal_def, yul_abrupt_def, yul_invalid_def,
  yul_literal_value_def, yul_sign_extend_def
]

(* The shaping the frame rule builds with, unfolded unconditionally: it is a
 * plain recursion over the result names, and unfolding it is what puts the
 * spine -- `HD vals`, `HD (TL vals)`, ... -- in the branch, where the arity the
 * clause tests and the binding the block writes can read it.  `helper_defs` is
 * the list a form's residues are read against, and this is not one of them: it
 * is this conversion's own construction and never part of an evaluator clause. *)
val shape_defs = [yul_take_shape_def]

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
 *
 * One of these clauses does not cover what the evaluator asks of it:
 * `yul_memory_read`'s are `0` and `SUC k`, and the length is the literal 32
 * `yul_mload` reads with, which no clause matches, so a memory read is a step
 * the conversion leaves standing.  `Definition` proves a `yul_memory_read_compute`
 * beside it for exactly this (HOL4's `Defn.add_defs_to_EVAL`, through
 * `SUC_TO_NUMERAL_DEFN_CONV`), and the scrub above is what takes it out of the
 * body's set.  Reading it is not free: the read then unfolds one byte at a time,
 * so `yul_memory_read … 32` becomes 32 reads -- all of them `0w` over a memory
 * the conversion has, and 32 stuck lookups over one it does not -- which is a
 * change to what a form says about the memory path, and to the sizes a form is
 * judged by, rather than one more clause here.
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
 * The lemmas are `TypeBase.case_rand_of`'s: the kernel states the distribution
 * for every datatype, on the case its `case_def` gives, which is the one the
 * evaluator's own clauses leave behind.  A structure compiled as a library has
 * no theory open to prove a lemma into, and nothing here needs one. *)

(* A case on the evaluator's expression result.  After the compute set has run
 * over a statement this is what being stuck looks like -- for a call, or for a
 * name that reads a machine a call returned -- and it is what the split needs
 * to see. *)
fun is_yul_case tm =
  is_const_named "yulEvaluator" "yul_expr_result_CASE" (head_const tm)

(*---------------------------------------------------------------------------
   Recognising a call's case the frame rule has already settled.

   The frame rule below rewrites a case on a folded call, `case (invoke_yul …)
   of … | EvalValues vals m' => CONT`, to the same case with the branch's own
   two variables read through what the call answered: `vals` through
   `yul_take_shape fd.function_results vals`, and `m'` through the caller's own
   scope stack, `m' with scopes := m.scopes`.

   Both halves of what the rule wrote are gone from the term by the time a
   later pass sees it: the conversion's own set unfolds the shaping
   (`yul_take_shape_def` is in it, deliberately: the spine is what the clause's
   arity test and the block's binding read), and the scope stack is the record
   package's own update, which the set reduces through.  A marker that looks
   for the rule's own output therefore finds nothing after the round that took
   the shaping out, and the rule fires again on every later pass over the same
   case: a sweep counts 1 283 applications for `fun_bitwise`, whose body has
   five calls, and 24 303 for `checked_exp_signed`.

   What a later application writes is the term that was already there -- the
   branch's values have been read by then, and the machine is up to
   `(m with scopes := s) with scopes := s` -- so what the re-fires cost is the
   rule's instantiation and the re-reduction of the clause, not a larger form.
   The forms of all 137 conversions are what they were before this marker, and
   the 133 the suite covers convert faster: 31.9s against 64.9s at the old one
   (one run each, the same set, the same box), `checked_exp_unsigned` alone at
   1.0s against 3.8.

   So the marker is not what the rule wrote but where it wrote it, and it is a
   question about the branch's own variables rather than about the rule's
   terms.  A case is settled when neither variable the rule rebinds appears
   anywhere the rule's output would not have put it: the values variable
   outside the argument `HD`, `TL` and `yul_take_shape` are handed, and the
   machine variable outside the record the frame's own update writes.  Before
   the rule runs the branch is the caller's continuation, and a continuation
   uses the machine it was handed as a whole -- `yul_normal m'`,
   `yul_bind names vs m'`, `eval_yul_block n fns ss m'` -- so an occurrence
   outside those is what an unsettled case has and a settled one has not.

   The search is over the branch alone.  A case nested in the continuation --
   settled earlier in the same bottom-up pass -- carries a marker of its own,
   over a variable of its own, and must not stop this one.
 ---------------------------------------------------------------------------*)

(* The constant the frame's update is written with, off the frame's own
 * equation rather than by name: the record package generates the name, and it
 * is not one to spell here. *)
val frame_update_key =
  const_key (dest_thy_const
    (fst (strip_comb
            (lhs (concl (SPEC_ALL yul_machine_scopes_update_self))))))

val vals_shape_keys = [("list", "HD"), ("list", "TL"),
                       ("yulEvaluatorProps", "yul_take_shape")]

(* The number of arguments a term of this type takes. *)
fun args_of_ty ty =
  case Lib.total Type.dom_rng ty of
    SOME (_, r) => 1 + args_of_ty r
  | NONE => 0

(* Whether `t` is one of `keys` applied to its own last argument -- `HD vals`,
 * `TL vals`, `yul_take_shape fd.function_results vals`, and the frame's own
 * `m' with scopes := m.scopes`, whose record is the last argument of the
 * update's constant.  Those are the positions the rule's output puts each
 * variable in, and the only places the search below may stop at: the argument
 * there is the rule's own construction, and descending into it would find the
 * marker the rule wrote rather than a use of what the call answered.
 *
 * Everywhere else is searched, the arguments in front of the last one
 * included, because those are the rule's own data -- `yul_take_shape`'s
 * callee results, the expression an update writes -- and a use of either
 * variable among them is not one the rule put there.  `yul_pop_scope` is what
 * makes that case real: the set reduces the caller's `yul_pop_scope m'` to
 * `m' with scopes := TL m'.scopes`, whose record is the machine variable but
 * whose expression is too, and the rule is what that branch is waiting for. *)
fun keyed t keys =
  let val (f, args) = strip_comb t in
    List.exists (fn (thy, nm) => is_const_named thy nm f) keys andalso
    List.length args = args_of_ty (type_of f)
  end

(* Whether `v` occurs in `tm` at a place `keys` does not account for. *)
fun escapes keys v tm =
  if aconv tm v then true
  else
    case dest_term tm of
      Term.LAMB (bv, b) => not (aconv bv v) andalso escapes keys v b
    | Term.COMB (x, y) =>
        escapes keys v x orelse (not (keyed tm keys) andalso escapes keys v y)
    | _ => false

(* The frame rule's own guard, off the term alone: a case on a folded call
 * whose values branch the rule has not settled.  It is the whole of what the
 * rule tests before it does any work, so a case it has settled -- the case
 * every pass after the first sees -- costs the search below and nothing
 * else. *)
fun frame_pending tm =
  is_yul_case tm andalso
  (let val cargs = snd (strip_comb tm) in
     List.length cargs = 3 andalso is_invoke (head_const (hd cargs)) andalso
     is_abs (List.nth (cargs, 1)) andalso
     (let val (vals_v, rest) = dest_abs (List.nth (cargs, 1)) in
        is_abs rest andalso
        (let val (mach_v, body) = dest_abs rest in
           escapes vals_shape_keys vals_v body orelse
           escapes [frame_update_key] mach_v body
         end)
      end)
   end
   handle HOL_ERR _ => false)

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
 * binding is left for the compute set, whose own rule for `let`
 * (`let_yul_conv`, below) pushes a binding into a decision and otherwise
 * substitutes the bound term at every use. *)
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
 * the body out of that branch, and a body of k calls at 2^k times the size.
 *
 * Three shapes, one per form the test takes when the rule reaches it:
 * `_record`, where the branch is the result record with the machine a function
 * of the case's own variables; `_cond`, where the field read has already taken
 * the record apart and the test is the completion variable alone; and
 * `_abrupt`, where the branch is `yul_abrupt`.  `_lit` is `_record` with the
 * machine the branch's own, and is not listed: `_record` matches that shape
 * too, through the higher-order match below. *)
val prune_lemmas = [yul_expr_result_CASE_invoke_abrupt_record,
                    yul_expr_result_CASE_invoke_abrupt_cond,
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
  (* Every lemma above is stated on a case whose scrutinee is the call itself,
   * and none matches anything else, so the shape is checked here rather than
   * left to the rewrite match: the prune is run at every node below, and
   * almost every node of a form is not a case at all. *)
  if not (is_yul_case tm) then raise Conv.UNCHANGED
  else
    let val args = snd (strip_comb tm) in
      if List.length args <> 3 orelse not (is_invoke (head_const (hd args)))
      then raise Conv.UNCHANGED
      else
        let
          fun try_ho lem = Conv.HO_REWR_CONV lem tm handle HOL_ERR _ => raise Conv.UNCHANGED
          fun first [] = raise Conv.UNCHANGED
            | first (lem :: rest) =
                (Conv.REWR_CONV lem tm handle HOL_ERR _ => try_ho lem)
                handle Conv.UNCHANGED => first rest
        in
          first prune_lemmas
        end
    end

(* The prune at every node, not only at the top.  A call's case is surfaced by
 * the taking apart into a branch or a test as often as to the top, and the same
 * pass reads fields (`reduce_field`), which rewrites the conditional
 * `_record`/`_lit` are stated on -- the test `(<|completion := c; …|>).completion
 * = YulNormal` becomes `c = YulNormal` -- into the one `_cond` is stated on.
 * `prune_lemmas` carries a lemma per shape the test can be in, so a case is
 * dropped wherever the taking apart has left it; the pass below is what reaches
 * it there, and this one, between the push and the taking apart, is what drops
 * it before the taking apart has carried the branch it sits in any further. *)
local
  val frame_ref : (term -> thm) ref = ref (fn _ => raise Conv.UNCHANGED)
in
  (* The frame rule below settles a folded call's values branch -- the values it
   * answered with, and the machine it came back on -- and it needs the table
   * reader to know what the callee declared, which is defined further down.  The
   * passes that run it reach it through this reference. *)
  fun frame_conv tm = !frame_ref tm
  fun set_frame_conv f = frame_ref := f
end

(* A call's case with its values branch settled if the frame rule takes it, and
 * otherwise the prune.  One or the other: both rewrite the same case, and the
 * frame rule's own guard is what stops it firing on the term it produced. *)
fun call_case_conv tm =
  frame_conv tm handle Conv.UNCHANGED => prune_call_conv tm

fun prune_deep_conv tm = Conv.QCONV (Conv.DEPTH_CONV call_case_conv) tm

fun prune_all_conv tm =
  let
    fun go acc 0 = acc
      | go acc k =
          case Lib.total prune_call_conv (rhs (concl acc)) of
            NONE => acc
          | SOME th => go (Thm.TRANS acc th) (k - 1)
  in
    go (prune_deep_conv tm) 4
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
  val fallback_ref : compset option ref = ref NONE
in
  fun cs () =
    case !cs_ref of
      SOME c => c
    | NONE => raise ERR "yulConvLib" "the compute set is not set yet"

  (* The same set with the clause constants' own clauses in place of the
   * conversion, for a term the conversion's clause does not match (see
   * `eval_conv_raw`): the set it runs on would hand such a term back to it. *)
  fun fallback_cs () =
    case !fallback_ref of
      SOME c => c
    | NONE => raise ERR "yulConvLib" "the compute set is not set yet"

  fun set_block_compset c fb =
    (cs_ref := SOME c; fallback_ref := SOME fb;
     blocks := Termtab.empty; clear_answers ())
end
(* A field, read off a record: `sel v` for a term whose selector is one of the
 * datatype's fields.  Anything else is left alone, which is what keeps this
 * out of the way of the rest of `step_conv`'s work. *)
fun reduce_field tm =
  case Lib.total dest_comb tm of
    SOME (acc, _) =>
      if not (is_result_field acc) then raise Conv.UNCHANGED
      else
        let
          val th = computeLib.CBV_CONV (cs ()) tm
        in
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
 * and they are what the `_invoke_abrupt` lemmas do for a call by hand. *)

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
val yul_expr_result_RAND = TypeBase.case_rand_of ``:yul_expr_result``
val option_RAND = TypeBase.case_rand_of ``:'a option``
val list_RAND = TypeBase.case_rand_of ``:'a list``

val distribute_lemmas = [boolTheory.COND_RAND,
                         yul_expr_result_RAND,
                         option_RAND,
                         list_RAND]

(* The first of a list of equations or lemmas that rewrites the term: the same
 * rule, offered each in turn, with `UNCHANGED` once the list runs out. *)
fun matching [] tm = raise Conv.UNCHANGED
  | matching (eq :: rest) tm =
      Conv.REWR_CONV eq tm handle HOL_ERR _ => matching rest tm

fun is_binding tm =
  is_comb tm andalso
  (is_abs (rator tm) orelse is_const_named "bool" "LET" (fst (strip_comb tm)))

fun distribute_conv tm =
  if not (is_binding tm) then raise Conv.UNCHANGED
  else
    matching distribute_lemmas tm

(* A `yul_pop_result` over a decision, pushed in: the pop goes inside the
 * decision's branches, so the block's continuation meets a branch that already
 * carries it rather than the whole pop term copied into every branch.  The
 * rules are the ones a binding's continuation is pushed with -- here
 * `yul_pop_result` is the function -- and only a `yul_pop_result` node is
 * offered them, since a push at every application would copy the function. *)
fun pop_result_conv tm = matching distribute_lemmas tm

(* A `yul_pop_result` whose argument is one of the decisions the push above
 * goes inside: what a clause's own evaluation can leave at the top of its
 * result, and what its caller routes on rather than taking apart. *)
val pop_result_c = prim_mk_const {Thy = "yulEvaluator", Name = "yul_pop_result"}

(* A term whose head is one of the decisions `distribute_lemmas` push a
 * function into. *)
fun is_decision tm =
  let val c = head_const tm in
    is_const_named "yulEvaluator" "yul_expr_result_CASE" c orelse
    is_const_named "option" "option_CASE" c orelse
    is_const_named "list" "list_CASE" c orelse
    is_const_named "bool" "COND" c
  end

fun pop_over_decision tm =
  let
    val (h, args) = strip_comb tm
  in
    same_const h pop_result_c andalso
    (case args of
       [a] => is_decision a
     | _ => false)
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
      then (after_binding (case_conv tm) handle Conv.UNCHANGED =>
              (after_binding (push_conv tm) handle Conv.UNCHANGED =>
                 call_case_conv tm))
      else if is_beta orelse is_const_named "bool" "LET" c
      then binding_step_conv tm
      else if is_const_named "bool" "COND" c
      then (after_binding (decide_conv tm) handle Conv.UNCHANGED =>
              after_binding (Conv.REWR_CONV yul_expr_result_CASE_cond tm
                               handle HOL_ERR _ => raise Conv.UNCHANGED))
      else if is_const_named "yulEvaluator" "yul_pop_result" c
      then pop_result_conv tm
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
            (* The prune sits between the push and the taking apart: the push
             * is what surfaces a call's case into a branch or a test, and it is
             * dropped there, before the taking apart reads the fields around it
             * (`reduce_field`) and carries the branch it sits in any further.
             * The shapes are all in `prune_lemmas`, so a case the field read
             * rewrites is still reached by the pass after this one. *)
            val pruned = prune_deep_conv (rhs (concl pushed))
            val red = expose_conv (rhs (concl pruned))
            val next =
              Thm.TRANS acc (Thm.TRANS pushed (Thm.TRANS pruned red))
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
 * has just become reducible behind it.
 *
 * Pruning after the taking apart would reach every call case the push surfaced
 * as well -- `_cond` is the lemma for the shape the taking apart's field read
 * leaves -- but it would do so having carried the branch the case sits in
 * through that taking apart first, so `expose_all_conv` prunes between its push
 * and its own pass.
 *
 * The prune is not run before the taking apart here.  It was, while the only
 * lemmas that dropped a call's dead branch were stated on the branch written as
 * the record, which the taking apart's own field read rewrites; `_cond` is
 * stated on the completion variable that read leaves, so the shape is reachable
 * after it as well, and the earlier prune was measured to make no difference.
 * That measurement is the acceptance suite's own line at the head it was taken
 * on (`0f8e1cb`): the same count and the same largest form `fun_shifts` at
 * 176 309 nodes with the prune and without it.  The line reports a count, the
 * slowest form and the largest, so it would not show a change confined to one
 * covered form; what backs the deletion is that the prune rewrites nothing the
 * expose below does not, since the expose runs `step_conv` at every node and
 * that rule drops a call's dead branch like this one. *)
fun settle_conv tm =
  let
    fun go acc 0 = acc
      | go acc k =
          let
            val exposed = expose_all_conv (rhs (concl acc))
            val pruned = prune_all_conv (rhs (concl exposed))
            val next =
              Thm.TRANS acc (Thm.TRANS exposed pruned)
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
 * clause wrote, and the field extraction below replaces its test with the
 * variable it is on -- the shape `_cond` is stated on, which the prune after
 * this pass reaches, but only once the bindings around it have been pushed. *)
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
  (if is_decision v then raise Conv.UNCHANGED else result_conv v redex)
  handle Conv.UNCHANGED =>
    (let
       val pushed = distribute_conv redex
       val recd = Conv.QCONV (Conv.DEPTH_CONV binding_step_conv)
                    (rhs (concl pushed))
       val out = settle_conv (rhs (concl recd))
     in
       Thm.TRANS pushed (Thm.TRANS recd out)
     end
     handle Conv.UNCHANGED =>
       Conv.QCONV (Conv.DEPTH_CONV beta_conv) redex)
  | HOL_ERR _ =>
      Conv.QCONV (Conv.DEPTH_CONV beta_conv) redex

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

(* A clause of the evaluator, evaluated the way the block is: the sub-result the
 * clause tests is evaluated first and taken apart, so the clause's own function
 * meets the values and the machine a leaf holds rather than the case's bound
 * variables.
 *
 * Reducing the whole clause with the compute set instead leaves every step
 * inside it that reads those variables undecided -- the arity guard
 * `LENGTH names <> LENGTH vs`, the scope update behind it, the builtin's own
 * argument scan -- and the block's split then hands the rest of the body to
 * each branch of that undecided test, which is a copy per branch per step.  The
 * recursion is what keeps that from happening one level down as well: the
 * scrutinee is evaluated by this same rule rather than by the compute set, so
 * the argument list and the call inside it are taken apart the same way. *)
(* Whether a clause is one of the four the rule below takes: a statement's, an
 * expression's, an argument list's, or a switch's cases.  These are also the
 * constants the compute set runs this same rule for (see `eval_compset`), so a
 * clause nested inside another -- the tail of an argument list, a call among a
 * call's arguments -- is taken here rather than handed to the set whole. *)
fun is_eval_clause th =
  let val c = head_const_of th in
    is_const_named "yulEvaluator" "eval_yul_stmt" c orelse
    is_const_named "yulEvaluator" "eval_yul_expr" c orelse
    is_const_named "yulEvaluator" "eval_yul_args" c orelse
    is_const_named "yulEvaluator" "eval_yul_cases" c
  end

val eval_clauses = List.filter is_eval_clause clauses

(* The set `eval_conv_raw` falls back to: the one it is running on, with the
 * four constants' own clauses back in place of the conversion registered for
 * them.  The entry is deleted rather than added beside, so a term the clauses
 * do not match is left standing there rather than reaching the conversion
 * again, and the clauses are compiled the way they were before the
 * registration took them out.  A value, not a copy of the set: only these four
 * entries are touched, and the rest of the set is shared with the caller. *)
fun clause_set cs =
  let
    (* Every entry goes before any clause is put back: the entry carries all of
     * a constant's clauses, so a scrub after one of them is in takes that one
     * out again and leaves the constant with the last of them alone. *)
    val scrubbed =
      List.foldl (fn (th, cs) => computeLib.scrub_const cs (head_const_of th))
        cs eval_clauses
  in
    computeLib.add_thms eval_clauses scrubbed
  end

(* The scrutinee of the case a clause builds: the case constant's first
 * argument.  A clause that builds no case -- a literal's value, an empty
 * argument list -- is left to the compute set. *)
fun scrutinee_conv c tm =
  if is_yul_case tm orelse
     is_const_named "option" "option_CASE" (head_const tm)
  then Conv.RATOR_CONV (Conv.RATOR_CONV (Conv.RAND_CONV c)) tm
  else raise Conv.UNCHANGED

fun eval_conv_raw tm =
  let
    val clause = matching eval_clauses tm
    val body = rhs (concl clause)
    (* Repeated, since a clause can build a case on a case -- a `let` whose
     * value is an option the clause itself tests, and the expression behind it
     * -- and the second scrutinee is only at the top once the first is taken
     * apart. *)
    fun go acc 0 = acc
      | go acc k =
          let
            val cur = rhs (concl acc)
            val ev = scrutinee_conv eval_conv_raw cur
                       handle Conv.UNCHANGED => Thm.REFL cur
            val settled = settle_conv (rhs (concl ev))
            val next = Thm.TRANS acc (Thm.TRANS ev settled)
          in
            if aconv (rhs (concl next)) cur then next else go next (k - 1)
          end
    val settled = go (Thm.REFL body) 4
    val red = computeLib.CBV_CONV (cs ()) (rhs (concl settled))
    (* What the set unfolded above can leave something the settling never
     * saw: a case it surfaced in an argument list -- the second call of
     * `slt(cleanup(x), convert(y))`, still a case on a case inside the first
     * call's values branch.  Left there, the bindings and the builtin behind
     * it unfold on the case's bound variables, and every later read of the
     * scope they wrote is stuck.  So one more round whenever the set changed
     * the term.  A call the first round already framed is not framed again:
     * `frame_pending` recognises its settled branch. *)
    val out =
      if not (aconv (rhs (concl red)) (rhs (concl settled)))
      then let
             val settled2 = settle_conv (rhs (concl red))
             val red2 = computeLib.CBV_CONV (cs ()) (rhs (concl settled2))
           in
             (* What the outer composition wants here is the piece from the
              * set's own result on: `red` is already in it, and a theorem that
              * starts from the term before `red` does not join with the
              * `Thm.TRANS red …` around it. *)
             Thm.TRANS settled2 red2
           end
      else Thm.REFL (rhs (concl red))
  in
    Thm.TRANS clause (Thm.TRANS settled (Thm.TRANS red out))
  end
  (* A term whose clause does not match is reduced by the clauses in the set
   * (`clause_set` puts them back for these four constants).  It cannot be the
   * set the rule itself runs on: that one has this conversion registered for
   * them, and matching raises `UNCHANGED` exactly when the argument is not a
   * constructor application -- a body the caller's table writes over a
   * variable -- so the term would come back here without end. *)
  handle Conv.UNCHANGED => computeLib.CBV_CONV (fallback_cs ()) tm
       | HOL_ERR _ => computeLib.CBV_CONV (fallback_cs ()) tm

(* The statement rule, run as a compute rule (`add_conv` below): the clause is
 * instantiated, the statement is evaluated by `eval_conv_raw`, what is left of
 * it is reduced with the compute set, and what that reduced to is taken apart
 * as `split_conv` or `value_conv` says. *)
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
        if not (null ss) andalso contains_loop (List.nth (tms, 3))
        then raise Conv.UNCHANGED else
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
                val ev = eval_conv_raw stmt
                val ev_form = rhs (concl ev)
                val taken = Thm.TRANS clause
                              (Conv.RAND_CONV (fn _ => ev) redex)
                val redex' = rhs (concl taken)
              in
                (* A case at the top is the split; anything else is the
                 * statement's own result, and the binding is taken with
                 * whatever the result is (see `value_conv` above). *)
                if is_yul_case ev_form
                then Thm.TRANS taken (split_conv redex')
                else Thm.TRANS taken (value_conv ev_form redex')
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

(* A division by a divisor that is not a literal stays the value it is,
 * `with_zero word_div a b`.  Unfolded, its zero test is a decision on a value
 * rather than a guard the body branches on, and nothing takes it apart: every
 * step after it is evaluated over a result the conversion cannot read, once
 * per branch of everything that follows.  A literal divisor decides the test,
 * so that one is unfolded. *)
val with_zero_c = prim_mk_const {Thy = "vfmExecution", Name = "with_zero"}

fun with_zero_conv tm =
  if wordsSyntax.is_word_literal (rand tm)
  then Conv.REWR_CONV vfmExecutionTheory.with_zero_def tm
  else raise Conv.UNCHANGED

(* `yul_pop_result D`, as a compute rule in place of its definition.  Over a
 * decision the pop goes into the branches (`pop_result_conv`), and is only
 * unfolded on what reaches a branch.  Unfolded over the decision itself, the
 * definition -- `D with machine := yul_pop_scope D.machine` -- puts `D` at
 * three places, and the result's head is a record update rather than the
 * decision, so the block's split no longer sees the decision to hand the rest
 * of the body to.  Off a decision it is the guarded unfold it always was. *)
fun pop_conv eqs tm =
  if pop_over_decision tm then pop_result_conv tm else guarded_unfold eqs tm

(* A statement's result, the type the clauses' `let`s over a block bind. *)
val yul_result_ty =
  type_of (rand (lhs (concl (SPEC_ALL yul_pop_result_def))))

(* A result written out as a record: a field update, or the constructor.  The
 * fields are what a binding's body reads, and reading them off a record is a
 * reduction, so a record is bound by substitution whatever it holds. *)
fun is_result_record tm =
  let val c = head_const tm in
    is_const c andalso
    (String.isSuffix "_fupd" (fst (dest_const c)) orelse
     is_const_named "yulState" "yul_result" c)
  end

(* `LET f v`, as a compute rule in place of `LET`'s definition.  The set
 * reduces `v` first and leaves `f` -- an abstraction -- as it is, so this sees
 * the bound result before anything has been substituted.  A result that is a
 * decision has the binding pushed into its branches (`distribute_lemmas`), and
 * the set then meets the binding again at each branch, down to the records at
 * the leaves.  Substituting the decision instead copies all of it into each
 * use of the name -- seven in a call's clause, six of a loop iteration's body
 * result -- and every copy is then read and updated on its own.
 *
 * A result that is neither a decision nor a record, holds a folded call and is
 * used twice or more stays bound, for the reason `beta_conv` declines the same
 * redex.  Every other `let` is the substitution `LET`'s definition makes. *)
fun let_yul_conv tm =
  let val v = rand tm in
    if type_of v = yul_result_ty andalso is_decision v then
      matching distribute_lemmas tm
    else
      let
        val unlet = Conv.REWR_CONV boolTheory.LET_THM tm
        val f = rator (rhs (concl unlet))
      in
        if type_of v = yul_result_ty andalso not (is_result_record v) andalso
           is_abs f andalso contains_invoke v andalso
           occurrences (fst (dest_abs f)) (snd (dest_abs f)) >= 2
        then raise Conv.UNCHANGED
        else unlet
      end
  end
  handle HOL_ERR _ => raise Conv.UNCHANGED

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
 * what every later `EVAL` in the process reduces.
 *
 * The guarded operations' rules go in *before* the evaluator's clauses are
 * compiled into the set.  A rule compiled into the set reaches the constants of
 * its right-hand side through the entries that were there when it was compiled,
 * so replacing a definition's clauses takes the replacement going in first:
 * the evaluator's clauses name the frame and memory operations, and a guard
 * that is not in place when they are compiled is one those occurrences do not
 * see. *)
val eval_compset =
  let
    val base =
      let
        val cs0 =
          computeLib.scrub_const
            (computeLib.scrub_const
               (computeLib.copy (computeLib.the_compset ()))
               eval_yul_block_c)
            invoke_c
        val cs1 = computeLib.scrub_const
                    (computeLib.scrub_const cs0 eval_yul_builtin_c)
                    eval_yul_loop_c
        val cs2 = wordsLib.add_words_compset true cs1
        val cs3 =
          computeLib.scrub_const
            (computeLib.scrub_const cs2 word_exp_c)
            word_exp_tailrec_c
        val cs4 = computeLib.add_conv (word_exp_c, 2, word_exp_conv) cs3
        val cs4 = computeLib.add_conv (with_zero_c, 3, with_zero_conv)
                    (computeLib.scrub_const cs4 with_zero_c)
        (* A fuel written as a successor, which is how a caller states a run at
         * a fuel it does not know but knows is not zero: a call's test `n = 0`
         * and its decrement `n - 1` reduce on it, so the call is the folded
         * `invoke_yul` the rules that settle a call are stated on. *)
        val cs4 = computeLib.add_thms
                    [arithmeticTheory.SUC_SUB1, numTheory.NOT_SUC] cs4
        (* `let` as the rule above, before any clause is compiled: the
         * clauses' own bindings are what it is for. *)
        val cs4 = computeLib.add_conv (boolSyntax.let_tm, 2, let_yul_conv)
                    (computeLib.scrub_const cs4 boolSyntax.let_tm)
      in
        computeLib.add_conv (flookup_tm, 2, flookup_conv) cs4
      end
    (* A guarded operation has no equation in the set at all -- the set's own
     * clause would run before any conversion and take the copy -- so its
     * clauses go on as this one rule, which declines on a term holding a call. *)
    fun guard ((c, nhyp, eqs), cs) =
      computeLib.add_conv
        (c, nhyp,
         if same_const c pop_result_c then pop_conv eqs else guarded_unfold eqs)
        (computeLib.scrub_const cs c)
    (* The four constants the conversion itself is written for: their clauses
     * are not compiled into the set, and the conversion goes in their place.
     * A clause nested inside another -- the tail of an argument list, a call
     * among a call's arguments -- is then taken the way the block's own
     * statements are, instead of being handed to the set whole, which is the
     * treatment this rule exists to remove.  The arity comes off the clause:
     * `eval_yul_stmt n fns s m` and its three siblings take four arguments,
     * `eval_yul_cases n fns v cases default m` takes six. *)
    fun register (th, cs) =
      let val (c, args) = strip_comb (lhs (concl (SPEC_ALL th)))
      in
        computeLib.add_conv (c, List.length args, eval_conv_raw)
          (computeLib.scrub_const cs c)
      end
    (* These go on before the clauses below, as the guards do above and for the
     * same reason: a rule reaches the constants of its right-hand side through
     * the entries that were there when it was compiled, and the clauses that
     * reach `eval_yul_args` or `eval_yul_expr` are exactly the ones these
     * entries are for. *)
    val body_clauses =
      List.filter (fn th => not (is_eval_clause th)) evaluator_clauses
    val with_guards = List.foldl guard base guarded_helpers
    val with_convs = List.foldl register with_guards eval_clauses
  in
    computeLib.add_conv (eval_yul_block_c, 4, block_conv)
      (computeLib.add_thms
         (eval_yul_builtin_def :: body_clauses @ helper_defs @ shape_defs)
         with_convs)
  end

(* The rule above reduces a statement with this compute set; it has to be the
 * one it is part of, or a block nested in a statement would be taken the old
 * way.  With it goes the set the rule falls back to, which has to be made from
 * the same set: the same rules, with the clause constants' own clauses in place
 * of the conversion. *)
val () = set_block_compset eval_compset (clause_set eval_compset)

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
   * point of the memo is that the fold happens once.
   *
   * Keyed by the definitions as well as by the term, and by what those
   * definitions say rather than by which constants they are about: a fold is
   * only as complete as the equations it was given, and `CBV_CONV` leaves what
   * it cannot reach standing rather than failing, so a chain folded without
   * them is a partial fold, and a later call that gives them -- or gives a
   * fuller equation for the same constant -- would take that chain from here
   * and never fold the rest. *)
  val chains : (term list * term * thm) list ref = ref []
  fun chain_key defs = List.map (fn th => concl th) defs
in
  fun table_chain defs fns =
    let val key = chain_key defs in
      case List.find
             (fn (k, t, _) =>
                List.length k = List.length key andalso
                ListPair.all (fn (x, y) => aconv x y) (k, key) andalso
                aconv t fns)
             (!chains) of
        SOME (_, _, th) => th
      | NONE =>
          let val th = computeLib.CBV_CONV (table_compset defs) fns in
            chains := (key, fns, th) :: !chains; th
          end
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
   Settling a folded call's frame.

   A statement whose expression is a call is a case on `invoke_yul`, whose
   values branch is the rest of the body.  The call is folded, so the body's
   first use of its answer -- `yul_bind names vals m'`, `yul_assign`, a test on
   `m'` -- reads two things the conversion cannot resolve: the length of `vals`
   (against the names it is bound to) and the scope stack of `m'`.  Both are
   decided by the call itself, and neither needs the callee's body:

     - `vals` is as long as the callee declares results, so the spine the
       callee's own result names give is the spine `vals` has, and `ZIP` and
       `list_CASE` -- which match on `::` and `[]`, not on a length -- fire on
       it;
     - `m'` has the caller's own scope stack, because the frame is the callee's
       alone and `invoke_yul` hands the caller its scopes back.

   `yulEvaluatorProps.yul_expr_result_CASE_invoke_frame` states both on the
   case, so a single rewrite settles the branch; what is left in it is the
   caller's own machinery, which the conversion then resolves as it would for
   any other statement.  The callee's declaration comes from the table, read
   the way the entry call's is (`binding_thm`), and the arity the clause itself
   tests is decided on the term.

   Without this, every statement after a call carries a decision per read of
   the call's answer, so a body of k call statements comes out at about 2^k
   times the size -- which is where the corpus's remaining forms are.
 ---------------------------------------------------------------------------*)

(* The definitions the table is read from, for the callee lookup below: set by
 * the conversion that is running, like the compute set itself. *)
local
  val defs_ref : thm list ref = ref []
  (* The callee's declaration, one per name: a body's calls name the same
   * callees over and over -- the same statement is taken apart by every pass
   * over it -- and reading it off the table is a walk of the folded table
   * (138 entries for the corpus object) each time.  Cleared with the set of
   * definitions it is read from, which is what a conversion installs. *)
  val bindings : (term * thm) list ref = ref []
in
  fun set_frame_defs ds = (defs_ref := ds; bindings := [])
  fun frame_defs () = !defs_ref
  fun binding_memo defs fns name =
    case List.find (fn (n, _) => aconv n name) (!bindings) of
      SOME (_, th) => th
    | NONE =>
        let val th = binding_thm defs fns name in
          bindings := (name, th) :: !bindings; th
        end
end

(* The rule's own antecedent, decided on the term.  Its arity half is about the
 * table's declaration and the argument list, both literals by the time a case
 * is on the call, so the test set either answers it or the rule declines -- a
 * call the table's arity contradicts is one the clause itself answers abruptly,
 * and there is nothing to settle in its values branch. *)
fun arity_thm tm =
  let val th = eval_test tm in
    if aconv (rhs (concl th)) boolSyntax.T then EQT_ELIM th
    else raise Conv.UNCHANGED
  end

fun frame_conv_raw tm =
  if not (frame_pending tm) then raise Conv.UNCHANGED else
  let
    val cargs = snd (strip_comb tm)
    val inv = List.nth (cargs, 0)
    val b1 = List.nth (cargs, 1)
    val b2 = List.nth (cargs, 2)
    val itms = snd (strip_comb inv)
    val _ = if List.length itms = 5 then () else raise Conv.UNCHANGED
    val n_tm = List.nth (itms, 0)
    val fns_tm = List.nth (itms, 1)
    val name_tm = List.nth (itms, 2)
    val args_tm = List.nth (itms, 3)
    val mach_tm = List.nth (itms, 4)
    val bind = binding_memo (frame_defs ()) fns_tm name_tm
    val fd = rand (rhs (concl bind))
    val inst = ISPECL
      [n_tm, fns_tm, name_tm, args_tm, mach_tm, b1, b2, fd]
      yul_expr_result_CASE_invoke_frame
    val (ant, _) = dest_imp (concl inst)
    val (_, arity) = dest_conj ant
  in
    Thm.MP inst (Thm.CONJ bind (arity_thm arity))
  end

val () =
  set_frame_conv
    (fn tm => frame_conv_raw tm handle HOL_ERR _ => raise Conv.UNCHANGED)

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

(* By the clauses' own heads, not by the definition's: `Definition` gives a
 * function with a base case beside a recursive one as a conjunction, and
 * `head_const_of` reads a single equation's left-hand side.  Every clause of a
 * definition is about the same constant, so this is the same set of constants
 * as before for the single-equation definitions a caller usually passes. *)
fun scrub_defs cs defs =
  List.foldl (fn (c, cs) => scrub_const cs c) cs (clause_heads defs)

(* The table a caller gave, out of the set: the name itself for a table given
 * as a constant, and `yul_env` for one given as a term -- wherever it occurs
 * there, not only at the term's head, because `yul_env` is the identity on the
 * object it wraps and so is what exposes a literal object, whether the term is
 * that application itself or the caller's own record built around one
 * (`K (yul_env t) T`).  That one rule is what keeps the table opaque, which is
 * all this wants -- every constant *inside* a literal table ("K" and the
 * updates of the record it is built with) is what the evaluator's own clauses
 * build their machines out of, and scrubbing those takes the record operations
 * out from under the body's evaluation, leaving a form with the block still
 * standing in it.
 *
 * Only the table goes, and nothing else around it: a constant *around* the
 * table is the caller's own term with the table in it (`K table T`, a
 * conditional table), and taking that constant out of the set stops the body's
 * own evaluation reducing -- the same stranding, from a term the conversion was
 * not asked about.  A term that holds no `yul_env` and is not itself a constant
 * has nothing to scrub: nothing in it can unfold the table. *)
val yul_env_c = prim_mk_const {Thy = "yulAST", Name = "yul_env"}

fun opaque_table cs tm =
  if is_const tm then scrub_const cs tm
  else if Lib.mem (const_key (dest_thy_const yul_env_c)) (consts_in tm) then
    scrub_const cs yul_env_c
  else cs

(* The definitions the table needs *are* folded, deliberately, in
 * `table_compset`; this is the set the body's evaluation runs on. *)
fun body_set base defs table =
  opaque_table (scrub_defs base defs) table

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
     * client's table scrubbed out of it.  Its fallback set is made from that
     * one, for the same reason. *)
    val () = set_block_compset cs (clause_set cs)
    val () = set_frame_defs defs
    val res = computeLib.CBV_CONV cs (rhs (concl step))
  in
    Thm.TRANS step res
  end

(* The same evaluation on any term over a table: one iteration of a loop after
 * the loop's clause, or the rest of a body a loop handed its machine to.  No
 * binding is added, since no call is unfolded here. *)
fun yul_eval_conv defs fns tm =
  let
    val cs = body_set (computeLib.copy eval_compset) defs fns
    val () = set_block_compset cs (clause_set cs)
    val () = set_frame_defs defs
  in
    computeLib.CBV_CONV cs tm
  end

(* One iteration of a loop: its clause, then the evaluation above on what the
 * clause gives, which stops again at the next iteration's loop. *)
fun yul_loop_conv defs tm =
  let
    val (f, tms) = strip_comb tm
    val fns =
      case tms of
        [_, fns, _, _, _, _] =>
          if same_const eval_yul_loop_c f then fns
          else raise ERR "yulConvLib.yul_loop_conv"
                         "expected an eval_yul_loop application"
      | _ => raise ERR "yulConvLib.yul_loop_conv"
                       "expected an eval_yul_loop application"
  in
    (Conv.REWR_CONV loop_clause THENC yul_eval_conv defs fns) tm
  end

(*---------------------------------------------------------------------------
   Is a form the conversion produced closed?
 ---------------------------------------------------------------------------*)

(* Everything the conversion's own rules reach: the block and its clauses, which
 * it splits on, the builtin dispatch, whose clauses are compiled into the set
 * with the others so an application of it left in a term is the same kind of
 * residue as a statement, the scope readers and the binding operations, which
 * it unfolds only while their input is a value it has, FLOOKUP itself, which is
 * the way a scope that did not come out is seen, the result and value helpers,
 * and the calls it leaves folded.  A name in this list that is still in a term
 * is a step the conversion either could not take or declined; `residues` is
 * what a caller reads to see which. *)
val conversion_consts =
  List.map (const_key o dest_thy_const)
    (flookup_tm :: invoke_c :: eval_yul_loop_c :: eval_yul_builtin_c ::
     yul_lookup_c ::
     yul_lookup_names_c ::
     (clause_heads (evaluator_clauses @ helper_defs @ block_def_clauses) @
      List.map (fn (c, _, _) => c) guarded_helpers))

fun residues tm =
  Lib.mk_set (List.filter (fn k => Lib.mem k conversion_consts) (consts_in tm))

(* What a form may still be standing on: the call and the loop it left folded,
 * and the operations whose input is a value nobody has -- the frame and memory
 * operations of `guarded_helper_defs` (a binding over a machine that holds a
 * call, an `FLOOKUP` of a scope that came out of the callee's frame), the scope
 * readers, which are unguarded and so always unfold, but whose read of a scope
 * a callee has not returned yet has nothing to unfold to, and the result
 * helpers, which build a record out of a completion that is not a literal.
 * None of those is a step the conversion could have taken.
 *
 * What is *not* in here is the evaluation itself: the block, the statements and
 * the expressions.  A form with one of those in it is one whose body evaluation
 * stopped early, which a test says by requiring every residue of a form to be
 * one of these. *)
val permitted_residues =
  ("yulEvaluator", "invoke_yul") :: ("yulEvaluator", "eval_yul_loop")
  :: List.map (const_key o dest_thy_const)
       (flookup_tm :: yul_lookup_c :: yul_lookup_names_c ::
        (clause_heads helper_defs @
         List.map (fn (c, _, _) => c) guarded_helpers))

(* A form is closed when nothing in it is standing that a form may not stand
 * on, which is the same question the test asks of every residue. *)
fun is_closed_form tm =
  List.all (fn k => Lib.mem k permitted_residues) (residues tm)

(* The other half of what "closed" means, and the stronger half: the
 * conversion's own rules make no progress on the form, so nothing in it is a
 * step the conversion could still have taken.  A name list can only say which
 * constants are gone; this says there is nothing left for them to do, and it
 * catches a residue whose map or argument the conversion did not reach as
 * well as one it did.  The table reader is not in the set, so the function a
 * form names is not read again here. *)
(* The table a form carries: the `fns` argument of a call or a loop it left
 * folded.  A form with neither in it names no table, and then there is nothing
 * in it that could unfold one. *)
fun table_in tm =
  case dest_term tm of
    Term.COMB _ =>
      let val (f, args) = strip_comb tm in
        if is_invoke f andalso List.length args = 5 orelse
           same_const eval_yul_loop_c f andalso List.length args = 6 then
          SOME (List.nth (args, 1))
        else
          let val (x, y) = dest_comb tm in
            case table_in x of
              SOME t => SOME t
            | NONE => table_in y
          end
      end
  | Term.LAMB (_, b) => table_in b
  | _ => NONE

fun is_fixed_point defs tm =
  let
    (* The same two things the body's own evaluation has taken out of its set:
     * the definitions the table is read from, and the head the table term is
     * written with.  Without the second, a form over a literal table has that
     * table folded beneath it here and a real form reads as not a fixed
     * point. *)
    val cs = scrub_defs eval_compset defs
    val cs = case table_in tm of
               SOME t => opaque_table cs t
             | NONE => cs
    (* The set the reduction runs on is installed, as `yul_invoke_conv` installs
     * its own: the conversion is registered in it for the four clause
     * constants, and the rule reduces a statement on the installed set.  Left
     * uninstalled, this set's four entries would run their clause on whatever
     * set the last conversion left behind -- with the client's definitions
     * folded back in, which is the other thing this set exists to keep out. *)
    val () = set_block_compset cs (clause_set cs)
    val () = set_frame_defs defs
  in
    aconv tm (rhs (concl (computeLib.CBV_CONV cs tm)))
  end

end
