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
 *    `FLOOKUP_UPDATE` leaves is one `EVAL` answers.  Nothing else has to know
 *    the names are literals.
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

(*---------------------------------------------------------------------------
   One scope lookup.

   `FLOOKUP f k` where f is FEMPTY or an update of one: the evaluator's own
   equation, whose test k' = k a closed EVAL decides, then one update in when
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

fun flookup_conv tm =
  let val (f, _) = dest_flookup tm in
    if is_fempty f then
      Conv.REWR_CONV finite_mapTheory.FLOOKUP_EMPTY tm
    else if not (is_update f) then raise Conv.UNCHANGED
    else
      let
        val update = Conv.REWR_CONV finite_mapTheory.FLOOKUP_UPDATE tm
        val (test, _, _) = boolSyntax.dest_cond (rhs (concl update))
        val test_thm = EVAL test
        val truth = rhs (concl test_thm)
        val is_true = truth ~~ boolSyntax.T
        val is_false = truth ~~ boolSyntax.F
      in
        if not (is_true orelse is_false) then raise Conv.UNCHANGED
        else
          let
            val cond_thm = Rewrite.REWRITE_CONV [test_thm] (rhs (concl update))
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

(* What the equations reach on the way: the scope and binding operations, the
 * literal reader, memory, storage and the builtin dispatch. *)
val helper_defs = [
  yul_normal_def, yul_abrupt_def, yul_invalid_def,
  yul_pop_result_def, yul_pop_scope_def, yul_push_scope_def, yul_push_frame_def,
  yul_lookup_def, yul_lookup_names_def,
  yul_bind_def, yul_bind_scope_def, yul_assign_def, yul_assign_list_def,
  yul_update_def, yul_literal_value_def,
  yul_memory_byte_def, yul_memory_read_def, yul_memory_write_def,
  yul_memory_touch_def, yul_memory_region_def, yul_mload_def, yul_mstore_def,
  yul_sign_extend_def, yul_sload_def, yul_sstore_def, yul_call_def,
  yul_return_data_copy_def, yul_name_of_bytes_def,
  eval_yul_builtin_call_def
]

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
fun contains_invoke tm = Lib.mem ("yulEvaluator", "invoke_yul") (consts_in tm)

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
 * blowup this file exists to avoid.  A binding used once, or a binding whose
 * argument is a value, is a `let` of the evaluator's own and is reduced. *)
fun beta_conv tm =
  case dest_term tm of
    Term.COMB (rator, arg) =>
      if is_abs rator then
        let val (bv, body) = dest_abs rator in
          if occurrences bv body >= 2 andalso contains_invoke arg
          then raise Conv.UNCHANGED
          else Thm.BETA_CONV tm
        end
      else raise Conv.UNCHANGED
  | _ => raise Conv.UNCHANGED

(* `(λr. CONT r) (case stmt of ...)`: the continuation moves into the branches,
 * and the branches are reduced so it is not left as an application of a
 * lambda. *)
fun split_conv tm =
  let val split = Conv.REWR_CONV yul_expr_result_RAND tm
      val out = Conv.QCONV (Conv.DEPTH_CONV beta_conv) (rhs (concl split))
  in Thm.TRANS split out end

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

local
  (* The compute set, for reducing a statement on its own.  It has to be the one
   * with this rule in it, so that a block nested in the statement is taken the
   * same way; the reference closes that circle. *)
  val cs_ref : compset option ref = ref NONE
  fun cs () =
    case !cs_ref of
      SOME c => c
    | NONE => raise ERR "yulConvLib.block_conv" "the compute set is not set yet"
in
  fun set_block_compset c = cs_ref := SOME c

  fun block_conv tm =
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
                  (* A case at the top is the split; anything else the
                   * statement left is the let's own binding, and taking it
                   * is the beta reduction below.  Pushing cases out of the
                   * insides was measured too, and it is worse: a case
                   * inside a term is one copy of the surrounding work per
                   * branch, and the compute set's own descent does not pay
                   * that price. *)
                  if is_yul_case (rhs (concl ev)) then
                    Thm.TRANS taken (split_conv redex')
                  else
                    Thm.TRANS taken
                      (Conv.QCONV (Conv.DEPTH_CONV beta_conv) redex')
                end
            end
    end
end

(* The base is EVAL's own compute set rather than the boolean one: an
 * evaluator clause is full of `case` over the Yul datatypes, and a datatype's
 * case equations are put where its definition registered them, not into the
 * boolean set.  The word library's own rules go on top of it, because the
 * evaluator reaches its memory through `w2n` of an address and EVAL's set
 * alone leaves `w2n 0w` standing, which is enough to strand every memory
 * operation -- the byte it would read never becomes a list to recurse on.
 *)
val eval_compset =
  computeLib.add_conv (eval_yul_block_c, 4, block_conv)
    (computeLib.add_thms (evaluator_clauses @ helper_defs)
       (computeLib.add_conv (flookup_tm, 2, flookup_conv)
          (wordsLib.add_words_compset true
             (computeLib.scrub_const
                (computeLib.scrub_const
                   (computeLib.copy (computeLib.the_compset ()))
                   eval_yul_block_c)
                invoke_c))))

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

(* `|- FLOOKUP fns name = SOME fd`, off the folded chain. *)
fun binding_thm defs fns name =
  let
    val chain = table_chain defs fns
    val flk = mk_flookup (fns, name)
    val rw = if aconv (rhs (concl chain)) fns then Thm.REFL flk
             else Rewrite.REWRITE_CONV [chain] flk
    val lk = flookup_conv (rhs (concl rw))
    val th = Thm.TRANS rw lk
  in
    if is_some (rhs (concl th)) then th
    else raise ERR "yulConvLib.binding_thm"
                 ("the function table does not bind " ^ term_to_string name)
  end

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
    val cs = computeLib.add_thms [bind] (computeLib.copy eval_compset)
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
fun is_fixed_point tm =
  aconv tm (rhs (concl (computeLib.CBV_CONV eval_compset tm)))

end
