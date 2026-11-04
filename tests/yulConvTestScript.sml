(* The Yul-side evaluation conversion, run over every function of the corpus's
 * scalars suite.
 *
 * The fixture is the pinned compiler's own Yul for testdata/differential/
 * scalars.sol, committed under testdata/yul/expected so that CI, which has no
 * compiler, can import it -- the arrangement yulImportTest and yulContractTest
 * use for their fixtures, one step further on: the conversion is not checked
 * on a hand-built tree but run over a whole real object.
 *
 * What is checked is that each function of the runtime object reaches a
 * closed form, and how long that takes.  All but one of the object's
 * functions are loop-free -- checked_exp_helper has a loop, and a loop is a
 * lemma about a loop head rather than a closed form -- and the build fails if
 * any of them does not close, or closes with the evaluator's own functions
 * still in it.  A form is a case tree over the body's guards and over the
 * calls it makes, so a function that calls nothing has nothing of its own
 * frame left -- only the memory read itself, whose own clauses want a length
 * that is a successor while the evaluator reads with a numeral, so it does not
 * reduce even where the machine is one the conversion has in hand (the note on
 * `memory_read_residue` below) -- and one that calls is left waiting on the
 * frame a callee returned and nothing else (see semantics/yulConvLib.sml).
 * The number the test asserts is the slowest of them, so that a conversion
 * that regressed to the simplifier's cost fails the build on the clock alone;
 * the total is printed to say what the suite costs, and every conversion runs
 * under a clock, so one that stops coming back fails the build instead of
 * leaving it at the heap cap.
 *
 * A few functions are not covered by that bound yet: each is named in
 * `excluded` below with the reason it is there, every name has to be a function
 * of the object, and the list empties as the conversion stops copying the rest
 * of a body into a branch of a decision (see the comment on the list).  A line
 * that says a function produces no form is converted under that clock too, and
 * fails the build as soon as it comes back; one line says it, and the clock is
 * what makes the claim honest rather than taken on trust.
 *)
Theory yulConvTest
Ancestors
  yulAST yulDialect yulState yulEvaluator yulEvaluatorProps cv_string_fmap
  vfmCompute
Libs
  wordsLib yulImportLib yulConvLib Timeout

(* Read by holbuild's dependency scanner, which stages the fixture. *)
fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps [
  "../testdata/yul/expected/scalars.json",
  "../testdata/differential/scalars.sol"
]

val fixture = "../testdata/yul/expected/scalars.json"
val source = "testdata/differential/scalars.sol"
val contract = "Scalars"

(* The runtime object, as the pinned compiler emitted it. *)
Definition scalars_object_def:
  scalars_object =
    ^(yulImportLib.import_runtime_artifact fixture source contract
        yulImportLib.IrOptimized)
End

(* The table the evaluator's own calls read, built as run_yul builds it. *)
Definition scalars_function_table_def:
  scalars_function_table = yul_env scalars_object
End

(* The frame the bodies run on: empty, and written into each call as a literal
 * rather than bound to a name, so that a body which does touch it -- the
 * memory of an mload, the calldata of a calldataload -- reads a field of a
 * record the evaluation can see through.  It is not a frame the suite really
 * runs on: a body that reads a variable an initializer would have bound, or a
 * word written to memory from one, comes out with those steps still in it,
 * which is the frame's doing and not the conversion's.  What the test says
 * about a form is about its shape, not about this frame being the one a run
 * has.
 *)
Definition yul_conv_tx_params_def:
  yul_conv_tx_params =
    <| origin := 0w; gasPrice := 0; baseFeePerGas := 0; baseFeePerBlobGas := 0;
       blockNumber := 0; blockTimeStamp := 0; blockCoinBase := 0w;
       blockGasLimit := 0; prevRandao := 0w; prevHashes := []; blobHashes := [];
       chainId := 0; authRefund := 0 |>
End

Definition yul_conv_machine_def:
  yul_conv_machine =
    <| accounts := empty_accounts; logs := []; self_address := 0w;
       caller_address := 0w; call_value := 0w; call_data := []; return_data := [];
       immutables := (FEMPTY : string |-> bytes32); memory := FEMPTY;
       memory_size := 0; gas_limit := 0; scopes := [];
       transaction_parameters := yul_conv_tx_params |>
End

val yul_conv_machine_term = rhs (concl yul_conv_machine_def)

(* The two definitions the conversion unfolds to read the table: the object
 * itself, and the name the table is bound to. *)
val table_defs = [scalars_function_table_def, scalars_object_def]

val bytes32_ty = wordsSyntax.mk_int_word_type 256
val yulfun_c = prim_mk_const {Thy = "yulAST", Name = "YulFunction"}
val invoke_c = prim_mk_const {Thy = "yulEvaluator", Name = "invoke_yul"}

fun const_key (r : {Name : string, Thy : string, Ty : 'a}) = (#Thy r, #Name r)

fun consts_in tm =
  case dest_term tm of
    Term.VAR _ => []
  | Term.CONST r => [const_key r]
  | Term.LAMB (_, b) => consts_in b
  | Term.COMB (a, b) => consts_in a @ consts_in b

val yulfor_key = ("yulAST", "YulFor")
val yulapply_key = ("yulAST", "YulApply")

fun has_loop body = List.exists (fn k => k = yulfor_key) (consts_in body)
fun has_call body = List.exists (fn k => k = yulapply_key) (consts_in body)

(* The runtime object's own functions, in the order the compiler emitted
 * them: name, arity, body. *)
fun object_functions () =
  let
    val (stmts, _) = listSyntax.dest_list (rhs (concl scalars_object_def))
    fun one s =
      let val (c, a) = strip_comb s in
        if same_const c yulfun_c then
          case a of
            [nm, params, _, body] =>
              SOME (stringSyntax.fromHOLstring nm,
                    List.length (fst (listSyntax.dest_list params)), body)
          | _ => NONE
        else NONE
      end
  in
    List.mapPartial one stmts
  end

(* The call the test makes for one function, on fresh argument variables. *)
val arg_names = List.tabulate (8, fn i => mk_var ("a" ^ Int.toString i, bytes32_ty))

fun call_term (nm, arity, _) =
  let
    val args = listSyntax.mk_list (List.take (arg_names, arity), bytes32_ty)
  in
    list_mk_comb (invoke_c,
      [``20n``, ``scalars_function_table``, stringSyntax.fromMLstring nm,
       args, yul_conv_machine_term])
  end

fun fail msg = raise Fail ("yulConvTest: " ^ msg)

val functions = object_functions ()
val loop_free = List.filter (fn (_, _, body) => not (has_loop body)) functions
val looping = List.filter (fn (_, _, body) => has_loop body) functions

(* The shape of the object this test is about: if the compiler's output
 * changed, the numbers below stop meaning what they say. *)
val () =
  if List.length functions = 138 andalso List.length loop_free = 137 andalso
     List.map (fn (nm, _, _) => nm) looping = ["checked_exp_helper"]
  then () else
    fail ("expected 137 loop-free functions and checked_exp_helper, got "
          ^ Int.toString (List.length functions) ^ " functions, "
          ^ Int.toString (List.length loop_free) ^ " loop-free, looping: "
          ^ String.concatWith ", " (List.map (fn (nm, _, _) => nm) looping))

(* The functions the bound below is not asked of yet: those whose form comes out
 * at two hundred thousand nodes or more.  The number in each line is that
 * function's form as this suite measures it -- every node of the term, which is
 * the `size` this test prints below -- and every line here names a body that
 * calls: the external wrappers above all, and the four forms in the millions
 * at the top of the list.
 *
 * A call's answer is what leaves a decision standing -- the arity the callee
 * answered with, and the frame it came back on -- and a decision the conversion
 * has not settled takes a copy of the rest of the body per branch, so the
 * copies multiply and a body's form is linear in its statements only while
 * nothing reads what a call answered.  The conversion settles a clause's own
 * sub-result before the clause's function is reduced, and it runs for the
 * clause constants themselves rather than only at the top of a statement, so a
 * clause nested inside another -- an argument list's own tail, a call among a
 * call's arguments -- is taken the same way instead of being handed to the
 * compute set whole.  That is what took the largest form here down by an order
 * of magnitude, and it is what brought the `abi_decode_*` group under the line;
 * what is left is the same shape one level further in, in the steps that still
 * go to the compute set -- the builtin dispatch, the scope updates, the machine
 * a call answered.
 *
 * The line is drawn at a size rather than at a measured time because a time
 * moves with the machine the build runs on and a size does not.  The sizes on
 * these lines are a sweep's output over the list, not something the suite
 * checks -- they say how far over the line each one is, and they move when the
 * conversion does, so they are re-measured with the list rather than read as an
 * invariant.  The line is enforced from one side only: the suite fails if a
 * form it does cover reaches 200k nodes, so a covered function that grew past
 * the line cannot pass unnoticed, but nothing here converts the 25 named for
 * their size -- a name whose form has dropped under the line keeps its line
 * until the list is re-measured, which happens with each change to the
 * conversion.  Converting them here as well would put the large forms' cost --
 * seconds each, and tens of millions of nodes at the far end
 * (`checked_exp_signed`'s) -- on every run of this suite.  The gap is no longer
 * narrow: twenty-one of the twenty-five now come out under the line, between
 * 20 719 and 169 905 nodes, and are named for their time -- the four still over
 * it are `fun_signedLess` and `fun_boolLogic` at about a million nodes,
 * `checked_exp_unsigned` at 230 276, and `checked_exp_signed`, which does not
 * come back inside the sweep's clock.  What is left is 112 of the 137, whose
 * largest form is 79 639 nodes and whose slowest the check below bounds at five
 * seconds.
 *
 * One line says `no_form`: `checked_exp_signed` is the body a sweep of the
 * corpus did not see come back inside a clock of a minute, and it is the form
 * at the top of the list -- the one this suite had never seen.  A line that
 * claims no form is converted under a clock by the check below, so that the
 * claim is asked of the conversion rather than taken on trust: the run has to
 * abort, and one that comes back fails the check by name, with the size of its
 * form.  Without the clock a body that stopped coming back would sit at the
 * heap cap until the job's own limit rather than fail.
 *
 * So this list is the work list of the next piece, and it should empty: what the
 * suite is asked for is a conversion whose form is linear in the body, one leaf
 * per path rather than a copy of the continuation per branch.  A name that stops
 * needing its line is a line to delete; the test fails if a name is not a
 * function of the object, so a list left behind by a fixture change cannot pass
 * unnoticed.
 *)
val no_form = "no form within the clock"

(* The tag above is what the check on those lines matches, so it is one name
 * rather than a sentence written twice: the reason a line is on the list and
 * the check that asks the conversion for it have to say the same thing, and a
 * re-worded line that the check no longer recognises is a line whose claim
 * nobody asks about. *)
val excluded = [
  ("checked_exp_signed", no_form),
  ("fun_boolLogic", "form of 1008029 nodes"),
  ("checked_exp_unsigned", "form of 230276 nodes"),
  ("fun_signedLess", "form of 1083107 nodes"),
  ("fun_bitwise", "form of 169905 nodes"),
  ("checked_div_int8", "form of 129739 nodes"),
  ("external_fun_bitwise", "form of 29559 nodes"),
  ("fun_widen", "form of 146873 nodes"),
  ("external_fun_widen", "form of 26489 nodes"),
  ("external_fun_signedLess", "form of 26459 nodes"),
  ("external_fun_boolLogic", "form of 26379 nodes"),
  ("external_fun_truncate", "form of 24189 nodes"),
  ("external_fun_reinterpret", "form of 23949 nodes"),
  ("external_fun_shifts", "form of 23829 nodes"),
  ("external_fun_wrappingMultiply", "form of 22119 nodes"),
  ("external_fun_wrappingDivide", "form of 21919 nodes"),
  ("external_fun_signedShift", "form of 21899 nodes"),
  ("external_fun_signedPower", "form of 21719 nodes"),
  ("external_fun_remainder", "form of 21419 nodes"),
  ("external_fun_wrappingSubtract", "form of 21819 nodes"),
  ("external_fun_multiply", "form of 21319 nodes"),
  ("external_fun_divide", "form of 21119 nodes"),
  ("external_fun_wrappingPower", "form of 21519 nodes"),
  ("external_fun_subtract", "form of 21019 nodes"),
  ("external_fun_power", "form of 20719 nodes"),
]

val excluded_names = List.map #1 excluded

val () =
  List.app (fn nm =>
      if List.exists (fn (n, _, _) => n = nm) functions then () else
        fail ("the exclusion list names " ^ nm ^ ", which the object does not "
              ^ "define")) excluded_names

val measured = List.filter (fn (nm, _, _) => not (Lib.mem nm excluded_names))
                            loop_free

(* What a form may still be waiting on, and what it may not.  The conversion
 * takes the body's own evaluation -- the block, the statements, the
 * expressions -- so a form with one of those in it is one whose evaluation
 * stopped early, and every residue must be permitted.  Permitted are the call
 * a body left folded, the evaluator's own operations on a frame or on memory,
 * and its scope readers -- which wait on a value nobody has: a callee's frame
 * after a call, a word written to memory from a symbolic value, or a binding
 * read out of a scope a callee has not returned.  A body that calls nothing
 * may not be waiting on a call. *)
val call_residues = yulConvLib.permitted_residues

(* The one residue a body that calls nothing may have: a memory read, which the
 * guarded rule cannot take -- `yul_memory_read`'s clauses are `0` and `SUC k`,
 * and the length the evaluator reads with is a numeral (`yul_mload` reads 32),
 * so the read stands even where the machine is one the conversion has in hand.
 * `yulConvLib.permitted_residues` says the same. *)
val memory_read_residue = ("yulEvaluator", "yul_memory_read")

fun show_residues res =
  String.concatWith ", " (List.map (fn (t, n) => t ^ "." ^ n) res)

(* Every node of the form, not only its constants: the exception list above
 * quotes sizes in this metric, so the test's own `largest` has to be the same
 * number. *)
fun size_of tm =
  case dest_term tm of
    Term.VAR _ => 1
  | Term.CONST _ => 1
  | Term.LAMB (_, b) => 1 + size_of b
  | Term.COMB (x, y) => 1 + size_of x + size_of y

val started = Timer.startRealTimer ()

(* Every check a form has to pass, on one function's name, body and call term:
 * what the conversion is asked for is the body evaluated, so anything of the
 * body's own evaluation left in the form is a failure, and a form that is the
 * call it was given is a conversion that did nothing.  The two forms stated
 * further down are held to the same checks as these, so no form the test keeps
 * is one the suite never looked at. *)
fun checked_form (nm, body) t th =
  let
    val form = rhs (concl th)
    val res = yulConvLib.residues form
  in
    (* A theorem about some other term satisfies every check below, so the
     * equation is held to the call it was given first. *)
    if not (aconv (lhs (concl th)) t) then
      fail ("the form stated for " ^ nm ^ " is not about the call the "
            ^ "conversion was given")
    else if not (yulConvLib.is_fixed_point table_defs form) then
      fail ("the conversion left something to evaluate in " ^ nm)
    else if not (List.all (fn k => Lib.mem k call_residues) res) then
      fail ("the conversion left " ^ show_residues res ^ " in " ^ nm)
    (* A body that calls nothing reads its own frame, which the entry machine
     * gives concretely, so every scope and frame operation of the evaluator's
     * resolves: those are permitted residues only because a folded call leaves
     * the map symbolic, which is not a position a call-free body is in.  The
     * one residue left to it is a memory read, for the reason above. *)
    else if not (has_call body) andalso
            not (List.all (fn k => k = memory_read_residue) res) then
      fail ("the body of " ^ nm ^ " calls nothing, yet its form is left on "
            ^ show_residues res)
    (* A call the body makes is what the form carries in place of the callee's
     * body, so a form that names no call is one whose callees were unfolded
     * instead of left folded. *)
    else if has_call body andalso
            not (Lib.mem ("yulEvaluator", "invoke_yul") (consts_in form)) then
      fail ("the body of " ^ nm ^ " calls, but its form keeps no call")
    (* And the check that says the conversion did anything at all: the form has
     * to be a different term from the call it was given.  Every check above is
     * satisfied by a conversion that hands the call back -- the entry
     * application's own name is a permitted residue, and `invoke_yul`'s
     * equation is not in the fixed-point set, so the call is its own fixed
     * point.  For a body that calls nothing the check above catches that; this
     * is the one that catches it for a body that calls. *)
    else if aconv form t then
      fail ("the conversion returned " ^ nm ^ "'s call unchanged")
    else th
  end

(* A conversion that stopped coming back would sit at the heap cap until the
 * job's own limit, so the work a function costs is bounded here rather than
 * after the fact.  `Timeout.apply` runs the whole call under a clock of its
 * own: an expired one interrupts this thread, and an interrupt is not
 * something the reduction catches -- `No_match` is how a rule declines, and
 * anything else aborts the whole reduction -- so the call ends in the
 * `handle` below wherever in it the conversion was, the library's own passes
 * over the form between its rounds included.  That is what a hook consulted
 * only when the set tries an equation cannot reach.  The exception is one of
 * its own, not `Fail`, so a check that fails inside is not mistaken for a
 * timeout.
 *
 * The bound is generous: the slowest form this suite covers takes about a
 * second, and a loaded box moves that. *)
fun under_clock secs thunk =
  (SOME (Timeout.apply (Time.fromReal secs) thunk ())
     handle Timeout.TIMEOUT _ => NONE)

fun convert f =
  let val t = call_term f in
    case under_clock 60.0 (fn () => yulConvLib.yul_invoke_conv table_defs t) of
      NONE => fail (#1 f ^ " did not come back within 60s")
    | SOME th => (#1 f, checked_form (#1 f, #3 f) t th)
  end

fun stated_form nm =
  #2 (convert (valOf (List.find (fn (n, _, _) => n = nm) functions)))

(* Timed one at a time: what the conversion is asked for is seconds per
 * function, so the number the test bounds is the slowest of them, and the
 * total is printed to say what the suite costs.  The size of the largest form
 * is printed with them, since that is where a conversion that copies the rest
 * of a body once per statement instead of once per outcome shows up first.
 * Only the name, the time and the size are kept: holding all 137 forms holds
 * tens of gigabytes of heap, which is more than the per-process limit a build
 * runs a theory under.  The two forms stated below are converted again for
 * that, which costs a couple of seconds. *)
fun timed f =
  let
    val t0 = Timer.startRealTimer ()
    val (_, th) = convert f
    val t = Time.toReal (Timer.checkRealTimer t0)
  in
    (#1 f, t, size_of (rhs (concl th)))
  end

val timings = List.map timed measured

val elapsed = Time.toReal (Timer.checkRealTimer started)
val slowest =
  List.foldl (fn ((nm, t, _), best) => if t > #2 best then (nm, t) else best)
             ("", 0.0) timings
val largest =
  List.foldl (fn ((nm, _, n), best) => if n > #2 best then (nm, n) else best)
             ("", 0) timings
val calling = List.length (List.filter (fn (_, _, body) => has_call body)
                                       loop_free)

val () = print ("yulConvTest: " ^ Int.toString (List.length timings)
                ^ " of " ^ Int.toString (List.length loop_free)
                ^ " loop-free functions in " ^ Real.toString elapsed
                ^ "s, " ^ Int.toString (List.length excluded) ^ " excluded;"
                ^ " slowest " ^ #1 slowest ^ " at "
                ^ Real.toString (#2 slowest) ^ "s; largest " ^ #1 largest
                ^ " at " ^ Int.toString (#2 largest) ^ " nodes; "
                ^ Int.toString calling ^ " of the bodies call\n")

val () =
  if #2 slowest < 5.0 then ()
  else fail ("the slowest form took " ^ Real.toString (#2 slowest) ^ "s ("
             ^ #1 slowest ^ ")")

(* And the line the list above is drawn at, enforced from this side: a form this
 * suite does cover that has reached 200k nodes is one the list should have
 * named, so a conversion that stopped closing for a function (or a fixture
 * that changed under the list) fails here rather than passing quietly. *)
val () =
  if #2 largest < 200000 then ()
  else fail ("the largest covered form is " ^ Int.toString (#2 largest)
             ^ " nodes (" ^ #1 largest ^ "), at or over the line the "
             ^ "excluded list is drawn at")

(* Two of the forms, stated: one that calls nothing else, and one whose body
 * is calls and arithmetic.  These are the theorems a reader can look at, and
 * the terms the matching step of the translation-validation driver will be
 * given.  They are held to the checks above like every other conversion, and
 * both are among the forms this suite measures, so nothing here is converted a
 * second time for the checks' sake -- what these two add is a term a reader can
 * read and the driver's matching step can be handed. *)
val scalars_cleanup_uint8 = save_thm ("scalars_cleanup_uint8",
  stated_form "cleanup_uint8")

val scalars_checked_sub_uint8 = save_thm ("scalars_checked_sub_uint8",
  stated_form "checked_sub_uint8")

(* One function converted over the table *term* rather than over the constant it
 * is bound to.  A caller may give either, `defs` being what that term is folded
 * from; what keeps the table out of the body's own set has to hold for both.  A
 * literal table is a `yul_env` application, whose head is the one constant worth
 * taking out of the set -- everything *inside* it (the `K`s and updates of the
 * record the object is built with) is what the evaluator's own clauses build
 * their machines out of, and scrubbing those strands the body's evaluation.
 *)
val literal_table = rhs (concl scalars_function_table_def)

val scalars_cleanup_uint8_over_table_term =
  let
    val f = valOf (List.find (fn (nm, _, _) => nm = "cleanup_uint8") functions)
    val (nm, arity, _) = f
    val args = listSyntax.mk_list (List.take (arg_names, arity), bytes32_ty)
    val t = list_mk_comb
              (invoke_c,
               [``20n``, literal_table, stringSyntax.fromMLstring nm, args,
                yul_conv_machine_term])
    val th =
      case under_clock 60.0 (fn () => yulConvLib.yul_invoke_conv table_defs t) of
        NONE => fail "the table term's call did not come back within 60s"
      | SOME th => th
    val form = rhs (concl th)
  in
    if not (aconv (lhs (concl th)) t) then
      fail "the theorem about the table term's call is about some other call"
    else if not (yulConvLib.is_closed_form form) then
      fail ("the table term itself is left standing in a form: "
            ^ show_residues (yulConvLib.residues form))
    else if not (yulConvLib.is_fixed_point table_defs form) then
      fail "a form over the table term itself is not a fixed point"
    (* The same anti-degeneracy check the rest of the suite makes, and it matters
     * most here: this is the only call whose table is a term, and an unchanged
     * `invoke_yul` passes both checks above.  `cleanup_uint8`'s body calls
     * nothing, so a form that still holds a call is the call it was given. *)
    else if aconv form t then
      fail "the conversion returned the table term's call unchanged"
    else th
  end

(* The form is stated at a numeral fuel, and that costs nothing: fuel is only
 * ever tested for zero, so a run that completed at the numeral is the run at
 * every larger bound.  This is how the form reaches the shape the
 * per-function theorem's Yul side has, `invoke_yul n ... = r` at a
 * universally quantified fuel; the bound does not depend on the arguments or
 * the frame, so those stay the caller's.
 *)
Theorem scalars_checked_sub_uint8_fuel_stable:
  ∀m n a0 a1.
    20 ≤ n ∧
    yul_running (invoke_yul 20 scalars_function_table "checked_sub_uint8"
                   [a0; a1] m) ⇒
    invoke_yul n scalars_function_table "checked_sub_uint8" [a0; a1] m =
    invoke_yul 20 scalars_function_table "checked_sub_uint8" [a0; a1] m
Proof
  metis_tac [invoke_yul_fuel_stable]
QED



(* The claim on a "no form" line, asked of the conversion rather than taken on
 * trust.  A claim about a run that does not come back cannot be checked by
 * waiting for it: unclocked it would sit at the heap cap until the job's own
 * limit, which is the failure this bounds.  So each of those entries is
 * converted under the clock above and the run has to abort; one that comes
 * back is a line that has gone stale, and it fails here by name, with the size
 * of the form so the owner knows whether it belongs under the bound or on a
 * line of its own.
 *
 * The shapes that have left this class as the conversion has improved all nest
 * a call inside another call's arguments: `wrapping_exp_uint8_uint8` closes now
 * -- its `exp` call is reached through the builtin dispatch rather than left to
 * the word library -- `fun_bitwise` comes back inside this suite's own clock,
 * and the ones that carry a size above come back under a longer one; all of
 * them are measured with the rest.  The list is empty of them now, and the
 * check stays for the next body that stops coming back. *)
val () =
  List.app
    (fn (nm, why) =>
       if why <> no_form then () else
         let
           val f = valOf (List.find (fn (n, _, _) => n = nm) functions)
           val t = call_term f
         in
           case under_clock 20.0 (fn () => yulConvLib.yul_invoke_conv
                                            table_defs t) of
             NONE => ()
           | SOME th =>
               fail (nm ^ " now produces a form of "
                     ^ Int.toString (size_of (rhs (concl th))) ^ " nodes, so "
                     ^ "its line in the exclusion list is stale")
         end)
    excluded
