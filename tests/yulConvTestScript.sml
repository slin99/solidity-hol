(* The Yul-side evaluation conversion, run over every function of the corpus's
 * scalars suite.
 *
 * The fixture is the pinned compiler's own Yul for testdata/differential/
 * scalars.sol, committed under testdata/yul/expected so that CI, which has no
 * compiler, can import it -- the arrangement yulImportTest and yulContractTest
 * use for their fixtures, one step further on: the conversion is not checked
 * on a hand-built tree but run over a whole real object.
 *
 * What is checked is that each function of the runtime object reaches a closed
 * form within the size bound.  All but one of the object's functions are
 * loop-free -- checked_exp_helper has a loop, and a loop is a lemma about a
 * loop head rather than a closed form, so its form stops at the loop and one
 * iteration is converted on its own (at the end of this file) -- and the build
 * fails if any of them does not close, or closes with the evaluator's own
 * functions still in it.  A form is a case tree over the body's guards and over
 * the calls it makes, so a function that calls nothing has nothing of its own
 * frame left -- only the memory read itself, whose own clauses want a length
 * that is a successor while the evaluator reads with a numeral, so it does not
 * reduce even where the machine is one the conversion has in hand (the note on
 * `memory_read_residue` below) -- and one that calls is left waiting on the
 * frame a callee returned and nothing else (see semantics/yulConvLib.sml).  The
 * slowest conversion and the total time are printed to say what the suite
 * costs, and every conversion runs under a clock, so one that stops coming back
 * fails the build instead of leaving it at the heap cap.
 *
 * Every loop-free function is held to the size bound.  A function the bound
 * cannot be asked of goes in `excluded` below with the reason it is there, and
 * every name there has to be a function of the object (see the comment on the
 * list, which is empty now).  A line that says a function produces no form is
 * converted under that clock too, and fails the build as soon as it comes
 * back; the clock is what makes such a claim honest rather than taken on
 * trust.
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

(* The functions the size bound below is not asked of yet, each with why: the
 * form size this suite measures -- every node of the term, which is the `size`
 * this test prints below -- or a claim that no form comes back inside a clock.
 *
 * The list is empty.  It held the bodies whose forms the conversion copied a
 * decision into, two ways: a `let` over a statement's or a call's result that
 * was still a case, or a scope pop over one, substituted the case at every use
 * of the name, so the form grew by a factor per read; and a call among a
 * builtin's arguments (`slt(cleanup_int8(x), cleanup_int8(y))`) stayed a case
 * inside the other call's branch, where the binding behind it unfolded on the
 * branch's variables and left every later scope read stuck.  The conversion now
 * pushes a binding into a decision before anything is substituted, and settles
 * a clause again after the set's reduction (see semantics/yulConvLib.sml); the
 * three that were over the line -- `fun_signedLess` at 1 083 107 nodes,
 * `fun_boolLogic` at 1 008 029 and `checked_exp_signed` at 903 697 -- came
 * under it with both in.  Which of the two each one needed was not measured.
 *
 * The line is drawn at a size rather than a time because a time moves with the
 * machine the build runs on and a size does not.  A body that goes over it
 * again comes back here, with its measured size, until the conversion takes it.
 * A line that claims no form is converted under a clock below, so the claim is
 * asked of the conversion rather than taken on trust; without the clock a body
 * that stopped coming back would sit at the heap cap until the job's own limit
 * rather than fail. *)
val no_form = "no form within the clock"

(* The tag above is what the check on those lines matches, so it is one name
 * rather than a sentence written twice: the reason a line is on the list and
 * the check that asks the conversion for it have to say the same thing, and a
 * re-worded line that the check no longer recognises is a line whose claim
 * nobody asks about. *)
val excluded : (string * string) list = []

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
 * The bound is generous: the slowest form this suite covers takes about five
 * seconds, and a loaded machine moves that. *)
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

(* Timed one at a time: the slowest conversion and the total time are printed
 * to say what the suite costs.  The size of the largest form
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

(* A division by an argument stays the value it is: `wrapping_div_int8`'s
 * `sdiv(x, y)` comes out as `with_zero word_quot`, not as a test on `y` that
 * the rest of the body would be evaluated under.  A literal divisor, zero or
 * not, is still unfolded: no function here divides by one, so it is asked of
 * the set directly. *)
val with_zero_c = prim_mk_const {Thy = "vfmExecution", Name = "with_zero"}

val () =
  if can (find_term (same_const with_zero_c))
         (rhs (concl (stated_form "wrapping_div_int8")))
  then ()
  else fail "wrapping_div_int8's division did not stay folded"

val () =
  List.app (fn (t, folded) =>
      if yulConvLib.is_fixed_point [] t = folded then ()
      else fail (term_to_string t ^ (if folded then " was unfolded"
                                     else " was left folded")))
    [(“with_zero word_div (a : bytes32) b”, true),
     (“with_zero word_div (a : bytes32) 5w”, false),
     (“with_zero word_div (a : bytes32) 0w”, false)]

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
 * the word library -- and the rest are covered by the size bound.  No line is
 * left in the class now, and the check stays for the next body that stops
 * coming back. *)
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

(* The loop.  `checked_exp_helper`'s form at a fuel nobody knows stops at its
 * loop, which is left folded as a call is, and one iteration of that loop
 * converts on its own at such a fuel, with the next iteration folded in its
 * place.  Those are
 * the two steps an induction on the fuel takes over a loop head.  The fuel is
 * written `SUC k`: the body's calls test their fuel for zero, and on a bare
 * `k` that test is a decision every step after the call is evaluated under,
 * while a run at `0` is one a caller converts at that numeral.  Both forms are
 * held to the suite's own checks -- nothing of the evaluation left standing
 * but the folded loop and calls, a fixed point -- and to the size line the
 * excluded list is drawn at. *)
val loop_c = prim_mk_const {Thy = "yulEvaluator", Name = "eval_yul_loop"}

fun is_loop_at n t =
  let val (f, args) = strip_comb t in
    same_const loop_c f andalso List.length args = 6 andalso
    (case n of NONE => true | SOME n => aconv (hd args) n)
  end

fun loop_checked what t th =
  let
    val form = rhs (concl th)
    val res = yulConvLib.residues form
    val n = size_of form
  in
    if not (aconv (lhs (concl th)) t) then
      fail (what ^ "'s theorem is about some other term")
    else if not (List.all (fn k => Lib.mem k call_residues) res) then
      fail ("the conversion left " ^ show_residues res ^ " in " ^ what)
    else if not (yulConvLib.is_fixed_point table_defs form) then
      fail ("the conversion left something to evaluate in " ^ what)
    else if n >= 200000 then
      fail (what ^ " is " ^ Int.toString n ^ " nodes, at or over the line")
    else form
  end

val loop_entry =
  let
    val (_, args) =
      strip_comb (call_term (valOf (List.find (fn (n, _, _) =>
                                                 n = "checked_exp_helper")
                                              functions)))
    val n = mk_var ("n", numSyntax.num)
    val t = list_mk_comb (invoke_c, numSyntax.mk_suc n :: tl args)
    val form =
      case under_clock 60.0 (fn () => yulConvLib.yul_invoke_conv table_defs t) of
        NONE => fail "checked_exp_helper's entry did not come back within 60s"
      | SOME th => loop_checked "checked_exp_helper's entry" t th
  in
    if can (find_term (is_loop_at NONE)) form then form
    else fail "checked_exp_helper's entry does not stop at its loop"
  end

val loop_iteration =
  let
    val (_, args) = strip_comb (find_term (is_loop_at NONE) loop_entry)
    val k = mk_var ("k", numSyntax.num)
    val t = list_mk_comb (loop_c, numSyntax.mk_suc k :: tl args)
    val th =
      case under_clock 60.0 (fn () => yulConvLib.yul_loop_conv table_defs t) of
        NONE => fail "an iteration of checked_exp_helper's loop did not come \
                     \back within 60s"
      | SOME th => th
    val form = loop_checked "an iteration of checked_exp_helper's loop" t th
  in
    if not (can (find_term (is_loop_at (SOME k))) form) then
      fail "the iteration's form does not fold the next iteration at k"
    else th
  end

val () = print ("yulConvTest: checked_exp_helper's entry " ^ Int.toString
                (size_of loop_entry) ^ " nodes; an iteration at SUC k "
                ^ Int.toString (size_of (rhs (concl loop_iteration)))
                ^ " nodes\n")

(* A loop with statements after it.  `checked_exp_helper`'s loop is the last
 * statement of its body, so the rest after it is empty; here it is not: `f`'s
 * loop is followed by an assignment, and `g`'s is the same loop in a block of
 * its own, so the block's result is decided over the machine the loop returns.
 * An entry's form stops at the loop with the rest left unevaluated -- a form
 * that is not closed, since that rest is evaluation still to do -- at a numeral
 * fuel and at `SUC n` alike.  Taking the loop's iterations one at a time and
 * then finishing the rest with `yul_eval_conv` gives what the evaluator itself
 * gives.  On 2 the loop runs its post once before it exits. *)
Definition loop_rest_object_def:
  loop_rest_object =
    let loop = YulFor [] (YulBuiltin YLt [YulName "x"; YulLit (LitNumber 3w)])
                 [YulAssign ["x"]
                    (YulBuiltin YAdd [YulName "x"; YulLit (LitNumber 1w)])]
                 [];
        rest = YulAssign ["r"]
                 (YulBuiltin YAdd [YulName "x"; YulLit (LitNumber 1w)])
    in
      [YulFunction "f" ["x"] ["r"] [loop; rest];
       YulFunction "g" ["x"] ["r"] [YulBlock [loop]; rest]]
End

Definition loop_rest_table_def:
  loop_rest_table = yul_env loop_rest_object
End

val () =
  let
    val defs = [loop_rest_table_def, loop_rest_object_def]
    fun call fuel nm arg =
      list_mk_comb (invoke_c,
        [fuel, ``loop_rest_table``, stringSyntax.fromMLstring nm,
         listSyntax.mk_list ([arg], bytes32_ty), yul_conv_machine_term])
    fun clocked what conv t =
      case under_clock 60.0 (fn () => conv t) of
        NONE => fail (what ^ " did not come back within 60s")
      | SOME th => rhs (concl th)
    fun entry what t =
      let val form = clocked what (yulConvLib.yul_invoke_conv defs) t in
        if not (can (find_term (is_loop_at NONE)) form) then
          fail (what ^ " does not stop at its loop")
        else if yulConvLib.is_closed_form form then
          fail (what ^ " is closed, so the rest after its loop was dropped")
        else form
      end
    (* the loop's iterations, one at a time, until it exits *)
    fun run what i form =
      case Lib.total (find_term (is_loop_at NONE)) form of
        NONE => form
      | SOME loop =>
          if i > 3 then fail (what ^ "'s loop did not exit in 3 iterations")
          else
            run what (i + 1)
              (subst [loop |-> clocked (what ^ "'s loop")
                                 (yulConvLib.yul_loop_conv defs) loop] form)
    fun check nm =
      let
        val t = call ``20n`` nm ``2w : bytes32``
        val form = run nm 1 (entry (nm ^ "'s entry") t)
        val fns = ``loop_rest_table``
        val final = clocked ("the rest after " ^ nm ^ "'s loop")
                      (yulConvLib.yul_eval_conv defs fns) form
        (* EVAL also unfolds the frame's parameters, which the conversion
         * keeps by name, so the two are compared with those unfolded on both
         * sides. *)
        val direct = rhs (concl (EVAL t))
        val final' = rhs (concl (QCONV EVAL final))
        val n = mk_var ("n", numSyntax.num)
      in
        (* f and g call nothing, so the rest is held to what a call-free
         * body's form is: nothing left but a memory read, and a fixed
         * point *)
        if not (List.all (fn k => k = memory_read_residue)
                         (yulConvLib.residues final)) then
          fail ("the rest after " ^ nm ^ "'s loop left "
                ^ show_residues (yulConvLib.residues final))
        else if not (yulConvLib.is_fixed_point defs final) then
          fail ("the conversion left something to evaluate in the rest after "
                ^ nm ^ "'s loop")
        else if not (aconv final' direct) then
          fail ("the rest after " ^ nm ^ "'s loop gives "
                ^ term_to_string final ^ ", but the evaluator gives "
                ^ term_to_string direct)
        else
          ignore (entry (nm ^ "'s entry at SUC n")
                    (call (numSyntax.mk_suc n) nm (hd arg_names)))
      end
  in
    List.app check ["f", "g"]
  end

(* A message call's frame.  `call` hands its outcome to `run_external_call`,
 * a whole EVM run of the callee, which the form keeps folded, and writes the
 * output it got back -- `TAKE 32 outcome.call_return`, bytes no clause of the
 * memory write can list -- into memory.  The write then stays folded too, and
 * the statements after the call bind and assign locals on the machine it
 * returns: those have to read the scopes through the write, or every lookup
 * after the call comes out as a read of a scope the form does not have.  So
 * the form is held to what a call-free body's is, with the call and the write
 * it made as the only other steps standing. *)
Definition call_scope_object_def:
  call_scope_object =
    let lit = λn. YulLit (LitNumber n) in
      [YulFunction "f" ["a"] ["r"]
         [YulLet ["s"]
            (SOME (YulBuiltin YCall
                     [YulBuiltin YGas []; YulName "a"; lit 0w; lit 0w; lit 0w;
                      lit 0w; lit 32w]));
          YulLet ["x"] (SOME (YulBuiltin YMLoad [lit 0w]));
          YulAssign ["x"] (YulBuiltin YAdd [YulName "x"; YulName "s"]);
          YulAssign ["r"] (YulBuiltin YAdd [YulName "x"; YulName "a"])]]
End

Definition call_scope_table_def:
  call_scope_table = yul_env call_scope_object
End

val () =
  let
    val defs = [call_scope_table_def, call_scope_object_def]
    val t = list_mk_comb (invoke_c,
              [``20n``, ``call_scope_table``, stringSyntax.fromMLstring "f",
               listSyntax.mk_list ([hd arg_names], bytes32_ty),
               yul_conv_machine_term])
    val form =
      case under_clock 60.0 (fn () => yulConvLib.yul_invoke_conv defs t) of
        NONE => fail "the call's frame did not come back within 60s"
      | SOME th => rhs (concl th)
    val res = yulConvLib.residues form
    val allowed = [("externalCall", "run_external_call"), memory_read_residue,
                   ("yulEvaluator", "yul_memory_write")]
  in
    if not (yulConvLib.is_closed_form form) then
      fail ("the call's frame is not closed: " ^ show_residues res)
    else if not (yulConvLib.is_fixed_point defs form) then
      fail "the conversion left something to evaluate in the call's frame"
    else if not (Lib.mem ("externalCall", "run_external_call") res) then
      fail "the call's frame keeps no folded run_external_call"
    else if not (List.all (fn k => Lib.mem k allowed) res) then
      fail ("the scopes after the call are not resolved: " ^ show_residues res)
    else print ("yulConvTest: the call's frame closes at " ^
                Int.toString (size_of form) ^ " nodes\n")
  end
