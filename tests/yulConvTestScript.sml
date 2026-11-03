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
 * calls it makes, so a function that calls nothing has nothing left at all,
 * and one that calls is left waiting on the frame a callee returned and
 * nothing else (see semantics/yulConvLib.sml).  The number the test asserts is
 * the slowest of them, so that a conversion that regressed to the simplifier's
 * cost fails the build on the clock alone; the total is printed to say what
 * the suite costs.
 *)
Theory yulConvTest
Ancestors
  yulAST yulDialect yulState yulEvaluator yulEvaluatorProps cv_string_fmap
  vfmCompute
Libs
  wordsLib yulImportLib yulConvLib

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

(* What a form may still be waiting on, and what it may not.  The conversion
 * takes the body's own evaluation -- the block, the statements, the
 * expressions -- so a form with one of those in it is one whose evaluation
 * stopped early, and every residue must be permitted.  Permitted are the call
 * a body left folded and the evaluator's own operations on a frame or on
 * memory, which wait on a value nobody has: a callee's frame after a call, or
 * a word written to memory from a symbolic value.  A body that calls nothing
 * may not be waiting on a call. *)
val call_residues = yulConvLib.permitted_residues

fun show_residues res =
  String.concatWith ", " (List.map (fn (t, n) => t ^ "." ^ n) res)

val started = Timer.startRealTimer ()

fun convert f =
  let
    val nm = #1 f
    val th = yulConvLib.yul_invoke_conv table_defs (call_term f)
    val form = rhs (concl th)
    val res = yulConvLib.residues form
  in
    if not (yulConvLib.is_fixed_point form) then
      fail ("the conversion left something to evaluate in " ^ nm)
    else if not (List.all (fn k => Lib.mem k call_residues) res) then
      fail ("the conversion left " ^ show_residues res ^ " in " ^ nm)
    else if not (has_call (#3 f)) andalso
            Lib.mem ("yulEvaluator", "invoke_yul") res then
      fail ("the body of " ^ nm ^ " calls nothing, but its form is left "
            ^ "waiting on a call")
    else (nm, th)
  end

(* Timed one at a time: what the conversion is asked for is seconds per
 * function, so the number the test bounds is the slowest of them, and the
 * total is printed to say what the suite costs.  Only the name and the time
 * are kept: a form runs to a million constants, and holding all 137 of them
 * holds tens of gigabytes of heap, which is more than the per-process limit a
 * build runs a theory under.  The two forms stated below are converted again
 * for that, which costs a couple of seconds. *)
fun timed f =
  let
    val t0 = Timer.startRealTimer ()
    val _ = convert f
  in
    (#1 f, Time.toReal (Timer.checkRealTimer t0))
  end

val timings = List.map timed loop_free

val elapsed = Time.toReal (Timer.checkRealTimer started)
val slowest =
  List.foldl (fn ((nm, t), (bnm, bt)) => if t > bt then (nm, t) else (bnm, bt))
             (#1 (hd loop_free), 0.0) timings
val calling = List.length (List.filter (fn (_, _, body) => has_call body)
                                       loop_free)

val () = print ("yulConvTest: " ^ Int.toString (List.length timings)
                ^ " forms in " ^ Real.toString elapsed ^ "s; slowest "
                ^ #1 slowest ^ " at " ^ Real.toString (#2 slowest) ^ "s; "
                ^ Int.toString calling ^ " of the bodies call\n")

val () =
  if #2 slowest < 5.0 then ()
  else fail ("the slowest form took " ^ Real.toString (#2 slowest) ^ "s ("
             ^ #1 slowest ^ ")")

(* Two of the forms, stated: one that calls nothing else, and one whose body
 * is calls and arithmetic.  These are the theorems a reader can look at, and
 * the terms the matching step of the translation-validation driver will be
 * given. *)
val scalars_cleanup_uint8 = save_thm ("scalars_cleanup_uint8",
  yulConvLib.yul_invoke_conv table_defs
    (call_term (valOf (List.find (fn (nm, _, _) => nm = "cleanup_uint8")
                                 functions))))

val scalars_checked_sub_t_uint8 = save_thm ("scalars_checked_sub_t_uint8",
  yulConvLib.yul_invoke_conv table_defs
    (call_term (valOf (List.find (fn (nm, _, _) => nm = "checked_sub_t_uint8")
                                 functions))))

(* The form is stated at a numeral fuel, and that costs nothing: fuel is only
 * ever tested for zero, so a run that completed at the numeral is the run at
 * every larger bound.  This is how the form reaches the shape the
 * per-function theorem's Yul side has, `invoke_yul n ... = r` at a
 * universally quantified fuel; the bound does not depend on the arguments or
 * the frame, so those stay the caller's.
 *)
Theorem scalars_checked_sub_t_uint8_fuel_stable:
  ∀m n a0 a1.
    20 ≤ n ∧
    yul_running (invoke_yul 20 scalars_function_table "checked_sub_t_uint8"
                   [a0; a1] m) ⇒
    invoke_yul n scalars_function_table "checked_sub_t_uint8" [a0; a1] m =
    invoke_yul 20 scalars_function_table "checked_sub_t_uint8" [a0; a1] m
Proof
  metis_tac [invoke_yul_fuel_stable]
QED
