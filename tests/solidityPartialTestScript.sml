(* Per-function admission (testdata/frontend/partial.sol): the unsupported
 * functions of a unit, and those calling them, are marked with their reason
 * and have no procedure; the rest is checked and runs, and a call of an
 * unsupported function is refused rather than run as some other function.
 *)
Theory solidityPartialTest
Ancestors
  solidityDifferential
Libs
  solidityPrepareLib cv_transLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps [
  "../SOLIDITY_PIN", "../profiles/solc-0.8.37-via-ir-osaka.json",
  "../testdata/frontend/expected/partial.json",
  "../testdata/frontend/expected/fallback_params.json"
]

val prepared = #prepared (solidityPrepareLib.prepare_artifact
  {root = "..", path = "../testdata/frontend/expected/partial.json",
   source = "testdata/frontend/partial.sol"});

(* add is supported; digest and the fallback use sha256, as does Mid.twice,
 * which Partial.twice reaches by super, so Partial.twice, digestTwice and
 * callsTwice call unsupported functions; the constructor's halting assembly
 * does not elaborate. Once Partial.twice is unsupported its super calls
 * reach nothing, so neither Mid.twice nor Base.twice is among the
 * functions calls reach. The constant DIGITS does not elaborate, so it has
 * no procedure and digits, which reads it, fails to elaborate; so does
 * pointer, whose assembly names a bytes local. *)
val outcomes = map (fn {name, reason, ...} => (name, reason)) (#functions prepared);
fun reasons name =
  map #2 (List.filter (fn (n, _) => n = name) outcomes);
val calls_unsupported = SOME "calls an unsupported function";
val fails_to_elaborate = SOME "fails to elaborate (unsupported lowering)";
fun imported_failure r =
  case r of
    SOME m => not (String.isPrefix "calls" m) andalso r <> fails_to_elaborate
  | NONE => false;
val () =
  if reasons "add" = [NONE] andalso
     reasons "total" = [] andalso
     List.all imported_failure (reasons "digest") andalso
     length (reasons "digest") = 1 andalso
     length (reasons "") = 2 andalso
     List.exists imported_failure (reasons "") andalso
     List.exists (fn r => r = fails_to_elaborate) (reasons "") andalso
     reasons "digestTwice" = [calls_unsupported] andalso
     reasons "callsTwice" = [calls_unsupported] andalso
     reasons "twice" = [calls_unsupported] andalso
     reasons "digits" = [fails_to_elaborate] andalso
     reasons "pointer" = [fails_to_elaborate] andalso
     length outcomes = 9
  then ()
  else raise Fail ("unexpected function outcomes: " ^
    String.concatWith "; " (map (fn (n, r) => n ^ " " ^
      (case r of SOME m => m | NONE => "supported")) outcomes));

Definition partial_program_def:
  partial_program = ^(#program prepared)
End

val () = cv_auto_trans partial_program_def;

Definition partial_call_def:
  partial_call data =
    call_contract 1000 partial_program FEMPTY
      (differential_frame (n2w 0x1212) 0 data)
      (differential_world empty_accounts)
End

val () = cv_auto_trans partial_call_def;

fun selector hex =
  map (fn i => “n2w ^(numSyntax.term_of_int
         (valOf (StringCvt.scanString (Int.scan StringCvt.HEX)
                   (String.substring (hex, 2 * i, 2))))) : word8”)
    (List.tabulate (4, I));
fun with_word hex n =
  listSyntax.mk_list (selector hex, “:word8”) |> (fn s =>
    “^s ++ word_to_bytes (n2w ^(numSyntax.term_of_int n) : bytes32) T”);

(* add runs: add(5) returns 5. *)
Theorem partial_add_runs:
  ∃w. partial_call ^(with_word "1003e2d2" 5) =
      ContractReturned (word_to_bytes (5w : bytes32) T) w
Proof
  CONV_TAC (QUANT_CONV (LAND_CONV cv_eval)) >> simp[] >> EVAL_TAC
QED

(* twice is refused, not run as Base.twice (10) or with Mid.twice skipped. *)
Theorem partial_twice_refused:
  partial_call ^(with_word "3cf3bbf4" 5) = ContractInvalid "unknown procedure"
Proof
  CONV_TAC (LAND_CONV cv_eval) >> REFL_TAC
QED

Theorem partial_digest_refused:
  partial_call (^(listSyntax.mk_list (selector "1b27a36f", “:word8”)) ++
                word_to_bytes (32w : bytes32) T ++ REPLICATE 32 0w) =
  ContractInvalid "unknown procedure"
Proof
  CONV_TAC (LAND_CONV cv_eval) >> REFL_TAC
QED

Theorem partial_calls_twice_refused:
  partial_call ^(with_word "b8afe286" 5) = ContractInvalid "unknown procedure"
Proof
  CONV_TAC (LAND_CONV cv_eval) >> REFL_TAC
QED

(* The getter of the constant that does not elaborate is refused, as are
 * digits, which reads it, and pointer. *)
Theorem partial_constant_getter_refused:
  partial_call ^(listSyntax.mk_list (selector "d0263f8c", “:word8”)) =
  ContractInvalid "unknown procedure"
Proof
  CONV_TAC (LAND_CONV cv_eval) >> REFL_TAC
QED

Theorem partial_digits_refused:
  partial_call ^(listSyntax.mk_list (selector "9e20437c", “:word8”)) =
  ContractInvalid "unknown procedure"
Proof
  CONV_TAC (LAND_CONV cv_eval) >> REFL_TAC
QED

Theorem partial_pointer_refused:
  partial_call (^(listSyntax.mk_list (selector "8a237e56", “:word8”)) ++
                word_to_bytes (32w : bytes32) T ++ REPLICATE 32 0w) =
  ContractInvalid "unknown procedure"
Proof
  CONV_TAC (LAND_CONV cv_eval) >> REFL_TAC
QED

(* Unknown calldata reaches the unsupported fallback, which refuses rather
 * than reverting as a contract without one would. *)
Theorem partial_fallback_refused:
  partial_call [1w; 2w; 3w; 4w] = ContractInvalid "unknown procedure"
Proof
  CONV_TAC (LAND_CONV cv_eval) >> REFL_TAC
QED

(* The constructor is unsupported, so creation is refused. *)
Theorem partial_creation_refused:
  deploy_contract 1000 partial_program (differential_frame (n2w 0x1212) 0 [])
    (differential_world empty_accounts) = ContractInvalid "unknown procedure"
Proof
  CONV_TAC (LAND_CONV cv_eval) >> REFL_TAC
QED

(* A fallback with parameters and returns (testdata/frontend/fallback_params.sol)
 * is unsupported, since the core's fallback takes neither: add runs, and a
 * call reaching the fallback is refused. *)
val fallback_prepared = #prepared (solidityPrepareLib.prepare_artifact
  {root = "..", path = "../testdata/frontend/expected/fallback_params.json",
   source = "testdata/frontend/fallback_params.sol"});

val fallback_outcomes =
  map (fn {name, reason, ...} => (name, reason)) (#functions fallback_prepared);
val () =
  if fallback_outcomes =
     [("add", NONE), ("", SOME "fallback with parameters or returns")]
  then ()
  else raise Fail ("unexpected fallback_params outcomes: " ^
    String.concatWith "; " (map (fn (n, r) => n ^ " " ^
      (case r of SOME m => m | NONE => "supported")) fallback_outcomes));

Definition fallback_params_program_def:
  fallback_params_program = ^(#program fallback_prepared)
End

val () = cv_auto_trans fallback_params_program_def;

Definition fallback_params_call_def:
  fallback_params_call data =
    call_contract 1000 fallback_params_program FEMPTY
      (differential_frame (n2w 0x1212) 0 data)
      (differential_world empty_accounts)
End

val () = cv_auto_trans fallback_params_call_def;

(* add(2, 3) returns 5. *)
Theorem fallback_params_add_runs:
  ∃w. fallback_params_call (^(listSyntax.mk_list (selector "771602f7", “:word8”)) ++
                            word_to_bytes (2w : bytes32) T ++
                            word_to_bytes (3w : bytes32) T) =
      ContractReturned (word_to_bytes (5w : bytes32) T) w
Proof
  CONV_TAC (QUANT_CONV (LAND_CONV cv_eval)) >> simp[] >> EVAL_TAC
QED

Theorem fallback_params_fallback_refused:
  fallback_params_call [1w; 2w; 3w; 4w] = ContractInvalid "unknown procedure"
Proof
  CONV_TAC (LAND_CONV cv_eval) >> REFL_TAC
QED

(* The elaborator refuses such a fallback even when the importer has not
 * marked it: the unit elaborates as imported, and with the mark removed it
 * fails elaboration. *)
Definition fallback_params_unit_def:
  fallback_params_unit = ^(#unit fallback_prepared)
End

val () = cv_auto_trans fallback_params_unit_def;

Definition fallback_params_unmarked_def:
  fallback_params_unmarked =
    fallback_params_unit with unit_contracts :=
      MAP (λc. c with contract_functions :=
             MAP (λf. if f.fn_kind = "fallback" then f with fn_unsupported := NONE
                      else f) c.contract_functions)
        fallback_params_unit.unit_contracts
End

val () = cv_auto_trans fallback_params_unmarked_def;

Theorem fallback_params_unmarked_fails_elaboration:
  unit_elaboration_failures T fallback_params_unit = [] ∧
  LENGTH (unit_elaboration_failures T fallback_params_unmarked) = 1
Proof
  CONV_TAC cv_eval
QED
