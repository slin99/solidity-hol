(* Code-reading builtins observe the current stage's runtime image. *)
Theory yulDifferentialTest
Ancestors yulDifferential solidityDifferential
Libs cv_transLib wordsLib intLib solidityDifferentialLib

(* Exercise offset discovery on artifact bytes, before HOL checks the span. *)
local
  fun obj fields = JSON.OBJECT fields
  fun image bytes = obj [("object", JSON.STRING bytes)]
  fun offset creation runtime =
    solidityDifferentialLib.deployed_code_offset
      (obj [("output", obj [("contracts", obj [("s.sol", obj [("C", obj
        [("evm", obj [("bytecode", image creation),
                      ("deployedBytecode", image runtime)])])])])])])
      "s.sol" "C"
  fun expect_offset creation runtime expected =
    if offset creation runtime = expected then ()
    else raise ERR "yulDifferentialTest" "wrong runtime offset"
  fun expect_rejection creation runtime expected =
    (ignore (offset creation runtime);
     raise ERR "yulDifferentialTest" "accepted invalid runtime layout")
    handle solidityBytecodeLib.CorpusError msg =>
      if msg = expected then ()
      else raise ERR "yulDifferentialTest" ("wrong layout rejection: " ^ msg)
in
  val () = expect_offset "ff1122aa" "1122" 1
  val () = expect_offset "11221122" "1122" 2
  val () = expect_rejection "ff11aa" "1122"
    "runtime bytecode is not present in initcode"
  val () = expect_rejection "1122aa1122ff" "1122"
    "runtime bytecode has ambiguous locations in initcode"
  val () = expect_rejection "111111ff" "1111"
    "runtime bytecode has ambiguous locations in initcode"
  val () = expect_rejection "f1122f" "1122"
    "runtime bytecode is not present in initcode"
end

Definition code_reading_case_def:
  code_reading_case =
    <| case_sender := 0x2000w; case_value := 0; case_input := RawCall [];
       case_storage := []; case_peer_code := []; case_peer_storage := [];
       case_expect := ExpectReturn []; case_final := []; case_gas := []; case_logs := [];
       case_immutables := []; case_immutable_refs := [] |>
End

Definition code_reading_program_def:
  code_reading_program =
    <| runtime_body :=
         [YulExprStmt (YulBuiltin YCodeCopy
            [YulLit (LitNumber 0w); YulLit (LitNumber 0w);
             YulBuiltin YCodeSize []]);
          YulExprStmt (YulBuiltin YReturn
            [YulLit (LitNumber 0w); YulBuiltin YCodeSize []])];
       runtime_bytes := [0x11w; 0x22w]; runtime_refs := [];
       creation_program := NONE |>
End

val () = cv_auto_trans code_reading_case_def;
val () = cv_auto_trans code_reading_program_def;

Theorem runtime_reads_its_stage_code:
  FST (yul_case_execution [0xFFw] code_reading_program u
         code_reading_case 20) = Returned [0x11w; 0x22w]
Proof
  simp[yul_case_execution_def, code_reading_case_def,
       input_call_def, case_immutable_values_def] >>
  CONV_TAC cv_eval
QED

(* Copy a runtime image, patch its immutable from appended constructor data,
 * and return it. Marker bytes around the word make a wrong copy observable. *)
Definition creation_copy_program_def:
  creation_copy_program =
    <| creation_body :=
         [YulExprStmt (YulBuiltin YCodeCopy
            [YulLit (LitNumber 64w);
             YulBuiltin YDataSize [YulLit (LitBytes [0x63w])];
             YulBuiltin YSub
               [YulBuiltin YCodeSize [];
                YulBuiltin YDataSize [YulLit (LitBytes [0x63w])]]]);
          YulExprStmt (YulBuiltin YCodeCopy
            [YulLit (LitNumber 16w);
             YulBuiltin YDataOffset [YulLit (LitBytes [0x72w])];
             YulBuiltin YDataSize [YulLit (LitBytes [0x72w])]]);
          YulExprStmt (YulBuiltin YSetImmutable
            [YulLit (LitNumber 16w); YulLit (LitBytes [0x33w]);
             YulBuiltin YMLoad [YulLit (LitNumber 64w)]]);
          YulExprStmt (YulBuiltin YReturn
            [YulLit (LitNumber 16w);
             YulBuiltin YDataSize [YulLit (LitBytes [0x72w])]])];
       creation_name := "c"; deployed_name := "r";
       creation_bytes := [0xFFw; 0x11w] ++ REPLICATE 32 0w ++ [0x22w];
       deployed_bytes := [0x11w] ++ REPLICATE 32 0w ++ [0x22w];
       deployed_offset := 1;
       creation_refs := [(3, [1])] |>
End

Definition creation_copy_case_def:
  creation_copy_case = code_reading_case with
    case_input := Deploy [] (INR (word_to_bytes_be (42w : bytes32)))
End

val () = cv_auto_trans creation_copy_program_def;
val () = cv_auto_trans creation_copy_case_def;

Theorem creation_copies_and_patches_runtime:
  FST (yul_case_execution []
    (code_reading_program with creation_program := SOME creation_copy_program)
    u creation_copy_case 40) = Returned (word_to_bytes_be (42w : bytes32))
Proof
  simp[yul_case_execution_def, creation_copy_case_def, code_reading_case_def,
       input_call_def, case_immutable_values_def] >>
  CONV_TAC cv_eval
QED

Theorem creation_rejects_wrong_suffix:
  yul_creation_execution
    (creation_copy_program with creation_bytes := REPLICATE 35 0w)
    creation_copy_case (word_to_bytes_be (42w : bytes32)) 40 =
    (Diagnostic InvalidCompletion, NONE, [])
Proof
  CONV_TAC cv_eval
QED

Theorem creation_copies_runtime_before_trailing_data:
  FST (yul_case_execution []
    (code_reading_program with creation_program := SOME
      (creation_copy_program with creation_bytes :=
        creation_copy_program.creation_bytes ++ [0xAAw; 0xBBw]))
    u creation_copy_case 40) = Returned (word_to_bytes_be (42w : bytes32))
Proof
  simp[yul_case_execution_def, creation_copy_case_def, code_reading_case_def,
       input_call_def, case_immutable_values_def] >>
  CONV_TAC cv_eval
QED

Theorem creation_rejects_wrong_runtime_offset:
  yul_creation_execution
    (creation_copy_program with deployed_offset := 0)
    creation_copy_case (word_to_bytes_be (42w : bytes32)) 40 =
    (Diagnostic InvalidCompletion, NONE, [])
Proof
  CONV_TAC cv_eval
QED

Theorem creation_rejects_runtime_out_of_bounds:
  yul_creation_execution
    (creation_copy_program with deployed_offset := 2)
    creation_copy_case (word_to_bytes_be (42w : bytes32)) 40 =
    (Diagnostic InvalidCompletion, NONE, [])
Proof
  CONV_TAC cv_eval
QED

Theorem creation_rejects_wrong_returned_code:
  yul_creation_execution
    (creation_copy_program with creation_body :=
      [YulExprStmt (YulBuiltin YReturn
        [YulLit (LitNumber 0w); YulLit (LitNumber 0w)])])
    creation_copy_case (word_to_bytes_be (42w : bytes32)) 40 =
    (Diagnostic InvalidCompletion, NONE, [])
Proof
  CONV_TAC cv_eval
QED

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps [
  "../SOLIDITY_PIN",
  "../profiles/solc-0.8.37-via-ir-osaka.json",
  "../testdata/differential/shadowed_builtins.sol",
  "../testdata/differential/expected/shadowed_builtins.json",
  "../testdata/yul/expected/shadowed_builtins.json",
  "../testdata/yul/expected/shadowed_builtins-optimized.json"
]

(* This case would fail if evaluated. Gas evidence leaves it inconclusive
 * before either interpreter runs, with no agreement theorem to reuse. *)
val () = let
  val dir = "yul-gas-guard-test"
  fun read path = let val f = TextIO.openIn path
                 in TextIO.inputAll f before TextIO.closeIn f end
  fun write path text = let val f = TextIO.openOut path
                        in TextIO.output (f, text) before TextIO.closeOut f end
  val () = OS.FileSys.mkDir dir
  val () = write (dir ^ "/gas_guard.ir.json")
    (read "../testdata/yul/expected/shadowed_builtins.json")
  val () = write (dir ^ "/gas_guard.optimized.json")
    (read "../testdata/yul/expected/shadowed_builtins-optimized.json")
  val () = write (dir ^ "/suite.json")
    "{\"name\":\"gas_guard\",\"source\":\"testdata/differential/shadowed_builtins.sol\",\"contract\":\"ShadowedBuiltins\",\"artifact\":\"testdata/differential/expected/shadowed_builtins.json\",\"cases\":[{\"name\":\"probe\",\"calldata\":\"0x\",\"gas\":[1],\"expect\":{\"returned\":\"0xdead\"}}]}"
  val () = solidityDifferentialLib.with_results (dir ^ "/results.jsonl") (fn () =>
    solidityDifferentialLib.run_yul_suite_file
      {root = "..", suite_file = "tests/" ^ dir ^ "/suite.json", yul_root = dir})
  val prefix = "yul-differential-result: "
  val rows = map (JSONParser.parse o JSONParser.openString o
                 (fn line => String.extract (line, size prefix, NONE)))
    (String.tokens (fn c => c = #"\n") (read (dir ^ "/results.jsonl")))
  open solidityBytecodeLib
  val cases = List.filter (fn r => string_field r "kind" = "case") rows
  val () = if length cases = 3 andalso List.all (fn r =>
      string_field r "status" = "inconclusive" andalso
      string_field r "message" = "gas observations not modelled in raw Yul" andalso
      not (Option.isSome (JSONUtil.findField r "theorem"))) cases then ()
    else raise Fail "raw Yul gas evidence was not reported as inconclusive"
  val () = List.app (fn stage =>
    if can (DB.fetch (current_theory ())) ("yul_gas_guard_probe_" ^ stage) then
      raise Fail "raw Yul gas evidence saved an agreement theorem"
    else ()) ["ir", "ir_optimized", "optimized"]
  val () = List.app (fn file => OS.FileSys.remove (dir ^ "/" ^ file))
    ["gas_guard.ir.json", "gas_guard.optimized.json", "suite.json", "results.jsonl"]
  val () = OS.FileSys.rmDir dir
in () end
