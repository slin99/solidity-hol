(* Code-reading builtins observe the current stage's runtime image. *)
Theory yulDifferentialTest
Ancestors yulDifferential solidityDifferential
Libs cv_transLib wordsLib intLib

Definition code_reading_case_def:
  code_reading_case =
    <| case_sender := 0x2000w; case_value := 0; case_input := RawCall [];
       case_storage := []; case_peer_code := []; case_peer_storage := [];
       case_expect := ExpectReturn []; case_final := []; case_logs := [];
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
