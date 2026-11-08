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
