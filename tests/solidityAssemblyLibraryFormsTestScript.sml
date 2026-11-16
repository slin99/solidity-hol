(* Inline assembly the compiler runs but the source model leaves out: a
 * block that leaves the zero slot non-zero, which the compiler's empty byte
 * sequences and arrays would then read, and an enum local written past its
 * last member. *)
Theory solidityAssemblyLibraryFormsTest
Ancestors solidityCoreWf solidityDifferentialCorpus_assembly_library_forms
Libs solidityBytecodeLib cv_transLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps [
  "../SOLIDITY_PIN",
  "../profiles/solc-0.8.37-via-ir-osaka.json",
  "../testdata/differential/assembly_library_forms.sol",
  "../testdata/differential/expected/assembly_library_forms.json",
  "../testdata/differential/fail_closed/assembly_library_forms.json"
]

val () = solidityBytecodeLib.run_suite_file
  {root = "..", suite_file = "testdata/differential/fail_closed/assembly_library_forms.json"}

fun rejected_case name =
  let
    open solidityBytecodeLib
    val suite = JSONParser.parseFile
      "../testdata/differential/fail_closed/assembly_library_forms.json"
    val c = valOf (List.find (fn c => string_field c "name" = name)
                    (array_field suite "cases"))
  in
    case_term {peer = “[] : byte list”, libraries = “[] : (address # byte list) list”}
      {names = [], refs = “[] : (num # num list) list”}
      (call_input (fn () => “[] : byte list”) c) c
  end;

Theorem zero_slot_left_non_zero:
  source_execution bytecode_rejected_assembly_library_forms_code
    corpus_assembly_library_forms_unit corpus_assembly_library_forms_program 1000
    ^(rejected_case "zero_slot_left_non_zero") =
  (Diagnostic InvalidCompletion, NONE, [])
Proof
  CONV_TAC cv_eval
QED

Theorem enum_past_last_member:
  source_execution bytecode_rejected_assembly_library_forms_code
    corpus_assembly_library_forms_unit corpus_assembly_library_forms_program 1000
    ^(rejected_case "enum_past_last_member") =
  (Diagnostic InvalidCompletion, NONE, [])
Proof
  CONV_TAC cv_eval
QED
