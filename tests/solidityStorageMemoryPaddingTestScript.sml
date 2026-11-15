(* Storage copies preserve unknown padding in the compiler. Check its exact
 * words independently, then require source rejection rather than agreement. *)
Theory solidityStorageMemoryPaddingTest
Ancestors solidityDifferentialCorpus_storage_memory_padding
Libs solidityBytecodeLib cv_transLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps [
  "../SOLIDITY_PIN",
  "../profiles/solc-0.8.37-via-ir-osaka.json",
  "../testdata/differential/storage_memory_padding.sol",
  "../testdata/differential/expected/storage_memory_padding.json",
  "../testdata/differential/fail_closed/storage_memory_padding.json"
]

val () = solidityBytecodeLib.run_suite_file
  {root = "..", suite_file = "testdata/differential/fail_closed/storage_memory_padding.json"}

fun rejected_case name =
  let
    open solidityBytecodeLib
    val suite = JSONParser.parseFile
      "../testdata/differential/fail_closed/storage_memory_padding.json"
    val c = valOf (List.find (fn c => string_field c "name" = name)
                    (array_field suite "cases"))
  in
    case_term {peer = “[] : byte list”, libraries = “[] : (address # byte list) list”}
      {names = [], refs = “[] : (num # num list) list”}
      (call_input (fn () => “[] : byte list”) c) c
  end;

Theorem short_dirty_padding:
  source_execution bytecode_rejected_storage_memory_padding_code
    corpus_storage_memory_padding_unit corpus_storage_memory_padding_program 1000
    ^(rejected_case "short_dirty_padding") =
  (Diagnostic InvalidCompletion, NONE, [])
Proof
  CONV_TAC cv_eval
QED

Theorem short_zero_padding_still_unknown:
  source_execution bytecode_rejected_storage_memory_padding_code
    corpus_storage_memory_padding_unit corpus_storage_memory_padding_program 1000
    ^(rejected_case "short_zero_padding_still_unknown") =
  (Diagnostic InvalidCompletion, NONE, [])
Proof
  CONV_TAC cv_eval
QED

Theorem struct_dirty_padding:
  source_execution bytecode_rejected_storage_memory_padding_code
    corpus_storage_memory_padding_unit corpus_storage_memory_padding_program 1000
    ^(rejected_case "struct_dirty_padding") =
  (Diagnostic InvalidCompletion, NONE, [])
Proof
  CONV_TAC cv_eval
QED

Theorem array_dirty_padding:
  source_execution bytecode_rejected_storage_memory_padding_code
    corpus_storage_memory_padding_unit corpus_storage_memory_padding_program 1000
    ^(rejected_case "array_dirty_padding") =
  (Diagnostic InvalidCompletion, NONE, [])
Proof
  CONV_TAC cv_eval
QED

Theorem string_dirty_padding:
  source_execution bytecode_rejected_storage_memory_padding_code
    corpus_storage_memory_padding_unit corpus_storage_memory_padding_program 1000
    ^(rejected_case "string_dirty_padding") =
  (Diagnostic InvalidCompletion, NONE, [])
Proof
  CONV_TAC cv_eval
QED

Theorem long_dirty_tail:
  source_execution bytecode_rejected_storage_memory_padding_code
    corpus_storage_memory_padding_unit corpus_storage_memory_padding_program 1000
    ^(rejected_case "long_dirty_tail") =
  (Diagnostic InvalidCompletion, NONE, [])
Proof
  CONV_TAC cv_eval
QED
