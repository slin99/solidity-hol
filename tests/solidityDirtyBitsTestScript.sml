(* These calls are admitted source programs, but their non-canonical values
 * must fail closed. Compiler outcomes are checked independently by the ancestor;
 * an InvalidCompletion is never counted as differential agreement. *)
Theory solidityDirtyBitsTest
Ancestors solidityDifferential solidityDirtyBitsBytecodeTest
  solidityDifferentialCorpus_inline_assembly
  solidityDifferentialCorpus_storage
  solidityDifferentialCorpus_storage_arrays
  solidityDifferentialCorpus_enums
  solidityDifferentialCorpus_dirty_bits
  solidityDifferentialCorpus_udvt
  solidityDifferentialCorpus_typed_catches
Libs solidityBytecodeLib cv_transLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps [
  "../testdata/differential/fail_closed/inline_assembly.json",
  "../testdata/differential/fail_closed/storage.json",
  "../testdata/differential/fail_closed/storage_arrays.json",
  "../testdata/differential/fail_closed/enums.json",
  "../testdata/differential/fail_closed/dirty_bits.json",
  "../testdata/differential/fail_closed/udvt.json",
  "../testdata/differential/fail_closed/typed_catches.json"
]

fun rejected_suite group =
  JSONParser.parseFile ("../testdata/differential/fail_closed/" ^ group ^ ".json");

fun rejected_case group name =
  let
    open solidityBytecodeLib
    val suite = rejected_suite group
    val c = valOf (List.find (fn c => string_field c "name" = name)
                    (array_field suite "cases"))
    val peer =
      case JSONUtil.findField suite "peer" of
        NONE => “[] : byte list”
      | SOME _ => prim_mk_const {Thy = "solidityDirtyBitsBytecodeTest",
          Name = "bytecode_rejected_" ^ group ^ "_peer_code"}
  in
    case_term peer {names = [], refs = “[] : (num # num list) list”}
      (call_input (fn () => “[] : byte list”) c) c
  end;

Theorem reject_inline_assembly_dirty_uint8_cleaned:
  source_execution bytecode_rejected_inline_assembly_code
    corpus_inline_assembly_unit corpus_inline_assembly_program 1000
    ^(rejected_case "inline_assembly" "dirty_uint8_cleaned") =
  (Diagnostic InvalidCompletion, NONE, [])
Proof
  CONV_TAC cv_eval
QED

Theorem reject_inline_assembly_dirty_bool_true:
  source_execution bytecode_rejected_inline_assembly_code
    corpus_inline_assembly_unit corpus_inline_assembly_program 1000
    ^(rejected_case "inline_assembly" "dirty_bool_true") =
  (Diagnostic InvalidCompletion, NONE, [])
Proof
  CONV_TAC cv_eval
QED

Theorem reject_inline_assembly_signed_negative_sign_extended:
  source_execution bytecode_rejected_inline_assembly_code
    corpus_inline_assembly_unit corpus_inline_assembly_program 1000
    ^(rejected_case "inline_assembly" "signed_negative_sign_extended") =
  (Diagnostic InvalidCompletion, NONE, [])
Proof
  CONV_TAC cv_eval
QED

Theorem reject_inline_assembly_signed_positive:
  source_execution bytecode_rejected_inline_assembly_code
    corpus_inline_assembly_unit corpus_inline_assembly_program 1000
    ^(rejected_case "inline_assembly" "signed_positive") =
  (Diagnostic InvalidCompletion, NONE, [])
Proof
  CONV_TAC cv_eval
QED

Theorem reject_inline_assembly_address_low_order:
  source_execution bytecode_rejected_inline_assembly_code
    corpus_inline_assembly_unit corpus_inline_assembly_program 1000
    ^(rejected_case "inline_assembly" "address_low_order") =
  (Diagnostic InvalidCompletion, NONE, [])
Proof
  CONV_TAC cv_eval
QED

Theorem reject_inline_assembly_write_back_cleans_before_checked_add:
  source_execution bytecode_rejected_inline_assembly_code
    corpus_inline_assembly_unit corpus_inline_assembly_program 1000
    ^(rejected_case "inline_assembly" "write_back_cleans_before_checked_add") =
  (Diagnostic InvalidCompletion, NONE, [])
Proof
  CONV_TAC cv_eval
QED

Theorem reject_storage_dirty_bool_reads_true:
  source_execution bytecode_rejected_storage_code
    corpus_storage_unit corpus_storage_program 1000
    ^(rejected_case "storage" "dirty_bool_reads_true") =
  (Diagnostic InvalidCompletion, NONE, [])
Proof
  CONV_TAC cv_eval
QED

Theorem reject_storage_arrays_dirty_bool_reads_true:
  source_execution bytecode_rejected_storage_arrays_code
    corpus_storage_arrays_unit corpus_storage_arrays_program 1000
    ^(rejected_case "storage_arrays" "dirty_bool_reads_true") =
  (Diagnostic InvalidCompletion, NONE, [])
Proof
  CONV_TAC cv_eval
QED

Theorem reject_enums_stored_byte_out_of_range_panics:
  source_execution bytecode_rejected_enums_code
    corpus_enums_unit corpus_enums_program 1000
    ^(rejected_case "enums" "stored_byte_out_of_range_panics") =
  (Diagnostic InvalidCompletion, NONE, [])
Proof
  CONV_TAC cv_eval
QED

Theorem reject_enums_mapping_byte_out_of_range_panics:
  source_execution bytecode_rejected_enums_code
    corpus_enums_unit corpus_enums_program 1000
    ^(rejected_case "enums" "mapping_byte_out_of_range_panics") =
  (Diagnostic InvalidCompletion, NONE, [])
Proof
  CONV_TAC cv_eval
QED

Theorem reject_enums_array_byte_out_of_range_panics:
  source_execution bytecode_rejected_enums_code
    corpus_enums_unit corpus_enums_program 1000
    ^(rejected_case "enums" "array_byte_out_of_range_panics") =
  (Diagnostic InvalidCompletion, NONE, [])
Proof
  CONV_TAC cv_eval
QED

Theorem reject_enums_packed_byte_out_of_range_panics:
  source_execution bytecode_rejected_enums_code
    corpus_enums_unit corpus_enums_program 1000
    ^(rejected_case "enums" "packed_byte_out_of_range_panics") =
  (Diagnostic InvalidCompletion, NONE, [])
Proof
  CONV_TAC cv_eval
QED

Theorem reject_enums_getter_byte_out_of_range_panics:
  source_execution bytecode_rejected_enums_code
    corpus_enums_unit corpus_enums_program 1000
    ^(rejected_case "enums" "getter_byte_out_of_range_panics") =
  (Diagnostic InvalidCompletion, NONE, [])
Proof
  CONV_TAC cv_eval
QED

Theorem reject_enums_struct_field_byte_out_of_range_panics:
  source_execution bytecode_rejected_enums_code
    corpus_enums_unit corpus_enums_program 1000
    ^(rejected_case "enums" "struct_field_byte_out_of_range_panics") =
  (Diagnostic InvalidCompletion, NONE, [])
Proof
  CONV_TAC cv_eval
QED

Theorem reject_dirty_bits_bool_byte_2:
  source_execution bytecode_rejected_dirty_bits_code
    corpus_dirty_bits_unit corpus_dirty_bits_program 1000
    ^(rejected_case "dirty_bits" "bool_byte_2") =
  (Diagnostic InvalidCompletion, NONE, [])
Proof
  CONV_TAC cv_eval
QED

Theorem reject_dirty_bits_bool_byte_255:
  source_execution bytecode_rejected_dirty_bits_code
    corpus_dirty_bits_unit corpus_dirty_bits_program 1000
    ^(rejected_case "dirty_bits" "bool_byte_255") =
  (Diagnostic InvalidCompletion, NONE, [])
Proof
  CONV_TAC cv_eval
QED

Theorem reject_dirty_bits_unused_enum_byte_5:
  source_execution bytecode_rejected_dirty_bits_code
    corpus_dirty_bits_unit corpus_dirty_bits_program 1000
    ^(rejected_case "dirty_bits" "unused_enum_byte_5") =
  (Diagnostic InvalidCompletion, NONE, [])
Proof
  CONV_TAC cv_eval
QED

Theorem reject_dirty_bits_bool_abi_byte_2:
  source_execution bytecode_rejected_dirty_bits_code
    corpus_dirty_bits_unit corpus_dirty_bits_program 1000
    ^(rejected_case "dirty_bits" "bool_abi_byte_2") =
  (Diagnostic InvalidCompletion, NONE, [])
Proof
  CONV_TAC cv_eval
QED

Theorem reject_dirty_bits_enum_abi_byte_5:
  source_execution bytecode_rejected_dirty_bits_code
    corpus_dirty_bits_unit corpus_dirty_bits_program 1000
    ^(rejected_case "dirty_bits" "enum_abi_byte_5") =
  (Diagnostic InvalidCompletion, NONE, [])
Proof
  CONV_TAC cv_eval
QED

Theorem reject_dirty_bits_dynamic_bool_copy_byte_2:
  source_execution bytecode_rejected_dirty_bits_code
    corpus_dirty_bits_unit corpus_dirty_bits_program 1000
    ^(rejected_case "dirty_bits" "dynamic_bool_copy_byte_2") =
  (Diagnostic InvalidCompletion, NONE, [])
Proof
  CONV_TAC cv_eval
QED

Theorem reject_dirty_bits_fixed_bool_copy_byte_2:
  source_execution bytecode_rejected_dirty_bits_code
    corpus_dirty_bits_unit corpus_dirty_bits_program 1000
    ^(rejected_case "dirty_bits" "fixed_bool_copy_byte_2") =
  (Diagnostic InvalidCompletion, NONE, [])
Proof
  CONV_TAC cv_eval
QED

Theorem reject_dirty_bits_bool_array_abi_byte_2:
  source_execution bytecode_rejected_dirty_bits_code
    corpus_dirty_bits_unit corpus_dirty_bits_program 1000
    ^(rejected_case "dirty_bits" "bool_array_abi_byte_2") =
  (Diagnostic InvalidCompletion, NONE, [])
Proof
  CONV_TAC cv_eval
QED

Theorem reject_dirty_bits_fixed_bytes_dirty_padding:
  source_execution bytecode_rejected_dirty_bits_code
    corpus_dirty_bits_unit corpus_dirty_bits_program 1000
    ^(rejected_case "dirty_bits" "fixed_bytes_dirty_padding") =
  (Diagnostic InvalidCompletion, NONE, [])
Proof
  CONV_TAC cv_eval
QED

Theorem reject_udvt_wrap_cleans_underlying_bits:
  source_execution bytecode_rejected_udvt_code
    corpus_udvt_unit corpus_udvt_program 1000
    ^(rejected_case "udvt" "wrap_cleans_underlying_bits") =
  (Diagnostic InvalidCompletion, NONE, [])
Proof
  CONV_TAC cv_eval
QED


Theorem reject_typed_catches_unaligned_error_write_next_header:
  source_execution bytecode_rejected_typed_catches_code
    corpus_typed_catches_unit corpus_typed_catches_program 1000
    ^(rejected_case "typed_catches" "unaligned_error_write_next_header") =
  (Diagnostic InvalidCompletion, NONE, [])
Proof
  CONV_TAC cv_eval
QED
