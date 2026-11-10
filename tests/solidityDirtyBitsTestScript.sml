(* These calls are admitted source programs, but their non-canonical values
 * must fail closed. Compiler outcomes are checked independently by the ancestor;
 * an InvalidCompletion is never counted as differential agreement. *)
Theory solidityDirtyBitsTest
Ancestors solidityDifferential solidityDirtyBitsBytecodeTest
Libs solidityPrepareLib solidityBytecodeLib cv_transLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps [
  "../SOLIDITY_PIN",
  "../profiles/solc-0.8.37-via-ir-osaka.json",
  "../testdata/differential/fail_closed/inline_assembly.json",
  "../testdata/differential/expected/inline_assembly.json",
  "../testdata/differential/inline_assembly.sol",
  "../testdata/differential/fail_closed/storage.json",
  "../testdata/differential/expected/storage.json",
  "../testdata/differential/storage.sol",
  "../testdata/differential/fail_closed/storage_arrays.json",
  "../testdata/differential/expected/storage_arrays.json",
  "../testdata/differential/storage_arrays.sol",
  "../testdata/differential/fail_closed/enums.json",
  "../testdata/differential/expected/enums.json",
  "../testdata/differential/enums.sol",
  "../testdata/differential/fail_closed/dirty_bits.json",
  "../testdata/differential/expected/dirty_bits.json",
  "../testdata/differential/dirty_bits.sol",
  "../testdata/differential/fail_closed/udvt.json",
  "../testdata/differential/expected/udvt.json",
  "../testdata/differential/udvt.sol"
]

fun rejected_suite group =
  JSONParser.parseFile ("../testdata/differential/fail_closed/" ^ group ^ ".json");

fun prepare_rejected group =
  let
    val suite = rejected_suite group
    val prepared = #prepared (solidityPrepareLib.prepare_artifact
      {root = "..", path = "../" ^ solidityBytecodeLib.string_field suite "artifact",
       source = solidityBytecodeLib.string_field suite "source"})
    val failures = List.filter (isSome o #reason) (#functions prepared)
    val () = if null failures then () else
      raise Fail ("rejected test has unsupported functions: " ^
        String.concatWith "; " (map (fn {name, reason, ...} =>
          name ^ ": " ^ valOf reason) failures))
  in (#unit prepared, #program prepared) end;

fun rejected_case group name =
  let
    open solidityBytecodeLib
    val suite = rejected_suite group
    val c = valOf (List.find (fn c => string_field c "name" = name)
                    (array_field suite "cases"))
  in
    case_term “[] : byte list” {names = [], refs = “[] : (num # num list) list”}
      (call_input (fn () => “[] : byte list”) c) c
  end;

val (unit, program) = prepare_rejected "inline_assembly";

Definition rejected_inline_assembly_unit_def:
  rejected_inline_assembly_unit = ^unit
End

val () = cv_auto_trans rejected_inline_assembly_unit_def;

Definition rejected_inline_assembly_program_def:
  rejected_inline_assembly_program = ^program
End

val () = cv_auto_trans rejected_inline_assembly_program_def;

Theorem reject_inline_assembly_dirty_uint8_cleaned:
  source_execution bytecode_rejected_inline_assembly_code
    rejected_inline_assembly_unit rejected_inline_assembly_program 1000
    ^(rejected_case "inline_assembly" "dirty_uint8_cleaned") =
  (Diagnostic InvalidCompletion, NONE, [])
Proof
  CONV_TAC cv_eval
QED

Theorem reject_inline_assembly_dirty_bool_true:
  source_execution bytecode_rejected_inline_assembly_code
    rejected_inline_assembly_unit rejected_inline_assembly_program 1000
    ^(rejected_case "inline_assembly" "dirty_bool_true") =
  (Diagnostic InvalidCompletion, NONE, [])
Proof
  CONV_TAC cv_eval
QED

Theorem reject_inline_assembly_signed_negative_sign_extended:
  source_execution bytecode_rejected_inline_assembly_code
    rejected_inline_assembly_unit rejected_inline_assembly_program 1000
    ^(rejected_case "inline_assembly" "signed_negative_sign_extended") =
  (Diagnostic InvalidCompletion, NONE, [])
Proof
  CONV_TAC cv_eval
QED

Theorem reject_inline_assembly_signed_positive:
  source_execution bytecode_rejected_inline_assembly_code
    rejected_inline_assembly_unit rejected_inline_assembly_program 1000
    ^(rejected_case "inline_assembly" "signed_positive") =
  (Diagnostic InvalidCompletion, NONE, [])
Proof
  CONV_TAC cv_eval
QED

Theorem reject_inline_assembly_address_low_order:
  source_execution bytecode_rejected_inline_assembly_code
    rejected_inline_assembly_unit rejected_inline_assembly_program 1000
    ^(rejected_case "inline_assembly" "address_low_order") =
  (Diagnostic InvalidCompletion, NONE, [])
Proof
  CONV_TAC cv_eval
QED

Theorem reject_inline_assembly_write_back_cleans_before_checked_add:
  source_execution bytecode_rejected_inline_assembly_code
    rejected_inline_assembly_unit rejected_inline_assembly_program 1000
    ^(rejected_case "inline_assembly" "write_back_cleans_before_checked_add") =
  (Diagnostic InvalidCompletion, NONE, [])
Proof
  CONV_TAC cv_eval
QED

val (unit, program) = prepare_rejected "storage";

Definition rejected_storage_unit_def:
  rejected_storage_unit = ^unit
End

val () = cv_auto_trans rejected_storage_unit_def;

Definition rejected_storage_program_def:
  rejected_storage_program = ^program
End

val () = cv_auto_trans rejected_storage_program_def;

Theorem reject_storage_dirty_bool_reads_true:
  source_execution bytecode_rejected_storage_code
    rejected_storage_unit rejected_storage_program 1000
    ^(rejected_case "storage" "dirty_bool_reads_true") =
  (Diagnostic InvalidCompletion, NONE, [])
Proof
  CONV_TAC cv_eval
QED

val (unit, program) = prepare_rejected "storage_arrays";

Definition rejected_storage_arrays_unit_def:
  rejected_storage_arrays_unit = ^unit
End

val () = cv_auto_trans rejected_storage_arrays_unit_def;

Definition rejected_storage_arrays_program_def:
  rejected_storage_arrays_program = ^program
End

val () = cv_auto_trans rejected_storage_arrays_program_def;

Theorem reject_storage_arrays_dirty_bool_reads_true:
  source_execution bytecode_rejected_storage_arrays_code
    rejected_storage_arrays_unit rejected_storage_arrays_program 1000
    ^(rejected_case "storage_arrays" "dirty_bool_reads_true") =
  (Diagnostic InvalidCompletion, NONE, [])
Proof
  CONV_TAC cv_eval
QED

val (unit, program) = prepare_rejected "enums";

Definition rejected_enums_unit_def:
  rejected_enums_unit = ^unit
End

val () = cv_auto_trans rejected_enums_unit_def;

Definition rejected_enums_program_def:
  rejected_enums_program = ^program
End

val () = cv_auto_trans rejected_enums_program_def;

Theorem reject_enums_stored_byte_out_of_range_panics:
  source_execution bytecode_rejected_enums_code
    rejected_enums_unit rejected_enums_program 1000
    ^(rejected_case "enums" "stored_byte_out_of_range_panics") =
  (Diagnostic InvalidCompletion, NONE, [])
Proof
  CONV_TAC cv_eval
QED

Theorem reject_enums_mapping_byte_out_of_range_panics:
  source_execution bytecode_rejected_enums_code
    rejected_enums_unit rejected_enums_program 1000
    ^(rejected_case "enums" "mapping_byte_out_of_range_panics") =
  (Diagnostic InvalidCompletion, NONE, [])
Proof
  CONV_TAC cv_eval
QED

Theorem reject_enums_array_byte_out_of_range_panics:
  source_execution bytecode_rejected_enums_code
    rejected_enums_unit rejected_enums_program 1000
    ^(rejected_case "enums" "array_byte_out_of_range_panics") =
  (Diagnostic InvalidCompletion, NONE, [])
Proof
  CONV_TAC cv_eval
QED

Theorem reject_enums_packed_byte_out_of_range_panics:
  source_execution bytecode_rejected_enums_code
    rejected_enums_unit rejected_enums_program 1000
    ^(rejected_case "enums" "packed_byte_out_of_range_panics") =
  (Diagnostic InvalidCompletion, NONE, [])
Proof
  CONV_TAC cv_eval
QED

Theorem reject_enums_getter_byte_out_of_range_panics:
  source_execution bytecode_rejected_enums_code
    rejected_enums_unit rejected_enums_program 1000
    ^(rejected_case "enums" "getter_byte_out_of_range_panics") =
  (Diagnostic InvalidCompletion, NONE, [])
Proof
  CONV_TAC cv_eval
QED

Theorem reject_enums_struct_field_byte_out_of_range_panics:
  source_execution bytecode_rejected_enums_code
    rejected_enums_unit rejected_enums_program 1000
    ^(rejected_case "enums" "struct_field_byte_out_of_range_panics") =
  (Diagnostic InvalidCompletion, NONE, [])
Proof
  CONV_TAC cv_eval
QED

val (unit, program) = prepare_rejected "dirty_bits";

Definition rejected_dirty_bits_unit_def:
  rejected_dirty_bits_unit = ^unit
End

val () = cv_auto_trans rejected_dirty_bits_unit_def;

Definition rejected_dirty_bits_program_def:
  rejected_dirty_bits_program = ^program
End

val () = cv_auto_trans rejected_dirty_bits_program_def;

Theorem reject_dirty_bits_bool_byte_2:
  source_execution bytecode_rejected_dirty_bits_code
    rejected_dirty_bits_unit rejected_dirty_bits_program 1000
    ^(rejected_case "dirty_bits" "bool_byte_2") =
  (Diagnostic InvalidCompletion, NONE, [])
Proof
  CONV_TAC cv_eval
QED

Theorem reject_dirty_bits_bool_byte_255:
  source_execution bytecode_rejected_dirty_bits_code
    rejected_dirty_bits_unit rejected_dirty_bits_program 1000
    ^(rejected_case "dirty_bits" "bool_byte_255") =
  (Diagnostic InvalidCompletion, NONE, [])
Proof
  CONV_TAC cv_eval
QED

Theorem reject_dirty_bits_unused_enum_byte_5:
  source_execution bytecode_rejected_dirty_bits_code
    rejected_dirty_bits_unit rejected_dirty_bits_program 1000
    ^(rejected_case "dirty_bits" "unused_enum_byte_5") =
  (Diagnostic InvalidCompletion, NONE, [])
Proof
  CONV_TAC cv_eval
QED

Theorem reject_dirty_bits_bool_abi_byte_2:
  source_execution bytecode_rejected_dirty_bits_code
    rejected_dirty_bits_unit rejected_dirty_bits_program 1000
    ^(rejected_case "dirty_bits" "bool_abi_byte_2") =
  (Diagnostic InvalidCompletion, NONE, [])
Proof
  CONV_TAC cv_eval
QED

Theorem reject_dirty_bits_enum_abi_byte_5:
  source_execution bytecode_rejected_dirty_bits_code
    rejected_dirty_bits_unit rejected_dirty_bits_program 1000
    ^(rejected_case "dirty_bits" "enum_abi_byte_5") =
  (Diagnostic InvalidCompletion, NONE, [])
Proof
  CONV_TAC cv_eval
QED

Theorem reject_dirty_bits_dynamic_bool_copy_byte_2:
  source_execution bytecode_rejected_dirty_bits_code
    rejected_dirty_bits_unit rejected_dirty_bits_program 1000
    ^(rejected_case "dirty_bits" "dynamic_bool_copy_byte_2") =
  (Diagnostic InvalidCompletion, NONE, [])
Proof
  CONV_TAC cv_eval
QED

Theorem reject_dirty_bits_fixed_bool_copy_byte_2:
  source_execution bytecode_rejected_dirty_bits_code
    rejected_dirty_bits_unit rejected_dirty_bits_program 1000
    ^(rejected_case "dirty_bits" "fixed_bool_copy_byte_2") =
  (Diagnostic InvalidCompletion, NONE, [])
Proof
  CONV_TAC cv_eval
QED

Theorem reject_dirty_bits_bool_array_abi_byte_2:
  source_execution bytecode_rejected_dirty_bits_code
    rejected_dirty_bits_unit rejected_dirty_bits_program 1000
    ^(rejected_case "dirty_bits" "bool_array_abi_byte_2") =
  (Diagnostic InvalidCompletion, NONE, [])
Proof
  CONV_TAC cv_eval
QED

Theorem reject_dirty_bits_fixed_bytes_dirty_padding:
  source_execution bytecode_rejected_dirty_bits_code
    rejected_dirty_bits_unit rejected_dirty_bits_program 1000
    ^(rejected_case "dirty_bits" "fixed_bytes_dirty_padding") =
  (Diagnostic InvalidCompletion, NONE, [])
Proof
  CONV_TAC cv_eval
QED

val (unit, program) = prepare_rejected "udvt";

Definition rejected_udvt_unit_def:
  rejected_udvt_unit = ^unit
End

val () = cv_auto_trans rejected_udvt_unit_def;

Definition rejected_udvt_program_def:
  rejected_udvt_program = ^program
End

val () = cv_auto_trans rejected_udvt_program_def;

Theorem reject_udvt_wrap_cleans_underlying_bits:
  source_execution bytecode_rejected_udvt_code
    rejected_udvt_unit rejected_udvt_program 1000
    ^(rejected_case "udvt" "wrap_cleans_underlying_bits") =
  (Diagnostic InvalidCompletion, NONE, [])
Proof
  CONV_TAC cv_eval
QED

