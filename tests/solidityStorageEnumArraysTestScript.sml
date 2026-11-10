(* Noncanonical enum bytes remain outside source values even when the
 * compiler copies them without validating their membership. *)
Theory solidityStorageEnumArraysTest
Ancestors solidityCoreWf solidityDifferentialCorpus_storage_enum_arrays
Libs solidityBytecodeLib cv_transLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps [
  "../SOLIDITY_PIN",
  "../profiles/solc-0.8.37-via-ir-osaka.json",
  "../testdata/differential/storage_enum_arrays.sol",
  "../testdata/differential/expected/storage_enum_arrays.json",
  "../testdata/differential/fail_closed/storage_enum_arrays.json"
]

val () = solidityBytecodeLib.run_suite_file
  {root = "..", suite_file = "testdata/differential/fail_closed/storage_enum_arrays.json"}

fun rejected_case name =
  let
    open solidityBytecodeLib
    val suite = JSONParser.parseFile
      "../testdata/differential/fail_closed/storage_enum_arrays.json"
    val c = valOf (List.find (fn c => string_field c "name" = name)
                    (array_field suite "cases"))
  in
    case_term “[] : byte list” {names = [], refs = “[] : (num # num list) list”}
      (call_input (fn () => “[] : byte list”) c) c
  end;

Theorem dynamic_invalid_enum_copy:
  source_execution bytecode_rejected_storage_enum_arrays_code
    corpus_storage_enum_arrays_unit corpus_storage_enum_arrays_program 1000
    ^(rejected_case "dynamic_invalid_enum_copy") =
  (Diagnostic InvalidCompletion, NONE, [])
Proof
  CONV_TAC cv_eval
QED

Theorem fixed_invalid_enum_copy:
  source_execution bytecode_rejected_storage_enum_arrays_code
    corpus_storage_enum_arrays_unit corpus_storage_enum_arrays_program 1000
    ^(rejected_case "fixed_invalid_enum_copy") =
  (Diagnostic InvalidCompletion, NONE, [])
Proof
  CONV_TAC cv_eval
QED

Theorem dynamic_enum_array_abi_value:
  storage_abi_value (core_program_environment corpus_storage_enum_arrays_program)
    (differential_accounts [] [(0, 2); (w2n (mapping_slot [] 0w), 512)] 0x2000w)
    contract_address 0w (ArrayT (EnumT (AstId 5)) NONE) =
  INL (ListV [NumV 0; NumV 2],
       enc (Uint 256) (NumV 2) ++ enc (Uint 8) (NumV 0) ++ enc (Uint 8) (NumV 2))
Proof
  CONV_TAC cv_eval
QED

Theorem fixed_enum_array_abi_value:
  storage_abi_value (core_program_environment corpus_storage_enum_arrays_program)
    (differential_accounts [] [(2, 512)] 0x2000w)
    contract_address 2w (ArrayT (EnumT (AstId 5)) (SOME 2)) =
  INL (ListV [NumV 0; NumV 2], enc (Uint 8) (NumV 0) ++ enc (Uint 8) (NumV 2))
Proof
  CONV_TAC cv_eval
QED

Theorem enum_array_location_boundary:
  (∀length. ¬located_value_type (LocatedT MemoryLoc (ArrayT (EnumT (AstId 5)) length))) ∧
  (∀length. ¬located_value_type (LocatedT CalldataLoc (ArrayT (EnumT (AstId 5)) length)))
Proof
  simp[located_value_type_def, memory_object_type_def, byte_sequence_type_def] >>
  Cases >> simp[calldata_object_type_def, memory_object_type_def, byte_sequence_type_def]
QED
