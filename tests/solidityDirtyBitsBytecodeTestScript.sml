(* Compiler outcomes for inputs deliberately outside the source model. *)
Theory solidityDirtyBitsBytecodeTest
Ancestors solidityBytecode
Libs solidityBytecodeLib

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
  "../testdata/differential/udvt.sol",
  "../testdata/differential/fail_closed/typed_catches.json",
  "../testdata/differential/expected/typed_catches.json",
  "../testdata/differential/expected/typed_catches_peer.json",
  "../testdata/differential/typed_catches.sol",
  "../testdata/differential/typed_catches_peer.sol"
]

val () = solidityBytecodeLib.run_suite_file
  {root = "..", suite_file = "testdata/differential/fail_closed/inline_assembly.json"}

val () = solidityBytecodeLib.run_suite_file
  {root = "..", suite_file = "testdata/differential/fail_closed/storage.json"}

val () = solidityBytecodeLib.run_suite_file
  {root = "..", suite_file = "testdata/differential/fail_closed/storage_arrays.json"}

val () = solidityBytecodeLib.run_suite_file
  {root = "..", suite_file = "testdata/differential/fail_closed/enums.json"}

val () = solidityBytecodeLib.run_suite_file
  {root = "..", suite_file = "testdata/differential/fail_closed/dirty_bits.json"}

val () = solidityBytecodeLib.run_suite_file
  {root = "..", suite_file = "testdata/differential/fail_closed/udvt.json"}


val () = solidityBytecodeLib.run_suite_file
  {root = "..", suite_file = "testdata/differential/fail_closed/typed_catches.json"}
