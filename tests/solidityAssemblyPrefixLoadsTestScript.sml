(* A sub-word load whose surviving bytes run past the memory the block was
 * given: the compiler reads whatever lies there, while the source model
 * fails closed. *)
Theory solidityAssemblyPrefixLoadsTest
Ancestors solidityCoreWf solidityDifferentialCorpus_assembly_prefix_loads
Libs solidityBytecodeLib cv_transLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps [
  "../SOLIDITY_PIN",
  "../profiles/solc-0.8.37-via-ir-osaka.json",
  "../testdata/differential/assembly_prefix_loads.sol",
  "../testdata/differential/expected/assembly_prefix_loads.json",
  "../testdata/differential/fail_closed/assembly_prefix_loads.json"
]

val () = solidityBytecodeLib.run_suite_file
  {root = "..", suite_file = "testdata/differential/fail_closed/assembly_prefix_loads.json"}

fun rejected_case name =
  let
    open solidityBytecodeLib
    val suite = JSONParser.parseFile
      "../testdata/differential/fail_closed/assembly_prefix_loads.json"
    val c = valOf (List.find (fn c => string_field c "name" = name)
                    (array_field suite "cases"))
  in
    case_term {peer = “[] : byte list”, libraries = “[] : (address # byte list) list”}
      {names = [], refs = “[] : (num # num list) list”}
      (call_input (fn () => “[] : byte list”) c) c
  end;

(* shr(224, mload(p)) two bytes before the end of a 32-byte sequence keeps
 * two bytes past it. *)
Theorem four_past_end:
  source_execution bytecode_rejected_assembly_prefix_loads_code
    corpus_assembly_prefix_loads_unit corpus_assembly_prefix_loads_program 1000
    ^(rejected_case "four_past_end") =
  (Diagnostic InvalidCompletion, NONE, [])
Proof
  CONV_TAC cv_eval
QED
