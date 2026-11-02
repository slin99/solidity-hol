(* The three-way corpus run: the compiler's own Yul held to the expectations
 * the corpus theory already holds the elaborated core and the deployed
 * bytecode to. See yulDifferentialTheory and solidityDifferentialLib, and
 * docs/yul-differential.md for the report this produces.
 *
 * The Yul artifacts this reads are generated from the pinned compiler by
 * tools/run_yul_differential.py, which writes them here and then builds this
 * theory; they are not committed (the ASTs of the corpus's suites are tens of
 * megabytes). The importer's own tests use the small committed fixture under
 * testdata/yul/expected (tests/yulImportTest).
 *)
Theory yulDifferentialCorpus
Ancestors
  solidityDifferential yulAST yulState yulEvaluator yulDifferential
Libs
  solidityDifferentialLib yulImportLib

(* Read by holbuild's dependency scanner, which stages the corpus, its
 * artifacts and the generated Yul artifacts.
 *)
fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps [
  "../testdata/differential/corpus.json",
  "../testdata/differential/expected/calldata_bytes.json",
  "../SOLIDITY_PIN",
  "../profiles/solc-0.8.37-via-ir-osaka.json",
  "../profiles/solc-0.8.37-via-ir-osaka-optimized.json",
  "../testdata/frontend/expected/pure_core.json",
  "../testdata/differential/expected/scalars.json",
  "../testdata/differential/expected/control.json",
  "../testdata/differential/expected/calls.json",
  "../testdata/differential/expected/storage.json",
  "../testdata/differential/expected/mappings.json",
  "../testdata/differential/expected/storage_arrays.json",
  "../testdata/differential/expected/dynamic_storage_arrays.json",
  "../testdata/differential/expected/builtins.json",
  "../testdata/differential/expected/shadowed_builtins.json",
  "../testdata/differential/expected/storage_structs.json",
  "../testdata/differential/expected/storage_structs_top_level.json",
  "../testdata/differential/expected/token.json",
  "../testdata/differential/expected/context.json",
  "../testdata/differential/expected/fallback.json",
  "../testdata/differential/expected/receive.json",
  "../testdata/differential/expected/external.json",
  "../testdata/differential/expected/inheritance.json",
  "../testdata/differential/expected/inheritance_diamond.json",
  "../testdata/differential/expected/constructors.json",
  "../testdata/differential/expected/inherited_payable.json",
  "../testdata/differential/expected/initializers_only.json",
  "../testdata/yul/generated/calldata_bytes.ir.json",
  "../testdata/yul/generated/calldata_bytes.optimized.json",
  "../testdata/yul/generated/pure_core.ir.json",
  "../testdata/yul/generated/pure_core.optimized.json",
  "../testdata/yul/generated/scalars.ir.json",
  "../testdata/yul/generated/scalars.optimized.json",
  "../testdata/yul/generated/control.ir.json",
  "../testdata/yul/generated/control.optimized.json",
  "../testdata/yul/generated/calls.ir.json",
  "../testdata/yul/generated/calls.optimized.json",
  "../testdata/yul/generated/storage.ir.json",
  "../testdata/yul/generated/storage.optimized.json",
  "../testdata/yul/generated/mappings.ir.json",
  "../testdata/yul/generated/mappings.optimized.json",
  "../testdata/yul/generated/storage_arrays.ir.json",
  "../testdata/yul/generated/storage_arrays.optimized.json",
  "../testdata/yul/generated/dynamic_storage_arrays.ir.json",
  "../testdata/yul/generated/dynamic_storage_arrays.optimized.json",
  "../testdata/yul/generated/builtins.ir.json",
  "../testdata/yul/generated/builtins.optimized.json",
  "../testdata/yul/generated/shadowed_builtins.ir.json",
  "../testdata/yul/generated/shadowed_builtins.optimized.json",
  "../testdata/yul/generated/storage_structs.ir.json",
  "../testdata/yul/generated/storage_structs.optimized.json",
  "../testdata/yul/generated/storage_structs_top_level.ir.json",
  "../testdata/yul/generated/storage_structs_top_level.optimized.json",
  "../testdata/yul/generated/token.ir.json",
  "../testdata/yul/generated/token.optimized.json",
  "../testdata/yul/generated/context.ir.json",
  "../testdata/yul/generated/context.optimized.json",
  "../testdata/yul/generated/fallback.ir.json",
  "../testdata/yul/generated/fallback.optimized.json",
  "../testdata/yul/generated/receive.ir.json",
  "../testdata/yul/generated/receive.optimized.json",
  "../testdata/yul/generated/external.ir.json",
  "../testdata/yul/generated/external.optimized.json",
  "../testdata/yul/generated/inheritance.ir.json",
  "../testdata/yul/generated/inheritance.optimized.json",
  "../testdata/yul/generated/inheritance_diamond.ir.json",
  "../testdata/yul/generated/inheritance_diamond.optimized.json",
  "../testdata/yul/generated/constructors.ir.json",
  "../testdata/yul/generated/constructors.optimized.json",
  "../testdata/yul/generated/inherited_payable.ir.json",
  "../testdata/yul/generated/inherited_payable.optimized.json",
  "../testdata/yul/generated/initializers_only.ir.json",
  "../testdata/yul/generated/initializers_only.optimized.json",
]

val () = solidityDifferentialLib.run_three_way
  {root = "..", corpus = "testdata/differential/corpus.json",
   yul_root = "../testdata/yul/generated"}
