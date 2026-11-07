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

(* Directories keep new suites and artifacts in the build's hashed,
 * staged inputs without a shared per-feature list. *)
fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps [
  "../SOLIDITY_PIN",
  "../profiles/solc-0.8.37-via-ir-osaka.json",
  "../testdata/differential/corpus.json",
  "../testdata/differential/suites",
  "../testdata/differential/expected",
  "../testdata/frontend/expected/pure_core.json",
  "../testdata/yul/generated"
]

val () = solidityDifferentialLib.run_three_way
  {root = "..", corpus = "testdata/differential/corpus.json",
   yul_root = "../testdata/yul/generated"}
