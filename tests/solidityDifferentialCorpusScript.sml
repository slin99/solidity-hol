(* The differential regression corpus, testdata/differential/corpus.json: every
 * case is a kernel-checked differential_agrees theorem relating the deployed
 * bytecode from the pinned compiler to the elaborated source. The build fails
 * if any suite or case does not agree. See docs/differential-testing.md.
 *)
Theory solidityDifferentialCorpus
Ancestors
  solidityDifferential
Libs
  solidityDifferentialLib

(* Directory patterns keep new suites and artifacts in the build's hashed,
 * staged inputs without a shared per-feature list. *)
fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps [
  "../SOLIDITY_PIN",
  "../profiles/solc-0.8.37-via-ir-osaka.json",
  "../testdata/differential/corpus.json",
  "../testdata/differential/suites/*.json",
  "../testdata/differential/expected/*.json",
  "../testdata/frontend/expected/pure_core.json"
]

val () = run_corpus {root = "..", corpus = "testdata/differential/corpus.json"}
