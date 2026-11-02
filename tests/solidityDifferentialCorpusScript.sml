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

(* Read by holbuild's dependency scanner, which stages the corpus; it must list
 * the corpus and every artifact the corpus names, which
 * tools/run_differential.py checks.
 *)
fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps [
  "../testdata/differential/corpus.json",
  "../SOLIDITY_PIN",
  "../profiles/solc-0.8.37-via-ir-osaka.json",
  "../testdata/frontend/expected/pure_core.json",
  "../testdata/differential/expected/scalars.json",
  "../testdata/differential/expected/control.json",
  "../testdata/differential/expected/calls.json",
  "../testdata/differential/expected/storage.json",
  "../testdata/differential/expected/mappings.json",
  "../testdata/differential/expected/storage_arrays.json",
  "../testdata/differential/expected/dynamic_storage_arrays.json",
  "../testdata/differential/expected/storage_structs.json",
  "../testdata/differential/expected/storage_structs_top_level.json",
  "../testdata/differential/expected/builtins.json",
  "../testdata/differential/expected/shadowed_builtins.json",
  "../testdata/differential/expected/token.json",
  "../testdata/differential/expected/context.json",
  "../testdata/differential/expected/fallback.json",
  "../testdata/differential/expected/receive.json",
  "../testdata/differential/expected/external.json",
  "../testdata/differential/expected/inheritance.json",
  "../testdata/differential/expected/inheritance_diamond.json",
  "../testdata/differential/expected/constructors.json",
  "../testdata/differential/expected/inherited_payable.json",
  "../testdata/differential/expected/initializers_only.json"
]

val () = run_corpus {root = "..", corpus = "testdata/differential/corpus.json"}
