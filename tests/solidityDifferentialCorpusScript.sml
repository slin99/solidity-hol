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
  "../testdata/differential/expected/calldata_bytes.json",
  "../testdata/differential/expected/memory_bytes.json",
  "../testdata/differential/expected/memory_arrays.json",
  "../testdata/differential/expected/calldata_arrays.json",
  "../testdata/differential/expected/calldata_arrays_peer.json",
  "../testdata/differential/expected/storage_array_values.json",
  "../testdata/differential/expected/storage_array_growth.json",
  "../testdata/differential/expected/super_calls.json",
  "../testdata/differential/expected/constants.json",
  "../testdata/differential/expected/immutables.json",
  "../testdata/differential/expected/immutables_creation.json",
  "../testdata/differential/expected/using_for.json",
  "../testdata/differential/expected/contract_types.json",
  "../testdata/differential/expected/enums.json",
  "../testdata/differential/expected/hashes.json",
  "../testdata/differential/expected/abi_encoding.json",
  "../testdata/differential/expected/interface_ids.json",
  "../testdata/differential/expected/named_arguments.json",
  "../testdata/differential/expected/struct_getters.json",
  "../testdata/differential/expected/conditionals.json",
  "../testdata/differential/expected/storage_bytes.json",
  "../testdata/differential/expected/dynamic_bytes.json",
  "../testdata/differential/expected/dynamic_bytes_peer.json",
  "../testdata/differential/expected/storage_bytes_aliases.json",
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
  "../testdata/differential/expected/initializers_only.json",
  "../testdata/differential/expected/imports.json",
  "../testdata/differential/expected/errors.json",
  "../testdata/differential/expected/type_bounds.json",
  "../testdata/differential/expected/oz_erc20.json",
  "../testdata/differential/expected/inline_assembly.json",
  "../testdata/differential/expected/modifiers.json",
  "../testdata/differential/expected/public_getters.json"
]

val () = run_corpus {root = "..", corpus = "testdata/differential/corpus.json"}
