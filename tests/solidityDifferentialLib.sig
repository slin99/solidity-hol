signature solidityDifferentialLib =
sig
  include Abbrev

  (* Also write result lines to this file, closing it even if the run fails. *)
  val with_results : string -> (unit -> unit) -> unit

  (* Locate the runtime image in an artifact's initcode, rejecting ambiguity. *)
  val deployed_code_offset : JSON.value -> string -> string -> int

  (* Runs the corpus file at the given path, a
   * solidity-hol-differential-corpus-v1 file whose paths are relative to the
   * repository root; root is the path of that root from the current
   * directory. For each suite it imports the source unit from its artifact,
   * defines corpus_<suite>_unit, _program and _code, and proves
   * corpus_<suite>_elaborates and corpus_<suite>_program_wf. For each case it
   * proves <suite>_<case>, a differential_agrees theorem. Every result is
   * printed as a line "differential-result: " followed by JSON; if any suite
   * or case fails, it raises an error after all have run.
   *)
  val run_suite_file :
    {root : string, suite_file : string, fuel : IntInf.int, bytecode_theory : string} -> unit
  val run_yul_suite_file :
    {root : string, suite_file : string, yul_root : string} -> unit

  val run_corpus : {root : string, corpus : string} -> unit
  (* Standalone upstream expectation sweep; calls share deployment state.
   * The manifest and result protocol are owned by run_semantic_expectations.py.
   *)
  val run_expectations : {root : string, manifest : string} -> unit
  (* Fuzz cases: the manifest lists contracts, each a suite (name, artifact,
   * source, contract, fuel, optional peer) whose cases are generated calls
   * with a recorded expectation. Each contract is prepared once; each case's
   * source run is compared with its recording (fuzz_verdict) and, on a
   * difference or when marked "confirm", with Verifereum's run of the
   * bytecode, which is compared with the recording too (confirm_verdict).
   * Every result is a line "fuzz-result: " followed by JSON. *)
  val run_fuzz_cases : {root : string, manifest : string} -> unit
  (* The three-way run: for each suite it imports the Yul the pinned compiler
   * emitted for the suite's source, at the three stages the design separates
   * (the code generator's output; what the Yul transformations leave with the
   * optimizer off; the production build with the optimizer on), and for each
   * case it proves yul_<suite>_<case>_<stage>, a yul_agrees theorem relating
   * the Yul run to the bytecode run and to the case's expectation
   * (yulDifferentialTheory). yul_root is the directory the artifacts were
   * written to, with one <suite>.ir.json (holding irAst and irOptimizedAst)
   * and one <suite>.optimized.json per suite. Every result is printed as a
   * line "yul-differential-result: " followed by JSON; if any suite or case
   * fails, it raises an error after all have run.
   *)
  val run_three_way : {root : string, corpus : string, yul_root : string} -> unit

  (* Evaluate a Yul tree's cv encoding, including boolean literal cells. *)
  val yul_encoding_conv : conv
end
