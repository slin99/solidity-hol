signature solidityDifferentialLib =
sig
  include Abbrev

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
  val run_corpus : {root : string, corpus : string} -> unit
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
end
