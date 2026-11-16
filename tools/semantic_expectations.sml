(* Run by tools/run_semantic_expectations.py under `holbuild run-action`, or
 * `holbuild run` without a fleet; deliberately absent from the CI theory
 * graph. On the fleet the batch manifest is staged beside this script and
 * results go to the declared output; locally the manifest is named by the
 * environment and results go to stdout.
 *)
load "solidityDifferentialLib";
val () = Theory.new_theory "semanticExpectations";

local
  val manifest =
    case OS.Process.getEnv "SEMANTIC_EXPECTATIONS_MANIFEST" of
      SOME m => m
    | NONE => "batch.json"
  (* run_expectations prints its results; on the fleet stdout is not kept. *)
  val output = Option.map
    (fn dir => TextIO.openOut (OS.Path.concat (dir, "results.jsonl")))
    (OS.Process.getEnv "HOLBUILD_RUN_OUTPUT_DIR")
  val stdout = TextIO.getOutstream TextIO.stdOut
  fun restore () =
    (TextIO.flushOut TextIO.stdOut;
     TextIO.setOutstream (TextIO.stdOut, stdout);
     Option.app TextIO.closeOut output)
  val () = Option.app
    (fn s => TextIO.setOutstream (TextIO.stdOut, TextIO.getOutstream s)) output
in
  val () = solidityDifferentialLib.run_expectations
             {root = ".", manifest = manifest}
           handle e => (restore (); raise e)
  val () = restore ()
end;
