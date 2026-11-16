(* Run by tools/run_differential_fuzz.py under `holbuild run-action`, or
 * `holbuild run` without a fleet; deliberately absent from the CI theory
 * graph. On the fleet the batch manifest is staged beside this script and
 * results go to the declared output; locally the manifest is named by the
 * environment and results go to stdout.
 *)
load "solidityDifferentialLib";
val () = Theory.new_theory "differentialFuzz";

val () =
  let
    val manifest = Option.getOpt (OS.Process.getEnv "DIFFERENTIAL_FUZZ_MANIFEST", "batch.json")
    fun run () = solidityDifferentialLib.run_fuzz_cases {root = ".", manifest = manifest}
  in
    case OS.Process.getEnv "HOLBUILD_RUN_OUTPUT_DIR" of
      SOME dir => solidityDifferentialLib.with_results
                    (OS.Path.concat (dir, "results.jsonl")) run
    | NONE => run ()
  end;
