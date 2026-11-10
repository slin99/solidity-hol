(* Standalone entry point; deliberately absent from the CI theory graph. *)
load "solidityDifferentialLib";
val () = Theory.new_theory "semanticExpectations";
val () = solidityDifferentialLib.run_expectations
  {root = ".", manifest = valOf (OS.Process.getEnv "SEMANTIC_EXPECTATIONS_MANIFEST")};
