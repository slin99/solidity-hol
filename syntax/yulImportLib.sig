signature yulImportLib =
sig
  include Abbrev

  (* Which of the artifact's two Yul ASTs to read: irAst (the code generator's
   * output) or irOptimizedAst (after the Yul transformations, including the
   * ones solc runs with the optimizer off).
   *)
  datatype stage = Ir | IrOptimized

  (* An unknown node kind, an unknown builtin, or an object form the Yul
   * semantics does not read, naming the offending node.
   *)
  exception ImportError of string
  (* Missing or ill-typed required JSON fields. *)
  exception MalformedInput of string

  (* The runtime object's code as a yul_stmt list term, ready for run_yul,
   * from the irAst (Ir) or irOptimizedAst (IrOptimized) output of one
   * contract of a parsed Standard JSON output.
   *)
  val import_runtime : JSON.value -> string -> string -> stage -> term

  (* The same, from an artifact file written by tools/export_solc_artifacts.py.
   *)
  val import_runtime_artifact : string -> string -> string -> stage -> term
end
