signature solidityPrepareLib =
sig
  include Abbrev

  datatype failure = MalformedInput | UnsupportedImport | UnsupportedLowering
                   | SourceRejected | InvalidCore
  exception PreparationError of failure * string
  val failure_name : failure -> string

  (* A function calls reach, or a library function, with its node id, its
   * name and, if the frontend could not model it, why. *)
  type function_outcome = {id : int, name : string, reason : string option}

  (* The unit is the imported one with its unsupported functions marked: the
   * theorems are about it, and the program has no procedure for them. *)
  type prepared = {unit : term, program : term, source_valid : thm,
                   elaborates : thm, core_wf : thm,
                   functions : function_outcome list}

  (* Check artifact format, compiler identity, pinned profile and exact settings.
   * root contains SOLIDITY_PIN and profiles/solc-0.8.37-via-ir-osaka.json.
   *)
  val read_artifact : {root : string, path : string} -> JSON.value

  (* Checked semantic preparation for an already imported unit. The caller
   * owns compiler/profile provenance when using this lower-level entry point.
   * A function that fails to elaborate, also by calling an unsupported
   * function, is marked unsupported, until none does;
   * what remains must pass for the unit as a whole.
   * SourceRejected includes source-subset restrictions of valid_src_unit.
   * HOL evaluation failures propagate; they are never input rejections.
   *)
  val prepare_unit : term -> prepared

  (* Import one source from an artifact already checked by read_artifact.
   * Consumers of several sources import them all before semantic preparation.
   *)
  val import_unit : JSON.value -> string -> term

  (* The normal consumer entry point; retain the checked artifact for bytecode. *)
  val prepare_artifact : {root : string, path : string, source : string} ->
    {artifact : JSON.value, prepared : prepared}
end
