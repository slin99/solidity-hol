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
   * theorems are about it, and the program has no procedure for them. When
   * the program has no procedure for the creation either while every
   * constructor is supported, creation lists why, one blocker per line;
   * otherwise it is empty. unit_def and program_def define constants equal to
   * unit and program, already translated for cv_eval: a consumer that needs
   * its own constant defines it as one of these instead of translating the
   * whole term again. *)
  type prepared = {unit : term, program : term, source_valid : thm,
                   elaborates : thm, core_wf : thm,
                   unit_def : thm, program_def : thm,
                   functions : function_outcome list, creation : string list}

  (* Check artifact format, compiler identity, pinned profile and exact settings.
   * input.settings may also contain remappings: an array of strings with '='.
   * Optimized source artifacts require recorded unoptimized stack-depth errors.
   * root contains SOLIDITY_PIN and the two pinned profiles in profiles/.
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
  (* Import one source and prepare it. A rejection lists every blocker
   * found, one per line: the importer's, source validation's and what
   * fails to elaborate, by node id. *)
  val prepare_source : JSON.value -> string -> prepared

  (* The normal consumer entry point; retain the checked artifact for bytecode. *)
  val prepare_artifact : {root : string, path : string, source : string} ->
    {artifact : JSON.value, prepared : prepared}
  (* The same with the unit's contract given by name, if one is
   * (solidityImportLib.import_contract_artifact_unit_blockers). *)
  val prepare_contract_artifact :
    {root : string, path : string, source : string, contract : string option} ->
    {artifact : JSON.value, prepared : prepared}
end
