(* Unfolding one Yul call without unfolding the calls its body makes. *)
signature yulConvLib =
sig
  include Abbrev

  (* `yul_invoke_conv defs` applied to
   *
   *   invoke_yul n fns "f" args m
   *
   * returns
   *
   *   |- invoke_yul n fns "f" args m = <form>
   *
   * with f's body evaluated: a case tree over the guards the body branches
   * on, with every scope lookup in it resolved to the value it holds, and
   * every call the body makes left as an `invoke_yul` application rather than
   * unfolded into the callee's body.  A call is a branch of that tree like any
   * other guard -- the rest of the body hangs off the outcomes the evaluator
   * gives a call -- so a leaf is the body's remainder with the calls on its
   * path made and the ones off it absent.
   *
   * `defs` are the definitions the table term needs to be folded: the name it
   * is bound to and the object behind it, in the usual arrangement.  They are
   * not used for the body's own evaluation, which sees only f's function.
   *
   * The table is read once per distinct fns term.
   *
   * The fuel must be a numeral.  Fuel is tested for zero on entering a call,
   * so a symbolic fuel would leave those tests in the form; a caller that
   * wants `invoke_yul n ...` at a symbolic n uses yulEvaluatorProps's fuel
   * stability at a numeral large enough for the run.
   *
   * Raises an error if fns does not bind that name, rather than returning a
   * form with the call still in it (a name the table does not have is the
   * caller's mistake, and `invoke_yul` would have answered YulInvalid).
   *)
  val yul_invoke_conv : thm list -> conv

  (* What the conversion did not get out of a form, as (theory, name)
   * constants: the steps of the evaluation that are still standing, of the
   * block, the statements and the expressions that the conversion takes, and
   * of the evaluator's own frame and memory operations that it does not.
   *)
  val residues : term -> (string * string) list

  (* The residues a form may have: the call it left folded, and the
   * evaluator's frame and memory operations.  A form with anything else in it
   * -- a block, a statement or an expression of the evaluator -- is one whose
   * body evaluation stopped early, which is what a test asks by requiring
   * every residue of a form to be one of these.
   *)
  val permitted_residues : (string * string) list

  (* Whether a form the conversion produced is closed: no residue in it, so
   * every part of it is a term over the arguments and the entry machine, the
   * guards the body branched on, and the calls it made.
   *)
  val is_closed_form : term -> bool

  (* Whether the evaluator's own equations have nothing left to do with a
   * term: running them over it again returns it unchanged.  The conversion's
   * output should be one, which is how a test says that no step of the
   * evaluation was left in a form, as opposed to a residue that is there on
   * purpose.
   *)
  val is_fixed_point : term -> bool
end
