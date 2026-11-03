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
   * on, with every scope lookup the body itself reads resolved to the value it
   * holds, and every call the body makes left as an `invoke_yul` application
   * rather than unfolded into the callee's body.  A call is a branch of that
   * tree like any other guard -- the rest of the body hangs off the outcomes
   * the evaluator gives a call -- so a leaf is the body's remainder with the
   * calls on its path made and the ones off it absent.
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

  (* What the conversion's own rules are still standing on in a term, as
   * (theory, name) constants: the block, the statements and the expressions it
   * takes apart, the frame and memory operations it declines, FLOOKUP, the
   * result helpers, and the calls it left folded.  An empty list means the
   * evaluation of the body is finished and nothing of it is left.
   *)
  val residues : term -> (string * string) list

  (* The residues a form may have: the call it left folded; the operations
   * whose input is a value nobody has -- the evaluator's own frame and memory
   * operations, FLOOKUP of a scope that came out of a callee's frame, and the
   * scope readers, which the conversion always unfolds but which have nothing
   * to unfold to over a scope a callee has not returned; and the result and
   * value helpers, which build a record out of a completion that is not a
   * literal.  A form with anything else in it -- a block, a statement or an
   * expression of the evaluator -- is one whose body evaluation stopped early,
   * which is what a test asks by requiring every residue of a form to be one of
   * these.
   *)
  val permitted_residues : (string * string) list

  (* Whether a form the conversion produced is closed: every residue in it is
   * one a form may have, so nothing in it is a step of the evaluation that is
   * still standing.  What is left is a term over the arguments and the entry
   * machine, the guards the body branched on, the calls it made, and the
   * operations that wait on a value nobody has.
   *)
  val is_closed_form : term -> bool

  (* Whether the evaluator's own equations have nothing left to do with a
   * term: running them over it again returns it unchanged.  The conversion's
   * output should be one, which is how a test says that no step of the
   * evaluation was left in a form, as opposed to a residue that is there on
   * purpose.
   *
   * `defs` are the same definitions yul_invoke_conv was given, and they are
   * left unfolded here too: a form names the table the caller gave it, and
   * folding that table back over the form would put the client's whole object
   * in it instead of judging the form.
   *)
  val is_fixed_point : thm list -> term -> bool
end
