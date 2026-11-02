(* Elaboration of the normalised source AST (solidityImport) to the ordered
 * core, for the pinned profile solc-0.8.37-via-ir-osaka.
 *
 * Admitted: one contract, flattened along its bases, of functions over
 * elementary value types, with value-type state variables, storage structs,
 * scalar-key mappings and fixed/dynamic storage arrays, member/indexed scalar
 * reads and updates, array lengths, scalar push/pop and locals
 * (including tuple declarations with holes), internal calls with single or
 * multiple returns, explicit elementary conversions, literals, unary, binary,
 * comparison and short-circuit operators, simple and compound assignment to
 * locals and state variables, tuple assignment, ++ and --, if, while,
 * do-while, for, break, continue, return and unchecked blocks. Built-in
 * require/assert/revert admit boolean conditions and literal string messages.
 * Reads of msg.sender, msg.value, tx.origin, tx.gasprice, block members and
 * address(this), and emits of events with elementary parameters. An internal
 * call runs the most derived override of the function it names (call_table);
 * the functions no other overrides are elaborated, and the external and
 * public ones among them, receive and fallback form the dispatch table.
 * State-variable initializers, constructors and base-constructor arguments
 * (inheritance specifiers or constructor modifiers) form one creation
 * procedure.
 * Other string runtime operations and unsupported forms are rejected (NONE).
 *
 * Schedules, read from the compiler's IR for this profile (the ir output in
 * testdata/frontend/expected/pure_core.json) and checked against the compiled
 * bytecode by the differential tests:
 *  - binary operands, call and emit arguments and tuple components are
 *    evaluated left to right, each read of a local or a state variable being a copy taken
 *    when it is evaluated;
 *  - && and || evaluate their right operand only when needed;
 *  - x op= e evaluates e, then reads x, then writes x;
 *  - ++ and -- read, step (checked unless unchecked) and write back, yielding
 *    the new (prefix) or old (postfix) value;
 *  - a tuple assignment evaluates its right-hand side into fresh values, then
 *    writes the targets from right to left;
 *  - return values and declared variables are converted as the source types
 *    require;
 *  - creation evaluates the base-constructor arguments of each contract, most
 *    derived first, then, base first, runs each contract's state-variable
 *    initializers in declaration order and then its constructor body.
 *
 * Loops: a while condition is elaborated into the loop prelude, which reruns
 * on every iteration. for (init; c; next) body runs init once, then a loop
 * whose prelude runs next on every iteration but the first, then c; so
 * continue reaches next before the condition. do body while (c) is a loop
 * whose prelude evaluates c on every iteration but the first; so continue
 * reaches the condition. A first-iteration flag implements both.
 *
 * Elaboration uses fresh ids above every node id of the unit for temporaries
 * and capture targets. Its output is checked by wf_core_program; it is not
 * proved to be well formed in general.
 *)
Theory solidityElaborate
Ancestors
  solidityImport solidityEvaluator
Libs
  cv_transLib wordsLib

Datatype:
  elab_ctx = <|
    functions : (num # src_function) list;
    structs : src_struct list;
    events : (num # src_event) list;
    variables : (num # sol_type) list;
    state : (num # sol_type) list;
    returns : (num # sol_type) list;
    mode : arithmetic_mode
  |>
End

(* Values and conversions *)

(* The type of an elaborated value: an elementary type, an integer literal
 * (whose atom is its value), or several values.
 *)
Datatype:
  elab_type = ElabType sol_type | ElabLiteral | ElabTuple (sol_type list)
End

Definition bind_value_def:
  bind_value (n : num) ty op =
    ([DefineStmt (AstId n) (SingleType ty) op], BoundAtom (AstId n))
End

(* A value of type ty: integer literals stand for themselves, other types are
 * converted.
 *)
Definition coerce_def:
  coerce n ty a vt =
    case vt of
      ElabType src =>
        if src = ty then SOME (([], a), n)
        else SOME (bind_value n ty (ConvertOperation ty a), n + 1)
    | ElabLiteral => if is_integer_type ty then SOME (([], a), n) else NONE
    | ElabTuple _ => NONE
End

(* A copy of a local, so that later writes in the same expression do not
 * change the value already evaluated.
 *)
Definition snapshot_def:
  snapshot n a vt =
    case (a, vt) of
      (BoundAtom _, ElabType ty) =>
        (bind_value n ty (ConvertOperation ty a), n + 1)
    | _ => (([], a), n)
End

Definition assign_local_def:
  assign_local (t : num) x ty a =
    [CaptureBindingStmt (AstId t) (AstId x); WriteScalarStmt (AstId t) ty a]
End

(* A destination is a local binding or an already evaluated concrete reference.
 * Its prelude captures the location; reads and writes share this representation.
 *)
Datatype:
  destination = LocalDestination num sol_type | ReferenceDestination core_atom sol_type
End

Definition destination_type_def:
  (destination_type (LocalDestination _ ty) = ty) ∧
  (destination_type (ReferenceDestination _ ty) = ty)
End

Definition variable_destination_def:
  variable_destination ctx (n : num) x =
    case ALOOKUP ctx.variables x of
      SOME ty => SOME (([], LocalDestination x ty), n)
    | NONE =>
        (case ALOOKUP ctx.state x of
           SOME ty => SOME (([DefineStmt (AstId n) (ReferenceType ty)
                                (StateReferenceOperation (AstId x))],
                             ReferenceDestination (BoundAtom (AstId n)) ty), n + 1)
         | NONE => NONE)
End

Definition read_destination_def:
  (read_destination n (LocalDestination x ty) = (([], BoundAtom (AstId x)), n)) ∧
  (read_destination n (ReferenceDestination ref ty) =
    (bind_value n ty (ReadOperation ty ref), n + 1))
End

Definition write_destination_def:
  (write_destination t (LocalDestination x ty) a = assign_local t x ty a) ∧
  (write_destination (t : num) (ReferenceDestination ref ty) a =
    [CaptureValueStmt (AstId t) ref; WriteScalarStmt (AstId t) ty a])
End

(* Operators *)

Definition arithmetic_operator_def:
  arithmetic_operator op =
    if op = "+" then SOME AddOp
    else if op = "-" then SOME SubtractOp
    else if op = "*" then SOME MultiplyOp
    else if op = "/" then SOME DivideOp
    else if op = "%" then SOME RemainderOp
    else if op = "**" then SOME ExponentOp
    else if op = "<<" then SOME ShiftLeftOp
    else if op = ">>" then SOME ShiftRightOp
    else if op = "&" then SOME BitAndOp
    else if op = "|" then SOME BitOrOp
    else if op = "^" then SOME BitXorOp
    else NONE
End

(* The type of the right operand of an arithmetic operator on type ty. *)
Definition right_operand_type_def:
  right_operand_type op ty =
    if op = ExponentOp ∨ op = ShiftLeftOp ∨ op = ShiftRightOp then UintT 256
    else ty
End

(* The operator of a compound assignment such as "+=". *)
Definition compound_operator_def:
  compound_operator op =
    if op ≠ "=" ∧ isPREFIX "=" (REVERSE op) then
      arithmetic_operator (TAKE (LENGTH op - 1) op)
    else NONE
End

Definition compare_value_def:
  compare_value n ty cop x y =
    bind_value n BoolT (ScalarOperation ty UncheckedArithmetic cop [x; y])
End

Definition negate_value_def:
  negate_value n (ss, a) =
    let (ss', a') = bind_value n BoolT
                      (ScalarOperation BoolT UncheckedArithmetic BoolNotOp [a])
    in ((ss ++ ss', a'), n + 1)
End

(* Comparisons of two operands of type ty, by equality and less-than. *)
Definition comparison_def:
  comparison n ty op al ar =
    if op = "==" then SOME (compare_value n ty EqualOp al ar, n + 1)
    else if op = "!=" then
      SOME (negate_value (n + 1) (compare_value n ty EqualOp al ar))
    else if op = "<" then SOME (compare_value n ty LessThanOp al ar, n + 1)
    else if op = ">" then SOME (compare_value n ty LessThanOp ar al, n + 1)
    else if op = "<=" then
      SOME (negate_value (n + 1) (compare_value n ty LessThanOp ar al))
    else if op = ">=" then
      SOME (negate_value (n + 1) (compare_value n ty LessThanOp al ar))
    else NONE
End

Definition unary_operator_def:
  unary_operator op =
    if op = "-" then SOME NegateOp
    else if op = "~" then SOME BitNotOp
    else if op = "!" then SOME BoolNotOp
    else NONE
End

(* Whether an expression writes a local. *)
Definition expr_assigns_def:
  (expr_assigns (SrcAssignment _ _ _ _ _) ⇔ T) ∧
  (expr_assigns (SrcUnaryOperation _ op _ e _) ⇔
    op = "++" ∨ op = "--" ∨ expr_assigns e) ∧
  (expr_assigns (SrcBinaryOperation _ _ l r _ _) ⇔
    expr_assigns l ∨ expr_assigns r) ∧
  (expr_assigns (SrcTupleExpression _ cs _) ⇔ components_assign cs) ∧
  (expr_assigns (SrcFunctionCall _ callee args _) ⇔
    expr_assigns callee ∨ exprs_assign args) ∧
  (expr_assigns (SrcArrayMember _ _ root_expr _) ⇔ expr_assigns root_expr) ∧
  (expr_assigns (SrcBuiltinCall _ _ _ condition message _) ⇔
    (case condition of NONE => F | SOME c => expr_assigns c) ∨
    (case message of NONE => F | SOME m => expr_assigns m)) ∧
  (expr_assigns (SrcIndexAccess _ b i _) ⇔ expr_assigns b ∨ expr_assigns i) ∧
  (expr_assigns (SrcMemberAccess _ root_expr _ _) ⇔ expr_assigns root_expr) ∧
  (expr_assigns (SrcArrayLength _ root_expr _) ⇔ expr_assigns root_expr) ∧
  (expr_assigns (SrcTypeConversion _ _ e _) ⇔ expr_assigns e) ∧
  (expr_assigns (SrcExternalCall _ _ _ operands _) ⇔ exprs_assign operands) ∧
  (expr_assigns _ ⇔ F) ∧
  (components_assign [] ⇔ F) ∧
  (components_assign (NONE :: cs) ⇔ components_assign cs) ∧
  (components_assign (SOME e :: cs) ⇔
    expr_assigns e ∨ components_assign cs) ∧
  (exprs_assign [] ⇔ F) ∧
  (exprs_assign (e :: es) ⇔ expr_assigns e ∨ exprs_assign es)
End

(* The parameter and return types of a callee. *)
Definition callee_types_def:
  callee_types (f : src_function) =
    case (all_some (MAP variable_type f.fn_parameters),
          all_some (MAP variable_type f.fn_returns)) of
      (SOME params, SOME rets) => SOME (params, rets)
    | _ => NONE
End

(* The value of a call, as call_result_type types it. *)
Definition call_value_def:
  (call_value [] = ElabTuple []) ∧
  (call_value [ty] = ElabType ty) ∧
  (call_value tys = ElabTuple tys)
End

(* A high-level call of a view or pure function is a static call. *)
Definition external_call_value_def:
  external_call_value n mutability selector params rets ss target value args =
    let kind = if mutability = "view" ∨ mutability = "pure"
               then ExternalStaticCall else ExternalCall in
    ((ss ++ [DefineStmt (AstId n) (call_result_type rets)
               (ExternalCallOperation kind selector params rets target value
                  args)],
      BoundAtom (AstId n), call_value rets), n + 1)
End

(* The components of a multiple-value binding, as fresh bindings. *)
Definition tuple_components_def:
  (tuple_components n r i [] = ([], [], n)) ∧
  (tuple_components n r i (ty :: tys) =
    let (ss, a) = bind_value n ty (TupleComponentOperation i r) in
    let (ss', vs, n') = tuple_components (n + 1) r (i + 1) tys in
    (ss ++ ss', (a, ElabType ty) :: vs, n'))
End

(* Writes of values to the locals of a tuple, right to left. *)
Definition tuple_writes_def:
  (tuple_writes ctx n [] [] = SOME ([], n)) ∧
  (tuple_writes ctx n (NONE :: cs) (_ :: vs) = tuple_writes ctx n cs vs) ∧
  (tuple_writes ctx n (SOME (SrcIdentifier _ _ x _) :: cs) ((a, vt) :: vs) =
    case tuple_writes ctx n cs vs of
      SOME (ws, n1) =>
        (case variable_destination ctx n1 x of
           SOME ((ls, target), n2) =>
             (case coerce n2 (destination_type target) a vt of
                SOME ((ss, a'), n3) =>
                  SOME (ws ++ ls ++ ss ++ write_destination n3 target a', n3 + 1)
              | NONE => NONE)
         | NONE => NONE)
    | NONE => NONE) ∧
  (tuple_writes ctx n _ _ = NONE)
End

(* Snapshots of the bound values of a tuple right-hand side. *)
Definition snapshot_values_def:
  (snapshot_values n [] = ([], [], n)) ∧
  (snapshot_values n ((a, vt) :: vs) =
    case snapshot n a vt of
      ((ss, a'), n') =>
        case snapshot_values n' vs of
          (ss', vs', n'') => (ss ++ ss', (a', vt) :: vs', n''))
End

(* Error(string): one dynamic ABI argument, encoded from literal bytes only. *)
Definition error_string_data_def:
  error_string_data value =
    let bytes = MAP (λc. n2w (ORD c) : byte) value in
    [0x08w; 0xc3w; 0x79w; 0xa0w] ++ num_to_bytes 32 32 ++
    num_to_bytes 32 (LENGTH bytes) ++ bytes ++
    REPLICATE ((32 - LENGTH bytes MOD 32) MOD 32) 0w
End

Definition builtin_failure_def:
  builtin_failure builtin message =
    if builtin = AssertBuiltin then PanicStmt 1 else
    RevertStmt (ConstantAtom (BytesValue
      (case message of NONE => []
       | SOME m => case literal_message m of
           SOME value => error_string_data value
         | NONE => [])))
End

(* Expressions: statements computing a value, the value as an atom, and its
 * decoded type. Multiple values (tuples and calls with several returns) are
 * elaborated by elab_values.
 *)
Definition elab_expr_def:
  (elab_expr ctx n expression =
    case expression of
      SrcIdentifier _ _ x _ =>
        (case variable_destination ctx n x of
           SOME ((ls, target), n1) =>
             let ty = destination_type target in
             if ¬is_elementary_type ty then NONE else
             let (read, n2) = read_destination n1 target in
             let (ss, a) = read in
             SOME ((ls ++ ss, a, ElabType ty), n2)
         | NONE => NONE)
    | SrcArrayLength _ root_expr _ =>
        (case elab_location ctx n root_expr of
           SOME ((ss, _, ArrayT _ (SOME length)), n1) =>
             SOME ((ss, ConstantAtom (IntegerValue (&length)),
                    ElabType (UintT 256)), n1)
         | SOME ((ss, ref, ArrayT _ NONE), n1) =>
             let (rs, a) = bind_value n1 (UintT 256) (ArrayLengthOperation ref) in
             SOME ((ss ++ rs, a, ElabType (UintT 256)), n1 + 1)
         | _ => NONE)
    | SrcLiteral _ kind value tid =>
        (if kind = "bool" then
           SOME (([], ConstantAtom (BoolValue (value = "true")), ElabType BoolT), n)
         else
           case identifier_integer tid of
             SOME i => SOME (([], ConstantAtom (IntegerValue i), ElabLiteral), n)
           | NONE => NONE)
    | SrcMemberAccess _ _ _ _ =>
        (case elab_location ctx n expression of
           SOME ((ss, ref, ty), n1) =>
             if is_elementary_type ty then
               let (rs, a) = bind_value n1 ty (ReadOperation ty ref) in
               SOME ((ss ++ rs, a, ElabType ty), n1 + 1)
             else NONE
         | NONE => NONE)
    | SrcIndexAccess info root_expr index tid =>
        (case elab_location ctx n expression of
           SOME ((ss, ref, ty), n1) =>
             if is_elementary_type ty then
               let (rs, a) = bind_value n1 ty (ReadOperation ty ref) in
               SOME ((ss ++ rs, a, ElabType ty), n1 + 1)
             else NONE
         | NONE => NONE)
    | SrcUnaryOperation _ op prefix e tid =>
        (if op = "++" ∨ op = "--" then
           case elab_destination ctx n e of
             SOME ((ls, target), n1) =>
               let ty = destination_type target in
               let (read, n2) = read_destination n1 target in
               let (rs, cur) = read in
               let (old, n3) = if prefix then (([], cur), n2)
                               else snapshot n2 cur (ElabType ty) in
               let (ss, old_atom) = old in
               let (step, new_atom) = bind_value n3 ty
                 (ScalarOperation ty ctx.mode
                   (if op = "++" then AddOp else SubtractOp)
                   [cur; ConstantAtom (IntegerValue 1)]) in
               SOME ((ls ++ rs ++ ss ++ step ++
                        write_destination (n3 + 1) target new_atom,
                      (if prefix then new_atom else old_atom), ElabType ty), n3 + 2)
           | NONE => NONE
         else
           case (unary_operator op, identifier_type tid, elab_expr ctx n e) of
             (SOME uop, SOME ty, SOME ((ss, a, vt), n')) =>
               (case coerce n' ty a vt of
                  SOME ((cs, a'), n'') =>
                    let (ss', v) = bind_value n'' ty
                                     (ScalarOperation ty ctx.mode uop [a']) in
                    SOME ((ss ++ cs ++ ss', v, ElabType ty), n'' + 1)
                | NONE => NONE)
           | _ => NONE)
    | SrcBinaryOperation _ op l r common tid =>
        (case (identifier_type common, elab_expr ctx n l) of
           (SOME ty, SOME ((sl, al, vl), n1)) =>
             if op = "&&" ∨ op = "||" then
               (case coerce n1 BoolT al vl of
                  SOME ((cl, al'), n2) =>
                    (case elab_expr ctx (n2 + 2) r of
                       SOME ((sr, ar, vr), n3) =>
                         (case coerce n3 BoolT ar vr of
                            SOME ((cr, ar'), n4) =>
                              let (rs, res) =
                                bind_value n2 BoolT (ConvertOperation BoolT al') in
                              let rhs = sr ++ cr ++
                                        assign_local (n2 + 1) n2 BoolT ar' in
                              SOME ((sl ++ cl ++ rs ++
                                     [if op = "&&" then IfStmt res rhs []
                                      else IfStmt res [] rhs],
                                     res, ElabType BoolT), n4)
                          | NONE => NONE)
                     | NONE => NONE)
                | NONE => NONE)
             else
               (* flat let patterns: nested ones do not cv-translate here *)
               let (copied, n2) =
                 if expr_assigns r then snapshot n1 al vl else (([], al), n1) in
               let (sl', al') = copied in
               (case elab_expr ctx n2 r of
                  SOME ((sr, ar, vr), n3) =>
                    (case arithmetic_operator op of
                       SOME aop =>
                         (case coerce n3 ty al' vl of
                            SOME ((cl, al''), n4) =>
                              (case coerce n4 (right_operand_type aop ty) ar vr of
                                 SOME ((cr, ar'), n5) =>
                                   let (ss, v) = bind_value n5 ty
                                                   (ScalarOperation ty ctx.mode aop
                                                      [al''; ar']) in
                                   SOME ((sl ++ sl' ++ sr ++ cl ++ cr ++ ss, v,
                                          ElabType ty), n5 + 1)
                               | NONE => NONE)
                          | NONE => NONE)
                     | NONE =>
                         (case coerce n3 ty al' vl of
                            SOME ((cl, al''), n4) =>
                              (case coerce n4 ty ar vr of
                                 SOME ((cr, ar'), n5) =>
                                   (case comparison n5 ty op al'' ar' of
                                      SOME ((ss, v), n6) =>
                                        SOME ((sl ++ sl' ++ sr ++ cl ++ cr ++ ss, v,
                                               ElabType BoolT), n6)
                                    | NONE => NONE)
                               | NONE => NONE)
                          | NONE => NONE))
                | NONE => NONE)
         | _ => NONE)
    | SrcAssignment _ op lhs rhs tid =>
        (case lhs of
           SrcTupleExpression _ cs _ =>
             (if op = "=" then
                case elab_values ctx n rhs of
                  SOME ((sr, vs), n1) =>
                    let (ss, vs', n2) = snapshot_values n1 vs in
                    (case tuple_writes ctx n2 cs vs' of
                       SOME (ws, n3) =>
                         SOME ((sr ++ ss ++ ws, ConstantAtom (BoolValue F),
                                ElabTuple []), n3)
                     | NONE => NONE)
                | NONE => NONE
              else NONE)
         | _ =>
             (case elab_expr ctx n rhs of
                SOME ((sr, ar, vr), n1) =>
                  let (copied, n2) = case lhs of
                      SrcIdentifier _ _ _ _ => (([], ar), n1)
                    | _ => snapshot n1 ar vr in
                  let (sc, ar') = copied in
                  (case elab_destination ctx n2 lhs of
                     SOME ((ls, target), n3) =>
                       let ty = destination_type target in
                       if op = "=" then
                         (case coerce n3 ty ar' vr of
                            SOME ((cr, a), n4) =>
                              SOME ((sr ++ sc ++ ls ++ cr ++
                                       write_destination n4 target a,
                                     a, ElabType ty), n4 + 1)
                          | NONE => NONE)
                       else
                         (case compound_operator op of
                            SOME aop =>
                              (case coerce n3 (right_operand_type aop ty) ar' vr of
                                 SOME ((cr, a), n4) =>
                                   let (read, n5) = read_destination n4 target in
                                   let (rs, cur) = read in
                                   let (step, v) = bind_value n5 ty
                                     (ScalarOperation ty ctx.mode aop [cur; a]) in
                                   SOME ((sr ++ sc ++ ls ++ cr ++ rs ++ step ++
                                            write_destination (n5 + 1) target v,
                                          v, ElabType ty), n5 + 2)
                               | NONE => NONE)
                          | NONE => NONE)
                   | NONE => NONE)
              | NONE => NONE))
    | SrcTupleExpression _ [SOME e] _ =>
        (elab_expr ctx n e)
    | SrcTupleExpression _ _ _ =>
        (NONE)
    | SrcArrayMember _ _ _ _ => NONE
    | SrcFunctionCall _ callee args _ =>
        (case callee of
           SrcArrayMember _ member root_expr _ =>
             (case elab_location ctx n root_expr of
                SOME ((ss, ref, ArrayT element NONE), n1) =>
                  if member = "push" then
                    (case args of
                       [] =>
                         let target = BoundAtom (AstId n1) in
                         let (rs, a) = bind_value (n1 + 1) element
                                         (ReadOperation element target) in
                         SOME ((ss ++ [DefineStmt (AstId n1) (ReferenceType element)
                                         (ArrayPushOperation ref NONE)] ++ rs,
                                a, ElabType element), n1 + 2)
                     | [arg] =>
                         (case elab_expr ctx n1 arg of
                            SOME ((sa, a, vt), n2) =>
                              (case coerce n2 element a vt of
                                 SOME ((cs, a'), n3) =>
                                   SOME ((ss ++ sa ++ cs ++
                                            [DefineStmt (AstId n3) (ReferenceType element)
                                               (ArrayPushOperation ref (SOME a'))],
                                          ConstantAtom (BoolValue F), ElabTuple []), n3 + 1)
                               | NONE => NONE)
                          | NONE => NONE)
                     | _ => NONE)
                  else if member = "pop" ∧ args = [] then
                    SOME ((ss ++ [DefineStmt (AstId n1) (ProductType [])
                                    (ArrayPopOperation ref)],
                           ConstantAtom (BoolValue F), ElabTuple []), n1 + 1)
                  else NONE
              | _ => NONE)
         | SrcIdentifier _ _ f _ =>
             (case ALOOKUP ctx.functions f of
                SOME callee =>
                  (case callee_types callee of
                     SOME (params, rets) =>
                       (case elab_args ctx n params args of
                          SOME ((sa, atoms), n1) =>
                            SOME ((sa ++ [DefineStmt (AstId n1) (call_result_type rets)
                                            (InternalCallOperation
                                               (AstId callee.fn_info.node_id) atoms)],
                                   BoundAtom (AstId n1), call_value rets), n1 + 1)
                        | NONE => NONE)
                   | NONE => NONE)
              | NONE => NONE)
         | _ => NONE)
    | SrcBuiltinCall _ _ builtin condition message _ =>
        (if ¬builtin_shape builtin condition message then NONE else
         let failure = builtin_failure builtin message in
         case condition of
           NONE => SOME (([failure;
             DefineStmt (AstId n) (ProductType []) (TupleOperation [])],
             BoundAtom (AstId n), ElabTuple []), n + 1)
         | SOME c =>
             (case elab_expr ctx n c of
                SOME ((ss, a, vt), n1) =>
                  (case coerce n1 BoolT a vt of
                     SOME ((cs, v), n2) =>
                       SOME ((ss ++ cs ++ [IfStmt v [] [failure];
                         DefineStmt (AstId n2) (ProductType []) (TupleOperation [])],
                         BoundAtom (AstId n2), ElabTuple []), n2 + 1)
                   | NONE => NONE)
              | NONE => NONE))
    | SrcExternalCall _ callee with_value operands _ =>
        (case (all_some (MAP variable_type callee.ext_parameters),
               all_some (MAP variable_type callee.ext_returns)) of
           (SOME params, SOME rets) =>
             (case elab_args ctx n
                     (AddressT NonpayableAddress ::
                      (if with_value then [UintT 256] else []) ++ params)
                     operands of
                SOME ((ss, t :: atoms), n1) =>
                  (case (with_value, atoms) of
                     (T, v :: args) =>
                       SOME (external_call_value n1 callee.ext_mutability
                               callee.ext_selector params rets ss t v args)
                   | (F, args) =>
                       SOME (external_call_value n1 callee.ext_mutability
                               callee.ext_selector params rets ss t
                               (ConstantAtom (IntegerValue 0)) args)
                   | _ => NONE)
              | _ => NONE)
         | _ => NONE)
    | SrcEnvironment _ f _ =>
        let (ss, a) = bind_value n (environment_type f) (EnvironmentOperation f) in
        SOME ((ss, a, ElabType (environment_type f)), n + 1)
    | SrcTypeConversion _ tn e _ =>
        (case (normalize_type_name tn, elab_expr ctx n e) of
           (SOME ty, SOME ((ss, a, vt), n1)) =>
             (case (vt, ty, a) of
                (ElabTuple _, _, _) => NONE
              | (ElabLiteral, AddressT _, ConstantAtom (IntegerValue i)) =>
                (* address(0): the literal is the address, as in solc *)
                if 0 ≤ i ∧ i < 2 ** 160 then
                  SOME ((ss, ConstantAtom (AddressValue (n2w (Num i))),
                         ElabType ty), n1)
                else NONE
              | _ =>
                let (cs, v) = bind_value n1 ty (ConvertOperation ty a) in
                SOME ((ss ++ cs, v, ElabType ty), n1 + 1))
         | _ => NONE)) ∧
  (* Arguments, converted to the parameter types. *)
  (elab_args ctx n [] [] = SOME (([], []), n)) ∧
  (elab_args ctx n (ty :: tys) (e :: es) =
    case elab_expr ctx n e of
      SOME ((ss, a, vt), n1) =>
        let (copied, n2) =
          if exprs_assign es then snapshot n1 a vt else (([], a), n1) in
        let (ss1, a1) = copied in
        (case coerce n2 ty a1 vt of
           SOME ((cs, a2), n3) =>
             (case elab_args ctx n3 tys es of
                SOME ((ss', as), n4) =>
                  SOME ((ss ++ ss1 ++ cs ++ ss', a2 :: as), n4)
              | NONE => NONE)
         | NONE => NONE)
    | NONE => NONE) ∧
  (elab_args ctx n _ _ = NONE) ∧
  (* Multiple values: tuple expressions, and calls with several returns. *)
  (elab_values ctx n e =
    case e of
      SrcTupleExpression _ cs _ =>
        (case cs of
           [SOME e'] => elab_values ctx n e'
         | _ => elab_components ctx n cs)
    | _ =>
      case elab_expr ctx n e of
        SOME ((ss, a, ElabTuple tys), n1) =>
          let (cs, vs, n2) = tuple_components n1 a 0 tys in
          SOME ((ss ++ cs, vs), n2)
      | SOME ((ss, a, vt), n1) => SOME ((ss, [(a, vt)]), n1)
      | NONE => NONE) ∧
  (elab_components ctx n [] = SOME (([], []), n)) ∧
  (elab_components ctx n (SOME e :: cs) =
    case elab_expr ctx n e of
      SOME ((ss, a, vt), n1) =>
        let (copied, n2) =
          if components_assign cs then snapshot n1 a vt else (([], a), n1) in
        let (ss1, a1) = copied in
        (case elab_components ctx n2 cs of
           SOME ((ss', vs), n3) =>
             SOME ((ss ++ ss1 ++ ss', (a1, vt) :: vs), n3)
         | NONE => NONE)
    | NONE => NONE) ∧
  (elab_components ctx n (NONE :: cs) = NONE) ∧
  (* Only state roots and indexed suffixes are storage locations. Index keys
   * are converted and consumed immediately, before later keys can mutate them.
   *)
  (elab_location ctx n e =
    case e of
      SrcIdentifier _ _ x _ =>
        (case ALOOKUP ctx.state x of
           SOME ty =>
             SOME (([DefineStmt (AstId n) (ReferenceType ty)
                       (StateReferenceOperation (AstId x))],
                    BoundAtom (AstId n), ty), n + 1)
         | NONE => NONE)
    | SrcMemberAccess _ root_expr member_id _ =>
        (case elab_location ctx n root_expr of
           SOME ((ss, ref, StructT (AstId id)), n1) =>
             (case source_struct_field ctx.structs id member_id of
                SOME ty =>
                  SOME ((ss ++
                    [DefineStmt (AstId n1) (ReferenceType ty)
                      (NavigateOperation ty ref (FieldNavigation (AstId member_id)))],
                    BoundAtom (AstId n1), ty), n1 + 1)
              | NONE => NONE)
         | _ => NONE)
    | SrcIndexAccess _ root_expr index _ =>
        (case elab_location ctx n root_expr of
           SOME ((ss, ref, MappingT key value), n1) =>
             (case elab_expr ctx n1 index of
                SOME ((si, a, vt), n2) =>
                  (case coerce n2 key a vt of
                     SOME ((cs, a'), n3) =>
                       SOME ((ss ++ si ++ cs ++
                              [DefineStmt (AstId n3) (ReferenceType value)
                                (NavigateOperation value ref (IndexNavigation a'))],
                              BoundAtom (AstId n3), value), n3 + 1)
                   | NONE => NONE)
              | NONE => NONE)
         | SOME ((ss, ref, ArrayT element _), n1) =>
             (case elab_expr ctx n1 index of
                SOME ((si, a, vt), n2) =>
                  (case coerce n2 (UintT 256) a vt of
                     SOME ((cs, a'), n3) =>
                       SOME ((ss ++ si ++ cs ++
                              [DefineStmt (AstId n3) (ReferenceType element)
                                (NavigateOperation element ref (IndexNavigation a'))],
                              BoundAtom (AstId n3), element), n3 + 1)
                   | NONE => NONE)
              | NONE => NONE)
         | _ => NONE)
    | SrcFunctionCall _ (SrcArrayMember _ member root_expr _) [] _ =>
        (if member ≠ "push" then NONE else
         case elab_location ctx n root_expr of
           SOME ((ss, ref, ArrayT element NONE), n1) =>
             SOME ((ss ++ [DefineStmt (AstId n1) (ReferenceType element)
                             (ArrayPushOperation ref NONE)],
                    BoundAtom (AstId n1), element), n1 + 1)
         | _ => NONE)
    | _ => NONE) ∧
  (elab_destination ctx n e =
    case e of
      SrcIdentifier _ _ x _ => variable_destination ctx n x
    | _ =>
        case elab_location ctx n e of
          SOME ((ss, ref, ty), n1) =>
            SOME ((ss, ReferenceDestination ref ty), n1)
        | NONE => NONE)
Termination
  WF_REL_TAC ‘measure (λx. case x of
     INL (ctx, n, e) => 3 * src_expr_size e + 2
   | INR (INL (ctx, n, tys, es)) => 3 * list_size src_expr_size es
   | INR (INR (INL (ctx, n, e))) => 3 * src_expr_size e + 3
   | INR (INR (INR (INL (ctx, n, cs)))) =>
       3 * list_size (option_size src_expr_size) cs
   | INR (INR (INR (INR (INL (ctx, n, e))))) => 3 * src_expr_size e + 1
   | INR (INR (INR (INR (INR (ctx, n, e))))) => 3 * src_expr_size e + 2)’ >>
  rw[solidityImportTheory.src_expr_size_def, listTheory.list_size_def,
     basicSizeTheory.option_size_def]
End

(* A boolean condition. *)
Definition elab_condition_def:
  elab_condition ctx n c =
    case elab_expr ctx n c of
      SOME ((ss, a, vt), n1) =>
        (case coerce n1 BoolT a vt of
           SOME ((cs, a'), n2) => SOME ((ss ++ cs, a'), n2)
         | NONE => NONE)
    | NONE => NONE
End

(* Values converted to a list of types, for returns and declarations. *)
Definition coerce_values_def:
  (coerce_values n [] [] = SOME ([], [], n)) ∧
  (coerce_values n (ty :: tys) ((a, vt) :: vs) =
    case coerce n ty a vt of
      SOME ((ss, a'), n1) =>
        (case coerce_values n1 tys vs of
           SOME (ss', as, n2) => SOME (ss ++ ss', a' :: as, n2)
         | NONE => NONE)
    | NONE => NONE) ∧
  (coerce_values n _ _ = NONE)
End

(* The variables of a declaration statement, defined from its values, which
 * are converted to the declared types; holes discard their values.
 *)
Definition declare_values_def:
  (declare_values ctx n [] [] = SOME ([], ctx, n)) ∧
  (declare_values ctx n (NONE :: ds) (_ :: vs) = declare_values ctx n ds vs) ∧
  (declare_values ctx n (SOME (v : src_variable) :: ds) ((a, vt) :: vs) =
    case variable_type v of
      SOME ty =>
        (case coerce n ty a vt of
           SOME ((cs, a'), n1) =>
             (case declare_values
                     (ctx with variables :=
                        (v.var_info.node_id, ty) :: ctx.variables)
                     n1 ds vs of
                SOME (ss, ctx', n2) =>
                  SOME (cs ++ [DefineStmt (AstId v.var_info.node_id)
                                 (SingleType ty) (ConvertOperation ty a')] ++
                        ss, ctx', n2)
              | NONE => NONE)
         | NONE => NONE)
    | NONE => NONE) ∧
  (declare_values ctx n _ _ = NONE)
End

Definition return_atoms_def:
  (return_atoms [] = []) ∧
  (return_atoms ((x, _) :: rs) = BoundAtom (AstId x) :: return_atoms rs)
End

(* A boolean flag set to T, and a write setting it to b. *)
Definition flag_def:
  flag (n : num) =
    DefineStmt (AstId n) (SingleType BoolT)
      (ConvertOperation BoolT (ConstantAtom (BoolValue T)))
End

Definition set_flag_def:
  set_flag (t : num) (n : num) a = assign_local t n BoolT a
End

(* Events: topic 0, the parameter types, and the arguments of EmitStmt. *)
Definition event_topic_def:
  event_topic (e : src_event) =
    if e.event_anonymous then NONE
    else SOME (word_of_bytes T (0w : bytes32) e.event_selector)
End

Definition event_parameter_def:
  event_parameter ((v : src_variable), (indexed : bool)) =
    OPTION_MAP (λty. (ty, indexed)) (variable_type v)
End

Definition emit_arguments_def:
  (emit_arguments ((ty, indexed) :: ps) (a :: as) =
    (ty, indexed, a) :: emit_arguments ps as) ∧
  (emit_arguments _ _ = [])
End

(* Statements; lists return the context after their declarations. Nested
 * blocks are spliced into the enclosing list: ids are unique, so the core
 * scopes need not mirror the source blocks.
 *)
Definition elab_stmts_def:
  (elab_stmts ctx n [] = SOME (([], ctx), n)) ∧
  (elab_stmts ctx n (st :: ss) =
    case elab_stmt ctx n st of
      SOME ((cs, ctx'), n1) =>
        (case elab_stmts ctx' n1 ss of
           SOME ((cs', ctx''), n2) => SOME ((cs ++ cs', ctx''), n2)
         | NONE => NONE)
    | NONE => NONE) ∧
  (elab_stmt ctx n (SrcBlock _ ss) =
    case elab_stmts ctx n ss of
      SOME ((cs, _), n1) => SOME ((cs, ctx), n1)
    | NONE => NONE) ∧
  (elab_stmt ctx n (SrcUncheckedBlock _ ss) =
    case elab_stmts (ctx with mode := UncheckedArithmetic) n ss of
      SOME ((cs, _), n1) => SOME ((cs, ctx), n1)
    | NONE => NONE) ∧
  (elab_stmt ctx n (SrcExpressionStatement _ e) =
    case elab_expr ctx n e of
      SOME ((ss, _, _), n1) => SOME ((ss, ctx), n1)
    | NONE => NONE) ∧
  (elab_stmt ctx n (SrcVariableDeclarationStatement _ _ [SOME v] NONE) =
    case variable_type v of
      SOME ty =>
        (case default_elementary ty of
           SOME d =>
             SOME (([DefineStmt (AstId v.var_info.node_id) (SingleType ty)
                       (ConvertOperation ty (ConstantAtom d))],
                    ctx with variables :=
                      (v.var_info.node_id, ty) :: ctx.variables), n)
         | NONE => NONE)
    | NONE => NONE) ∧
  (elab_stmt ctx n (SrcVariableDeclarationStatement _ _ decls (SOME e)) =
    case elab_values ctx n e of
      SOME ((ss, vs), n1) =>
        (case declare_values ctx n1 decls vs of
           SOME (ds, ctx', n2) => SOME ((ss ++ ds, ctx'), n2)
         | NONE => NONE)
    | NONE => NONE) ∧
  (elab_stmt ctx n (SrcVariableDeclarationStatement _ _ _ _) = NONE) ∧
  (elab_stmt ctx n (SrcIfStatement _ c t e) =
    case elab_condition ctx n c of
      SOME ((cs, a), n1) =>
        (case elab_stmt ctx n1 t of
           SOME ((ts, _), n2) =>
             (case e of
                NONE => SOME ((cs ++ [IfStmt a ts []], ctx), n2)
              | SOME e =>
                  (case elab_stmt ctx n2 e of
                     SOME ((es, _), n3) =>
                       SOME ((cs ++ [IfStmt a ts es], ctx), n3)
                   | NONE => NONE))
         | NONE => NONE)
    | NONE => NONE) ∧
  (elab_stmt ctx n (SrcWhileStatement _ c bd) =
    case elab_condition ctx n c of
      SOME ((cs, a), n1) =>
        (case elab_stmt ctx n1 bd of
           SOME ((bs, _), n2) => SOME (([WhileStmt cs a bs], ctx), n2)
         | NONE => NONE)
    | NONE => NONE) ∧
  (elab_stmt ctx n (SrcDoWhileStatement _ bd c) =
    (* n: first-iteration flag; n + 1: condition result; n + 2, n + 3: targets *)
    case elab_condition ctx (n + 4) c of
      SOME ((cs, a), n1) =>
        (case elab_stmt ctx n1 bd of
           SOME ((bs, _), n2) =>
             SOME (([flag n; flag (n + 1);
                     WhileStmt
                       ([IfStmt (BoundAtom (AstId n)) []
                           (cs ++ set_flag (n + 2) (n + 1) a)] ++
                        set_flag (n + 3) n (ConstantAtom (BoolValue F)))
                       (BoundAtom (AstId (n + 1))) bs], ctx), n2)
         | NONE => NONE)
    | NONE => NONE) ∧
  (elab_stmt ctx n (SrcForStatement _ ini c nx bd) =
    case elab_for_init ctx n ini of
      SOME ((is, ctx1), n1) =>
        (* n1: first-iteration flag; n1 + 1: its target *)
        (case (case c of
                 NONE => SOME (([], ConstantAtom (BoolValue T)), n1 + 2)
               | SOME c => elab_condition ctx1 (n1 + 2) c) of
           SOME ((cs, a), n2) =>
             (case elab_for_init ctx1 n2 nx of
                SOME ((ns, _), n3) =>
                  (case elab_stmt ctx1 n3 bd of
                     SOME ((bs, _), n4) =>
                       SOME ((is ++
                              [flag n1;
                               WhileStmt
                                 ([IfStmt (BoundAtom (AstId n1)) [] ns] ++
                                  set_flag (n1 + 1) n1
                                    (ConstantAtom (BoolValue F)) ++ cs)
                                 a bs], ctx), n4)
                   | NONE => NONE)
              | NONE => NONE)
         | NONE => NONE)
    | NONE => NONE) ∧
  (elab_stmt ctx n (SrcBreak _) = SOME (([BreakStmt], ctx), n)) ∧
  (elab_stmt ctx n (SrcContinue _) = SOME (([ContinueStmt], ctx), n)) ∧
  (elab_stmt ctx n (SrcReturn _ _ NONE) =
    SOME (([ReturnStmt (return_atoms ctx.returns)], ctx), n)) ∧
  (elab_stmt ctx n (SrcReturn _ _ (SOME e)) =
    case elab_values ctx n e of
      SOME ((ss, vs), n1) =>
        (case coerce_values n1 (MAP SND ctx.returns) vs of
           SOME (cs, as, n2) => SOME ((ss ++ cs ++ [ReturnStmt as], ctx), n2)
         | NONE => NONE)
    | NONE => NONE) ∧
  (elab_stmt ctx n (SrcEmit _ ev args) =
    case ALOOKUP ctx.events ev of
      NONE => NONE
    | SOME e =>
        case all_some (MAP event_parameter e.event_parameters) of
          NONE => NONE
        | SOME ps =>
            case elab_args ctx n (MAP FST ps) args of
              SOME ((ss, as), n1) =>
                SOME ((ss ++ [EmitStmt (event_topic e) (emit_arguments ps as)],
                       ctx), n1)
            | NONE => NONE) ∧
  (* An optional for initialization or loop expression. *)
  (elab_for_init ctx n NONE = SOME (([], ctx), n)) ∧
  (elab_for_init ctx n (SOME st) = elab_stmt ctx n st)
Termination
  WF_REL_TAC ‘measure (λx. case x of
     INL (ctx, n, ss) => list_size src_stmt_size ss
   | INR (INL (ctx, n, st)) => src_stmt_size st
   | INR (INR (ctx, n, st)) => option_size src_stmt_size st)’ >>
  rw[solidityImportTheory.src_stmt_size_def, listTheory.list_size_def,
     basicSizeTheory.option_size_def]
End

(* Functions and units *)

Definition variable_binding_def:
  variable_binding (v : src_variable) =
    case variable_type v of
      SOME ty => SOME (v.var_info.node_id, ty)
    | NONE => NONE
End

Definition core_bindings_def:
  (core_bindings [] = []) ∧
  (core_bindings ((x, ty) :: bs) = (AstId x, ty) :: core_bindings bs)
End

(* A procedure, checked arithmetic by default; parameters and returns keep
 * their declaration ids.
 *)
Definition elab_function_def:
  elab_function structs events functions state n (f : src_function) =
    case (all_some (MAP variable_binding f.fn_parameters),
          all_some (MAP variable_binding f.fn_returns), f.fn_body) of
      (SOME ps, SOME rs, SrcBlock _ ss) =>
        (case elab_stmts <| functions := functions; structs := structs;
                            events := events; variables := ps ++ rs;
                            state := state; returns := rs;
                            mode := CheckedArithmetic |> n ss of
           SOME ((code, _), n1) =>
             SOME (<| procedure_id := AstId f.fn_info.node_id;
                      parameters := core_bindings ps;
                      return_bindings := core_bindings rs;
                      body := code |>, n1)
         | NONE => NONE)
    | _ => NONE
End

Definition elab_functions_def:
  (elab_functions structs events functions state n [] = SOME ([], n)) ∧
  (elab_functions structs events functions state n (f :: fs) =
    case elab_function structs events functions state n f of
      SOME (p, n1) =>
        (case elab_functions structs events functions state n1 fs of
           SOME (ps, n2) => SOME (p :: ps, n2)
         | NONE => NONE)
    | NONE => NONE)
End

(* The state variables at their layout entries, which a valid unit lists in
 * the same order.
 *)
Definition core_state_variables_def:
  (core_state_variables [] [] = SOME []) ∧
  (core_state_variables ((x, ty) :: vs) (e :: es) =
    case core_state_variables vs es of
      SOME cvs =>
        SOME (<| state_id := AstId x; state_type := ty;
                 state_slot := n2w e.storage_slot;
                 state_offset := e.storage_offset |> :: cvs)
    | NONE => NONE) ∧
  (core_state_variables _ _ = NONE)
End

Definition elab_type_declarations_def:
  elab_type_declarations structs =
    all_some (MAP (λs.
      OPTION_MAP (λfields. (AstId s.struct_info.node_id, StructDeclaration fields))
        (all_some (MAP (λv. OPTION_MAP (λty. (AstId v.var_info.node_id, ty))
                           (field_variable_type v)) s.struct_members))) structs)
End

Definition elab_struct_layouts_def:
  (elab_struct_layouts [] = SOME []) ∧
  (elab_struct_layouts (s :: ss) =
    case elab_struct_layouts ss of
      NONE => NONE
    | SOME layouts =>
        case s.struct_layout of
          NONE => SOME layouts
        | SOME (bytes, fields) =>
            case all_some (MAP (λv. OPTION_MAP (λty. (v.var_info.node_id, ty))
                               (field_variable_type v)) s.struct_members) of
              NONE => NONE
            | SOME types =>
                case core_state_variables types fields of
                  NONE => NONE
                | SOME cvs =>
                    SOME (<| struct_id := AstId s.struct_info.node_id;
                             struct_fields := cvs; struct_slots := bytes DIV 32 |>
                          :: layouts))
End

(* The dispatch table: the functions with a selector, which the compiler
 * gives exactly the external and public ones. *)
Definition external_functions_def:
  (external_functions [] = []) ∧
  (external_functions ((f : src_function) :: fs) =
    case f.fn_selector of
      SOME selector =>
        <| selector := selector; external_procedure := AstId f.fn_info.node_id;
           payable := (f.fn_mutability = "payable") |> :: external_functions fs
    | NONE => external_functions fs)
End

(* The receive or fallback function, and whether it is payable. *)
Definition special_function_def:
  (special_function kind [] = NONE) ∧
  (special_function kind ((f : src_function) :: fs) =
    if f.fn_kind = kind then
      SOME (AstId f.fn_info.node_id, f.fn_mutability = "payable")
    else special_function kind fs)
End

(* Creation: the order of the compiler's IR for this profile (its constructor
 * functions in testdata/differential/expected/constructors.json). First the
 * base constructor arguments, in evaluation order, each list with the
 * parameters of the giving base's constructor in scope, define the
 * parameters of the constructor they are given to. Then, base first, each
 * base's state variable initializers in declaration order, then its
 * constructor.
 *)
Definition define_parameters_def:
  (define_parameters ((x, ty) :: ps) (a :: as) =
    DefineStmt (AstId x) (SingleType ty) (ConvertOperation ty a) ::
    define_parameters ps as) ∧
  (define_parameters _ _ = [])
End

Definition elab_base_arguments_def:
  (elab_base_arguments ctx fs n [] = SOME ([], n)) ∧
  (elab_base_arguments ctx fs n ((x, b, args) :: rest) =
    case (constructor_parameters x fs, constructor_parameters b fs) of
      (SOME xps, SOME bps) =>
        (case elab_args (ctx with variables := xps) n (MAP SND bps) args of
           SOME ((ss, atoms), n1) =>
             (case elab_base_arguments ctx fs n1 rest of
                SOME (ss', n2) => SOME (ss ++ define_parameters bps atoms ++ ss', n2)
              | NONE => NONE)
         | NONE => NONE)
    | _ => NONE)
End

(* The initializers of the state variables base x declares. *)
Definition elab_initializers_def:
  (elab_initializers ctx n x inits [] = SOME ([], n)) ∧
  (elab_initializers ctx n x inits ((v : src_variable) :: vs) =
    case (if v.var_scope = x then ALOOKUP inits v.var_info.node_id else NONE) of
      NONE => elab_initializers ctx n x inits vs
    | SOME e =>
        case elab_expr ctx n
               (SrcAssignment v.var_info "="
                  (SrcIdentifier v.var_info v.var_name v.var_info.node_id
                     v.var_type_id) e v.var_type_id) of
          SOME ((ss, _, _), n1) =>
            (case elab_initializers ctx n1 x inits vs of
               SOME (ss', n2) => SOME (ss ++ ss', n2)
             | NONE => NONE)
        | NONE => NONE)
End

(* Bases, base first. *)
Definition elab_constructors_def:
  (elab_constructors ctx (c : src_contract) n [] = SOME ([], n)) ∧
  (elab_constructors ctx c n (x :: xs) =
    case elab_initializers ctx n x c.contract_initializers
           c.contract_state_variables of
      NONE => NONE
    | SOME (ss, n1) =>
        let call =
          case contract_constructor x c.contract_functions of
            NONE => []
          | SOME f =>
              [DefineStmt (AstId n1) (call_result_type [])
                 (InternalCallOperation (AstId f.fn_info.node_id)
                    (MAP (λv. BoundAtom (AstId v.var_info.node_id))
                       f.fn_parameters))] in
        case elab_constructors ctx c (n1 + 1) xs of
          SOME (ss', n2) => SOME (ss ++ call ++ ss', n2)
        | NONE => NONE)
End

(* The creation procedure takes the parameters of the contract's own
 * constructor. *)
Definition elab_creation_def:
  elab_creation ctx (c : src_contract) n =
    case (constructor_parameters c.contract_info.node_id c.contract_functions,
          elab_base_arguments ctx c.contract_functions n
            c.contract_base_arguments) of
      (SOME ps, SOME (sa, n1)) =>
        (case elab_constructors ctx c (n1 + 1) (REVERSE c.contract_bases) of
           SOME (sc, n2) =>
             SOME (<| procedure_id := AstId n1; parameters := core_bindings ps;
                      return_bindings := []; body := sa ++ sc |>, n2)
         | NONE => NONE)
    | _ => NONE
End

(* Whether the creation transaction may carry value. *)
Definition creation_payable_def:
  creation_payable (c : src_contract) ⇔
    case contract_constructor c.contract_info.node_id c.contract_functions of
      SOME f => f.fn_mutability = "payable"
    | NONE => F
End

(* Raw lowering of a valid unit of one contract, with fresh ids above its
 * node ids; the first live function is the entry procedure, or the creation
 * procedure when there is none. A SOME result is
 * not yet a checked program: consumers must establish wf_core_program
 * through solidityPrepareLib before execution.
 *)
Definition elaborate_unit_def:
  elaborate_unit (u : src_unit) =
    if ¬valid_src_unit u then NONE else
    case u.unit_contracts of
      [c] =>
        let fs = live_functions c.contract_functions in
        (case all_some (MAP variable_binding c.contract_state_variables) of
           NONE => NONE
         | SOME state =>
             case (elab_type_declarations c.contract_structs,
                   elab_struct_layouts c.contract_structs,
                   core_state_variables state c.contract_storage,
                   elab_functions c.contract_structs
                     (MAP (λe. (e.event_info.node_id, e)) c.contract_events)
                     (call_table c.contract_functions)
                     state (MAX_LIST (unit_ids u) + 1) fs) of
               (SOME decls, SOME layouts, SOME cvs, SOME (ps, n)) =>
                 (case elab_creation
                         <| functions := call_table c.contract_functions;
                            structs := c.contract_structs;
                            events := MAP (λe. (e.event_info.node_id, e))
                                        c.contract_events;
                            variables := []; state := state; returns := [];
                            mode := CheckedArithmetic |> c n of
                    NONE => NONE
                  | SOME (creation, _) =>
                 SOME <| procedures := ps ++ [creation]; state_variables := cvs;
                         struct_layouts := layouts; type_declarations := decls;
                         entry_procedure :=
                           (case ps of
                              p :: _ => p.procedure_id
                            | [] => creation.procedure_id);
                         external_functions :=
                           external_functions fs;
                         receive_procedure := OPTION_MAP FST
                           (special_function "receive" fs);
                         fallback_procedure :=
                           special_function "fallback" fs;
                         creation_procedure :=
                           SOME (creation.procedure_id, creation_payable c) |>)
             | _ => NONE)
    | _ => NONE
End

(* cv translation, so that units are elaborated by cv_eval. The mutually
 * recursive elaborators terminate on scaled cv sizes of their syntax.
 *)

val () = cv_auto_trans bind_value_def;
val () = cv_auto_trans coerce_def;
val () = cv_auto_trans snapshot_def;
val () = cv_auto_trans assign_local_def;
val () = cv_auto_trans variable_destination_def;
val () = cv_auto_trans destination_type_def;
val () = cv_auto_trans read_destination_def;
val () = cv_auto_trans write_destination_def;
val () = cv_auto_trans arithmetic_operator_def;
val () = cv_auto_trans right_operand_type_def;
val () = cv_auto_trans compound_operator_def;
val () = cv_auto_trans compare_value_def;
val () = cv_auto_trans negate_value_def;
val () = cv_auto_trans comparison_def;
val () = cv_auto_trans unary_operator_def;
val () = cv_auto_trans callee_types_def;
val () = cv_auto_trans call_value_def;
val () = cv_auto_trans tuple_components_def;
val () = cv_auto_trans tuple_writes_def;
val snapshot_values_pre_def =
  cv_auto_trans_pre "snapshot_values_pre" snapshot_values_def;

Theorem snapshot_values_pre[cv_pre,local]:
  ∀vs n. snapshot_values_pre n vs
Proof
  Induct >> simp[Once snapshot_values_pre_def] >> rw[] >> fs[]
QED

val () = cv_auto_trans_rec expr_assigns_def (
  WF_REL_TAC ‘measure (λx. case x of
                 INL e => cv_size e
               | INR (INL cs) => cv_size cs
               | INR (INR es) => cv_size es)’ >>
  cv_termination_tac
);

val () = cv_auto_trans error_string_data_def;
val () = cv_auto_trans builtin_failure_def;

val elab_expr_pre_def = cv_auto_trans_pre_rec
  "elab_expr_pre elab_args_pre elab_values_pre elab_components_pre elab_location_pre elab_destination_pre"
  elab_expr_def (
  WF_REL_TAC ‘measure (λx. case x of
     INL (ctx, n, e) => 3 * cv_size e + 2
   | INR (INL (ctx, n, tys, es)) => 3 * cv_size es
   | INR (INR (INL (ctx, n, e))) => 3 * cv_size e + 3
   | INR (INR (INR (INL (ctx, n, cs)))) => 3 * cv_size cs
   | INR (INR (INR (INR (INL (ctx, n, e))))) => 3 * cv_size e + 1
   | INR (INR (INR (INR (INR (ctx, n, e))))) => 3 * cv_size e + 2)’ >>
  cv_termination_tac
);

Theorem elab_expr_pre[cv_pre,local]:
  (∀ctx n v. elab_expr_pre ctx n v) ∧
  (∀ctx n tys es. elab_args_pre ctx n tys es) ∧
  (∀ctx n e. elab_values_pre ctx n e) ∧
  (∀ctx n cs. elab_components_pre ctx n cs) ∧
  (∀ctx n e. elab_location_pre ctx n e) ∧
  (∀ctx n e. elab_destination_pre ctx n e)
Proof
  ho_match_mp_tac elab_expr_ind >> rpt strip_tac
  >~ [‘elab_expr_pre ctx n expression’] >-
    (Cases_on ‘expression’ >>
     rule_assum_tac (SIMP_RULE (srw_ss()) []) >>
     simp_tac std_ss [Once elab_expr_pre_def] >>
     rw[] >> fs[]) >>
  simp_tac std_ss [Once elab_expr_pre_def] >> rw[] >> fs[]
QED

val () = cv_auto_trans elab_condition_def;
val () = cv_auto_trans
  (REWRITE_RULE [GSYM byteTheory.word_of_bytes_be_def] event_topic_def);
val () = cv_auto_trans event_parameter_def;
val () = cv_auto_trans emit_arguments_def;

val coerce_values_pre_def =
  cv_auto_trans_pre "coerce_values_pre" coerce_values_def;

Theorem coerce_values_pre[cv_pre,local]:
  ∀n tys vs. coerce_values_pre n tys vs
Proof
  ho_match_mp_tac coerce_values_ind >> rpt strip_tac >>
  simp[Once coerce_values_pre_def] >> rw[] >> fs[]
QED

val declare_values_pre_def =
  cv_auto_trans_pre "declare_values_pre" declare_values_def;

Theorem declare_values_pre[cv_pre,local]:
  ∀ctx n ds vs. declare_values_pre ctx n ds vs
Proof
  ho_match_mp_tac declare_values_ind >> rpt strip_tac >>
  simp[Once declare_values_pre_def] >> rw[] >> fs[] >>
  (* the record update appears as a case on the context *)
  Cases_on ‘ctx’ >> gvs[fetch "-" "elab_ctx_fn_updates"]
QED

val () = cv_auto_trans return_atoms_def;
val () = cv_auto_trans flag_def;
val () = cv_auto_trans set_flag_def;

val elab_stmts_pre_def = cv_auto_trans_pre_rec
  "elab_stmts_pre elab_stmt_pre elab_for_init_pre" elab_stmts_def (
  WF_REL_TAC ‘measure (λx. case x of
     INL (ctx, n, ss) => cv_size ss
   | INR (INL (ctx, n, st)) => cv_size st
   | INR (INR (ctx, n, st)) => cv_size st)’ >>
  cv_termination_tac
);

Theorem elab_stmts_pre[cv_pre,local]:
  (∀ctx n ss. elab_stmts_pre ctx n ss) ∧
  (∀ctx n st. elab_stmt_pre ctx n st) ∧
  (∀ctx n st. elab_for_init_pre ctx n st)
Proof
  ho_match_mp_tac elab_stmts_ind >> rpt strip_tac >>
  simp[Once elab_stmts_pre_def, elab_expr_pre] >> rw[] >> fs[] >>
  (* the record update appears as a case on the context *)
  Cases_on ‘ctx’ >> gvs[fetch "-" "elab_ctx_fn_updates"]
QED

val () = cv_auto_trans variable_binding_def;
val () = cv_auto_trans core_bindings_def;
val () = cv_auto_trans elab_function_def;
val () = cv_auto_trans elab_functions_def;
val () = cv_auto_trans core_state_variables_def;
val () = cv_auto_trans elab_type_declarations_def;
val () = cv_auto_trans elab_struct_layouts_def;
val () = cv_auto_trans external_functions_def;
val () = cv_auto_trans special_function_def;
val () = cv_auto_trans define_parameters_def;
val elab_base_arguments_pre_def =
  cv_auto_trans_pre "elab_base_arguments_pre" elab_base_arguments_def;

Theorem elab_base_arguments_pre[cv_pre,local]:
  ∀ctx fs n v. elab_base_arguments_pre ctx fs n v
Proof
  ho_match_mp_tac elab_base_arguments_ind >> rw[] >>
  simp[Once elab_base_arguments_pre_def] >> rw[] >>
  Cases_on ‘ctx’ >> gvs[fetch "-" "elab_ctx_fn_updates"]
QED

val () = cv_auto_trans elab_initializers_def;
val () = cv_auto_trans elab_constructors_def;
val () = cv_auto_trans elab_creation_def;
val () = cv_auto_trans creation_payable_def;
val () = cv_auto_trans elaborate_unit_def;
