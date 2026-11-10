(* Elaboration of the normalised source AST (solidityImport) to the ordered
 * core, for the pinned profile solc-0.8.37-via-ir-osaka.
 * docs/frontend-boundary.md lists the admitted subset.
 *
 * Elaboration also checks each function body against the compiler's
 * annotations, at the node whose type it computes: every type annotation
 * agrees with the elaborated type (source_type_matches), operators and
 * literal kinds are in the admitted sets, calls and emits have matching
 * arity, declarations, returns, break, continue and placeholders occur
 * where the source allows them, and a pure function reads no state
 * variable. A function that fails returns its blockers, which preparation
 * (solidityPrepareLib) turns into marking that function unsupported.
 *
 * One contract is elaborated, flattened along its bases. An internal call
 * runs the most derived override of the function it names (call_table), and
 * a super call the function super_table finds along the bases after the
 * caller's; the functions no other overrides are elaborated, and the external
 * and public ones among them, receive and fallback form the dispatch table.
 * Each constant is two procedures that return its value converted to its
 * type, one with checked and one with wrapping arithmetic, and a reference
 * to it calls the one of its own arithmetic, as the compiler's IR calls a
 * function per constant. State-variable initializers, constructors and
 * base-constructor arguments form one creation procedure.
 *
 * Schedules, read from the compiler's IR for this profile (the ir output in
 * testdata/frontend/expected/pure_core.json) and checked against the compiled
 * bytecode by the differential tests:
 *  - binary operands, call, emit and error arguments and tuple components are
 *    evaluated left to right, each read of a local or a state variable being a copy taken
 *    when it is evaluated;
 *  - && and || evaluate their right operand only when needed;
 *  - x op= e evaluates e, then reads x, then writes x;
 *  - ++ and -- read, step (checked unless unchecked) and write back, yielding
 *    the new (prefix) or old (postfix) value;
 *  - a tuple assignment evaluates its right-hand side into fresh values,
 *    captures its targets left to right, then writes them right to left;
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

(* What an expression or statement sees: the functions callable by id, and
 * those super calls run, by the declaration they name; the struct, enum
 * (member count) and event declarations; the variables in lexical scope; the
 * state variables it may read and write (none in a pure or library
 * function), and those inline assembly may name by slot and offset; the
 * immutables and constants (with the id of the constant's wrapping
 * procedure); the enclosing function's return variables and, in a modifier,
 * the procedure its placeholder calls with the function's parameters; the
 * arithmetic mode; whether in the creation; the innermost scope node, which
 * declares the locals of a declaration statement; the id of the return
 * parameter list a return names; whether in a loop body; the declarations
 * that failed to elaborate, whose references fail with no blocker of their
 * own, since the failure is reported where they are declared.
 *)
Datatype:
  elab_ctx = <|
    functions : (num # src_function) list;
    supers : (num # src_function) list;
    structs : src_struct list;
    enums : (num # num) list;
    events : (num # src_event) list;
    variables : (num # sol_type) list;
    state : (num # sol_type) list;
    locations : (num # sol_type) list;
    immutables : (num # sol_type) list;
    constants : (num # sol_type # num) list;
    returns : (num # sol_type) list;
    placeholder : (num # (num # sol_type) list) option;
    mode : arithmetic_mode;
    creation : bool;
    scope : num;
    returns_id : num;
    in_loop : bool;
    bad_ids : num list
  |>
End

(* Values and conversions *)

(* The type of an elaborated value: an elementary type, an integer literal
 * (whose atom is its value), a fractional literal, which only an operation
 * over literals the compiler folds to an integer takes, a bytes or string
 * literal, or several values.
 *)
Datatype:
  elab_type = ElabType sol_type | ElabLiteral | ElabRational | ElabBytesLiteral
            | ElabTuple (sol_type list)
End

(* Rejections: elaboration fails with its blockers, each the id of the node it
 * is about and a short fixed phrase saying what is unsupported there (or,
 * for a placeholder of the import, the importer's line). A node elaborates
 * all of its independent children and reports the blockers of every one
 * that fails, together with a blocker of its own if it has one.
 *)
Definition blockers_def:
  (blockers (INL _) = ([] : (num # string) list)) ∧
  (blockers (INR bs) = bs)
End

(* The result r of a node's children, with the node's blocker b added when
 * its own check ok fails. *)
Definition ensure_def:
  ensure ok (b : num # string) r =
    case r of
      INL x => if ok then INL x else INR [b]
    | INR bs => INR (if ok then bs else b :: bs)
End

(* A node that fails with blocker b, after elaborating its children r. *)
Definition reject_def:
  reject (b : num # string) r = INR (b :: blockers r)
End

(* A reference to x that names nothing in scope: no blocker if x's
 * declaration failed, where that failure is reported. *)
Definition unknown_reference_def:
  unknown_reference ctx (id : num) tag (x : num) =
    INR (if MEM x ctx.bad_ids then [] else [(id, tag)])
End

Definition expr_id_def:
  (expr_id (SrcIdentifier info _ _ _) = info.node_id) ∧
  (expr_id (SrcArrayLength info _ _) = info.node_id) ∧
  (expr_id (SrcMemberAccess info _ _ _) = info.node_id) ∧
  (expr_id (SrcArrayMember info _ _ _) = info.node_id) ∧
  (expr_id (SrcLiteral info _ _ _) = info.node_id) ∧
  (expr_id (SrcUnaryOperation info _ _ _ _) = info.node_id) ∧
  (expr_id (SrcBinaryOperation info _ _ _ _ _) = info.node_id) ∧
  (expr_id (SrcConditional info _ _ _ _) = info.node_id) ∧
  (expr_id (SrcAssignment info _ _ _ _) = info.node_id) ∧
  (expr_id (SrcIndexAccess info _ _ _) = info.node_id) ∧
  (expr_id (SrcTupleExpression info _ _) = info.node_id) ∧
  (expr_id (SrcFunctionCall info _ _ _ _) = info.node_id) ∧
  (expr_id (SrcSuperCall info _ _ _ _) = info.node_id) ∧
  (expr_id (SrcBuiltinCall info _ _ _ _ _) = info.node_id) ∧
  (expr_id (SrcTypeConversion info _ _ _) = info.node_id) ∧
  (expr_id (SrcEnvironment info _ _) = info.node_id) ∧
  (expr_id (SrcExternalCall info _ _ _ _ _) = info.node_id) ∧
  (expr_id (SrcTypeMember info _ _ _) = info.node_id) ∧
  (expr_id (SrcNew info _ _ _) = info.node_id) ∧
  (expr_id (SrcEnumValue info _ _ _) = info.node_id) ∧
  (expr_id (SrcKeccak256 info _ _ _) = info.node_id) ∧
  (expr_id (SrcModular info _ _ _ _) = info.node_id) ∧
  (expr_id (SrcAddressCodeLength info _ _ _) = info.node_id) ∧
  (expr_id (SrcSelector info _ _) = info.node_id) ∧
  (expr_id (SrcEcrecover info _ _ _) = info.node_id) ∧
  (expr_id (SrcAbiEncode info _ _ _ _) = info.node_id) ∧
  (expr_id (SrcAbiDecode info _ _ _ _) = info.node_id) ∧
  (expr_id (SrcStaticCall info _ _ _ _) = info.node_id) ∧
  (expr_id (SrcUnsupportedExpr info _ _) = info.node_id)
End

(* The placeholders of the import in a type name. *)
Definition unsupported_type_names_def:
  (unsupported_type_names (SrcUnsupportedTypeName info msg) = [(info.node_id, msg)]) ∧
  (unsupported_type_names (SrcArrayTypeName _ element _) =
    unsupported_type_names element) ∧
  (unsupported_type_names (SrcDynamicArrayTypeName _ element) =
    unsupported_type_names element) ∧
  (unsupported_type_names (SrcMappingTypeName _ key value) =
    unsupported_type_names key ++ unsupported_type_names value) ∧
  (unsupported_type_names _ = [])
End

(* A type name that does not normalize: its placeholders, else b. *)
Definition type_name_blockers_def:
  type_name_blockers b tn =
    case normalize_type_name tn of
      SOME _ => []
    | NONE => (case unsupported_type_names tn of [] => [b] | bs => bs)
End

(* A variable whose type is not supported: the placeholders in its type
 * name, else the variable tagged. *)
Definition variable_blockers_def:
  variable_blockers tag (v : src_variable) =
    case unsupported_type_names v.var_type_name of
      [] => [(v.var_info.node_id, tag)]
    | bs => bs
End

(* The declared variables (NONE for a hole) without a type. *)
Definition variables_blockers_def:
  (variables_blockers [] = []) ∧
  (variables_blockers (NONE :: vs) = variables_blockers vs) ∧
  (variables_blockers (SOME v :: vs) =
    (case variable_type v of
       SOME _ => []
     | NONE => variable_blockers "unsupported variable type" v) ++
    variables_blockers vs)
End

Definition bind_value_def:
  bind_value (n : num) ty op =
    ([DefineStmt (AstId n) (SingleType ty) op], BoundAtom (AstId n))
End

(* The value a local of type ty starts with when declared without one. *)
Definition default_operation_def:
  default_operation ty =
    case ty of
      LocatedT MemoryLoc element => SOME (DefaultMemoryOperation element)
    | _ => if located_value_type ty then NONE
           else case default_elementary ty of
                  SOME d => SOME (ConvertOperation ty (ConstantAtom d))
                | NONE => NONE
End

(* A value of type ty: integer literals stand for themselves, or for their
 * bytes as a fixed-size bytes; other types are converted. Fails with what
 * cannot be converted, for the caller to tag with the operand.
 *)
Definition coerce_def:
  coerce n ty a vt =
    case vt of
      ElabType src =>
        if src = ty then INL (([], a), n)
        else (case (src, ty) of
          (LocatedT loc (ArrayT e l), LocatedT MemoryLoc element') =>
            if loc = MemoryLoc ∨ element' ≠ ArrayT e l
            then INR "type conversion between these types"
            else INL (bind_value n ty (CopyToMemoryOperation a), n + 1)
        | (LocatedT loc element, LocatedT MemoryLoc element') =>
            if loc = MemoryLoc ∨ element ≠ element' ∨ ¬byte_sequence_type element
            then INR "type conversion between these types"
            else let (ls, len) = bind_value n (UintT 256) (ArrayLengthOperation a) in
                 let (ds, dst) = bind_value (n + 1) ty (AllocateMemoryOperation element len) in
                 INL ((ls ++ ds ++ [CopyContentsStmt src ty a dst], dst), n + 2)
        | _ => INL (bind_value n ty (ConvertOperation ty a), n + 1))
    | ElabBytesLiteral =>
        (case (ty, a) of
           (FixedBytesT k, ConstantAtom (BytesValue bs)) =>
             if valid_fixed_bytes_width k ∧ LENGTH bs ≤ k then
               INL (bind_value n ty
                       (ConvertOperation ty (ConstantAtom (BytesValue (take_pad_0 k bs)))), n + 1)
             else INR "string literal conversion"
         | (LocatedT MemoryLoc element, ConstantAtom (BytesValue bs)) =>
             if byte_sequence_type element then
               INL (bind_value n ty (BytesLiteralOperation element bs), n + 1)
             else INR "string literal conversion"
         | _ => INR "string literal conversion")
    | ElabLiteral =>
        if is_integer_type ty then INL (([], a), n) else
        (* a number literal the compiler takes as a bytesN: zero, or hex
           digits that fill it *)
        (case (ty, a) of
           (FixedBytesT k, ConstantAtom (IntegerValue i)) =>
             if valid_fixed_bytes_width k ∧ 0 ≤ i ∧ Num i < 256 ** k then
               INL (bind_value n ty
                       (ConvertOperation ty (ConstantAtom (BytesValue (num_to_bytes k (Num i))))), n + 1)
             else INR "number literal conversion"
         | _ => INR "number literal conversion")
    | ElabRational => INR "rational number value"
    | ElabTuple _ => INR "tuple used as a value"
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

(* A write to a captured target: a located value rebinds the reference. *)
Definition store_target_def:
  store_target (t : num) ty a =
    if located_value_type ty then BindReferenceStmt (AstId t) ty a
    else WriteScalarStmt (AstId t) ty a
End

Definition assign_local_def:
  assign_local (t : num) x ty a =
    [CaptureBindingStmt (AstId t) (AstId x); store_target t ty a]
End

(* A destination is a local binding, an already evaluated concrete reference,
 * or a memory element (the container, its index and its container type),
 * captured when written. Its prelude evaluates the location; reads and
 * writes share this representation.
 *)
Datatype:
  destination = LocalDestination num sol_type | ReferenceDestination core_atom sol_type
              | ElementDestination core_atom core_atom sol_type
End

Definition destination_type_def:
  (destination_type (LocalDestination _ ty) = ty) ∧
  (destination_type (ReferenceDestination _ ty) = ty) ∧
  (destination_type (ElementDestination _ _ ty) =
    if ty = BytesT then FixedBytesT 1 else
    case ty of ArrayT element _ => element_type MemoryLoc element | _ => ty)
End

(* The variable an identifier annotated with tid names, of that type. *)
Definition variable_destination_def:
  variable_destination ctx (n : num) x tid =
    case ALOOKUP ctx.variables x of
      SOME ty =>
        if source_type_matches ty tid then SOME (([], LocalDestination x ty), n)
        else NONE
    | NONE =>
        (case ALOOKUP ctx.state x of
           SOME ty =>
             if ¬source_type_matches ty tid then NONE else
             SOME (([DefineStmt (AstId n) (ReferenceType ty)
                       (StateReferenceOperation (AstId x))],
                    ReferenceDestination (BoundAtom (AstId n)) ty), n + 1)
         | NONE =>
             case ALOOKUP ctx.immutables x of
               SOME ty =>
                 if ¬source_type_matches ty tid then NONE else
                 SOME (([DefineStmt (AstId n) (ReferenceType ty)
                           (ImmutableReferenceOperation (AstId x))],
                        ReferenceDestination (BoundAtom (AstId n)) ty), n + 1)
             | NONE => NONE)
End

(* Reading a storage byte sequence or array yields a reference to it. *)
Definition read_value_type_def:
  read_value_type ty = if memory_object_type ty then LocatedT StorageLoc ty else ty
End

Definition read_destination_def:
  (read_destination n (LocalDestination x ty) = (([], BoundAtom (AstId x)), n)) ∧
  (read_destination n (ReferenceDestination ref ty) =
    (bind_value n (read_value_type ty) (ReadOperation ty ref), n + 1)) ∧
  (read_destination n (ElementDestination array index ty) =
    (bind_value n (destination_type (ElementDestination array index ty))
       (if ty = BytesT then ByteIndexOperation array index
        else ArrayIndexOperation array index), n + 1))
End

Definition capture_destination_def:
  (capture_destination t (LocalDestination x _) = [CaptureBindingStmt (AstId t) (AstId x)]) ∧
  (capture_destination t (ElementDestination array index _) =
    [CaptureReferenceFieldStmt (AstId t) array (IndexNavigation index)]) ∧
  (capture_destination t (ReferenceDestination ref _) = [CaptureValueStmt (AstId t) ref])
End

Definition write_destination_def:
  write_destination t target a =
    capture_destination t target ++ [store_target t (destination_type target) a]
End

(* Assigning a storage byte sequence or array copies contents, converting an
 * array's elements as storage_copy_type allows; binding a local storage
 * pointer continues to use the ordinary alias-preserving local assignment. *)
Definition plain_assignment_def:
  plain_assignment n target a vt =
    case target of
      ReferenceDestination ref ty =>
        if memory_object_type ty then
          let source =
            case vt of
              ElabBytesLiteral => coerce n (LocatedT MemoryLoc ty) a vt
            | ElabType (LocatedT loc element) =>
                if storage_copy_type element ty then INL (([], a), n)
                else INR "storage copy between these types"
            | _ => INR "storage copy between these types" in
          (case source of
             INR why => INR why
           | INL ((cs, src), n1) =>
               let source_ty = case vt of
                 ElabType src_ty => src_ty
               | _ => LocatedT MemoryLoc ty in
               let dst_ty = LocatedT StorageLoc ty in
               let (ds, dst) = bind_value n1 dst_ty (ReadOperation ty ref) in
               INL ((cs ++ ds ++ [CopyContentsStmt source_ty dst_ty src dst],
                     dst, dst_ty), n1 + 1))
        else (case coerce n ty a vt of
           INL ((cs, value), n1) =>
             INL ((cs ++ write_destination n1 target value, value, ty), n1 + 1)
         | INR why => INR why)
    | _ =>
        let ty = destination_type target in
        (case coerce n ty a vt of
           INL ((cs, value), n1) =>
             INL ((cs ++ write_destination n1 target value, value, ty), n1 + 1)
         | INR why => INR why)
End

(* Operators *)

Definition arithmetic_operator_def:
  arithmetic_operator op =
    if op = SrcAdd then SOME AddOp
    else if op = SrcSub then SOME SubtractOp
    else if op = SrcMul then SOME MultiplyOp
    else if op = SrcDiv then SOME DivideOp
    else if op = SrcMod then SOME RemainderOp
    else if op = SrcExp then SOME ExponentOp
    else if op = SrcShl then SOME ShiftLeftOp
    else if op = SrcShr then SOME ShiftRightOp
    else if op = SrcBitAnd then SOME BitAndOp
    else if op = SrcBitOr then SOME BitOrOp
    else if op = SrcBitXor then SOME BitXorOp
    else NONE
End

(* The type of the right operand of an arithmetic operator on type ty. *)
Definition right_operand_type_def:
  right_operand_type op ty =
    if op = ExponentOp ∨ op = ShiftLeftOp ∨ op = ShiftRightOp then UintT 256
    else ty
End

(* The operator of a compound assignment such as "+=". *)
(* Solidity has no **=. *)
Definition compound_operator_def:
  compound_operator op =
    case op of
      SOME bop => if bop = SrcExp then NONE else arithmetic_operator bop
    | NONE => NONE
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
    if op = SrcEq then SOME (compare_value n ty EqualOp al ar, n + 1)
    else if op = SrcNe then
      SOME (negate_value (n + 1) (compare_value n ty EqualOp al ar))
    else if op = SrcLt then SOME (compare_value n ty LessThanOp al ar, n + 1)
    else if op = SrcGt then SOME (compare_value n ty LessThanOp ar al, n + 1)
    else if op = SrcLe then
      SOME (negate_value (n + 1) (compare_value n ty LessThanOp ar al))
    else if op = SrcGe then
      SOME (negate_value (n + 1) (compare_value n ty LessThanOp al ar))
    else NONE
End

Definition unary_operator_def:
  unary_operator op =
    if op = SrcNegate then SOME NegateOp
    else if op = SrcBitNot then SOME BitNotOp
    else if op = SrcNot then SOME BoolNotOp
    else NONE
End

(* Whether an expression writes a local. *)
Definition expr_assigns_def:
  (expr_assigns (SrcAssignment _ _ _ _ _) ⇔ T) ∧
  (expr_assigns (SrcUnaryOperation _ op _ e _) ⇔
    op = SrcIncrement ∨ op = SrcDecrement ∨ expr_assigns e) ∧
  (expr_assigns (SrcBinaryOperation _ _ l r _ _) ⇔
    expr_assigns l ∨ expr_assigns r) ∧
  (expr_assigns (SrcTupleExpression _ cs _) ⇔ components_assign cs) ∧
  (expr_assigns (SrcFunctionCall _ callee args _ _) ⇔
    expr_assigns callee ∨ exprs_assign args) ∧
  (expr_assigns (SrcArrayMember _ _ root_expr _) ⇔ expr_assigns root_expr) ∧
  (expr_assigns (SrcBuiltinCall _ _ _ condition message _) ⇔
    (case condition of NONE => F | SOME c => expr_assigns c) ∨
    (case message of NONE => F | SOME m => expr_assigns m)) ∧
  (expr_assigns (SrcConditional _ c t f _) ⇔
    expr_assigns c ∨ expr_assigns t ∨ expr_assigns f) ∧
  (expr_assigns (SrcIndexAccess _ b i _) ⇔ expr_assigns b ∨ expr_assigns i) ∧
  (expr_assigns (SrcMemberAccess _ root_expr _ _) ⇔ expr_assigns root_expr) ∧
  (expr_assigns (SrcArrayLength _ root_expr _) ⇔ expr_assigns root_expr) ∧
  (expr_assigns (SrcTypeConversion _ _ e _) ⇔ expr_assigns e) ∧
  (expr_assigns (SrcExternalCall _ _ _ operands _ _) ⇔ exprs_assign operands) ∧
  (expr_assigns (SrcNew _ _ e _) ⇔ expr_assigns e) ∧
  (expr_assigns (SrcKeccak256 _ _ e _) ⇔ expr_assigns e) ∧
  (expr_assigns (SrcModular _ _ _ args _) ⇔ exprs_assign args) ∧
  (expr_assigns (SrcAddressCodeLength _ _ e _) ⇔ expr_assigns e) ∧
  (expr_assigns (SrcAbiEncode _ _ _ args _) ⇔ exprs_assign args) ∧
  (expr_assigns (SrcEcrecover _ _ args _) ⇔ exprs_assign args) ∧
  (expr_assigns (SrcAbiDecode _ _ e _ _) ⇔ expr_assigns e) ∧
  (expr_assigns (SrcStaticCall _ _ target data _) ⇔ expr_assigns target ∨ expr_assigns data) ∧
  (expr_assigns (SrcSuperCall _ _ args _ _) ⇔ exprs_assign args) ∧
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
    let kind = if mutability = ViewMut ∨ mutability = PureMut
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

(* Memory bounds checks happen at the reverse write, after all target
 * operands have run. Other scalar targets were captured left to right. *)
Definition tuple_write_def:
  tuple_write n (id : num) t target a vt =
    case target of
      ReferenceDestination _ ty =>
        if memory_object_type ty then
          (case plain_assignment n target a vt of
             INL ((ss, _, _), n1) => INL (ss, n1)
           | INR why => INR [(id, why)])
        else
          (case coerce n ty a vt of
             INL ((ss, value), n1) => INL (ss ++ [store_target t ty value], n1)
           | INR why => INR [(id, why)])
    | ElementDestination _ _ _ =>
        (case plain_assignment n target a vt of
           INL ((ss, _, _), n1) => INL (ss, n1)
         | INR why => INR [(id, why)])
    | _ =>
        let ty = destination_type target in
        (case coerce n ty a vt of
           INL ((ss, value), n1) => INL (ss ++ [store_target t ty value], n1)
         | INR why => INR [(id, why)])
End

Definition tuple_writes_def:
  (tuple_writes n (id : num) [] [] = INL ([], n)) ∧
  (tuple_writes n id (NONE :: cs) (_ :: vs) = tuple_writes n id cs vs) ∧
  (tuple_writes n id (SOME (t, target) :: cs) ((a, vt) :: vs) =
    case tuple_writes n id cs vs of
      INL (ws, n1) =>
        (case tuple_write n1 id t target a vt of
           INL (ss, n2) => INL (ws ++ ss, n2)
         | INR bs => INR bs)
    | INR bs => INR (blockers (tuple_write n id t target a vt) ++ bs)) ∧
  (tuple_writes n id _ _ = INR [(id, "unsupported tuple assignment")])
End

(* A conditional's components are joined through separate locals. Branch
 * preludes and conversions run only in the selected arm. *)
Definition conditional_targets_def:
  (conditional_targets n [] [] [] = SOME ([], [], [], [], n)) ∧
  (conditional_targets n (ty :: tys) (a :: as) (b :: bs) =
    case (default_operation ty, conditional_targets (n + 3) tys as bs) of
      (SOME op, SOME (ds, ts, fs, vs, n1)) =>
        let (ss, v) = bind_value n ty op in
        SOME (ss ++ ds, assign_local (n + 1) n ty a ++ ts,
              assign_local (n + 2) n ty b ++ fs, v :: vs, n1)
    | _ => NONE) ∧
  (conditional_targets n _ _ _ = NONE)
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
(* How an operand is converted: to a type (ValueOf); for ABI encoding as a
 * type (EncodedAs), keeping byte-sequence and array references live until
 * serialization, since an encoded argument needs no location copy and the
 * encoder reads it where it is, in memory, calldata or storage; or for ABI
 * encoding as its own type (Encoded, packed or not). *)
Datatype:
  operand_target = ValueOf sol_type | EncodedAs sol_type | Encoded bool
End

Definition values_of_def:
  (values_of [] = []) ∧
  (values_of (ty :: tys) = ValueOf ty :: values_of tys)
End

Definition encoded_as_def:
  (encoded_as [] = []) ∧
  (encoded_as (ty :: tys) = EncodedAs ty :: encoded_as tys)
End

Definition expr_ids_def:
  (expr_ids [] = []) ∧
  (expr_ids (e :: es) = expr_id e :: expr_ids es)
End

(* An argument of abi.encode*, with the ABI type it is encoded as: a scalar
 * as its type; a byte sequence, or a string literal, where it is, as the
 * compiler encodes it in place; an integer literal (unpacked only) as its
 * mobile type, whose encoding is that of int256 or uint256. *)
Definition abi_argument_def:
  abi_argument packed a vt =
    case vt of
      ElabType ty =>
        if is_stored_scalar_type ty then INL (ty, a) else
        (case ty of
           LocatedT _ element =>
             if byte_sequence_type element
             then INL (LocatedT MemoryLoc element, a)
             else INR "abi encoding of this type"
         | _ => INR "abi encoding of this type")
    | ElabBytesLiteral => INL (LocatedT MemoryLoc StringT, a)
    | ElabLiteral =>
        (case a of
           ConstantAtom (IntegerValue i) =>
             if packed then INR "packed encoding of a number literal"
             else INL ((if i < 0 then IntT 256 else UintT 256), a)
         | _ => INR "abi encoding of this type")
    | _ => INR "abi encoding of this type"
End

(* An operand converted to its target: the statements, the type it has and
 * its atom. *)
Definition convert_operand_def:
  convert_operand n target a vt =
    case target of
      ValueOf ty =>
        (case coerce n ty a vt of
           INL ((ss, a'), n1) => INL ((ss, ty, a'), n1)
         | INR why => INR why)
    | EncodedAs ty =>
        (case (ty, vt) of
           (LocatedT _ element, ElabType (LocatedT _ actual)) =>
             if element = actual then INL (([], ty, a), n)
             else INR "type conversion between these types"
         | (LocatedT _ element, ElabBytesLiteral) =>
             if byte_sequence_type element then INL (([], ty, a), n)
             else INR "string literal conversion"
         | _ =>
             (case coerce n ty a vt of
                INL ((ss, a'), n1) => INL ((ss, ty, a'), n1)
              | INR why => INR why))
    | Encoded packed =>
        (case abi_argument packed a vt of
           INL (ty, a') => INL (([], ty, a'), n)
         | INR why => INR why)
End

(* Every operand list goes through here: the operands' values converted to
 * their targets in order, ids being the operands' node ids and id the
 * node's, for a count mismatch. Every operand that fails is reported, under
 * its own id. *)
Definition convert_operands_def:
  (convert_operands n (id : num) [] [] [] = INL ([], [], [], n)) ∧
  (convert_operands n id (i :: ids) (t :: ts) ((a, vt) :: vs) =
    case convert_operand n t a vt of
      INL ((ss, ty, a'), n1) =>
        (case convert_operands n1 id ids ts vs of
           INL (ss', tys, as, n2) => INL (ss ++ ss', ty :: tys, a' :: as, n2)
         | INR bs => INR bs)
    | INR why => INR ((i, why) :: blockers (convert_operands n id ids ts vs))) ∧
  (convert_operands n id _ _ _ = INR [(id, "value count mismatch")])
End

(* The operation of abi.encode* on the values of its arguments, after any
 * statements converting the arguments: a selector given as an argument is
 * a bytes4, and the other arguments are scalars or byte sequences (integer
 * literals only unpacked, as the compiler requires). *)
Definition selector_encoding_def:
  selector_encoding (i : num) s svt r =
    let selector = (if svt = ElabType (FixedBytesT 4) then []
                    else [(i, "selector not a bytes4")]) in
    case r of
      INL (css, tys, args, n1) =>
        if selector = [] then INL ((css, AbiEncodeOperation (SOME s) tys args), n1)
        else INR selector
    | INR bs => INR (selector ++ bs)
End

Definition abi_encoding_def:
  abi_encoding n (id : num) ids form vs =
    case (form, ids, vs) of
      (AbiWithSelector, i :: rest_ids, (s, svt) :: rest) =>
        selector_encoding i s svt
          (convert_operands n id rest_ids (REPLICATE (LENGTH rest) (Encoded F)) rest)
    | (AbiCall tids, i :: rest_ids, (s, svt) :: rest) =>
        (case all_some (MAP abi_call_parameter tids) of
           SOME tys =>
             selector_encoding i s svt (convert_operands n id rest_ids (encoded_as tys) rest)
         | NONE =>
             selector_encoding i s svt (INR [(id, "abi encoding of this type")]))
    | (AbiWithSelector, _, _) => INR [(id, "missing selector")]
    | (AbiCall _, _, _) => INR [(id, "missing selector")]
    | (AbiPacked, _, _) =>
        (case convert_operands n id ids (REPLICATE (LENGTH vs) (Encoded T)) vs of
           INL (_, tys, args, _) => INL (([], AbiEncodePackedOperation tys args), n)
         | INR bs => INR bs)
    | (AbiStringConcat, _, _) =>
        (case convert_operands n id ids (REPLICATE (LENGTH vs) (Encoded T)) vs of
           INL (_, tys, args, _) => INL (([], AbiEncodePackedOperation tys args), n)
         | INR bs => INR bs)
    | (AbiPlain, _, _) =>
        (case convert_operands n id ids (REPLICATE (LENGTH vs) (Encoded F)) vs of
           INL (_, tys, args, _) => INL (([], AbiEncodeOperation NONE tys args), n)
         | INR bs => INR bs)
    | (AbiWithSignature signature, _, _) =>
        (case convert_operands n id ids (REPLICATE (LENGTH vs) (Encoded F)) vs of
           INL (_, tys, args, _) =>
             INL (([], AbiEncodeOperation
                         (SOME (ConstantAtom (BytesValue (TAKE 4 (Keccak_256_w64 signature)))))
                         tys args), n)
         | INR bs => INR bs)
End

(* An array or byte index, or an allocation length: an unsigned integer or a
 * non-negative integer literal. *)
Definition index_value_ok_def:
  index_value_ok a vt ⇔
    case vt of
      ElabType (UintT _) => T
    | ElabLiteral => (case a of ConstantAtom (IntegerValue i) => 0 ≤ i | _ => F)
    | _ => F
End

(* An element dynamic storage arrays push and pop. *)
Definition push_element_ok_def:
  push_element_ok element ⇔
    case element of EnumT _ => T | _ => elementary_storage_type_ok element
End

(* A call of an internal function or a super call, annotated with tid: as
 * many arguments as parameters, in a valid order, a callee that is not
 * external, and the callee's return types as its type. *)
Definition internal_call_ok_def:
  internal_call_ok (callee : src_function) rets args order tid ⇔
    LENGTH args = LENGTH callee.fn_parameters ∧
    argument_order_ok order (LENGTH args) ∧
    callee.fn_visibility ≠ ExternalVisibility ∧
    decode_type_identifier tid = SOME (call_value_type rets)
End

(* A call's argument values, evaluated in the call's order, in its
 * parameters' order: order gives, for each parameter, the position of its
 * argument (argument_order_ok). The values are those of the call's
 * arguments, after those of an external call's target and value. *)
Definition arrange_def:
  arrange (order : num list) vs =
    if order = [] then SOME vs else
    let k = LENGTH vs - LENGTH order in
    OPTION_MAP (λws. TAKE k vs ++ ws) (all_some (MAP (λi. oEL (k + i) vs) order))
End

(* An expression the compiler annotated with tid may elaborate to a value of
 * type vt: a scalar of the annotated type, or anything else whose annotation
 * decodes. *)
Definition annotation_matches_def:
  annotation_matches tid vt ⇔
    case vt of
      ElabType ty =>
        if is_stored_scalar_type ty then source_type_matches ty tid
        else IS_SOME (decode_type_identifier tid)
    | _ => IS_SOME (decode_type_identifier tid)
End

(* A declaration is a statement of a block, never the body of an if, a loop
 * or a try clause. *)
Definition is_declaration_def:
  (is_declaration (SrcVariableDeclarationStatement _ _ _ _) ⇔ T) ∧
  (is_declaration _ ⇔ F)
End

Definition elab_expr_def:
  (elab_expr ctx n expression =
    case expression of
      SrcIdentifier info _ x tid =>
        (case variable_destination ctx n x tid of
           SOME ((ls, target), n1) =>
             let ty = destination_type target in
             if ¬(is_stored_scalar_type ty ∨ memory_object_type ty ∨ located_value_type ty)
             then INR [(info.node_id, "read of a value of this type")] else
             let (read, n2) = read_destination n1 target in
             let (ss, a) = read in
             INL ((ls ++ ss, a, ElabType (read_value_type ty)), n2)
         | NONE =>
             case ALOOKUP ctx.constants x of
               SOME (ty, w) =>
                 if ¬source_type_matches ty tid
                 then INR [(info.node_id, "type annotation mismatch")] else
                 let p = if ctx.mode = CheckedArithmetic then x else w in
                 let (ss, a) = bind_value n ty (InternalCallOperation (AstId p) []) in
                 INL ((ss, a, ElabType ty), n + 1)
             | NONE => unknown_reference ctx info.node_id "unsupported identifier" x)
    | SrcArrayLength info root_expr tid =>
        ensure (tid = "t_uint256") (info.node_id, "type annotation mismatch")
        (case elab_expr ctx n root_expr of
           INL ((ss, ref, ElabType (LocatedT loc BytesT)), n1) =>
             let (rs, a) = bind_value n1 (UintT 256) (ArrayLengthOperation ref) in
             INL ((ss ++ rs, a, ElabType (UintT 256)), n1 + 1)
         | INL ((ss, ref, ElabType (LocatedT _ (ArrayT _ (SOME length)))), n1) =>
             INL ((ss, ConstantAtom (IntegerValue (&length)), ElabType (UintT 256)), n1)
         | INL ((ss, ref, ElabType (LocatedT _ (ArrayT _ NONE))), n1) =>
             let (rs, a) = bind_value n1 (UintT 256) (ArrayLengthOperation ref) in
             INL ((ss ++ rs, a, ElabType (UintT 256)), n1 + 1)
         | r =>
           (* a storage array is a location: when that fails too, the reason
              is the value's, unless the value was elaborated *)
           case elab_location ctx n root_expr of
             INL ((ss, _, ArrayT _ (SOME length)), n1) =>
               INL ((ss, ConstantAtom (IntegerValue (&length)),
                     ElabType (UintT 256)), n1)
           | INL ((ss, ref, ArrayT _ NONE), n1) =>
               let (rs, a) = bind_value n1 (UintT 256) (ArrayLengthOperation ref) in
               INL ((ss ++ rs, a, ElabType (UintT 256)), n1 + 1)
           | INL _ => INR [(info.node_id, "length of a non-array")]
           | INR _ => reject (info.node_id, "length of a non-array") r)
    | SrcLiteral info kind value tid =>
        (if kind = BoolLiteral then
           if (value = "true" ∨ value = "false") ∧ tid = "t_bool" then
             INL (([], ConstantAtom (BoolValue (value = "true")), ElabType BoolT), n)
           else INR [(info.node_id, "unsupported literal")]
         else if kind ≠ NumberLiteral ∧ isPREFIX "t_stringliteral_" tid then
           INL (([], ConstantAtom (BytesValue (MAP (n2w o ORD) value)),
                 ElabBytesLiteral), n)
         else if kind ≠ NumberLiteral then INR [(info.node_id, "unsupported literal")]
         else
           case decode_type_identifier tid of
             SOME (SrcRational i d) =>
               if d = 1 then INL (([], ConstantAtom (IntegerValue i), ElabLiteral), n)
               else INL (([], ConstantAtom (BoolValue F), ElabRational), n)
           | _ => INR [(info.node_id, "unsupported literal")])
    | SrcMemberAccess info _ _ _ =>
        (case elab_location ctx n expression of
           INL ((ss, ref, ty), n1) =>
             if is_stored_scalar_type ty ∨ memory_object_type ty then
               let (rs, a) = bind_value n1 (read_value_type ty) (ReadOperation ty ref) in
               INL ((ss ++ rs, a, ElabType (read_value_type ty)), n1 + 1)
             else INR [(info.node_id, "read of a value of this type")]
         | INR bs => INR bs)
    | SrcIndexAccess info root_expr index tid =>
        (case elab_expr ctx n root_expr of
           INL ((ss, ref, ElabType (LocatedT loc BytesT)), n1) =>
             let (captured, next) = snapshot n1 ref (ElabType (LocatedT loc BytesT)) in
             let (saved, ref') = captured in
             ensure (tid = "t_bytes1") (info.node_id, "type annotation mismatch")
             (case elab_expr ctx next index of
                INL ((si, i, vt), n2) =>
                  if ¬index_value_ok i vt then INR [(expr_id index, "index of this type")] else
                  (case coerce n2 (UintT 256) i vt of
                     INL ((cs, i'), n3) =>
                       let (rs, a) = bind_value n3 (FixedBytesT 1)
                                       (ByteIndexOperation ref' i') in
                       INL ((ss ++ saved ++ si ++ cs ++ rs, a, ElabType (FixedBytesT 1)), n3 + 1)
                   | INR why => INR [(expr_id index, why)])
              | INR bs => INR bs)
         | INL ((ss, ref, ElabType (LocatedT loc (ArrayT element length))), n1) =>
             let ty = LocatedT loc (ArrayT element length) in
             let (captured, next) = snapshot n1 ref (ElabType ty) in
             let (saved, ref') = captured in
             (* a storage array's elements are annotated as stored, unlocated *)
             ensure (source_type_matches
                       (if loc = StorageLoc then element else element_type loc element) tid)
               (info.node_id, "type annotation mismatch")
             (case elab_expr ctx next index of
                INL ((si, i, vt), n2) =>
                  if ¬index_value_ok i vt then INR [(expr_id index, "index of this type")] else
                  (case coerce n2 (UintT 256) i vt of
                     INL ((cs, i'), n3) =>
                       let ety = element_type loc element in
                       let (rs, a) = bind_value n3 ety (ArrayIndexOperation ref' i') in
                       INL ((ss ++ saved ++ si ++ cs ++ rs, a, ElabType ety), n3 + 1)
                   | INR why => INR [(expr_id index, why)])
              | INR bs => INR bs)
         | _ =>
           (* elab_location reports the value's reason when both fail *)
           case elab_location ctx n expression of
             INL ((ss, ref, ty), n1) =>
               if is_stored_scalar_type ty ∨ memory_object_type ty then
                 let (rs, a) = bind_value n1 (read_value_type ty) (ReadOperation ty ref) in
                 INL ((ss ++ rs, a, ElabType (read_value_type ty)), n1 + 1)
               else INR [(info.node_id, "read of a value of this type")]
           | INR bs => INR bs)
    | SrcUnaryOperation info op prefix e tid =>
        (case identifier_integer tid of
           SOME i =>
             (* folded by the compiler: the operand is a literal operation *)
             (case elab_expr ctx n e of
                INL (([], _, _), _) =>
                  if op = SrcDelete then INR [(info.node_id, "unsupported unary operator")]
                  else INL (([], ConstantAtom (IntegerValue i), ElabLiteral), n)
              | INL _ => INR [(info.node_id, "folded operand not a literal")]
              | INR bs => INR bs)
         | NONE =>
         if op = SrcIncrement ∨ op = SrcDecrement then
           case elab_destination ctx n e of
             INL ((ls, target), n1) =>
               let ty = destination_type target in
               if ¬annotation_matches tid (ElabType ty)
               then INR [(info.node_id, "type annotation mismatch")] else
               let (read, n2) = read_destination n1 target in
               let (rs, cur) = read in
               let (old, n3) = if prefix then (([], cur), n2)
                               else snapshot n2 cur (ElabType ty) in
               let (ss, old_atom) = old in
               let (step, new_atom) = bind_value n3 ty
                 (ScalarOperation ty ctx.mode
                   (if op = SrcIncrement then AddOp else SubtractOp)
                   [cur; ConstantAtom (IntegerValue 1)]) in
               INL ((ls ++ rs ++ ss ++ step ++
                       write_destination (n3 + 1) target new_atom,
                     (if prefix then new_atom else old_atom), ElabType ty), n3 + 2)
           | INR bs => INR bs
         else
           case elab_expr ctx n e of
             INL ((ss, a, vt), n') =>
               (case (unary_operator op, identifier_type tid) of
                  (SOME uop, SOME ty) =>
                    (case coerce n' ty a vt of
                       INL ((cs, a'), n'') =>
                         let (ss', v) = bind_value n'' ty
                                          (ScalarOperation ty ctx.mode uop [a']) in
                         INL ((ss ++ cs ++ ss', v, ElabType ty), n'' + 1)
                     | INR why => INR [(expr_id e, why)])
                | (NONE, _) => INR [(info.node_id, "unsupported unary operator")]
                | _ => INR [(info.node_id, "unsupported operator type")])
           | INR bs => INR bs)
    | SrcBinaryOperation info op l r common tid =>
        (case identifier_integer tid of
           SOME i =>
             (* folded by the compiler: the operands are literal operations *)
             (case (elab_expr ctx n l, elab_expr ctx n r) of
                (INL (([], _, _), _), INL (([], _, _), _)) =>
                  INL (([], ConstantAtom (IntegerValue i), ElabLiteral), n)
              | (INL _, INL _) => INR [(info.node_id, "folded operand not a literal")]
              | (rl, rr) => INR (blockers rl ++ blockers rr))
         | NONE =>
         case elab_expr ctx n l of
           INR bl => INR (bl ++ blockers (elab_expr ctx n r))
         | INL ((sl, al, vl), n1) =>
         case (identifier_type common, identifier_type tid) of
           (SOME ty, SOME _) =>
             if op = SrcAnd ∨ op = SrcOr then
               (case coerce n1 BoolT al vl of
                  INL ((cl, al'), n2) =>
                    (case elab_expr ctx (n2 + 2) r of
                       INL ((sr, ar, vr), n3) =>
                         (case coerce n3 BoolT ar vr of
                            INL ((cr, ar'), n4) =>
                              if ¬annotation_matches tid (ElabType BoolT)
                              then INR [(info.node_id, "type annotation mismatch")] else
                              let (rs, res) =
                                bind_value n2 BoolT (ConvertOperation BoolT al') in
                              let rhs = sr ++ cr ++
                                        assign_local (n2 + 1) n2 BoolT ar' in
                              INL ((sl ++ cl ++ rs ++
                                    [if op = SrcAnd then IfStmt res rhs []
                                     else IfStmt res [] rhs],
                                    res, ElabType BoolT), n4)
                          | INR why => INR [(expr_id r, why)])
                     | INR bs => INR bs)
                | INR why =>
                    reject (expr_id l, why)
                      (case elab_expr ctx n r of
                         INL ((_, ar, vr), n2) =>
                           (case coerce n2 BoolT ar vr of
                              INL x => INL x
                            | INR why' => INR [(expr_id r, why')])
                       | INR bs => INR bs))
             else
               (* flat let patterns: nested ones do not cv-translate here *)
               let (copied, n2) =
                 if expr_assigns r then snapshot n1 al vl else (([], al), n1) in
               let (sl', al') = copied in
               (case elab_expr ctx n2 r of
                  INL ((sr, ar, vr), n3) =>
                    (case arithmetic_operator op of
                       SOME aop =>
                         ensure (annotation_matches tid (ElabType ty))
                           (info.node_id, "type annotation mismatch")
                         (case convert_operands n3 info.node_id [expr_id l; expr_id r]
                                 [ValueOf ty; ValueOf (right_operand_type aop ty)]
                                 [(al', vl); (ar, vr)] of
                            INL (cs, _, [al''; ar'], n5) =>
                              let (ss, v) = bind_value n5 ty
                                              (ScalarOperation ty ctx.mode aop [al''; ar']) in
                              INL ((sl ++ sl' ++ sr ++ cs ++ ss, v, ElabType ty), n5 + 1)
                          | INL _ => INR [(info.node_id, "value count mismatch")]
                          | INR bs => INR bs)
                     | NONE =>
                         ensure (annotation_matches tid (ElabType BoolT))
                           (info.node_id, "type annotation mismatch")
                         (case convert_operands n3 info.node_id [expr_id l; expr_id r]
                                 [ValueOf ty; ValueOf ty] [(al', vl); (ar, vr)] of
                            INL (cs, _, [al''; ar'], n5) =>
                              (case comparison n5 ty op al'' ar' of
                                 SOME ((ss, v), n6) =>
                                   INL ((sl ++ sl' ++ sr ++ cs ++ ss, v, ElabType BoolT), n6)
                               | NONE => INR [(info.node_id, "unsupported binary operator")])
                          | INL _ => INR [(info.node_id, "value count mismatch")]
                          | INR bs => INR bs))
                | INR bs => INR bs)
         | _ => reject (info.node_id, "unsupported operator type") (elab_expr ctx n1 r))
    | SrcAssignment info op lhs rhs tid =>
        ensure (IS_SOME (decode_type_identifier tid)) (info.node_id, "type annotation mismatch")
        (case lhs of
           SrcTupleExpression linfo cs ltid =>
             (case elab_values ctx n rhs of
                INL ((sr, vs), n1) =>
                  (* Each destination checks its own annotation; holes have
                   * no type in the enclosing tuple identifier. *)
                  if op ≠ NONE then INR [(info.node_id, "unsupported tuple assignment")] else
                  let (ss, vs', n2) = snapshot_values n1 vs in
                  (case elab_destinations ctx n2 cs of
                     INL ((ls, targets), n3) =>
                       (case tuple_writes n3 linfo.node_id targets vs' of
                          INL (ws, n4) =>
                            INL ((sr ++ ss ++ ls ++ ws, ConstantAtom (BoolValue F),
                                  ElabTuple []), n4)
                        | INR bs => INR bs)
                   | INR bs => INR bs)
              | INR bs => INR bs)
         | _ =>
             (case elab_expr ctx n rhs of
                INL ((sr, ar, vr), n1) =>
                  let (copied, n2) = case lhs of
                      SrcIdentifier _ _ _ _ => (([], ar), n1)
                    | _ => snapshot n1 ar vr in
                  let (sc, ar') = copied in
                  (case elab_destination ctx n2 lhs of
                     INL ((ls, target), n3) =>
                       let ty = destination_type target in
                       if op = NONE then
                         (case plain_assignment n3 target ar' vr of
                            INL ((cr, a, value_ty), n4) =>
                              if annotation_matches tid (ElabType value_ty) then
                                INL ((sr ++ sc ++ ls ++ cr, a, ElabType value_ty), n4)
                              else INR [(info.node_id, "type annotation mismatch")]
                          | INR why => INR [(expr_id rhs, why)])
                       else
                         (case compound_operator op of
                            SOME aop =>
                              if ¬annotation_matches tid (ElabType ty)
                              then INR [(info.node_id, "type annotation mismatch")] else
                              (case coerce n3 (right_operand_type aop ty) ar' vr of
                                 INL ((cr, a), n4) =>
                                   let (read, n5) = read_destination n4 target in
                                   let (rs, cur) = read in
                                   let (step, v) = bind_value n5 ty
                                     (ScalarOperation ty ctx.mode aop [cur; a]) in
                                   INL ((sr ++ sc ++ ls ++ cr ++ rs ++ step ++
                                           write_destination (n5 + 1) target v,
                                         v, ElabType ty), n5 + 2)
                               | INR why => INR [(expr_id rhs, why)])
                          | NONE => INR [(info.node_id, "unsupported compound assignment")])
                   | INR bs => INR bs)
              | INR bs => INR (bs ++ blockers (elab_destination ctx n lhs))))
    | SrcTupleExpression info [SOME e] tid =>
        (case elab_expr ctx n e of
           INL ((ss, a, vt), n1) =>
             if annotation_matches tid vt then INL ((ss, a, vt), n1)
             else INR [(info.node_id, "type annotation mismatch")]
         | INR bs => INR bs)
    | SrcTupleExpression info cs tid =>
        (case (decode_type_identifier tid, elab_components ctx n cs) of
           (SOME (SrcTupleType tys), INL ((ss, vs), n1)) =>
             if MEM NONE cs then INR [(info.node_id, "tuple with an empty component")] else
             (case convert_operands n1 info.node_id
                     (MAP (λc. case c of NONE => info.node_id | SOME e => expr_id e) cs)
                     (values_of tys) vs of
                INL (cs', _, atoms, n2) =>
                  INL ((ss ++ cs' ++ [DefineStmt (AstId n2) (ProductType (MAP SingleType tys))
                           (TupleOperation atoms)], BoundAtom (AstId n2), ElabTuple tys), n2 + 1)
              | INR bs => INR bs)
         | (_, INR bs) => INR bs
         | _ => INR [(info.node_id, "type annotation mismatch")])
    | SrcArrayMember info _ _ _ => INR [(info.node_id, "array member as a value")]
    | SrcFunctionCall info callee args order tid =>
        (case callee of
           SrcArrayMember _ member root_expr _ =>
             (case elab_location ctx n root_expr of
                INL ((ss, ref, ArrayT element NONE), n1) =>
                  if order ≠ [] ∨ ¬push_element_ok element
                  then INR [(info.node_id, "unsupported array member call")] else
                  if member = "push" then
                    (case args of
                       [] =>
                         if ¬source_type_matches element tid
                         then INR [(info.node_id, "type annotation mismatch")] else
                         let target = BoundAtom (AstId n1) in
                         let (rs, a) = bind_value (n1 + 1) element
                                         (ReadOperation element target) in
                         INL ((ss ++ [DefineStmt (AstId n1) (ReferenceType element)
                                        (ArrayPushOperation ref NONE)] ++ rs,
                               a, ElabType element), n1 + 2)
                     | [arg] =>
                         ensure (tid = "t_tuple$__$") (info.node_id, "type annotation mismatch")
                         (case elab_expr ctx n1 arg of
                            INL ((sa, a, vt), n2) =>
                              (case coerce n2 element a vt of
                                 INL ((cs, a'), n3) =>
                                   INL ((ss ++ sa ++ cs ++
                                           [DefineStmt (AstId n3) (ReferenceType element)
                                              (ArrayPushOperation ref (SOME a'))],
                                         ConstantAtom (BoolValue F), ElabTuple []), n3 + 1)
                               | INR why => INR [(expr_id arg, why)])
                          | INR bs => INR bs)
                     | _ => INR [(info.node_id, "unsupported array member call")])
                  else if member = "pop" ∧ args = [] ∧ tid = "t_tuple$__$" then
                    INL ((ss ++ [DefineStmt (AstId n1) (ProductType [])
                                   (ArrayPopOperation ref)],
                          ConstantAtom (BoolValue F), ElabTuple []), n1 + 1)
                  else INR [(info.node_id, "unsupported array member call")]
              | INL _ =>
                  reject (info.node_id, "unsupported array member call")
                    (elab_arg_values ctx n args)
              | INR bs => INR (bs ++ blockers (elab_arg_values ctx n args)))
         | SrcIdentifier finfo _ f _ =>
             (case ALOOKUP ctx.functions f of
                SOME callee =>
                  (case callee_types callee of
                     SOME (params, rets) =>
                       if ¬internal_call_ok callee rets args order tid
                       then reject (info.node_id, "call does not match the function")
                              (elab_arg_values ctx n args) else
                       (case elab_args ctx n info.node_id order params args of
                          INL ((sa, atoms), n1) =>
                            INL ((sa ++ [DefineStmt (AstId n1) (call_result_type rets)
                                           (InternalCallOperation
                                              (AstId callee.fn_info.node_id) atoms)],
                                  BoundAtom (AstId n1), call_value rets), n1 + 1)
                        | INR bs => INR bs)
                   | NONE =>
                       reject (info.node_id, "unsupported parameter type")
                         (elab_arg_values ctx n args))
              | NONE =>
                  INR ((finfo.node_id, "call of an unsupported function") ::
                       blockers (elab_arg_values ctx n args)))
         | _ =>
             INR ((info.node_id, "unsupported callee") ::
                  blockers (elab_arg_values ctx n args)))
    | SrcSuperCall info r args order tid =>
        (case ALOOKUP ctx.supers r of
           SOME callee =>
             (case callee_types callee of
                SOME (params, rets) =>
                  if ¬internal_call_ok callee rets args order tid
                  then reject (info.node_id, "call does not match the function")
                         (elab_arg_values ctx n args) else
                  (case elab_args ctx n info.node_id order params args of
                     INL ((sa, atoms), n1) =>
                       INL ((sa ++ [DefineStmt (AstId n1) (call_result_type rets)
                                      (InternalCallOperation
                                         (AstId callee.fn_info.node_id) atoms)],
                             BoundAtom (AstId n1), call_value rets), n1 + 1)
                   | INR bs => INR bs)
              | NONE =>
                  reject (info.node_id, "unsupported parameter type")
                    (elab_arg_values ctx n args))
         | NONE =>
             INR ((info.node_id, "unresolved super call") ::
                  blockers (elab_arg_values ctx n args)))
    | SrcBuiltinCall info _ builtin condition message tid =>
        if ¬(builtin_shape builtin condition message ∧ tid = "t_tuple$__$") then
          INR ((info.node_id, "unsupported builtin call") ::
               (case condition of NONE => [] | SOME c => blockers (elab_expr ctx n c)) ++
               (case message of NONE => [] | SOME m => blockers (elab_expr ctx n m)))
        else
        (let failure = builtin_failure builtin message in
         case condition of
           NONE => INL (([failure;
             DefineStmt (AstId n) (ProductType []) (TupleOperation [])],
             BoundAtom (AstId n), ElabTuple []), n + 1)
         | SOME c =>
             (case elab_expr ctx n c of
                INL ((ss, v, ElabType BoolT), n1) =>
                  INL ((ss ++ [IfStmt v [] [failure];
                    DefineStmt (AstId n1) (ProductType []) (TupleOperation [])],
                    BoundAtom (AstId n1), ElabTuple []), n1 + 1)
              | INL _ => INR [(expr_id c, "condition not a bool")]
              | INR bs => INR bs))
    (* Value only for a payable callee, as the compiler requires; calls
       returning enums are not supported yet. *)
    | SrcExternalCall info callee with_value operands order tid =>
        (let shape =
           (case (all_some (MAP call_variable_type callee.ext_parameters),
                  all_some (MAP call_variable_type callee.ext_returns)) of
              (SOME params, SOME rets) =>
                if (with_value ⇒ callee.ext_mutability = PayableMut) ∧
                   LENGTH operands = LENGTH params + (if with_value then 2 else 1) ∧
                   argument_order_ok order (LENGTH params) ∧
                   decode_type_identifier tid = SOME (call_value_type rets) ∧
                   EVERY (λty. case ty of EnumT _ => F | _ => T) rets
                then INL (params, rets) else INR (info.node_id, "unsupported external call")
            | _ => INR (info.node_id, "unsupported external call")) in
         case (shape, elab_arg_values ctx n operands) of
           (INR b, r) => reject b r
         | (INL _, INR bs) => INR bs
         | (INL (params, rets), INL ((ss, vs0), next)) =>
             (case (arrange order vs0, arrange order (expr_ids operands)) of
                (SOME vs, SOME ids) =>
                  (case convert_operands next info.node_id ids
                          (encoded_as (AddressT NonpayableAddress ::
                             (if with_value then [UintT 256] else []) ++ params)) vs of
                     INL (cs, _, t :: atoms, n1) =>
                       (case (with_value, atoms) of
                          (T, v :: args) =>
                            INL (external_call_value n1 callee.ext_mutability
                                   callee.ext_selector params rets (ss ++ cs) t v args)
                        | (F, args) =>
                            INL (external_call_value n1 callee.ext_mutability
                                   callee.ext_selector params rets (ss ++ cs) t
                                   (ConstantAtom (IntegerValue 0)) args)
                        | _ => INR [(info.node_id, "unsupported external call")])
                   | INL _ => INR [(info.node_id, "unsupported external call")]
                   | INR bs => INR bs)
              | _ => INR [(info.node_id, "unsupported external call")]))
    (* new T(n) of a byte sequence or dynamic memory array type *)
    | SrcNew info tn e tid =>
        (case elab_expr ctx n e of
           INL ((ss, a, vt), n1) =>
             (case normalize_type_name tn of
                SOME ty =>
                  if ¬((byte_sequence_type ty ∨
                        (memory_object_type ty ∧ case ty of ArrayT _ NONE => T | _ => F)) ∧
                       index_value_ok a vt ∧
                       source_type_matches (LocatedT MemoryLoc ty) tid)
                  then INR [(info.node_id, "unsupported new expression")] else
                  (case coerce n1 (UintT 256) a vt of
                     INL ((cs, a'), n2) =>
                       let (rs, v) = bind_value n2 (LocatedT MemoryLoc ty)
                                       (AllocateMemoryOperation ty a') in
                       INL ((ss ++ cs ++ rs, v, ElabType (LocatedT MemoryLoc ty)), n2 + 1)
                   | INR why => INR [(expr_id e, why)])
              | NONE => INR (type_name_blockers (info.node_id, "unsupported type name") tn))
         | INR bs =>
             INR (bs ++ type_name_blockers (info.node_id, "unsupported type name") tn))
    | SrcEnvironment info f tid =>
        if ¬source_type_matches (environment_type f) tid
        then INR [(info.node_id, "type annotation mismatch")] else
        let (ss, a) = bind_value n (environment_type f) (EnvironmentOperation f) in
        INL ((ss, a, ElabType (environment_type f)), n + 1)
    | SrcEnumValue info tn index tid =>
        (case normalize_type_name tn of
           SOME (EnumT (AstId id)) =>
             (case ALOOKUP ctx.enums id of
                SOME members =>
                  if ¬(index < members ∧ source_type_matches (EnumT (AstId id)) tid)
                  then INR [(info.node_id, "unsupported enum value")] else
                  let ty = EnumT (AstId id) in
                  let (ss, a) = bind_value n ty
                                  (ConvertOperation ty (ConstantAtom (IntegerValue (&index)))) in
                  INL ((ss, a, ElabType ty), n + 1)
              | NONE => INR [(info.node_id, "unsupported enum value")])
         | SOME _ => INR [(info.node_id, "unsupported enum value")]
         | NONE => INR (type_name_blockers (info.node_id, "unsupported enum value") tn))
    | SrcConditional info c t f tid =>
        (case decode_type_identifier tid of
           SOME (SrcTupleType tys) =>
             (case elab_expr ctx n c of
                INL ((sc, cond, ElabType BoolT), n1) =>
                  (case elab_values ctx n1 t of
                     INL ((st, vt), n2) =>
                       (case elab_values ctx n2 f of
                          INL ((sf, vf), n3) =>
                            (case convert_operands n3 info.node_id
                                    (REPLICATE (LENGTH vt) (expr_id t)) (values_of tys) vt of
                               INL (ct, _, at, n4) =>
                                 (case convert_operands n4 info.node_id
                                         (REPLICATE (LENGTH vf) (expr_id f)) (values_of tys) vf of
                                    INL (cf, _, af, n5) =>
                                      (case conditional_targets n5 tys at af of
                                         SOME (ds, ts, fs, atoms, n6) =>
                                           INL ((sc ++ ds ++
                                             [IfStmt cond (st ++ ct ++ ts) (sf ++ cf ++ fs);
                                              DefineStmt (AstId n6) (ProductType (MAP SingleType tys))
                                                (TupleOperation atoms)],
                                             BoundAtom (AstId n6), ElabTuple tys), n6 + 1)
                                       | NONE => INR [(info.node_id, "unsupported conditional type")])
                                  | INR bs => INR bs)
                             | INR bs => INR bs)
                        | INR bs => INR bs)
                   | INR bs => INR (bs ++ blockers (elab_values ctx n f)))
              | INL _ => INR [(expr_id c, "condition not a bool")]
              | INR bs => INR bs)
         | _ =>
        (* the result is declared first, and each branch writes it: a value
           or a memory reference, which the result local can hold *)
        (case elab_expr ctx n c of
           INL ((sc, ac', ElabType BoolT), n2) =>
             (case elab_expr ctx (n2 + 2) t of
                INL ((st, at, vt), n3) =>
                  (case identifier_type tid of
                     SOME ty =>
                       if ¬(case ty of LocatedT loc _ => loc = MemoryLoc
                                     | _ => is_stored_scalar_type ty)
                       then reject (info.node_id, "unsupported conditional type")
                              (elab_expr ctx n f) else
                       (case default_operation ty of
                          SOME op =>
                            (case coerce n3 ty at vt of
                               INL ((ct, at'), n4) =>
                                 (case elab_expr ctx (n4 + 1) f of
                                    INL ((sf, af, vf), n5) =>
                                      (case coerce n5 ty af vf of
                                         INL ((cf, af'), n6) =>
                                           let (rs, res) = bind_value n2 ty op in
                                           INL ((sc ++ rs ++
                                                 [IfStmt ac'
                                                    (st ++ ct ++ assign_local (n2 + 1) n2 ty at')
                                                    (sf ++ cf ++ assign_local n4 n2 ty af')],
                                                 res, ElabType ty), n6)
                                       | INR why => INR [(expr_id f, why)])
                                  | INR bs => INR bs)
                             | INR why =>
                                 reject (expr_id t, why)
                                   (case elab_expr ctx n f of
                                      INL ((_, af, vf), n4) =>
                                        (case coerce n4 ty af vf of
                                           INL x => INL x
                                         | INR why' => INR [(expr_id f, why')])
                                    | INR bs => INR bs))
                        | NONE =>
                            reject (info.node_id, "unsupported conditional type")
                              (elab_expr ctx n f))
                   | NONE =>
                       reject (info.node_id, "unsupported conditional type")
                         (elab_expr ctx n f))
              | INR bs => INR (bs ++ blockers (elab_expr ctx n f)))
         | INL _ =>
             INR ((expr_id c, "condition not a bool") ::
                  blockers (elab_expr ctx n t) ++ blockers (elab_expr ctx n f))
         | INR bs =>
             INR (bs ++ blockers (elab_expr ctx n t) ++ blockers (elab_expr ctx n f))))
    | SrcAddressCodeLength info _ e tid =>
        (case elab_expr ctx n e of
           INL ((ss, a, ElabType (AddressT _)), n1) =>
             if tid ≠ "t_uint256" then INR [(info.node_id, "type annotation mismatch")] else
             let (rs, r) = bind_value n1 (UintT 256) (CodeLengthOperation a) in
             INL ((ss ++ rs, r, ElabType (UintT 256)), n1 + 1)
         | INL _ => INR [(info.node_id, "code length of a non-address")]
         | INR bs => INR bs)
    (* keccak256 takes bytes memory; a literal, or bytes in another location,
       converts to it as an argument would *)
    | SrcKeccak256 info _ e tid =>
        (case elab_expr ctx n e of
           INL ((ss, a, vt), n1) =>
             if ¬(source_type_matches (FixedBytesT 32) tid ∧
                  case vt of
                    ElabBytesLiteral => T
                  | ElabType (LocatedT _ BytesT) => T
                  | _ => F) then INR [(info.node_id, "keccak256 of this type")] else
             (case coerce n1 (LocatedT MemoryLoc BytesT) a vt of
                INL ((cs, b), n2) =>
                  let (hs, h) = bind_value n2 (FixedBytesT 32) (Keccak256Operation b) in
                  INL ((ss ++ cs ++ hs, h, ElabType (FixedBytesT 32)), n2 + 1)
              | INR why => INR [(expr_id e, why)])
         | INR bs => INR bs)
    | SrcModular info _ op args tid =>
        (* the operands in order, then the modulus check and the operation *)
        ensure (source_type_matches (UintT 256) tid) (info.node_id, "type annotation mismatch")
        (case elab_arg_values ctx n args of
           INL ((ss, vs), n1) =>
             (case convert_operands n1 info.node_id (expr_ids args)
                     (values_of [UintT 256; UintT 256; UintT 256]) vs of
                INL (cs, _, as, n2) =>
                  let (rs, r) = bind_value n2 (UintT 256)
                                  (ScalarOperation (UintT 256) CheckedArithmetic op as) in
                  INL ((ss ++ cs ++ rs, r, ElabType (UintT 256)), n2 + 1)
              | INR bs => INR bs)
         | INR bs => INR bs)
    | SrcAbiEncode info _ form args tid =>
        (let ty = LocatedT MemoryLoc
                    (if form = AbiStringConcat then StringT else BytesT) in
         ensure (source_type_matches ty tid) (info.node_id, "type annotation mismatch")
         (case elab_arg_values ctx n args of
            INL ((ss, vs), n1) =>
              (case abi_encoding n1 info.node_id (expr_ids args) form vs of
                 INL ((cs, op), n2) =>
                   let (es, r) = bind_value n2 ty op in
                   INL ((ss ++ cs ++ es, r, ElabType ty), n2 + 1)
               | INR bs => INR bs)
          | INR bs => INR bs))
    | SrcEcrecover info _ args tid =>
        let ty = AddressT NonpayableAddress in
        ensure (annotation_matches tid (ElabType ty)) (info.node_id, "type annotation mismatch")
        (case elab_arg_values ctx n args of
           INL ((ss, vs), n1) =>
             (case convert_operands n1 info.node_id (expr_ids args)
                     (values_of [FixedBytesT 32; UintT 8; FixedBytesT 32;
                                 FixedBytesT 32]) vs of
                INL (cs, _, [h; v; r; s], n2) =>
                  let (es, a) = bind_value n2 ty (EcrecoverOperation h v r s) in
                  INL ((ss ++ cs ++ es, a, ElabType ty), n2 + 1)
              | INL _ => INR [(info.node_id, "value count mismatch")]
              | INR bs => INR bs)
         | INR bs => INR bs)
    | SrcStaticCall info _ target data tid =>
        (* the data is passed where it is, so it must already be memory bytes *)
        (case elab_expr ctx n target of
           INL ((st, t, tvt), n1) =>
             if ¬(case tvt of ElabType (AddressT _) => T | _ => F) ∨
                decode_type_identifier tid ≠
                  SOME (call_value_type [BoolT; LocatedT MemoryLoc BytesT])
             then reject (info.node_id, "unsupported static call") (elab_expr ctx n1 data) else
             let (copied, n2) =
               if expr_assigns data then snapshot n1 t tvt else (([], t), n1) in
             let (st', t') = copied in
             (case elab_expr ctx n2 data of
                INL ((sd, d, ElabType (LocatedT MemoryLoc BytesT)), n3) =>
                  (case coerce n3 (AddressT NonpayableAddress) t' tvt of
                     INL ((cs, t''), n4) =>
                       let tys = [BoolT; LocatedT MemoryLoc BytesT] in
                       INL ((st ++ st' ++ sd ++ cs ++
                             [DefineStmt (AstId n4) (call_result_type tys)
                                (StaticCallOperation t'' d)],
                             BoundAtom (AstId n4), call_value tys), n4 + 1)
                   | INR why => INR [(expr_id target, why)])
              | INL _ => INR [(expr_id data, "static call data not memory bytes")]
              | INR bs => INR bs)
         | INR bs => INR (bs ++ blockers (elab_expr ctx n data)))
    | SrcAbiDecode info _ e tns tid =>
        (* the data is decoded where it is, so it must already be memory bytes *)
        (case elab_expr ctx n e of
           INL ((ss, a, ElabType (LocatedT MemoryLoc BytesT)), n1) =>
             (case OPTION_MAP (MAP decoded_type) (all_some (MAP normalize_type_name tns)) of
                SOME (ty :: tys) =>
                  (* only elementary types decode: bytes and string are type names too *)
                  if ¬EVERY is_elementary_type (ty :: tys) ∨
                     decode_type_identifier tid ≠ SOME (call_value_type (ty :: tys))
                  then INR [(info.node_id, "abi decoding of these types")] else
                  INL ((ss ++ [DefineStmt (AstId n1) (call_result_type (ty :: tys))
                                 (AbiDecodeOperation (ty :: tys) a)],
                        BoundAtom (AstId n1), call_value (ty :: tys)), n1 + 1)
              | SOME [] => INR [(info.node_id, "abi decoding of these types")]
              | NONE =>
                  INR (FLAT (MAP (λtn. type_name_blockers
                                         (info.node_id, "unsupported type name") tn) tns)))
         | INL _ => INR [(expr_id e, "abi decoding of data not in memory bytes")]
         | INR bs => INR bs)
    (* f.selector, E.selector: the selector the compiler records on the
       declaration, bytes4 or (for an event) bytes32; bound, so that a later
       conversion converts a bytesN local *)
    | SrcSelector info bs tid =>
        let ty = FixedBytesT (LENGTH bs) in
        if ¬((LENGTH bs = 4 ∨ LENGTH bs = 32) ∧ source_type_matches ty tid)
        then INR [(info.node_id, "unsupported selector")] else
        let (ss, a) = bind_value n ty (ConvertOperation ty (ConstantAtom (BytesValue bs))) in
        INL ((ss, a, ElabType ty), n + 1)
    | SrcTypeMember info member tn tid =>
        (case normalize_type_name tn of
           SOME ty =>
             if ¬source_type_matches ty tid
             then INR [(info.node_id, "type annotation mismatch")] else
             (* bound to a local of type T, the source type of any
                later conversion *)
             (case type_bound member ty of
                SOME i =>
                  let (ss, a) = bind_value n ty
                                  (ConvertOperation ty (ConstantAtom (IntegerValue i))) in
                  INL ((ss, a, ElabType ty), n + 1)
              | NONE => INR [(info.node_id, "unsupported type member")])
         | NONE => INR (type_name_blockers (info.node_id, "unsupported type name") tn))
    (* to the target type, or a byte sequence to the annotated location *)
    | SrcTypeConversion info tn e tid =>
        (case elab_expr ctx n e of
           INL ((ss, a, vt), n1) =>
             (case (normalize_type_name tn, identifier_type tid) of
                (SOME target, SOME ty) =>
                  if ¬(ty = target ∨ (byte_sequence_type target ∧
                         case ty of LocatedT _ element => target = element | _ => F))
                  then INR [(info.node_id, "unsupported type conversion")] else
                  (case (vt, ty, a) of
                     (ElabTuple _, _, _) => INR [(expr_id e, "tuple used as a value")]
                   | (ElabRational, _, _) => INR [(expr_id e, "rational number value")]
                   (* bytes to bytesN: the core has no such conversion *)
                   | (ElabType (LocatedT _ _), FixedBytesT _, _) =>
                       INR [(info.node_id, "unsupported type conversion")]
                   | (ElabBytesLiteral, _, _) =>
                       (case coerce n1 ty a vt of
                          INL ((cs, v), n2) => INL ((ss ++ cs, v, ElabType ty), n2)
                        | INR why => INR [(expr_id e, why)])
                   | (ElabLiteral, AddressT _, ConstantAtom (IntegerValue i)) =>
                     (* address(0): the literal is the address, as in solc *)
                     if 0 ≤ i ∧ i < 2 ** 160 then
                       INL ((ss, ConstantAtom (AddressValue (n2w (Num i))),
                             ElabType ty), n1)
                     else INR [(info.node_id, "unsupported type conversion")]
                   | (ElabLiteral, FixedBytesT k, ConstantAtom (IntegerValue i)) =>
                     (* bytesN(0) or a hex literal of N bytes: the literal is the
                        bytes, as in solc; bound like the min/max members above *)
                     if 0 ≤ i ∧ i < 2 ** (8 * k) then
                       let (cs, v) = bind_value n1 ty
                             (ConvertOperation ty
                                (ConstantAtom (BytesValue (num_to_bytes k (Num i))))) in
                       INL ((ss ++ cs, v, ElabType ty), n1 + 1)
                     else INR [(info.node_id, "unsupported type conversion")]
                   | (ElabType src, _, ConstantAtom s) =>
                     if src = ty then
                       let (cs, v) = bind_value n1 ty
                             (ConvertOperation ty (ConstantAtom s)) in
                       INL ((ss ++ cs, v, ElabType ty), n1 + 1)
                     else
                       let (bs, b) = bind_value n1 src
                             (ConvertOperation src (ConstantAtom s)) in
                       let (cs, v) = bind_value (n1 + 1) ty (ConvertOperation ty b) in
                       INL ((ss ++ bs ++ cs, v, ElabType ty), n1 + 2)
                   | _ =>
                     let (cs, v) = bind_value n1 ty (ConvertOperation ty a) in
                     INL ((ss ++ cs, v, ElabType ty), n1 + 1))
              | (NONE, _) =>
                  INR (type_name_blockers (info.node_id, "unsupported type name") tn)
              | _ => INR [(info.node_id, "type annotation mismatch")])
         | INR bs =>
             INR (bs ++ type_name_blockers (info.node_id, "unsupported type name") tn))
    | SrcUnsupportedExpr info msg es =>
        INR ((info.node_id, msg) :: blockers (elab_arg_values ctx n es))) ∧
  (* Capture every argument before any location conversion copies contents. *)
  (* Arguments are evaluated in the call's order and passed in the
     parameters' (arrange); id is the call's. *)
  (elab_args ctx n (id : num) order tys es =
    case elab_arg_values ctx n es of
      INL ((ss, vs), n1) =>
        (case (arrange order vs, arrange order (expr_ids es)) of
           (SOME vs', SOME ids) =>
             (case convert_operands n1 id ids (values_of tys) vs' of
                INL (cs, _, as, n2) => INL ((ss ++ cs, as), n2)
              | INR bs => INR bs)
         | _ => INR [(id, "argument order")])
    | INR bs => INR bs) ∧
  (* Multiple values: tuple expressions, and calls with several returns. *)
  (elab_values ctx n e =
    case e of
      SrcTupleExpression info cs tid =>
        ensure (IS_SOME (decode_type_identifier tid)) (info.node_id, "type annotation mismatch")
        (case cs of
           [SOME e'] => elab_values ctx n e'
         | _ =>
           case elab_components ctx n cs of
             INL r =>
               if MEM NONE cs then INR [(info.node_id, "tuple with an empty component")]
               else INL r
           | INR bs => INR bs)
    | _ =>
      case elab_expr ctx n e of
        INL ((ss, a, ElabTuple tys), n1) =>
          let (cs, vs, n2) = tuple_components n1 a 0 tys in
          INL ((ss ++ cs, vs), n2)
      | INL ((ss, a, vt), n1) =>
          if vt = ElabRational then INR [(expr_id e, "rational number value")]
          else INL ((ss, [(a, vt)]), n1)
      | INR bs => INR bs) ∧
  (* The components of a tuple, its holes (which it rejects) left out. *)
  (elab_components ctx n [] = INL (([], []), n)) ∧
  (elab_components ctx n (SOME e :: cs) =
    case elab_expr ctx n e of
      INL ((ss, a, vt), n1) =>
        if vt = ElabRational then
          INR ((expr_id e, "rational number value") :: blockers (elab_components ctx n cs))
        else
        let (copied, n2) =
          if components_assign cs then snapshot n1 a vt else (([], a), n1) in
        let (ss1, a1) = copied in
        (case elab_components ctx n2 cs of
           INL ((ss', vs), n3) =>
             INL ((ss ++ ss1 ++ ss', (a1, vt) :: vs), n3)
         | INR bs => INR bs)
    | INR bs => INR (bs ++ blockers (elab_components ctx n cs))) ∧
  (elab_components ctx n (NONE :: cs) = elab_components ctx n cs) ∧
  (* Only state roots and indexed suffixes are storage locations. Index keys
   * are converted and consumed immediately, before later keys can mutate them.
   *)
  (elab_location ctx n e =
    case e of
      SrcIdentifier info _ x tid =>
        (case ALOOKUP ctx.state x of
           SOME ty =>
             if ¬source_type_matches ty tid
             then INR [(info.node_id, "type annotation mismatch")] else
             INL (([DefineStmt (AstId n) (ReferenceType ty)
                      (StateReferenceOperation (AstId x))],
                   BoundAtom (AstId n), ty), n + 1)
         | NONE => unknown_reference ctx info.node_id "not a storage location" x)
    | SrcMemberAccess info root_expr member_id tid =>
        (case elab_location ctx n root_expr of
           INL ((ss, ref, StructT (AstId id)), n1) =>
             (case source_struct_field ctx.structs id member_id of
                SOME ty =>
                  if ¬source_type_matches ty tid
                  then INR [(info.node_id, "type annotation mismatch")] else
                  INL ((ss ++
                    [DefineStmt (AstId n1) (ReferenceType ty)
                      (NavigateOperation ty ref (FieldNavigation (AstId member_id)))],
                    BoundAtom (AstId n1), ty), n1 + 1)
              | NONE => INR [(info.node_id, "unknown struct member")])
         | INL _ => INR [(info.node_id, "member access on a non-struct")]
         | INR bs => INR bs)
    | SrcIndexAccess info root_expr index tid =>
        (case elab_expr ctx n root_expr of
           INL ((ss, ref, ElabType (LocatedT loc BytesT)), n1) =>
             let (captured, next) = snapshot n1 ref (ElabType (LocatedT loc BytesT)) in
             let (saved, ref') = captured in
             ensure (loc ≠ CalldataLoc) (info.node_id, "write to calldata")
             (ensure (tid = "t_bytes1") (info.node_id, "type annotation mismatch")
              (case elab_expr ctx next index of
                 INL ((si, a, vt), n2) =>
                   if ¬index_value_ok a vt then INR [(expr_id index, "index of this type")] else
                   (case coerce n2 (UintT 256) a vt of
                      INL ((cs, a'), n3) =>
                        INL ((ss ++ saved ++ si ++ cs ++
                          [DefineStmt (AstId n3) (ReferenceType (FixedBytesT 1))
                            (NavigateOperation (FixedBytesT 1) ref' (IndexNavigation a'))],
                          BoundAtom (AstId n3), FixedBytesT 1), n3 + 1)
                    | INR why => INR [(expr_id index, why)])
               | INR bs => INR bs))
         | r =>
           (* a storage root is a location: when that fails too, the reason
              is the value's, unless the value was elaborated *)
           case elab_location ctx n root_expr of
           INL ((ss, ref, MappingT key value), n1) =>
             ensure (source_type_matches value tid) (info.node_id, "type annotation mismatch")
             (case elab_expr ctx n1 index of
                INL ((si, a, vt), n2) =>
                  (case coerce n2 key a vt of
                     INL ((cs, a'), n3) =>
                       INL ((ss ++ si ++ cs ++
                             [DefineStmt (AstId n3) (ReferenceType value)
                               (NavigateOperation value ref (IndexNavigation a'))],
                             BoundAtom (AstId n3), value), n3 + 1)
                   | INR why => INR [(expr_id index, why)])
              | INR bs => INR bs)
         | INL ((ss, ref, ArrayT element _), n1) =>
             ensure (source_type_matches element tid) (info.node_id, "type annotation mismatch")
             (case elab_expr ctx n1 index of
                INL ((si, a, vt), n2) =>
                  if ¬index_value_ok a vt then INR [(expr_id index, "index of this type")] else
                  (case coerce n2 (UintT 256) a vt of
                     INL ((cs, a'), n3) =>
                       INL ((ss ++ si ++ cs ++
                             [DefineStmt (AstId n3) (ReferenceType element)
                               (NavigateOperation element ref (IndexNavigation a'))],
                             BoundAtom (AstId n3), element), n3 + 1)
                   | INR why => INR [(expr_id index, why)])
              | INR bs => INR bs)
         | INL _ => INR [(info.node_id, "index access on this type")]
         | INR _ =>
             INR ((case r of
                     INL _ => [(info.node_id, "index access on this type")]
                   | INR bs => bs) ++
                  blockers (elab_expr ctx n index)))
    | SrcFunctionCall info (SrcArrayMember _ member root_expr _) [] [] tid =>
        (case elab_location ctx n root_expr of
           INL ((ss, ref, ArrayT element NONE), n1) =>
             if ¬(member = "push" ∧ push_element_ok element ∧ source_type_matches element tid)
             then INR [(info.node_id, "unsupported array member call")] else
             INL ((ss ++ [DefineStmt (AstId n1) (ReferenceType element)
                            (ArrayPushOperation ref NONE)],
                   BoundAtom (AstId n1), element), n1 + 1)
         | INL _ => INR [(info.node_id, "unsupported array member call")]
         | INR bs => INR bs)
    | SrcUnsupportedExpr info msg es =>
        INR ((info.node_id, msg) :: blockers (elab_arg_values ctx n es))
    | _ => INR [(expr_id e, "not a storage location")]) ∧
  (elab_destination ctx n e =
    case e of
      SrcIdentifier info _ x tid =>
        (case variable_destination ctx n x tid of
           SOME d => INL d
         | NONE => unknown_reference ctx info.node_id "assignment to this target" x)
    | SrcIndexAccess info root_expr index tid =>
          (case elab_expr ctx n root_expr of
             INL ((ss, ref, ElabType (LocatedT MemoryLoc ty)), n1) =>
               if ¬(ty = BytesT ∨ case ty of ArrayT _ _ => T | _ => F)
               then INR [(info.node_id, "index access on this type")] else
               let (captured, next) =
                 snapshot n1 ref (ElabType (LocatedT MemoryLoc ty)) in
               let (saved, ref') = captured in
               ensure (source_type_matches
                         (destination_type (ElementDestination ref' ref' ty)) tid)
                 (info.node_id, "type annotation mismatch")
               (case elab_expr ctx next index of
                  INL ((si, i, vt), n2) =>
                    if ¬index_value_ok i vt then INR [(expr_id index, "index of this type")] else
                    (case coerce n2 (UintT 256) i vt of
                       INL ((cs, i'), n3) =>
                         INL ((ss ++ saved ++ si ++ cs,
                               ElementDestination ref' i' ty), n3)
                     | INR why => INR [(expr_id index, why)])
                | INR bs => INR bs)
           | _ =>
             (* elab_location reports the value's reason when both fail *)
             case elab_location ctx n e of
               INL ((ss, ref, ty), n1) =>
                 INL ((ss, ReferenceDestination ref ty), n1)
             | INR bs => INR bs)
    | _ =>
        case elab_location ctx n e of
          INL ((ss, ref, ty), n1) =>
            INL ((ss, ReferenceDestination ref ty), n1)
        | INR bs => INR bs)
  ∧
  (elab_arg_values ctx n [] = INL (([], []), n)) ∧
  (elab_arg_values ctx n (e :: es) =
    case elab_expr ctx n e of
      INL ((ss, a, vt), n1) =>
        let (captured, n2) =
          if exprs_assign es then snapshot n1 a vt else (([], a), n1) in
        let (saved, a') = captured in
        (case elab_arg_values ctx n2 es of
           INL ((ss', vs), n3) => INL ((ss ++ saved ++ ss', (a', vt) :: vs), n3)
         | INR bs => INR bs)
    | INR bs => INR (bs ++ blockers (elab_arg_values ctx n es))) ∧
  (elab_destinations ctx n [] = INL (([], []), n)) ∧
  (elab_destinations ctx n (NONE :: cs) =
    case elab_destinations ctx n cs of
      INL ((ss, targets), n1) => INL ((ss, NONE :: targets), n1)
    | INR bs => INR bs) ∧
  (elab_destinations ctx n (SOME e :: cs) =
    case elab_destination ctx n e of
      INL ((ss, target), n1) =>
        let (saved, target', next) = case target of
          ElementDestination ref index ty =>
            let (captured, n2) = snapshot n1 index (ElabType (UintT 256)) in
            let (is, i) = captured in
            (is, ElementDestination ref i ty, n2)
        | ReferenceDestination _ ty =>
            (if memory_object_type ty then [] else capture_destination n1 target,
             target, n1 + 1)
        | _ => (capture_destination n1 target, target, n1 + 1) in
        (case elab_destinations ctx next cs of
           INL ((ss', targets), n2) =>
             INL ((ss ++ saved ++ ss', SOME (n1, target') :: targets), n2)
         | INR bs => INR bs)
    | INR bs => INR (bs ++ blockers (elab_destinations ctx n cs)))
Termination
  qexists_tac ‘measure (λx. case x of
     INL (ctx, n, e) => 4 * src_expr_size e + 2
   | INR (INL (ctx, n, id, order, tys, es)) => 4 * list_size src_expr_size es + 1
   | INR (INR (INL (ctx, n, e))) => 4 * src_expr_size e + 3
   | INR (INR (INR (INL (ctx, n, cs)))) =>
       4 * list_size (option_size src_expr_size) cs
   | INR (INR (INR (INR (INL (ctx, n, e))))) => 4 * src_expr_size e + 1
   | INR (INR (INR (INR (INR (INL (ctx, n, e)))))) => 4 * src_expr_size e + 2
   | INR (INR (INR (INR (INR (INR (INL (ctx, n, es))))))) => 4 * list_size src_expr_size es
   | INR (INR (INR (INR (INR (INR (INR (ctx, n, cs))))))) =>
       4 * list_size (option_size src_expr_size) cs + 3)’ >>
  conj_tac >- simp[prim_recTheory.WF_measure] >>
  (* only the equations naming the node matter: the case hypotheses about
     the children's results are large, so they are dropped, not simplified *)
  rpt strip_tac >> rpt BasicProvers.VAR_EQ_TAC >> rpt (pop_assum kall_tac) >>
  simp[prim_recTheory.measure_thm, solidityImportTheory.src_expr_size_def,
       listTheory.list_size_def, basicSizeTheory.option_size_def]
End

(* A boolean condition. *)
Definition elab_condition_def:
  elab_condition ctx n c =
    case elab_expr ctx n c of
      INL ((ss, a, ElabType BoolT), n1) => INL ((ss, a), n1)
    | INL _ => INR [(expr_id c, "condition not a bool")]
    | INR bs => INR bs
End

(* A declaration statement lists its declarations' ids as assignments, and
 * declares its locals in the current scope; the locals are visible after the
 * statement only. *)
Definition declaration_ok_def:
  declaration_ok ctx assigned decls ⇔
    decls ≠ [] ∧
    assigned = MAP (OPTION_MAP (λ(v : src_variable). v.var_info.node_id)) decls ∧
    EVERY (λd. case d of NONE => T | SOME v => v.var_scope = ctx.scope) decls
End

(* The variables of a declaration statement, defined from its values, which
 * are converted to the declared types; holes discard their values.
 *)
Definition declare_values_def:
  (declare_values ctx n (id : num) [] [] = INL ([], ctx, n)) ∧
  (declare_values ctx n id (NONE :: ds) (_ :: vs) = declare_values ctx n id ds vs) ∧
  (declare_values ctx n id (SOME (v : src_variable) :: ds) ((a, vt) :: vs) =
    case variable_type v of
      SOME ty =>
        (case coerce n ty a vt of
           INL ((cs, a'), n1) =>
             (case declare_values
                     (ctx with variables :=
                        (v.var_info.node_id, ty) :: ctx.variables)
                     n1 id ds vs of
                INL (ss, ctx', n2) =>
                  INL (cs ++ [DefineStmt (AstId v.var_info.node_id)
                                (SingleType ty) (ConvertOperation ty a')] ++
                       ss, ctx', n2)
              | INR bs => INR bs)
         | INR why =>
             INR ((v.var_info.node_id, why) :: blockers (declare_values ctx n id ds vs)))
    | NONE =>
        INR (variable_blockers "unsupported variable type" v ++
             blockers (declare_values ctx n id ds vs))) ∧
  (declare_values ctx n id _ _ = INR [(id, "value count mismatch")])
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
    OPTION_MAP (λty. (ty, indexed)) (event_variable_type v)
End

Definition emit_arguments_def:
  (emit_arguments ((ty, indexed) :: ps) (a :: as) =
    (ty, indexed, a) :: emit_arguments ps as) ∧
  (emit_arguments _ _ = [])
End

(* Writes of a call's values to return variables. *)
Definition return_writes_def:
  (return_writes n ((x, ty) :: rs) ((a, _) :: vs) =
    assign_local n x ty a ++ return_writes (n + 1) rs vs) ∧
  (return_writes n _ _ = [])
End

(* The placeholder of a modifier: a call of the procedure of the rest of the
 * function with its parameters, whose values become the return variables.
 *)
Definition placeholder_call_def:
  placeholder_call n next ps rs =
    let call = DefineStmt (AstId n) (call_result_type (MAP SND rs))
                 (InternalCallOperation (AstId next) (return_atoms ps)) in
    let (ss, vs, n1) =
      case rs of
        [(_, ty)] => ([], [(BoundAtom (AstId n), ElabType ty)], n + 1)
      | _ => tuple_components (n + 1) (BoundAtom (AstId n)) 0 (MAP SND rs) in
    (call :: ss ++ return_writes n1 rs vs, n1 + LENGTH rs)
End

(* Statements; lists return the context after their declarations. Nested
 * blocks are spliced into the enclosing list: ids are unique, so the core
 * scopes need not mirror the source blocks.
 *)
(* A local keeps its declared type, one of the value types the block can read
 * and write as a word, or a memory byte sequence, which the block reads as
 * its address. A constant of value type is read before the block, as an
 * expression reads it.
 *)
Definition elab_assembly_reference_def:
  (elab_assembly_reference ctx n (id : num) (SrcAssemblyValue x) =
    case ALOOKUP ctx.variables x of
      SOME ty =>
        if assembly_value_type ty then INL (([], AssemblyLocal (AstId x) ty), n)
        else
          (case ty of
             LocatedT MemoryLoc t =>
               if byte_sequence_type t then INL (([], AssemblyMemory (AstId x) t), n)
               else INR [(id, "assembly reference of this type")]
           | _ => INR [(id, "assembly reference of this type")])
    | NONE =>
      case ALOOKUP ctx.constants x of
        SOME (ty, w) =>
          if assembly_value_type ty then
            let p = if ctx.mode = CheckedArithmetic then x else w in
            let (ss, a) = bind_value n ty (InternalCallOperation (AstId p) []) in
            INL ((ss, AssemblyConstant a ty), n + 1)
          else INR [(id, "assembly reference of this type")]
      | NONE => unknown_reference ctx id "unsupported assembly reference" x) ∧
  (elab_assembly_reference ctx n id (SrcAssemblySlot x) =
    if IS_SOME (ALOOKUP ctx.locations x) then INL (([], AssemblySlot (AstId x)), n)
    else unknown_reference ctx id "unsupported assembly reference" x) ∧
  (elab_assembly_reference ctx n id (SrcAssemblyOffset x) =
    if IS_SOME (ALOOKUP ctx.locations x) then INL (([], AssemblyOffset (AstId x)), n)
    else unknown_reference ctx id "unsupported assembly reference" x)
End

Definition elab_assembly_references_def:
  (elab_assembly_references ctx n (id : num) [] = INL (([], []), n)) ∧
  (elab_assembly_references ctx n id ((name, r) :: refs) =
    case elab_assembly_reference ctx n id r of
      INL ((ss, r'), n1) =>
        (case elab_assembly_references ctx n1 id refs of
           INL ((ss', rs), n2) => INL ((ss ++ ss', (name, r') :: rs), n2)
         | INR bs => INR bs)
    | INR bs => INR (bs ++ blockers (elab_assembly_references ctx n id refs)))
End

(* Ordinary external-call lowering has already evaluated and coerced every
 * operand; only its final operation belongs inside the catching boundary. *)
Definition try_external_call_def:
  try_external_call ss result =
    case REVERSE ss of
      DefineStmt x _ (ExternalCallOperation kind selector params rets target value args) :: pre =>
        if result = BoundAtom x ∧ EVERY is_stored_scalar_type rets then
          let types = BoolT :: rets ++ [LocatedT MemoryLoc BytesT] in
          SOME (REVERSE pre ++
            [DefineStmt x (ProductType (MAP SingleType types))
              (TryExternalCallOperation kind selector params rets target value args)],
            types)
        else NONE
    | _ => NONE
End

(* A try statement's call as a catching external call: its statements, the
 * success flag, the values of the success clause's variables and the revert
 * data, when the call is an external call returning scalars, which the
 * success clause's variables take, and the catch clause takes memory bytes;
 * ok and err are the clauses' ids. *)
Definition try_call_def:
  try_call n call ok err ps reason body handler ss r =
    case (call, all_some (MAP (scoped_variable ok) ps),
          scoped_variable err reason, try_external_call ss r) of
      (SrcExternalCall _ callee _ _ _ _, SOME locals,
       SOME (_, LocatedT MemoryLoc BytesT), SOME (cs, types)) =>
        if ¬(EVERY (is_stored_scalar_type o SND) locals ∧
             all_some (MAP variable_type callee.ext_returns) = SOME (MAP SND locals) ∧
             ¬is_declaration body ∧ ¬is_declaration handler)
        then NONE else
        let (xs, values, n1) = tuple_components n r 0 types in
        (case values of
           (condition, _) :: rest =>
             (case DROP (LENGTH ps) rest of
                [failure] =>
                  SOME (cs ++ xs, condition, TAKE (LENGTH ps) rest, failure, n1)
              | _ => NONE)
         | [] => NONE)
    | _ => NONE
End

(* The context after a declaration statement that failed: its variables of a
 * supported type are bound, and the others are bad, so that the statements
 * after it report only their own blockers. *)
Definition bind_failed_def:
  (bind_failed ctx [] = ctx) ∧
  (bind_failed ctx (NONE :: ds) = bind_failed ctx ds) ∧
  (bind_failed ctx (SOME (v : src_variable) :: ds) =
    bind_failed
      (case variable_type v of
         SOME ty => ctx with variables := (v.var_info.node_id, ty) :: ctx.variables
       | NONE => ctx with bad_ids := v.var_info.node_id :: ctx.bad_ids) ds)
End

Definition after_failure_def:
  after_failure ctx st =
    case st of
      SrcVariableDeclarationStatement _ _ decls _ => bind_failed ctx decls
    | _ => ctx
End

Definition elab_stmts_def:
  (elab_stmts ctx n [] = INL (([], ctx), n)) ∧
  (elab_stmts ctx n (st :: ss) =
    case elab_stmt ctx n st of
      INL ((cs, ctx'), n1) =>
        (case elab_stmts ctx' n1 ss of
           INL ((cs', ctx''), n2) => INL ((cs ++ cs', ctx''), n2)
         | INR bs => INR bs)
    | INR bs => INR (bs ++ blockers (elab_stmts (after_failure ctx st) n ss))) ∧
  (elab_stmt ctx n (SrcBlock info ss) =
    case elab_stmts (ctx with scope := info.node_id) n ss of
      INL ((cs, _), n1) => INL ((cs, ctx), n1)
    | INR bs => INR bs) ∧
  (elab_stmt ctx n (SrcUncheckedBlock info ss) =
    case elab_stmts (ctx with <| mode := UncheckedArithmetic;
                                 scope := info.node_id |>) n ss of
      INL ((cs, _), n1) => INL ((cs, ctx), n1)
    | INR bs => INR bs) ∧
  (elab_stmt ctx n (SrcExpressionStatement _ e) =
    case elab_expr ctx n e of
      INL ((ss, _, vt), n1) =>
        if vt = ElabRational then INR [(expr_id e, "rational number value")]
        else INL ((ss, ctx), n1)
    | INR bs => INR bs) ∧
  (* try of an external call returning scalars, its success clause binding
     them and its catch clause the revert data *)
  (elab_stmt ctx n (SrcTryStatement info call ok ps body err reason handler) =
    case elab_expr ctx n call of
      INR bs =>
        INR (bs ++ blockers (elab_stmt (bind_failed ctx (MAP SOME ps)) n body) ++
             blockers (elab_stmt (bind_failed ctx [SOME reason]) n handler))
    | INL ((ss, r, _), n1) =>
    case try_call n1 call ok.node_id err.node_id ps reason body handler ss r of
      NONE =>
        INR ((case variables_blockers (MAP SOME (reason :: ps)) of
                [] => [(info.node_id, "unsupported try statement")]
              | bs => bs) ++
             blockers (elab_stmt (bind_failed ctx (MAP SOME ps)) n body) ++
             blockers (elab_stmt (bind_failed ctx [SOME reason]) n handler))
    | SOME (cs, condition, values, failure, n2) =>
        (case declare_values ctx n2 info.node_id (MAP SOME ps) values of
           INL (ds, ctx1, n3) =>
             (case elab_stmt ctx1 n3 body of
                INL ((bs, _), n4) =>
                  (case declare_values ctx n4 info.node_id [SOME reason] [failure] of
                     INL (es, ctx2, n5) =>
                       (case elab_stmt ctx2 n5 handler of
                          INL ((hs, _), n6) =>
                            INL ((cs ++ [IfStmt condition (ds ++ bs) (es ++ hs)], ctx), n6)
                        | INR bs => INR bs)
                   | INR bs =>
                       INR (bs ++ blockers (elab_stmt
                              (bind_failed ctx [SOME reason]) n handler)))
              | INR bs =>
                  INR (bs ++ blockers (elab_stmt
                         (bind_failed ctx [SOME reason]) n handler)))
         | INR bs =>
             INR (bs ++ blockers (elab_stmt (bind_failed ctx (MAP SOME ps)) n body) ++
                  blockers (elab_stmt (bind_failed ctx [SOME reason]) n handler)))) ∧
  (elab_stmt ctx n (SrcVariableDeclarationStatement info assigned [SOME v] NONE) =
    case variable_type v of
      SOME ty =>
        if ¬declaration_ok ctx assigned [SOME v]
        then INR [(info.node_id, "unsupported declaration")] else
        (case default_operation ty of
           SOME op =>
             INL (([DefineStmt (AstId v.var_info.node_id) (SingleType ty) op],
                   ctx with variables := (v.var_info.node_id, ty) :: ctx.variables), n)
         | NONE => INR [(v.var_info.node_id, "local of this type without a value")])
    | NONE => INR (variable_blockers "unsupported variable type" v)) ∧
  (elab_stmt ctx n (SrcVariableDeclarationStatement info assigned decls (SOME e)) =
    case elab_values ctx n e of
      INL ((ss, vs), n1) =>
        if ¬declaration_ok ctx assigned decls
        then INR [(info.node_id, "unsupported declaration")] else
        (case declare_values ctx n1 info.node_id decls vs of
           INL (ds, ctx', n2) => INL ((ss ++ ds, ctx'), n2)
         | INR bs => INR bs)
    | INR bs => INR (bs ++ variables_blockers decls)) ∧
  (elab_stmt ctx n (SrcVariableDeclarationStatement info _ _ _) =
    INR [(info.node_id, "declaration without a value")]) ∧
  (elab_stmt ctx n (SrcIfStatement info c t e) =
    ensure (¬(is_declaration t ∨ (case e of SOME e => is_declaration e | NONE => F)))
      (info.node_id, "declaration as a body")
    (case elab_condition ctx n c of
       INL ((cs, a), n1) =>
         (case elab_stmt ctx n1 t of
            INL ((ts, _), n2) =>
              (case e of
                 NONE => INL ((cs ++ [IfStmt a ts []], ctx), n2)
               | SOME e =>
                   (case elab_stmt ctx n2 e of
                      INL ((es, _), n3) =>
                        INL ((cs ++ [IfStmt a ts es], ctx), n3)
                    | INR bs => INR bs))
          | INR bs => INR (bs ++ blockers (elab_for_init ctx n e)))
     | INR bs =>
         INR (bs ++ blockers (elab_stmt ctx n t) ++ blockers (elab_for_init ctx n e)))) ∧
  (elab_stmt ctx n (SrcWhileStatement info c bd) =
    ensure (¬is_declaration bd) (info.node_id, "declaration as a body")
    (case elab_condition ctx n c of
       INL ((cs, a), n1) =>
         (case elab_stmt (ctx with in_loop := T) n1 bd of
            INL ((bs, _), n2) => INL (([WhileStmt cs a bs], ctx), n2)
          | INR bs => INR bs)
     | INR bs => INR (bs ++ blockers (elab_stmt (ctx with in_loop := T) n bd)))) ∧
  (elab_stmt ctx n (SrcDoWhileStatement info bd c) =
    (* n: first-iteration flag; n + 1: condition result; n + 2, n + 3: targets *)
    ensure (¬is_declaration bd) (info.node_id, "declaration as a body")
    (case elab_condition ctx (n + 4) c of
       INL ((cs, a), n1) =>
         (case elab_stmt (ctx with in_loop := T) n1 bd of
            INL ((bs, _), n2) =>
              INL (([flag n; flag (n + 1);
                     WhileStmt
                       ([IfStmt (BoundAtom (AstId n)) []
                           (cs ++ set_flag (n + 2) (n + 1) a)] ++
                        set_flag (n + 3) n (ConstantAtom (BoolValue F)))
                       (BoundAtom (AstId (n + 1))) bs], ctx), n2)
          | INR bs => INR bs)
     | INR bs => INR (bs ++ blockers (elab_stmt (ctx with in_loop := T) n bd)))) ∧
  (* for (init; c; next): init a declaration or an expression statement,
     next an expression statement, in the scope of the for statement *)
  (elab_stmt ctx n (SrcForStatement info ini c nx bd) =
    ensure ((case ini of
               NONE => T
             | SOME (SrcVariableDeclarationStatement _ _ _ _) => T
             | SOME (SrcExpressionStatement _ _) => T
             | _ => F) ∧
            (case nx of NONE => T | SOME (SrcExpressionStatement _ _) => T | _ => F) ∧
            ¬is_declaration bd)
      (info.node_id, "unsupported for statement")
    (case elab_for_init (ctx with scope := info.node_id) n ini of
       INL ((is, ctx1), n1) =>
         (* n1: first-iteration flag; n1 + 1: its target *)
         (case (case c of
                  NONE => INL (([], ConstantAtom (BoolValue T)), n1 + 2)
                | SOME c => elab_condition ctx1 (n1 + 2) c) of
            INL ((cs, a), n2) =>
              (case elab_for_init ctx1 n2 nx of
                 INL ((ns, _), n3) =>
                   (case elab_stmt (ctx1 with in_loop := T) n3 bd of
                      INL ((bs, _), n4) =>
                        INL ((is ++
                              [flag n1;
                               WhileStmt
                                 ([IfStmt (BoundAtom (AstId n1)) [] ns] ++
                                  set_flag (n1 + 1) n1
                                    (ConstantAtom (BoolValue F)) ++ cs)
                                 a bs], ctx), n4)
                    | INR bs => INR bs)
               | INR bs =>
                   INR (bs ++ blockers (elab_stmt (ctx1 with in_loop := T) n bd)))
          | INR bs =>
              INR (bs ++ blockers (elab_for_init ctx1 n nx) ++
                   blockers (elab_stmt (ctx1 with in_loop := T) n bd)))
     | INR bs =>
         let ctx1 = (case ini of
                       SOME st => after_failure (ctx with scope := info.node_id) st
                     | NONE => ctx with scope := info.node_id) in
         INR (bs ++
              (case c of NONE => [] | SOME c => blockers (elab_condition ctx1 n c)) ++
              blockers (elab_for_init ctx1 n nx) ++
              blockers (elab_stmt (ctx1 with in_loop := T) n bd)))) ∧
  (elab_stmt ctx n (SrcPlaceholder info) =
    case ctx.placeholder of
      SOME (next, ps) =>
        let (ss, n1) = placeholder_call n next ps ctx.returns in
        INL ((ss, ctx), n1)
    | NONE => INR [(info.node_id, "placeholder outside a modifier")]) ∧
  (elab_stmt ctx n (SrcBreak info) =
    if ctx.in_loop then INL (([BreakStmt], ctx), n)
    else INR [(info.node_id, "break outside a loop")]) ∧
  (elab_stmt ctx n (SrcContinue info) =
    if ctx.in_loop then INL (([ContinueStmt], ctx), n)
    else INR [(info.node_id, "continue outside a loop")]) ∧
  (* a return names the enclosing function's return list (none, 0, in a
     modifier) *)
  (elab_stmt ctx n (SrcReturn info returns_id NONE) =
    if returns_id = ctx.returns_id
    then INL (([ReturnStmt (return_atoms ctx.returns)], ctx), n)
    else INR [(info.node_id, "return of another function")]) ∧
  (elab_stmt ctx n (SrcReturn info returns_id (SOME e)) =
    ensure (returns_id = ctx.returns_id) (info.node_id, "return of another function")
    (case elab_values ctx n e of
       INL ((ss, vs), n1) =>
         (case convert_operands n1 (expr_id e) (REPLICATE (LENGTH vs) (expr_id e))
                 (values_of (MAP SND ctx.returns)) vs of
            INL (cs, _, as, n2) => INL ((ss ++ cs ++ [ReturnStmt as], ctx), n2)
          | INR bs => INR (if MEM ctx.returns_id ctx.bad_ids then [] else bs))
     | INR bs => INR bs)) ∧
  (elab_stmt ctx n (SrcEmit info ev args order) =
    let event =
      (case ALOOKUP ctx.events ev of
         NONE => INR (info.node_id, "unknown event")
       | SOME e =>
           if LENGTH args ≠ LENGTH e.event_parameters ∨
              ¬argument_order_ok order (LENGTH args)
           then INR (info.node_id, "emit does not match the event") else
           (case all_some (MAP event_parameter e.event_parameters) of
              NONE => INR (info.node_id, "unsupported event parameter type")
            | SOME ps => INL (e, ps))) in
    case (event, elab_arg_values ctx n args) of
      (INR b, r) => reject b r
    | (INL _, INR bs) => INR bs
    | (INL (e, ps), INL ((ss, vs0), next)) =>
        case (arrange order vs0, arrange order (expr_ids args)) of
          (SOME vs, SOME ids) =>
            (case convert_operands next info.node_id ids (encoded_as (MAP FST ps)) vs of
               INL (cs, _, as, n1) =>
                 INL ((ss ++ cs ++ [EmitStmt (event_topic e) (emit_arguments ps as)],
                       ctx), n1)
             | INR bs => INR bs)
        | _ => INR [(info.node_id, "argument order")]) ∧
  (* Arguments are coerced to the error's parameter types, which must be
     elementary for the revert data's ABI encoding. *)
  (elab_stmt ctx n (SrcRevertError info err args order) =
    case all_some (MAP variable_type err.error_parameters) of
      NONE =>
        INR (variables_blockers (MAP SOME err.error_parameters) ++
             blockers (elab_arg_values ctx n args))
    | SOME params =>
        if ¬EVERY is_elementary_type params ∨ LENGTH err.error_selector ≠ 4 ∨
           LENGTH args ≠ LENGTH params ∨ ¬argument_order_ok order (LENGTH args)
        then reject (info.node_id, "revert does not match the error")
               (elab_arg_values ctx n args) else
        case elab_args ctx n info.node_id order params args of
          INL ((ss, as), n1) =>
            INL ((ss ++ [RevertErrorStmt err.error_selector params as], ctx), n1)
        | INR bs => INR bs) ∧
  (* A constructor, and the modifiers it runs, may not halt from assembly:
   * the source installs no runtime code from the returned bytes. The
   * instruction checks are separate: the constructor's forbids more. *)
  (elab_stmt ctx n (SrcInlineAssembly info code refs) =
    let own =
      (if ¬assembly_stmts_ok assembly_unsupported code
       then [(info.node_id, "unsupported assembly instruction")]
       else if ctx.creation ∧
               ¬assembly_stmts_ok (YReturn :: YStop :: assembly_unsupported) code
       then [(info.node_id, "assembly halt in a constructor")]
       else []) ++
      (if assembly_memory_ok code then []
       else [(info.node_id, "unsupported assembly memory use")]) ++
      (if assembly_calls_ok code then []
       else [(info.node_id, "unsupported assembly gas or return data use")]) ++
      (if ALL_DISTINCT (MAP FST refs) then []
       else [(info.node_id, "repeated assembly reference")]) in
    case elab_assembly_references ctx n info.node_id refs of
      INL ((ss, rs), n1) =>
        (* a memory reference is read as a literal, so it can't be assigned *)
        let own' = own ++
          (if assembly_assigns_ok (assembly_memory_names rs) code then []
           else [(info.node_id, "assignment to an assembly memory reference")]) in
        if own' = [] then INL ((ss ++ [AssemblyStmt code rs], ctx), n1) else INR own'
    | INR bs => INR (own ++ bs)) ∧
  (elab_stmt ctx n (SrcUnsupportedStmt info msg es ss) =
    INR ((info.node_id, msg) :: blockers (elab_arg_values ctx n es) ++
         blockers (elab_stmts ctx n ss))) ∧
  (* An optional for initialization or loop expression. *)
  (elab_for_init ctx n NONE = INL (([], ctx), n)) ∧
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

(* Parameters defined by arguments. *)
Definition define_parameters_def:
  (define_parameters ((x, ty) :: ps) (a :: as) =
    DefineStmt (AstId x) (SingleType ty) (ConvertOperation ty a) ::
    define_parameters ps as) ∧
  (define_parameters _ _ = [])
End

(* A modifier invocation's arguments, each evaluated, converted to its
 * parameter's type and bound to the parameter before the next is evaluated:
 * the compiler binds a modifier's parameters one by one, where an internal
 * call evaluates every argument before converting any.
 *)
Definition elab_modifier_args_def:
  (elab_modifier_args ctx n (id : num) [] [] = INL ([], n)) ∧
  (elab_modifier_args ctx n id ((x, ty) :: ps) (e :: es) =
    case elab_args ctx n (expr_id e) [] [ty] [e] of
      INL ((ss, as), n1) =>
        (case elab_modifier_args ctx n1 id ps es of
           INL (ss', n2) =>
             INL (ss ++ define_parameters [(x, ty)] as ++ ss', n2)
         | INR bs => INR bs)
    | INR bs => INR (bs ++ blockers (elab_modifier_args ctx n id ps es))) ∧
  (elab_modifier_args ctx n id _ _ = INR [(id, "modifier argument count")])
End

(* A static memory array return variable starts as a zeroed array, allocated
 * on entry. *)
Definition return_defaults_def:
  (return_defaults n [] = ([], n)) ∧
  (return_defaults n ((x, ty) :: rs) =
    case ty of
      LocatedT MemoryLoc (ArrayT element (SOME k)) =>
        let (ss, n1) = return_defaults (n + 2) rs in
          (DefineStmt (AstId n) (SingleType ty)
             (DefaultMemoryOperation (ArrayT element (SOME k))) ::
           assign_local (n + 1) x ty (BoundAtom (AstId n)) ++ ss, n1)
    | _ => return_defaults n rs)
End

(* The compiler allocates a static memory return array once and passes it
 * through a function's modifiers, so a body run twice by `_; _;` sees its
 * first run's writes. Procedures here start from fresh return values, so
 * modified functions with such returns are rejected. *)
Definition static_memory_returns_def:
  (static_memory_returns [] ⇔ F) ∧
  (static_memory_returns ((x, ty) :: rs) ⇔
    (case ty of LocatedT MemoryLoc (ArrayT _ (SOME _)) => T | _ => F) ∨
    static_memory_returns rs)
End

(* The procedures of a function with modifiers: one per modifier invocation,
 * the first with the function's id, then one for the body. Each takes the
 * function's parameters and has its return variables; the invocation's
 * arguments define the modifier's parameters, and the modifier's
 * placeholder calls the next procedure (the compiler's IR does the same).
 * Fresh ids name the procedures after the first.
 *
 * Modifier arguments see the parameters but not the return variables: the
 * compiler's IR passes each modifier its own copies of the return variables,
 * which are not modelled. A modifier body has no super calls and no return
 * values (return list id 0).
 *)
Definition elab_levels_def:
  (elab_levels ctx modifiers ps rs x n [] ss =
    let (ds, n0) = return_defaults n rs in
    case elab_stmts ctx n0 ss of
      INL ((code, _), n1) =>
        INL ([<| procedure_id := AstId x; parameters := core_bindings ps;
                 return_bindings := core_bindings rs; body := ds ++ code |>], n1)
    | INR bs => INR bs) ∧
  (elab_levels ctx modifiers ps rs x n ((m, args) :: ms) ss =
    case ALOOKUP modifiers m of
      NONE =>
        INR ((m, "unknown modifier") ::
             blockers (elab_levels ctx modifiers ps rs n n ms ss))
    | SOME (md : src_modifier) =>
        case (all_some (MAP variable_binding md.modifier_parameters),
              md.modifier_body) of
          (SOME mps, SrcBlock minfo mss) =>
            let own = if static_memory_returns rs
                      then [(m, "modifier of a function returning a static memory array")]
                      else [] in
            let mctx = ctx with <| supers := []; variables := mps;
                                   placeholder := SOME (n, ps);
                                   scope := minfo.node_id;
                                   returns_id := 0 |> in
            (case elab_modifier_args (ctx with variables := ps) (n + 1) m mps args of
               INL (sa, n1) =>
                 (case elab_stmts mctx n1 mss of
                    INL ((code, _), n2) =>
                      (case elab_levels ctx modifiers ps rs n n2 ms ss of
                         INL (levels, n3) =>
                           if own ≠ [] then INR own else
                           INL (<| procedure_id := AstId x;
                                   parameters := core_bindings ps;
                                   return_bindings := core_bindings rs;
                                   body := sa ++ code |> :: levels, n3)
                       | INR bs => INR (own ++ bs))
                  | INR bs =>
                      INR (own ++ bs ++
                           blockers (elab_levels ctx modifiers ps rs n n ms ss)))
             | INR bs =>
                 INR (own ++ bs ++ blockers (elab_stmts mctx n mss) ++
                      blockers (elab_levels ctx modifiers ps rs n n ms ss)))
        | (NONE, _) =>
            INR (variables_blockers (MAP SOME md.modifier_parameters) ++
                 blockers (elab_levels ctx modifiers ps rs n n ms ss))
        | _ =>
            INR ((m, "unsupported modifier") ::
                 blockers (elab_levels ctx modifiers ps rs n n ms ss)))
End

(* A function's context, with the parameters and return variables vs. *)
Definition function_ctx_def:
  function_ctx ctx library (f : src_function) supers vs rs scope =
    ctx with <| supers := supers; variables := vs;
                state := if library ∨ f.fn_mutability = PureMut then []
                         else ctx.state;
                locations := if library then [] else ctx.locations;
                immutables := if library then [] else ctx.immutables;
                returns := rs; creation := (f.fn_kind = ConstructorKind);
                scope := scope; returns_id := f.fn_returns_id |>
End

Definition bound_variables_def:
  (bound_variables [] = []) ∧
  (bound_variables (v :: vs) =
    case variable_binding v of
      SOME b => b :: bound_variables vs
    | NONE => bound_variables vs)
End

(* The context of a contract's code: the callable functions calls, its
 * structs, enums and events, and its state variables, immutables and
 * constants. Inline assembly may name any state variable's slot. *)
Definition contract_ctx_def:
  contract_ctx (c : src_contract) calls state immutables constants =
    <| functions := calls; supers := []; structs := c.contract_structs;
       enums := c.contract_enums;
       events := MAP (λe. (e.event_info.node_id, e)) c.contract_events;
       variables := []; state := state; locations := state;
       immutables := immutables; constants := constants; returns := [];
       placeholder := NONE; mode := CheckedArithmetic; creation := F;
       scope := 0; returns_id := 0; in_loop := F; bad_ids := [] |>
End

(* A function's procedures, checked arithmetic by default; parameters and
 * returns keep their declaration ids. A pure function reads no state
 * variable, and a library function has no state variables or immutables.
 * A fallback takes no parameters and returns nothing, as the core's does
 * (plain_procedure); the importer marks one that does unsupported.
 * When strict, every super call must reach a supported function. A function
 * whose variables fail is elaborated with those that bind, for the blockers
 * of its modifiers and body; a failed return variable marks the return list
 * failed, so that its return statements add no blocker.
 *)
Definition elab_function_def:
  elab_function ctx (c : src_contract) strict library n (f : src_function) =
    let (fs, bases) = if library then (c.contract_library_functions, c.contract_libraries)
                      else (c.contract_functions, c.contract_bases) in
    let modifiers = MAP (λm. (m.modifier_info.node_id, m)) c.contract_modifiers in
    case (all_some (MAP variable_binding f.fn_parameters),
          all_some (MAP variable_binding f.fn_returns), f.fn_body,
          super_table fs bases f) of
      (SOME ps, SOME rs, SrcBlock info ss, SOME supers) =>
        ensure (¬strict ∨ EVERY (λ(_, g). g.fn_unsupported = NONE) supers)
          (f.fn_info.node_id, "super call of an unsupported function")
        (ensure (f.fn_kind ≠ FallbackKind ∨ (f.fn_parameters = [] ∧ f.fn_returns = []))
           (f.fn_info.node_id, "fallback with parameters or returns")
        (elab_levels (function_ctx ctx library f supers (ps ++ rs) rs info.node_id)
          modifiers ps rs f.fn_info.node_id n f.fn_modifiers ss))
    | (SOME _, SOME _, SrcBlock _ _, NONE) =>
        INR [(f.fn_info.node_id, "unresolved super call")]
    | (SOME _, SOME _, _, _) => INR [(f.fn_info.node_id, "function body not a block")]
    | (_, _, SrcBlock info ss, SOME supers) =>
        let vs = MAP SOME (f.fn_parameters ++ f.fn_returns) in
        let ps = bound_variables f.fn_parameters in
        let rs = bound_variables f.fn_returns in
        let fctx = function_ctx ctx library f supers [] rs info.node_id in
        let fctx = if LENGTH rs = LENGTH f.fn_returns then fctx
                   else fctx with bad_ids := f.fn_returns_id :: fctx.bad_ids in
        INR (variables_blockers vs ++
             blockers (ensure (¬strict ∨ EVERY (λ(_, g). g.fn_unsupported = NONE) supers)
               (f.fn_info.node_id, "super call of an unsupported function")
               (elab_levels (bind_failed fctx vs)
                  modifiers ps rs f.fn_info.node_id n f.fn_modifiers ss)))
    | _ => INR (variables_blockers (MAP SOME (f.fn_parameters ++ f.fn_returns)))
End

Definition elab_functions_def:
  (elab_functions ctx c strict library n [] = INL ([], n)) ∧
  (elab_functions ctx c strict library n (f :: fs) =
    case elab_function ctx c strict library n f of
      INL (ps, n1) =>
        (case elab_functions ctx c strict library n1 fs of
           INL (ps', n2) => INL (ps ++ ps', n2)
         | INR bs => INR bs)
    | INR bs => INR (bs ++ blockers (elab_functions ctx c strict library n fs)))
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
  elab_type_declarations enums structs =
    OPTION_MAP (λds. MAP (λ(id, members). (AstId id, EnumDeclaration members)) enums ++ ds)
    (all_some (MAP (λs.
      OPTION_MAP (λfields. (AstId s.struct_info.node_id, StructDeclaration fields))
        (all_some (MAP (λv. OPTION_MAP (λty. (AstId v.var_info.node_id, ty))
                           (field_variable_type v)) s.struct_members))) structs))
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

(* Getters. The location a getter reads, from the state variable's
 * reference ref of type ty, one parameter per mapping key or array index:
 * an index past an array's length reverts with no data, as the compiler's
 * getters do.
 *)
Definition getter_location_def:
  (getter_location n ref ty [] = (([], ref, ty), n)) ∧
  (getter_location n ref ty (p :: ps) =
    case ty of
      MappingT key value =>
        let ((ss, r, t), n1) = getter_location (n + 1) (BoundAtom (AstId n)) value ps in
        (([DefineStmt (AstId n) (ReferenceType value)
             (NavigateOperation value ref (IndexNavigation (BoundAtom (AstId p))))] ++ ss,
          r, t), n1)
    | ArrayT element len =>
        let ((ss, r, t), n1) = getter_location (n + 3) (BoundAtom (AstId (n + 2))) element ps in
        let (ls, length) =
          case len of
            SOME k => ([], ConstantAtom (IntegerValue (&k)))
          | NONE => ([DefineStmt (AstId n) (SingleType (UintT 256)) (ArrayLengthOperation ref)],
                     BoundAtom (AstId n)) in
        ((ls ++
          [DefineStmt (AstId (n + 1)) (SingleType BoolT)
             (ScalarOperation (UintT 256) UncheckedArithmetic LessThanOp
                [BoundAtom (AstId p); length]);
           IfStmt (BoundAtom (AstId (n + 1))) [] [RevertStmt (ConstantAtom (BytesValue []))];
           DefineStmt (AstId (n + 2)) (ReferenceType element)
             (NavigateOperation element ref (IndexNavigation (BoundAtom (AstId p))))] ++ ss,
          r, t), n1)
    | _ => (([], ref, ty), n))
End

(* A getter's parameters: fresh ids from n, one per key. *)
Definition getter_parameters_def:
  (getter_parameters (n : num) [] = []) ∧
  (getter_parameters n (k :: ks) = (n, k) :: getter_parameters (n + 1) ks)
End

(* What a getter returns: a byte sequence is returned in memory. *)
Definition getter_result_def:
  getter_result ty = if byte_sequence_type ty then LocatedT MemoryLoc ty else ty
End

(* A getter's read of one result from ref, the location it reached: the
 * value there, or a struct member there, a byte sequence copied to memory. *)
Definition getter_read_def:
  getter_read n ref (field, ty) =
    let (ns, r, n1) =
      case field of
        NONE => ([], ref, n)
      | SOME f => ([DefineStmt (AstId n) (ReferenceType ty)
                      (NavigateOperation ty ref (FieldNavigation (AstId f)))],
                   BoundAtom (AstId n), n + 1) in
    let (rs, a) = bind_value n1 (read_value_type ty) (ReadOperation ty r) in
    case coerce (n1 + 1) (getter_result ty) a (ElabType (read_value_type ty)) of
      INR _ => NONE
    | INL ((cs, a'), n2) => SOME ((ns ++ rs ++ cs, a'), n2)
End

Definition getter_reads_def:
  (getter_reads n ref [] = SOME (([], []), n)) ∧
  (getter_reads n ref (r :: rs) =
    case getter_read n ref r of
      NONE => NONE
    | SOME ((ss, a), n1) =>
        case getter_reads n1 ref rs of
          NONE => NONE
        | SOME ((ss', as), n2) => SOME ((ss ++ ss', a :: as), n2))
End

(* The getter of the public state variable or immutable x of type ty, the
 * procedure its selector reaches: it returns what getter_results says of the
 * location its arguments name. *)
Definition elab_getter_def:
  elab_getter structs state immutables n (x : num) =
    case ALOOKUP (state ++ immutables) x of
      NONE => NONE
    | SOME ty =>
        case getter_shape structs ty of
          NONE => NONE
        | SOME (keys, results) =>
            let params = getter_parameters n keys in
            let root = n + LENGTH keys in
            let ((nav, ref, _), n1) =
                  getter_location (root + 1) (BoundAtom (AstId root)) ty (MAP FST params) in
            case getter_reads n1 ref results of
              NONE => NONE
            | SOME ((rs, as), n2) =>
                SOME (<| procedure_id := AstId x;
                         parameters := core_bindings params;
                         return_bindings :=
                           core_bindings (getter_parameters n2 (MAP (getter_result o SND) results));
                         body := [DefineStmt (AstId root) (ReferenceType ty)
                                    (if IS_SOME (ALOOKUP state x)
                                     then StateReferenceOperation (AstId x)
                                     else ImmutableReferenceOperation (AstId x))] ++
                                 nav ++ rs ++ [ReturnStmt as] |>, n2 + LENGTH results)
End

Definition elab_getters_def:
  (elab_getters structs state immutables n [] = SOME ([], n)) ∧
  (elab_getters structs state immutables n (x :: gs) =
    case elab_getter structs state immutables n x of
      SOME (p, n1) =>
        (case elab_getters structs state immutables n1 gs of
           SOME (ps, n2) => SOME (p :: ps, n2)
         | NONE => NONE)
    | NONE => NONE)
End

(* The procedures of a constant, as the compiler's IR has them: one
 * evaluates its value with checked arithmetic, and is its getter if it is
 * public; the other, which references in unchecked code call, wraps. Each
 * returns the value converted to the constant's type. *)
Definition constant_procedure_def:
  constant_procedure ctx n p ty e =
    case elab_expr ctx n e of
      INL ((ss, a, vt), n1) =>
        (case coerce n1 ty a vt of
           INL ((cs, a'), n2) =>
             INL (<| procedure_id := AstId p; parameters := [];
                     return_bindings := [(AstId n2, ty)];
                     body := ss ++ cs ++ [ReturnStmt [a']] |>, n2 + 1)
         | INR why => INR [(expr_id e, why)])
    | INR bs => INR bs
End

Definition elab_constant_def:
  elab_constant ctx n ((v : src_variable), e) =
    case ALOOKUP ctx.constants v.var_info.node_id of
      SOME (ty, w) =>
        (case constant_procedure (ctx with mode := CheckedArithmetic) n
                v.var_info.node_id ty e of
           INL (checked, n1) =>
             (case constant_procedure (ctx with mode := UncheckedArithmetic) n1 w ty e of
                INL (wrapping, n2) => INL ([checked; wrapping], n2)
              | INR bs => INR bs)
         | INR bs => INR bs)
    | NONE => INR [(v.var_info.node_id, "unsupported constant")]
End

Definition elab_constants_def:
  (elab_constants ctx n [] = INL ([], n)) ∧
  (elab_constants ctx n (c :: cs) =
    case elab_constant ctx n c of
      INL (ps, n1) =>
        (case elab_constants ctx n1 cs of
           INL (ps', n2) => INL (ps ++ ps', n2)
         | INR bs => INR bs)
    | INR bs => INR (bs ++ blockers (elab_constants ctx n cs)))
End

(* The constants with fresh ids from n for their wrapping procedures. *)
Definition number_constants_def:
  (number_constants n [] = []) ∧
  (number_constants n ((x, ty) :: cs) =
    (x, (ty : sol_type), (n : num)) :: number_constants (n + 1) cs)
End

(* The dispatch table: the functions with a selector, which the compiler
 * gives exactly the external and public ones. *)
Definition external_functions_def:
  (external_functions [] = []) ∧
  (external_functions ((f : src_function) :: fs) =
    case f.fn_selector of
      SOME selector =>
        <| selector := selector; external_procedure := AstId f.fn_info.node_id;
           payable := (f.fn_mutability = PayableMut) |> :: external_functions fs
    | NONE => external_functions fs)
End

(* The receive or fallback function, and whether it is payable. *)
Definition special_function_def:
  (special_function kind [] = NONE) ∧
  (special_function kind ((f : src_function) :: fs) =
    if f.fn_kind = kind then
      SOME (AstId f.fn_info.node_id, f.fn_mutability = PayableMut)
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
Definition elab_base_arguments_def:
  (elab_base_arguments ctx fs n [] = INL ([], n)) ∧
  (elab_base_arguments ctx fs n ((x, b, args) :: rest) =
    case (constructor_parameters x fs, constructor_parameters b fs) of
      (SOME xps, SOME bps) =>
        (case elab_args (ctx with variables := xps) n b [] (MAP SND bps) args of
           INL ((ss, atoms), n1) =>
             (case elab_base_arguments ctx fs n1 rest of
                INL (ss', n2) => INL (ss ++ define_parameters bps atoms ++ ss', n2)
              | INR bs => INR bs)
         | INR bs => INR (bs ++ blockers (elab_base_arguments ctx fs n rest)))
    | _ =>
        INR ((b, "unsupported constructor parameters") ::
             blockers (elab_base_arguments ctx fs n rest)))
End

Definition variable_with_id_def:
  (variable_with_id y [] = NONE) ∧
  (variable_with_id y ((v : src_variable) :: vs) =
    if v.var_info.node_id = y then SOME v else variable_with_id y vs)
End

(* The initializers of the state variables and immutables vs that base x
 * declares, in declaration order. *)
Definition elab_initializers_def:
  (elab_initializers ctx n x vs [] = INL ([], n)) ∧
  (elab_initializers ctx n x vs ((y, e) :: inits) =
    case variable_with_id y vs of
      NONE =>
        INR ((y, "initializer of an unknown variable") ::
             blockers (elab_initializers ctx n x vs inits))
    | SOME v =>
        if v.var_scope ≠ x then elab_initializers ctx n x vs inits else
        case elab_expr ctx n
               (SrcAssignment v.var_info NONE
                  (SrcIdentifier v.var_info v.var_name v.var_info.node_id
                     v.var_type_id) e v.var_type_id) of
          INL ((ss, _, _), n1) =>
            (case elab_initializers ctx n1 x vs inits of
               INL (ss', n2) => INL (ss ++ ss', n2)
             | INR bs => INR bs)
        | INR bs => INR (bs ++ blockers (elab_initializers ctx n x vs inits)))
End

(* Bases, base first. *)
Definition elab_constructors_def:
  (elab_constructors ctx (c : src_contract) n [] = INL ([], n)) ∧
  (elab_constructors ctx c n (x :: xs) =
    case elab_initializers ctx n x
           (c.contract_state_variables ++ c.contract_immutables)
           c.contract_initializers of
      INR bs => INR (bs ++ blockers (elab_constructors ctx c n xs))
    | INL (ss, n1) =>
        let call =
          case contract_constructor x c.contract_functions of
            NONE => []
          | SOME f =>
              [DefineStmt (AstId n1) (call_result_type [])
                 (InternalCallOperation (AstId f.fn_info.node_id)
                    (MAP (λv. BoundAtom (AstId v.var_info.node_id))
                       f.fn_parameters))] in
        case elab_constructors ctx c (n1 + 1) xs of
          INL (ss', n2) => INL (ss ++ call ++ ss', n2)
        | INR bs => INR bs)
End

(* The creation procedure takes the parameters of the contract's own
 * constructor. *)
Definition elab_creation_def:
  elab_creation ctx (c : src_contract) n =
    case (constructor_parameters c.contract_info.node_id c.contract_functions,
          elab_base_arguments ctx c.contract_functions n
            c.contract_base_arguments) of
      (SOME ps, INL (sa, n1)) =>
        (case elab_constructors ctx c (n1 + 1) (REVERSE c.contract_bases) of
           INL (sc, n2) =>
             INL (<| procedure_id := AstId n1; parameters := core_bindings ps;
                     return_bindings := []; body := sa ++ sc |>, n2)
         | INR bs => INR bs)
    | (ps, ra) =>
        INR ((if IS_SOME ps then []
              else [(c.contract_info.node_id, "unsupported constructor parameters")]) ++
             blockers ra ++
             blockers (elab_constructors ctx c n (REVERSE c.contract_bases)))
End

(* Whether the creation transaction may carry value. *)
Definition creation_payable_def:
  creation_payable (c : src_contract) ⇔
    case contract_constructor c.contract_info.node_id c.contract_functions of
      SOME f => f.fn_mutability = PayableMut
    | NONE => F
End

(* The functions elaborated: the supported functions calls reach, and the
 * supported library functions. The unsupported ones get no procedure. *)
Definition elaborated_functions_def:
  elaborated_functions (c : src_contract) =
    FILTER (λf. f.fn_unsupported = NONE)
      (checked_functions c.contract_functions c.contract_bases)
End

Definition elaborated_library_functions_def:
  elaborated_library_functions (c : src_contract) =
    FILTER (λf. f.fn_unsupported = NONE) c.contract_library_functions
End

Definition unsupported_functions_def:
  unsupported_functions (c : src_contract) =
    MAP (λf. AstId f.fn_info.node_id)
      (FILTER (λf. f.fn_unsupported ≠ NONE)
         (checked_functions c.contract_functions c.contract_bases ++
          c.contract_library_functions))
End

(* Creation runs every constructor of the bases, so it is unsupported when
 * one of them is. *)
Definition unsupported_creation_def:
  unsupported_creation (c : src_contract) ⇔
    EXISTS (λf. f.fn_kind = ConstructorKind ∧ f.fn_unsupported ≠ NONE)
      c.contract_functions
End

(* The contract without the constants whose values do not elaborate, given
 * the constants that remain: a constant may read another, so dropping one can
 * make another fail; each round drops one or more, or ends. A function
 * reading a dropped constant then fails to elaborate on its own.
 *)
Definition live_constants_def:
  (live_constants 0 c = c) ∧
  (live_constants (SUC k) (c : src_contract) =
    case constant_table c of
      NONE => c
    | SOME table =>
        let ctx = contract_ctx c [] [] [] (number_constants 0 table) in
        let cs = FILTER (λx. ISL (elab_constant ctx 0 x)) c.contract_constants in
        if LENGTH cs = LENGTH c.contract_constants then c
        else live_constants k (c with contract_constants := cs))
End

(* The checked procedures of the constants live_constants dropped, which a
 * getter may still name. *)
Definition dropped_constants_def:
  dropped_constants (c0 : src_contract) (c : src_contract) =
    MAP (λx. AstId (FST x).var_info.node_id)
      (FILTER (λx. ¬MEM (FST x).var_info.node_id
                       (MAP (λy. (FST y).var_info.node_id) c.contract_constants))
         c0.contract_constants)
End

Definition elaborate_contract_def:
  elaborate_contract ctx (c0 : src_contract) (c : src_contract) state immutables n =
    let fs = live_functions c.contract_functions in
    case (elab_type_declarations c.contract_enums c.contract_structs,
          elab_struct_layouts c.contract_structs,
          core_state_variables state c.contract_storage,
          elab_functions ctx c T F n (elaborated_functions c)) of
      (SOME decls, SOME layouts, SOME cvs, INL (cfps, n00)) =>
        (case elab_functions ctx c T T n00 (elaborated_library_functions c) of
          INR _ => NONE
        | INL (lfps, n0) =>
        let fps = cfps ++ lfps in
        (case elab_getters c.contract_structs state immutables n0
                (FILTER (λx. IS_SOME (ALOOKUP (state ++ immutables) x))
                   (MAP FST c.contract_getters)) of
           NONE => NONE
         | SOME (gps, n1) =>
        case elab_constants (contract_ctx c [] [] [] ctx.constants)
               n1 c.contract_constants of
          INR _ => NONE
        | INL (cps, n) =>
        let ps = fps ++ gps ++ cps in
        (case (if unsupported_creation c then INL (INR (AstId n))
               else case elab_creation (ctx with creation := T) c n of
                      INL (p, _) => INL (INL p)
                    | INR bs => INR bs) of
           INR _ => NONE
         | INL creation =>
        let creation_id = (case creation of
                             INL p => p.procedure_id
                           | INR x => x) in
        case (ps, creation) of
          ([], INR _) => NONE
        | _ =>
        SOME <| procedures :=
                  ps ++ (case creation of INL p => [p] | INR _ => []);
                unsupported_procedures :=
                  unsupported_functions c ++ dropped_constants c0 c ++
                  (case creation of INL _ => [] | INR x => [x]);
                state_variables := cvs;
                immutables := MAP (λ(x, ty). (AstId x, ty)) immutables;
                struct_layouts := layouts; type_declarations := decls;
                entry_procedure :=
                  (case ps of
                     p :: _ => p.procedure_id
                   | [] => creation_id);
                external_functions :=
                  external_functions fs ++
                  MAP (λ(x, selector).
                         <| selector := selector;
                            external_procedure := AstId x;
                            payable := F |>) c.contract_getters;
                receive_procedure := OPTION_MAP FST
                  (special_function ReceiveKind fs);
                fallback_procedure :=
                  special_function FallbackKind fs;
                creation_procedure :=
                  SOME (creation_id, creation_payable c) |>)))
    | _ => NONE
End

(* The blockers of the state variables, constants and immutables without a
 * table entry. *)
Definition table_blockers_def:
  table_blockers (c : src_contract) =
    FLAT (MAP (λv. if IS_SOME (state_variable c.contract_bases v) then []
                   else variable_blockers "unsupported state variable" v)
           c.contract_state_variables) ++
    FLAT (MAP (λx. if IS_SOME (constant_variable
                                 (c.contract_bases ++ c.contract_libraries) (FST x))
                   then [] else variable_blockers "unsupported constant" (FST x))
           c.contract_constants) ++
    FLAT (MAP (λv. if IS_SOME (immutable_variable c.contract_bases v) then []
                   else variable_blockers "unsupported immutable" v)
           c.contract_immutables)
End

(* The blockers of a contract whose tables elaborate, from the parts that
 * elaborate_contract elaborates, each from fresh id n. *)
Definition contract_blockers_def:
  contract_blockers ctx (c : src_contract) state immutables n =
    let members =
      FLAT (MAP (λs. FLAT (MAP (λv. if IS_SOME (field_variable_type v) then []
                                    else variable_blockers "unsupported member type" v)
                             s.struct_members)) c.contract_structs) in
    members ++
    (if members = [] ∧ IS_NONE (elab_struct_layouts c.contract_structs)
     then [(c.contract_info.node_id, "struct layout mismatch")] else []) ++
    (if IS_SOME (core_state_variables state c.contract_storage) then []
     else [(c.contract_info.node_id, "storage layout mismatch")]) ++
    blockers (elab_functions ctx c T F n (elaborated_functions c)) ++
    blockers (elab_functions ctx c T T n (elaborated_library_functions c)) ++
    MAP (λx. (x, "unsupported getter"))
      (FILTER (λx. IS_SOME (ALOOKUP (state ++ immutables) x) ∧
                   IS_NONE (elab_getter c.contract_structs state immutables n x))
         (MAP FST c.contract_getters)) ++
    blockers (elab_constants (contract_ctx c [] [] [] ctx.constants) n
                c.contract_constants) ++
    (if unsupported_creation c then []
     else blockers (elab_creation (ctx with creation := T) c n))
End

(* Raw lowering of a unit of one contract, with fresh ids above its node ids;
 * the first live function or getter is the entry procedure, or the creation
 * procedure when there is none, and a unit with neither has no lowering. The
 * procedures of unsupported functions, of constants that do not elaborate,
 * and of an unsupported creation are left out and listed as unsupported,
 * with their dispatch entries kept. It fails with its blockers.
 *)
Definition elaborate_unit_reason_def:
  elaborate_unit_reason (u : src_unit) =
    case u.unit_contracts of
      [c0] =>
        let c = live_constants (LENGTH c0.contract_constants) c0 in
        let calls = function_table (c.contract_functions ++
                                    c.contract_library_functions) in
        (case (all_some (MAP (state_variable c.contract_bases) c.contract_state_variables),
               constant_table c, immutable_table c) of
           (SOME state, SOME table, SOME immutables) =>
             let constants = number_constants (MAX_LIST (unit_ids u) + 1) table in
             let ctx = contract_ctx c calls state immutables constants in
             let n = MAX_LIST (unit_ids u) + 1 + LENGTH table in
             (case elaborate_contract ctx c0 c state immutables n of
                SOME p => INL p
              | NONE =>
                  INR (case contract_blockers ctx c state immutables n of
                         [] => [(c0.contract_info.node_id,
                                 "no supported function or creation")]
                       | bs => bs))
         | _ => INR (table_blockers c0))
    | [] => INR [(u.unit_info.node_id, "no contract")]
    | cs => INR (MAP (λc. (c.contract_info.node_id, "more than one contract")) cs)
End

(* The lowering of a valid unit. A SOME result is not yet a checked program:
 * consumers must establish wf_core_program through solidityPrepareLib before
 * execution. *)
Definition elaborate_unit_def:
  elaborate_unit (u : src_unit) =
    if ¬valid_src_unit u then NONE else
    case elaborate_unit_reason u of
      INL p => SOME p
    | INR _ => NONE
End

(* A contract's failures, as unit_elaboration_failures lists them: its own
 * blockers under its id, then each function that fails. Its tables leave out
 * the entries that do not elaborate, whose references then fail with no
 * blocker of their own; a constant is reported only if it fails with every
 * typed constant in scope. *)
Definition contract_elaboration_failures_def:
  contract_elaboration_failures strict n0 several (c0 : src_contract) =
    let typed = FILTER (λx. IS_SOME (constant_variable
                                       (c0.contract_bases ++ c0.contract_libraries) (FST x)))
                  c0.contract_constants in
    let c = live_constants (LENGTH typed) (c0 with contract_constants := typed) in
    let table = (case constant_table c of SOME t => t | NONE => []) in
    let state = FLAT (MAP (λv. case state_variable c.contract_bases v of
                                 SOME b => [b] | NONE => [])
                        c.contract_state_variables) in
    let immutables = FLAT (MAP (λv. case immutable_variable c.contract_bases v of
                                      SOME b => [b] | NONE => [])
                             c.contract_immutables) in
    let live = MAP (λx. (FST x).var_info.node_id) c.contract_constants in
    let bad = MAP (λv. v.var_info.node_id)
                (FILTER (λv. IS_NONE (state_variable c.contract_bases v))
                   c.contract_state_variables ++
                 FILTER (λv. IS_NONE (immutable_variable c.contract_bases v))
                   c.contract_immutables ++
                 MAP FST (FILTER (λx. ¬MEM (FST x).var_info.node_id live)
                            c0.contract_constants)) in
    let fs = c.contract_functions ++ c.contract_library_functions in
    let ctx = (contract_ctx c (if strict then function_table fs else call_table fs)
                 state immutables (number_constants n0 table)) with bad_ids := bad in
    let n = n0 + LENGTH table in
    let typed_ctx = contract_ctx c [] [] []
                      (number_constants 0
                         (case constant_table (c0 with contract_constants := typed) of
                            SOME t => t | NONE => [])) in
    let own = (if several then [(c0.contract_info.node_id, "more than one contract")]
               else []) ++
              table_blockers c0 ++
              FLAT (MAP (λx. if MEM (FST x).var_info.node_id live then []
                             else blockers (elab_constant typed_ctx 0 x)) typed) ++
              blockers (elab_creation (ctx with creation := T) c n) in
    (if own = [] then [] else [(c0.contract_info.node_id, own)]) ++
    FLAT (MAP (λf. case elab_function ctx c strict F n f of
                     INL _ => []
                   | INR bs => [(f.fn_info.node_id, bs)])
            (checked_functions c.contract_functions c.contract_bases)) ++
    FLAT (MAP (λf. case elab_function ctx c strict T n f of
                     INL _ => []
                   | INR bs => [(f.fn_info.node_id, bs)])
            c.contract_library_functions)
End

(* Every part of a unit that fails to elaborate, with its blockers: each
 * contract, by id, for its own blockers (its tables, constants and creation),
 * and each function, supported or not, elaborated as elaborate_unit elaborates
 * it when strict. When not strict, calls and super calls may reach unsupported
 * functions: a function failing only strictly fails because it calls one.
 * Preparation marks the supported functions listed unsupported. *)
Definition unit_elaboration_failures_def:
  unit_elaboration_failures strict (u : src_unit) =
    FLAT (MAP (λc. contract_elaboration_failures strict (MAX_LIST (unit_ids u) + 1)
                     (LENGTH u.unit_contracts > 1) c) u.unit_contracts)
End

(* cv translation, so that units are elaborated by cv_eval. The mutually
 * recursive elaborators terminate on scaled cv sizes of their syntax.
 *)

val () = cv_auto_trans blockers_def;
val () = cv_auto_trans ensure_def;
val () = cv_auto_trans reject_def;
val () = cv_auto_trans unknown_reference_def;
val () = cv_auto_trans expr_id_def;
val () = cv_auto_trans unsupported_type_names_def;
val () = cv_auto_trans type_name_blockers_def;
val () = cv_auto_trans variable_blockers_def;
val () = cv_auto_trans variables_blockers_def;
val () = cv_auto_trans bind_value_def;
val () = cv_auto_trans default_operation_def;
val () = cv_auto_trans coerce_def;
val () = cv_auto_trans annotation_matches_def;
val () = cv_auto_trans is_declaration_def;
val () = cv_auto_trans snapshot_def;
val () = cv_auto_trans store_target_def;
val () = cv_auto_trans assign_local_def;
val () = cv_auto_trans variable_destination_def;
val () = cv_auto_trans destination_type_def;
val () = cv_auto_trans read_value_type_def;
val () = cv_auto_trans read_destination_def;
val () = cv_auto_trans capture_destination_def;
val () = cv_auto_trans write_destination_def;
val () = cv_auto_trans plain_assignment_def;
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
val () = cv_auto_trans tuple_write_def;
val () = cv_auto_trans tuple_writes_def;
val () = cv_auto_trans conditional_targets_def;
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

val () = cv_auto_trans values_of_def;
val () = cv_auto_trans encoded_as_def;
val () = cv_auto_trans expr_ids_def;
val () = cv_auto_trans abi_argument_def;
val () = cv_auto_trans convert_operand_def;

val convert_operands_pre_def =
  cv_auto_trans_pre "convert_operands_pre" convert_operands_def;

Theorem convert_operands_pre[cv_pre,local]:
  ∀n id ids ts vs. convert_operands_pre n id ids ts vs
Proof
  ho_match_mp_tac convert_operands_ind >> rpt strip_tac >>
  simp[Once convert_operands_pre_def] >> rw[] >> fs[]
QED

val () = cv_auto_trans selector_encoding_def;
val () = cv_auto_trans abi_encoding_def;
val () = cv_auto_trans arrange_def;

val elab_expr_pre_def = cv_auto_trans_pre_rec
  "elab_expr_pre elab_args_pre elab_values_pre elab_components_pre elab_location_pre elab_destination_pre elab_arg_values_pre elab_destinations_pre"
  elab_expr_def (
  WF_REL_TAC ‘measure (λx. case x of
     INL (ctx, n, e) => 4 * cv_size e + 2
   | INR (INL (ctx, n, id, order, tys, es)) => 4 * cv_size es + 1
   | INR (INR (INL (ctx, n, e))) => 4 * cv_size e + 3
   | INR (INR (INR (INL (ctx, n, cs)))) => 4 * cv_size cs
   | INR (INR (INR (INR (INL (ctx, n, e))))) => 4 * cv_size e + 1
   | INR (INR (INR (INR (INR (INL (ctx, n, e)))))) => 4 * cv_size e + 2
   | INR (INR (INR (INR (INR (INR (INL (ctx, n, es))))))) => 4 * cv_size es
   | INR (INR (INR (INR (INR (INR (INR (ctx, n, cs))))))) => 4 * cv_size cs + 3)’ >>
  cv_termination_tac
);

Theorem elab_pre_bounded[local]:
  !b.
  (!ctx n e. 4 * src_expr_size e + 2 < b ==> elab_expr_pre ctx n e) /\
  (!ctx n id order tys es. 4 * list_size src_expr_size es + 1 < b ==>
     elab_args_pre ctx n id order tys es) /\
  (!ctx n e. 4 * src_expr_size e + 3 < b ==> elab_values_pre ctx n e) /\
  (!ctx n cs. 4 * list_size (option_size src_expr_size) cs < b ==>
     elab_components_pre ctx n cs) /\
  (!ctx n e. 4 * src_expr_size e + 1 < b ==> elab_location_pre ctx n e) /\
  (!ctx n e. 4 * src_expr_size e + 2 < b ==> elab_destination_pre ctx n e) /\
  (!ctx n es. 4 * list_size src_expr_size es < b ==> elab_arg_values_pre ctx n es) /\
  (!ctx n cs. 4 * list_size (option_size src_expr_size) cs + 3 < b ==>
     elab_destinations_pre ctx n cs)
Proof
  completeInduct_on ‘b’ >> rpt conj_tac >> rpt gen_tac >> disch_tac >>
  qpat_x_assum ‘!m. m < b ==> _’ (drule_then strip_assume_tac)
  (* Unfold before splitting on the expression: after a case split, every
   * constructor's goal would rewrite and normalise the whole precondition. *)
  >~ [‘elab_expr_pre ctx n e’] >-
    (PURE_ONCE_REWRITE_TAC [elab_expr_pre_def] >>
     rpt conj_tac >> rpt gen_tac >> disch_then SUBST_ALL_TAC >>
     simp[solidityImportTheory.src_expr_size_def])
  >~ [‘elab_location_pre ctx n e’] >-
    (PURE_ONCE_REWRITE_TAC [elab_expr_pre_def] >>
     rpt conj_tac >> rpt gen_tac >> disch_then SUBST_ALL_TAC >>
     simp[solidityImportTheory.src_expr_size_def])
  >~ [‘elab_args_pre ctx n id order tys es’] >-
    (Cases_on ‘es’ >> simp_tac std_ss [Once elab_expr_pre_def] >>
     simp[listTheory.list_size_def])
  >~ [‘elab_arg_values_pre ctx n es’] >-
    (Cases_on ‘es’ >> simp_tac std_ss [Once elab_expr_pre_def] >>
     simp[listTheory.list_size_def])
  >~ [‘elab_destinations_pre ctx n cs’] >-
    (Cases_on ‘cs’ >> simp_tac std_ss [Once elab_expr_pre_def] >>
     simp[listTheory.list_size_def, basicSizeTheory.option_size_def])
  >~ [‘elab_components_pre ctx n cs’] >-
    (Cases_on ‘cs’ >> simp_tac std_ss [Once elab_expr_pre_def] >>
     simp[listTheory.list_size_def, basicSizeTheory.option_size_def]) >>
  simp_tac std_ss [Once elab_expr_pre_def] >>
  simp[solidityImportTheory.src_expr_size_def]
QED

Theorem elab_expr_pre[cv_pre,local]:
  (∀ctx n v. elab_expr_pre ctx n v) ∧
  (∀ctx n id order tys es. elab_args_pre ctx n id order tys es) ∧
  (∀ctx n e. elab_values_pre ctx n e) ∧
  (∀ctx n cs. elab_components_pre ctx n cs) ∧
  (∀ctx n e. elab_location_pre ctx n e) ∧
  (∀ctx n e. elab_destination_pre ctx n e)
Proof
  conj_tac >-
    (rpt gen_tac >> irule (cj 1 elab_pre_bounded) >>
     qexists_tac ‘4 * src_expr_size v + 3’ >> simp[]) >>
  conj_tac >-
    (rpt gen_tac >> irule (cj 2 elab_pre_bounded) >>
     qexists_tac ‘4 * list_size src_expr_size es + 2’ >> simp[]) >>
  conj_tac >-
    (rpt gen_tac >> irule (cj 3 elab_pre_bounded) >>
     qexists_tac ‘4 * src_expr_size e + 4’ >> simp[]) >>
  conj_tac >-
    (rpt gen_tac >> irule (cj 4 elab_pre_bounded) >>
     qexists_tac ‘4 * list_size (option_size src_expr_size) cs + 1’ >> simp[]) >>
  conj_tac >-
    (rpt gen_tac >> irule (cj 5 elab_pre_bounded) >>
     qexists_tac ‘4 * src_expr_size e + 2’ >> simp[]) >>
  rpt gen_tac >> irule (cj 6 elab_pre_bounded) >>
  qexists_tac ‘4 * src_expr_size e + 3’ >> simp[]
QED

Theorem elab_arg_values_pre[cv_pre,local]:
  ∀ctx n es. elab_arg_values_pre ctx n es
Proof
  rpt gen_tac >> irule (cj 7 elab_pre_bounded) >>
  qexists_tac ‘4 * list_size src_expr_size es + 1’ >> simp[]
QED

Theorem elab_destinations_pre[cv_pre,local]:
  ∀ctx n cs. elab_destinations_pre ctx n cs
Proof
  rpt gen_tac >> irule (cj 8 elab_pre_bounded) >>
  qexists_tac ‘4 * list_size (option_size src_expr_size) cs + 4’ >> simp[]
QED

val () = cv_auto_trans elab_condition_def;
val () = cv_auto_trans
  (REWRITE_RULE [GSYM byteTheory.word_of_bytes_be_def] event_topic_def);
val () = cv_auto_trans event_parameter_def;
val () = cv_auto_trans emit_arguments_def;

val declare_values_pre_def =
  cv_auto_trans_pre "declare_values_pre" declare_values_def;

Theorem declare_values_pre[cv_pre,local]:
  ∀ctx n id ds vs. declare_values_pre ctx n id ds vs
Proof
  ho_match_mp_tac declare_values_ind >> rpt strip_tac >>
  simp[Once declare_values_pre_def] >> rw[] >> fs[] >>
  (* a record update appears as a case on the context it updates *)
  Cases_on ‘ctx’ >> gvs[fetch "-" "elab_ctx_fn_updates"] >>
  rpt (CASE_TAC >> gvs[fetch "-" "elab_ctx_fn_updates"])
QED

val () = cv_auto_trans return_atoms_def;
val () = cv_auto_trans elab_assembly_reference_def;
val elab_assembly_references_pre_def =
  cv_auto_trans_pre "elab_assembly_references_pre" elab_assembly_references_def;

Theorem elab_assembly_references_pre[cv_pre,local]:
  ∀ctx n id refs. elab_assembly_references_pre ctx n id refs
Proof
  ho_match_mp_tac elab_assembly_references_ind >> rpt strip_tac >>
  simp[Once elab_assembly_references_pre_def] >> rw[] >> gvs[]
QED
val () = cv_auto_trans return_writes_def;
val () = cv_auto_trans placeholder_call_def;
val () = cv_auto_trans return_defaults_def;
val () = cv_auto_trans static_memory_returns_def;
val () = cv_auto_trans flag_def;
val () = cv_auto_trans set_flag_def;

val () = cv_auto_trans try_external_call_def;
val () = cv_auto_trans try_call_def;
val bind_failed_pre_def = cv_auto_trans_pre "bind_failed_pre" bind_failed_def;

Theorem bind_failed_pre[cv_pre,local]:
  ∀ds ctx. bind_failed_pre ctx ds
Proof
  Induct >> simp[Once bind_failed_pre_def]
QED

val () = cv_auto_trans after_failure_def;

val elab_stmts_pre_def = cv_auto_trans_pre_rec
  "elab_stmts_pre elab_stmt_pre elab_for_init_pre" elab_stmts_def (
  WF_REL_TAC ‘measure (λx. case x of
     INL (ctx, n, ss) => cv_size ss
   | INR (INL (ctx, n, st)) => cv_size st
   | INR (INR (ctx, n, st)) => cv_size st)’ >>
  cv_termination_tac
);

(* By the size of the syntax, so that each hypothesis is for every context;
 * the precondition is unfolded once before splitting on the statement. *)
Theorem elab_stmts_pre_bounded[local]:
  !b.
  (!ctx n ss. list_size src_stmt_size ss < b ==> elab_stmts_pre ctx n ss) /\
  (!ctx n st. src_stmt_size st < b ==> elab_stmt_pre ctx n st) /\
  (!ctx n st. option_size src_stmt_size st < b ==> elab_for_init_pre ctx n st)
Proof
  completeInduct_on ‘b’ >> rpt conj_tac >> rpt gen_tac >> disch_tac >>
  qpat_x_assum ‘!m. m < b ==> _’ (drule_then strip_assume_tac)
  >~ [‘elab_stmt_pre ctx n st’] >-
    (PURE_ONCE_REWRITE_TAC [elab_stmts_pre_def] >>
     rpt conj_tac >> rpt gen_tac >> disch_then strip_assume_tac >>
     rpt BasicProvers.VAR_EQ_TAC >>
     simp[solidityImportTheory.src_stmt_size_def, listTheory.list_size_def,
          basicSizeTheory.option_size_def, elab_expr_pre, elab_arg_values_pre,
          declare_values_pre, elab_assembly_references_pre, bind_failed_pre])
  >~ [‘elab_stmts_pre ctx n ss’] >-
    (Cases_on ‘ss’ >> simp_tac std_ss [Once elab_stmts_pre_def] >>
     simp[listTheory.list_size_def, bind_failed_pre]) >>
  Cases_on ‘st’ >> simp_tac std_ss [Once elab_stmts_pre_def] >>
  simp[basicSizeTheory.option_size_def]
QED

Theorem elab_stmts_pre[cv_pre,local]:
  (∀ctx n ss. elab_stmts_pre ctx n ss) ∧
  (∀ctx n st. elab_stmt_pre ctx n st) ∧
  (∀ctx n st. elab_for_init_pre ctx n st)
Proof
  rpt conj_tac >> rpt gen_tac >| [
    irule (cj 1 elab_stmts_pre_bounded) >>
    qexists_tac ‘list_size src_stmt_size ss + 1’,
    irule (cj 2 elab_stmts_pre_bounded) >>
    qexists_tac ‘src_stmt_size st + 1’,
    irule (cj 3 elab_stmts_pre_bounded) >>
    qexists_tac ‘option_size src_stmt_size st + 1’] >>
  simp[]
QED

val () = cv_auto_trans variable_binding_def;
val () = cv_auto_trans core_bindings_def;
val () = cv_auto_trans define_parameters_def;
val elab_modifier_args_pre_def =
  cv_auto_trans_pre "elab_modifier_args_pre" elab_modifier_args_def;

Theorem elab_modifier_args_pre[cv_pre,local]:
  ∀ctx n id tys es. elab_modifier_args_pre ctx n id tys es
Proof
  ho_match_mp_tac elab_modifier_args_ind >> rpt strip_tac >>
  simp[Once elab_modifier_args_pre_def, elab_expr_pre]
QED
val elab_levels_pre_def = cv_auto_trans_pre "elab_levels_pre" elab_levels_def;

Theorem elab_levels_pre[cv_pre,local]:
  ∀ms ctx modifiers ps rs x n ss. elab_levels_pre ctx modifiers ps rs x n ms ss
Proof
  Induct >- simp[Once elab_levels_pre_def, elab_stmts_pre] >>
  Cases >>
  simp[Once elab_levels_pre_def, elab_stmts_pre, elab_modifier_args_pre]
QED

val () = cv_auto_trans function_ctx_def;
val () = cv_auto_trans bound_variables_def;
val () = cv_auto_trans elab_function_def;
val () = cv_auto_trans contract_ctx_def;
val () = cv_auto_trans elab_functions_def;
val () = cv_auto_trans core_state_variables_def;
val () = cv_auto_trans elab_type_declarations_def;
val () = cv_auto_trans elab_struct_layouts_def;
val () = cv_auto_trans getter_location_def;
val () = cv_auto_trans getter_result_def;
val () = cv_auto_trans getter_parameters_def;
val () = cv_auto_trans getter_read_def;
val () = cv_auto_trans getter_reads_def;
val () = cv_auto_trans elab_getter_def;
val () = cv_auto_trans elab_getters_def;
val () = cv_auto_trans constant_procedure_def;
val () = cv_auto_trans elab_constant_def;
val () = cv_auto_trans elab_constants_def;
val () = cv_auto_trans number_constants_def;
val () = cv_auto_trans external_functions_def;
val () = cv_auto_trans special_function_def;
val elab_base_arguments_pre_def =
  cv_auto_trans_pre "elab_base_arguments_pre" elab_base_arguments_def;

Theorem elab_base_arguments_pre[cv_pre,local]:
  ∀ctx fs n v. elab_base_arguments_pre ctx fs n v
Proof
  ho_match_mp_tac elab_base_arguments_ind >> rw[] >>
  simp[Once elab_base_arguments_pre_def] >> rw[] >>
  Cases_on ‘ctx’ >> gvs[fetch "-" "elab_ctx_fn_updates"]
QED

val () = cv_auto_trans variable_with_id_def;
val elab_initializers_pre_def =
  cv_auto_trans_pre "elab_initializers_pre" elab_initializers_def;

Theorem elab_initializers_pre[cv_pre,local]:
  ∀ctx n x vs inits. elab_initializers_pre ctx n x vs inits
Proof
  ho_match_mp_tac elab_initializers_ind >> rw[] >>
  simp[Once elab_initializers_pre_def] >> rw[] >> gvs[]
QED
val () = cv_auto_trans elab_constructors_def;
val () = cv_auto_trans elab_creation_def;
val () = cv_auto_trans creation_payable_def;
val () = cv_auto_trans elaborated_functions_def;
val () = cv_auto_trans elaborated_library_functions_def;
val () = cv_auto_trans unsupported_functions_def;
val () = cv_auto_trans unsupported_creation_def;
val () = cv_auto_trans live_constants_def;
val () = cv_auto_trans dropped_constants_def;
val () = cv_auto_trans elaborate_contract_def;
val () = cv_auto_trans table_blockers_def;
val () = cv_auto_trans contract_blockers_def;
val () = cv_auto_trans elaborate_unit_reason_def;
val () = cv_auto_trans elaborate_unit_def;
val () = cv_auto_trans contract_elaboration_failures_def;
val () = cv_auto_trans unit_elaboration_failures_def;
