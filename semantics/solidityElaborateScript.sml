(* Elaboration of the normalised source AST (solidityImport) to the ordered
 * core, for the pinned profile solc-0.8.37-via-ir-osaka.
 *
 * Admitted: one contract, flattened along its bases, of functions over
 * elementary value types, with value-type state variables, storage structs,
 * scalar-key mappings and fixed/dynamic storage arrays, member/indexed scalar
 * reads and updates, array lengths, scalar push/pop and locals
 * (including tuple declarations with holes), internal calls with single or
 * multiple returns, explicit elementary conversions, literals, type(T).max
 * and .min of integer types (values of type T), unary, binary,
 * comparison and short-circuit operators, simple and compound assignment to
 * locals and state variables, tuple assignment, ++ and --, if, while,
 * do-while, for, break, continue, return and unchecked blocks. Built-in
 * require/assert/revert admit boolean conditions and literal string messages.
 * Reads of msg.sender, msg.value, tx.origin, tx.gasprice, block members and
 * address(this), emits of events and reverts with custom errors, both with
 * elementary parameters. An internal
 * call runs the most derived override of the function it names (call_table),
 * and a super call the function super_table finds along the bases after the
 * caller's; the functions no other overrides are elaborated, and the external
 * and public ones among them, receive and fallback form the dispatch table.
 * The overridden functions super calls reach are elaborated too, but not
 * dispatched.
 * Each constant is two procedures that return its value converted to its
 * type, one with checked and one with wrapping arithmetic, and a reference
 * to it calls the one of its own arithmetic, as the compiler's IR calls a
 * function per constant; a public constant's getter is the checked one. An
 * operation over literals that the compiler types as an integer is that
 * integer, as the compiler folds it.
 * State-variable initializers, constructors and base-constructor arguments
 * (inheritance specifiers or constructor modifiers) form one creation
 * procedure.
 * Bytes/string literals and memory/calldata values retain their locations.
 * Memory assignments alias; calldata-to-memory assignments copy contents.
 * Storage byte sequences and dynamic ABI values are rejected (NONE).
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
    supers : (num # src_function) list;
    structs : src_struct list;
    events : (num # src_event) list;
    variables : (num # sol_type) list;
    state : (num # sol_type) list;
    immutables : (num # sol_type) list;
    constants : (num # sol_type # num) list;
    returns : (num # sol_type) list;
    placeholder : (num # (num # sol_type) list) option;
    mode : arithmetic_mode;
    creation : bool
  |>
End

(* Values and conversions *)

(* The type of an elaborated value: an elementary type, an integer literal
 * (whose atom is its value), or several values.
 *)
Datatype:
  elab_type = ElabType sol_type | ElabLiteral | ElabBytesLiteral | ElabTuple (sol_type list)
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

(* A value of type ty: integer literals stand for themselves, other types are
 * converted.
 *)
Definition coerce_def:
  coerce n ty a vt =
    case vt of
      ElabType src =>
        if src = ty then SOME (([], a), n)
        else (case (src, ty) of
          (LocatedT loc (ArrayT e l), LocatedT MemoryLoc element') =>
            if loc = MemoryLoc ∨ element' ≠ ArrayT e l then NONE
            else SOME (bind_value n ty (CopyToMemoryOperation a), n + 1)
        | (LocatedT loc element, LocatedT MemoryLoc element') =>
            if loc = MemoryLoc ∨ element ≠ element' ∨ ¬byte_sequence_type element then NONE
            else let (ls, len) = bind_value n (UintT 256) (ArrayLengthOperation a) in
                 let (ds, dst) = bind_value (n + 1) ty (AllocateMemoryOperation element len) in
                 SOME ((ls ++ ds ++ [CopyContentsStmt src ty a dst], dst), n + 2)
        | _ => SOME (bind_value n ty (ConvertOperation ty a), n + 1))
    | ElabBytesLiteral =>
        (case (ty, a) of
           (LocatedT MemoryLoc element, ConstantAtom (BytesValue bs)) =>
             if byte_sequence_type element then
               SOME (bind_value n ty (BytesLiteralOperation element bs), n + 1)
             else NONE
         | _ => NONE)
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
 * or an element of a memory array (the array, its index and the element's
 * type), captured when written. Its prelude evaluates the location; reads and
 * writes share this representation.
 *)
Datatype:
  destination = LocalDestination num sol_type | ReferenceDestination core_atom sol_type
              | ElementDestination core_atom core_atom sol_type
End

Definition destination_type_def:
  (destination_type (LocalDestination _ ty) = ty) ∧
  (destination_type (ReferenceDestination _ ty) = ty) ∧
  (destination_type (ElementDestination _ _ ty) = ty)
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
         | NONE =>
             case ALOOKUP ctx.immutables x of
               SOME ty => SOME (([DefineStmt (AstId n) (ReferenceType ty)
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
    (bind_value n ty (ArrayIndexOperation array index), n + 1))
End

Definition write_destination_def:
  (write_destination t (LocalDestination x ty) a = assign_local t x ty a) ∧
  (write_destination t (ElementDestination array index ty) a =
    [CaptureReferenceFieldStmt (AstId t) array (IndexNavigation index);
     store_target t ty a]) ∧
  (write_destination (t : num) (ReferenceDestination ref ty) a =
    [CaptureValueStmt (AstId t) ref; WriteScalarStmt (AstId t) ty a])
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
                if storage_copy_type element ty then SOME (([], a), n) else NONE
            | _ => NONE in
          (case source of
             NONE => NONE
           | SOME ((cs, src), n1) =>
               let source_ty = case vt of
                 ElabType src_ty => src_ty
               | _ => LocatedT MemoryLoc ty in
               let dst_ty = LocatedT StorageLoc ty in
               let (ds, dst) = bind_value n1 dst_ty (ReadOperation ty ref) in
               SOME ((cs ++ ds ++ [CopyContentsStmt source_ty dst_ty src dst],
                      dst, dst_ty), n1 + 1))
        else (case coerce n ty a vt of
           SOME ((cs, value), n1) =>
             SOME ((cs ++ write_destination n1 target value, value, ty), n1 + 1)
         | NONE => NONE)
    | _ =>
        let ty = destination_type target in
        (case coerce n ty a vt of
           SOME ((cs, value), n1) =>
             SOME ((cs ++ write_destination n1 target value, value, ty), n1 + 1)
         | NONE => NONE)
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
  (expr_assigns (SrcAbiEncode _ _ _ args _) ⇔ exprs_assign args) ∧
  (expr_assigns (SrcEcrecover _ _ args _) ⇔ exprs_assign args) ∧
  (expr_assigns (SrcAbiDecode _ _ e _ _) ⇔ expr_assigns e) ∧
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
             (case plain_assignment n2 target a vt of
                SOME ((ss, _, _), n3) => SOME (ws ++ ls ++ ss, n3)
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

(* Keep byte-sequence and array references live until ABI serialization:
 * unlike an internal memory parameter, an encoded argument needs no location
 * copy, and the encoder reads it where it is, in memory, calldata or storage. *)
Definition coerce_abi_values_def:
  (coerce_abi_values n [] [] = SOME ([], [], n)) ∧
  (coerce_abi_values n (ty :: tys) ((a, vt) :: vs) =
    let converted = case (ty, vt) of
      (LocatedT _ element, ElabType (LocatedT _ actual)) =>
        if element = actual then SOME (([], a), n)
        else NONE
    | (LocatedT _ element, ElabBytesLiteral) =>
        if byte_sequence_type element then SOME (([], a), n) else NONE
    | _ => coerce n ty a vt in
    case converted of
      SOME ((ss, a'), n1) =>
        (case coerce_abi_values n1 tys vs of
           SOME (ss', as, n2) => SOME (ss ++ ss', a' :: as, n2)
         | NONE => NONE)
    | NONE => NONE) ∧
  (coerce_abi_values n _ _ = NONE)
End

(* An argument of abi.encode*, with the ABI type it is encoded as: a scalar
 * as its type; a byte sequence, or a string literal, where it is, as the
 * compiler encodes it in place; an integer literal (unpacked only) as its
 * mobile type, whose encoding is that of int256 or uint256. *)
Definition abi_argument_def:
  abi_argument packed a vt =
    case vt of
      ElabType ty =>
        if is_stored_scalar_type ty then SOME (ty, a) else
        (case ty of
           LocatedT _ element =>
             if byte_sequence_type element
             then SOME (LocatedT MemoryLoc element, a) else NONE
         | _ => NONE)
    | ElabBytesLiteral => SOME (LocatedT MemoryLoc StringT, a)
    | ElabLiteral =>
        (case a of
           ConstantAtom (IntegerValue i) =>
             if packed then NONE
             else SOME ((if i < 0 then IntT 256 else UintT 256), a)
         | _ => NONE)
    | _ => NONE
End

Definition abi_arguments_def:
  (abi_arguments packed [] = SOME ([], [])) ∧
  (abi_arguments packed ((a, vt) :: vs) =
    case (abi_argument packed a vt, abi_arguments packed vs) of
      (SOME (ty, a'), SOME (tys, args)) => SOME (ty :: tys, a' :: args)
    | _ => NONE)
End

(* The operation of abi.encode* on the values of its arguments, after any
 * statements converting the selector. *)
Definition abi_encoding_def:
  abi_encoding n form vs =
    case (form, vs) of
      (AbiWithSelector, (s, svt) :: rest) =>
        (case (coerce n (FixedBytesT 4) s svt, abi_arguments F rest) of
           (SOME ((cs, s'), n1), SOME (tys, args)) =>
             SOME ((cs, AbiEncodeOperation (SOME s') tys args), n1)
         | _ => NONE)
    | (AbiWithSelector, []) => NONE
    | (AbiPacked, _) =>
        (case abi_arguments T vs of
           SOME (tys, args) => SOME (([], AbiEncodePackedOperation tys args), n)
         | NONE => NONE)
    | (AbiPlain, _) =>
        (case abi_arguments F vs of
           SOME (tys, args) => SOME (([], AbiEncodeOperation NONE tys args), n)
         | NONE => NONE)
    | (AbiWithSignature signature, _) =>
        (case abi_arguments F vs of
           SOME (tys, args) =>
             SOME (([], AbiEncodeOperation
                          (SOME (ConstantAtom (BytesValue (TAKE 4 (Keccak_256_w64 signature)))))
                          tys args), n)
         | NONE => NONE)
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

Definition elab_expr_def:
  (elab_expr ctx n expression =
    case expression of
      SrcIdentifier _ _ x _ =>
        (case variable_destination ctx n x of
           SOME ((ls, target), n1) =>
             let ty = destination_type target in
             if ¬(is_stored_scalar_type ty ∨ memory_object_type ty ∨ located_value_type ty) then NONE else
             let (read, n2) = read_destination n1 target in
             let (ss, a) = read in
             SOME ((ls ++ ss, a, ElabType (read_value_type ty)), n2)
         | NONE =>
             case ALOOKUP ctx.constants x of
               SOME (ty, w) =>
                 let p = if ctx.mode = CheckedArithmetic then x else w in
                 let (ss, a) = bind_value n ty (InternalCallOperation (AstId p) []) in
                 SOME ((ss, a, ElabType ty), n + 1)
             | NONE => NONE)
    | SrcArrayLength _ root_expr _ =>
        (case elab_expr ctx n root_expr of
           SOME ((ss, ref, ElabType (LocatedT loc BytesT)), n1) =>
             let (rs, a) = bind_value n1 (UintT 256) (ArrayLengthOperation ref) in
             SOME ((ss ++ rs, a, ElabType (UintT 256)), n1 + 1)
         | SOME ((ss, ref, ElabType (LocatedT _ (ArrayT _ (SOME length)))), n1) =>
             SOME ((ss, ConstantAtom (IntegerValue (&length)), ElabType (UintT 256)), n1)
         | SOME ((ss, ref, ElabType (LocatedT _ (ArrayT _ NONE))), n1) =>
             let (rs, a) = bind_value n1 (UintT 256) (ArrayLengthOperation ref) in
             SOME ((ss ++ rs, a, ElabType (UintT 256)), n1 + 1)
         | _ =>
           case elab_location ctx n root_expr of
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
         else if (kind = "string" ∨ kind = "unicodeString" ∨ kind = "hexString") ∧
                 isPREFIX "t_stringliteral_" tid then
           SOME (([], ConstantAtom (BytesValue (MAP (n2w o ORD) value)),
                  ElabBytesLiteral), n)
         else
           case identifier_integer tid of
             SOME i => SOME (([], ConstantAtom (IntegerValue i), ElabLiteral), n)
           | NONE => NONE)
    | SrcMemberAccess _ _ _ _ =>
        (case elab_location ctx n expression of
           SOME ((ss, ref, ty), n1) =>
             if is_stored_scalar_type ty ∨ memory_object_type ty then
               let (rs, a) = bind_value n1 (read_value_type ty) (ReadOperation ty ref) in
               SOME ((ss ++ rs, a, ElabType (read_value_type ty)), n1 + 1)
             else NONE
         | NONE => NONE)
    | SrcIndexAccess info root_expr index tid =>
        (case elab_expr ctx n root_expr of
           SOME ((ss, ref, ElabType (LocatedT loc BytesT)), n1) =>
             let (captured, next) = snapshot n1 ref (ElabType (LocatedT loc BytesT)) in
             let (saved, ref') = captured in
             (case elab_expr ctx next index of
                SOME ((si, i, vt), n2) =>
                  (case coerce n2 (UintT 256) i vt of
                     SOME ((cs, i'), n3) =>
                       let (rs, a) = bind_value n3 (FixedBytesT 1)
                                       (ByteIndexOperation ref' i') in
                       SOME ((ss ++ saved ++ si ++ cs ++ rs, a, ElabType (FixedBytesT 1)), n3 + 1)
                   | NONE => NONE)
              | NONE => NONE)
         | SOME ((ss, ref, ElabType (LocatedT loc (ArrayT element length))), n1) =>
             let ty = LocatedT loc (ArrayT element length) in
             let (captured, next) = snapshot n1 ref (ElabType ty) in
             let (saved, ref') = captured in
             (case elab_expr ctx next index of
                SOME ((si, i, vt), n2) =>
                  (case coerce n2 (UintT 256) i vt of
                     SOME ((cs, i'), n3) =>
                       let ety = element_type loc element in
                       let (rs, a) = bind_value n3 ety (ArrayIndexOperation ref' i') in
                       SOME ((ss ++ saved ++ si ++ cs ++ rs, a, ElabType ety), n3 + 1)
                   | NONE => NONE)
              | NONE => NONE)
         | _ =>
           case elab_location ctx n expression of
             SOME ((ss, ref, ty), n1) =>
               if is_stored_scalar_type ty ∨ memory_object_type ty then
                 let (rs, a) = bind_value n1 (read_value_type ty) (ReadOperation ty ref) in
                 SOME ((ss ++ rs, a, ElabType (read_value_type ty)), n1 + 1)
               else NONE
           | NONE => NONE)
    | SrcUnaryOperation _ op prefix e tid =>
        (case identifier_integer tid of
           SOME i => SOME (([], ConstantAtom (IntegerValue i), ElabLiteral), n)
         | NONE =>
         if op = "++" ∨ op = "--" then
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
        (case identifier_integer tid of
           SOME i => SOME (([], ConstantAtom (IntegerValue i), ElabLiteral), n)
         | NONE =>
         case (identifier_type common, elab_expr ctx n l) of
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
                         (case plain_assignment n3 target ar' vr of
                            SOME ((cr, a, value_ty), n4) =>
                              SOME ((sr ++ sc ++ ls ++ cr, a, ElabType value_ty), n4)
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
    | SrcFunctionCall _ callee args order _ =>
        (case callee of
           SrcArrayMember _ member root_expr _ =>
             (if order ≠ [] then NONE else
              case elab_location ctx n root_expr of
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
                       (case elab_args ctx n order params args of
                          SOME ((sa, atoms), n1) =>
                            SOME ((sa ++ [DefineStmt (AstId n1) (call_result_type rets)
                                            (InternalCallOperation
                                               (AstId callee.fn_info.node_id) atoms)],
                                   BoundAtom (AstId n1), call_value rets), n1 + 1)
                        | NONE => NONE)
                   | NONE => NONE)
              | NONE => NONE)
         | _ => NONE)
    | SrcSuperCall _ r args order _ =>
        (case ALOOKUP ctx.supers r of
           SOME callee =>
             (case callee_types callee of
                SOME (params, rets) =>
                  (case elab_args ctx n order params args of
                     SOME ((sa, atoms), n1) =>
                       SOME ((sa ++ [DefineStmt (AstId n1) (call_result_type rets)
                                       (InternalCallOperation
                                          (AstId callee.fn_info.node_id) atoms)],
                              BoundAtom (AstId n1), call_value rets), n1 + 1)
                   | NONE => NONE)
              | NONE => NONE)
         | NONE => NONE)
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
    | SrcExternalCall _ callee with_value operands order _ =>
        (case (all_some (MAP call_variable_type callee.ext_parameters),
               all_some (MAP call_variable_type callee.ext_returns)) of
           (SOME params, SOME rets) =>
             (case OPTION_BIND (elab_arg_values ctx n operands)
                     (λ((ss, vs), next). OPTION_MAP (λvs'. ((ss, vs'), next))
                                           (arrange order vs)) of
                SOME ((ss, vs), next) =>
                  (case coerce_abi_values next
                          (AddressT NonpayableAddress ::
                           (if with_value then [UintT 256] else []) ++ params) vs of
                     SOME (cs, t :: atoms, n1) =>
                       (case (with_value, atoms) of
                          (T, v :: args) =>
                            SOME (external_call_value n1 callee.ext_mutability
                                    callee.ext_selector params rets (ss ++ cs) t v args)
                        | (F, args) =>
                            SOME (external_call_value n1 callee.ext_mutability
                                    callee.ext_selector params rets (ss ++ cs) t
                                    (ConstantAtom (IntegerValue 0)) args)
                        | _ => NONE)
                   | _ => NONE)
              | NONE => NONE)
         | _ => NONE)
    | SrcNew _ tn e tid =>
        (case (normalize_type_name tn, elab_expr ctx n e) of
           (SOME ty, SOME ((ss, a, vt), n1)) =>
             (case coerce n1 (UintT 256) a vt of
                SOME ((cs, a'), n2) =>
                  let (rs, v) = bind_value n2 (LocatedT MemoryLoc ty)
                                  (AllocateMemoryOperation ty a') in
                  SOME ((ss ++ cs ++ rs, v, ElabType (LocatedT MemoryLoc ty)), n2 + 1)
              | NONE => NONE)
         | _ => NONE)
    | SrcEnvironment _ f _ =>
        let (ss, a) = bind_value n (environment_type f) (EnvironmentOperation f) in
        SOME ((ss, a, ElabType (environment_type f)), n + 1)
    | SrcEnumValue _ tn index _ =>
        (case normalize_type_name tn of
           SOME ty =>
             let (ss, a) = bind_value n ty
                             (ConvertOperation ty (ConstantAtom (IntegerValue (&index)))) in
             SOME ((ss, a, ElabType ty), n + 1)
         | NONE => NONE)
    | SrcConditional _ c t f tid =>
        (* the result is declared first, and each branch writes it *)
        (case (identifier_type tid, elab_expr ctx n c) of
           (SOME ty, SOME ((sc, ac, vc), n1)) =>
             (case (default_operation ty, coerce n1 BoolT ac vc) of
                (SOME op, SOME ((cc, ac'), n2)) =>
                  (case elab_expr ctx (n2 + 2) t of
                     SOME ((st, at, vt), n3) =>
                       (case coerce n3 ty at vt of
                          SOME ((ct, at'), n4) =>
                            (case elab_expr ctx (n4 + 1) f of
                               SOME ((sf, af, vf), n5) =>
                                 (case coerce n5 ty af vf of
                                    SOME ((cf, af'), n6) =>
                                      let (rs, res) = bind_value n2 ty op in
                                      SOME ((sc ++ cc ++ rs ++
                                             [IfStmt ac'
                                                (st ++ ct ++ assign_local (n2 + 1) n2 ty at')
                                                (sf ++ cf ++ assign_local n4 n2 ty af')],
                                             res, ElabType ty), n6)
                                  | NONE => NONE)
                             | NONE => NONE)
                        | NONE => NONE)
                   | NONE => NONE)
              | _ => NONE)
         | _ => NONE)
    | SrcKeccak256 _ _ e _ =>
        (case elab_expr ctx n e of
           SOME ((ss, a, vt), n1) =>
             (case coerce n1 (LocatedT MemoryLoc BytesT) a vt of
                SOME ((cs, b), n2) =>
                  let (hs, h) = bind_value n2 (FixedBytesT 32) (Keccak256Operation b) in
                  SOME ((ss ++ cs ++ hs, h, ElabType (FixedBytesT 32)), n2 + 1)
              | NONE => NONE)
         | NONE => NONE)
    | SrcAbiEncode _ _ form args _ =>
        (case elab_arg_values ctx n args of
           SOME ((ss, vs), n1) =>
             (case abi_encoding n1 form vs of
                SOME ((cs, op), n2) =>
                  let ty = LocatedT MemoryLoc BytesT in
                  let (es, r) = bind_value n2 ty op in
                  SOME ((ss ++ cs ++ es, r, ElabType ty), n2 + 1)
              | NONE => NONE)
         | NONE => NONE)
    | SrcEcrecover _ _ args _ =>
        (case elab_arg_values ctx n args of
           SOME ((ss, vs), n1) =>
             (case coerce_values n1 [FixedBytesT 32; UintT 8; FixedBytesT 32;
                                     FixedBytesT 32] vs of
                SOME (cs, [h; v; r; s], n2) =>
                  let ty = AddressT NonpayableAddress in
                  let (es, a) = bind_value n2 ty (EcrecoverOperation h v r s) in
                  SOME ((ss ++ cs ++ es, a, ElabType ty), n2 + 1)
              | _ => NONE)
         | NONE => NONE)
    | SrcAbiDecode _ _ e tns _ =>
        (* the data is decoded where it is, so it must already be memory bytes *)
        (case (elab_expr ctx n e, all_some (MAP normalize_type_name tns)) of
           (SOME ((ss, a, ElabType (LocatedT MemoryLoc BytesT)), n1), SOME (ty :: tys)) =>
             SOME ((ss ++ [DefineStmt (AstId n1) (call_result_type (ty :: tys))
                                (AbiDecodeOperation (ty :: tys) a)],
                    BoundAtom (AstId n1), call_value (ty :: tys)), n1 + 1)
         | _ => NONE)
    | SrcSelector _ bs _ =>
        (* bound, so that a later conversion converts a bytesN local *)
        let ty = FixedBytesT (LENGTH bs) in
        let (ss, a) = bind_value n ty (ConvertOperation ty (ConstantAtom (BytesValue bs))) in
        SOME ((ss, a, ElabType ty), n + 1)
    | SrcTypeMember _ member tn _ =>
        (case normalize_type_name tn of
           SOME ty =>
             (* bound to a local of type T, the source type of any
                later conversion *)
             (case type_bound member ty of
                SOME i =>
                  let (ss, a) = bind_value n ty
                                  (ConvertOperation ty (ConstantAtom (IntegerValue i))) in
                  SOME ((ss, a, ElabType ty), n + 1)
              | NONE => NONE)
         | NONE => NONE)
    | SrcTypeConversion _ tn e tid =>
        (case (identifier_type tid, elab_expr ctx n e) of
           (SOME ty, SOME ((ss, a, vt), n1)) =>
             (case (vt, ty, a) of
                (ElabTuple _, _, _) => NONE
              | (ElabBytesLiteral, _, _) =>
                  (case coerce n1 ty a vt of
                     SOME ((cs, v), n2) => SOME ((ss ++ cs, v, ElabType ty), n2)
                   | NONE => NONE)
              | (ElabLiteral, AddressT _, ConstantAtom (IntegerValue i)) =>
                (* address(0): the literal is the address, as in solc *)
                if 0 ≤ i ∧ i < 2 ** 160 then
                  SOME ((ss, ConstantAtom (AddressValue (n2w (Num i))),
                         ElabType ty), n1)
                else NONE
              | (ElabLiteral, FixedBytesT k, ConstantAtom (IntegerValue i)) =>
                (* bytesN(0) or a hex literal of N bytes: the literal is the
                   bytes, as in solc; bound like the min/max members above *)
                if 0 ≤ i ∧ i < 2 ** (8 * k) then
                  let (cs, v) = bind_value n1 ty
                        (ConvertOperation ty
                           (ConstantAtom (BytesValue (num_to_bytes k (Num i))))) in
                  SOME ((ss ++ cs, v, ElabType ty), n1 + 1)
                else NONE
              | _ =>
                let (cs, v) = bind_value n1 ty (ConvertOperation ty a) in
                SOME ((ss ++ cs, v, ElabType ty), n1 + 1))
         | _ => NONE)) ∧
  (* Capture every argument before any location conversion copies contents. *)
  (* Arguments are evaluated in the call's order and passed in the
     parameters' (arrange). *)
  (elab_args ctx n order tys es =
    case elab_arg_values ctx n es of
      SOME ((ss, vs), n1) =>
        (case arrange order vs of
           SOME vs' =>
             (case coerce_values n1 tys vs' of
                SOME (cs, as, n2) => SOME ((ss ++ cs, as), n2)
              | NONE => NONE)
         | NONE => NONE)
    | NONE => NONE) ∧
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
        (case elab_expr ctx n root_expr of
           SOME ((ss, ref, ElabType (LocatedT loc BytesT)), n1) =>
             let (captured, next) = snapshot n1 ref (ElabType (LocatedT loc BytesT)) in
             let (saved, ref') = captured in
             (if loc = CalldataLoc then NONE else
              case elab_expr ctx next index of
                SOME ((si, a, vt), n2) =>
                  (case coerce n2 (UintT 256) a vt of
                     SOME ((cs, a'), n3) =>
                       SOME ((ss ++ saved ++ si ++ cs ++
                         [DefineStmt (AstId n3) (ReferenceType (FixedBytesT 1))
                           (NavigateOperation (FixedBytesT 1) ref' (IndexNavigation a'))],
                         BoundAtom (AstId n3), FixedBytesT 1), n3 + 1)
                   | NONE => NONE)
              | NONE => NONE)
         | _ => case elab_location ctx n root_expr of
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
    | SrcFunctionCall _ (SrcArrayMember _ member root_expr _) [] [] _ =>
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
    | SrcIndexAccess _ root_expr index _ =>
          (case elab_expr ctx n root_expr of
             SOME ((ss, ref, ElabType (LocatedT MemoryLoc (ArrayT element length))), n1) =>
               let (captured, next) =
                 snapshot n1 ref (ElabType (LocatedT MemoryLoc (ArrayT element length))) in
               let (saved, ref') = captured in
               (case elab_expr ctx next index of
                  SOME ((si, i, vt), n2) =>
                    (case coerce n2 (UintT 256) i vt of
                       SOME ((cs, i'), n3) =>
                         SOME ((ss ++ saved ++ si ++ cs,
                                ElementDestination ref' i' (element_type MemoryLoc element)), n3)
                     | NONE => NONE)
                | NONE => NONE)
           | _ =>
             case elab_location ctx n e of
               SOME ((ss, ref, ty), n1) =>
                 SOME ((ss, ReferenceDestination ref ty), n1)
             | NONE => NONE)
    | _ =>
        case elab_location ctx n e of
          SOME ((ss, ref, ty), n1) =>
            SOME ((ss, ReferenceDestination ref ty), n1)
        | NONE => NONE)
  ∧
  (elab_arg_values ctx n [] = SOME (([], []), n)) ∧
  (elab_arg_values ctx n (e :: es) =
    case elab_expr ctx n e of
      SOME ((ss, a, vt), n1) =>
        let (captured, n2) =
          if exprs_assign es then snapshot n1 a vt else (([], a), n1) in
        let (saved, a') = captured in
        (case elab_arg_values ctx n2 es of
           SOME ((ss', vs), n3) => SOME ((ss ++ saved ++ ss', (a', vt) :: vs), n3)
         | NONE => NONE)
    | NONE => NONE)
Termination
  qexists_tac ‘measure (λx. case x of
     INL (ctx, n, e) => 3 * src_expr_size e + 2
   | INR (INL (ctx, n, order, tys, es)) => 3 * list_size src_expr_size es + 1
   | INR (INR (INL (ctx, n, e))) => 3 * src_expr_size e + 3
   | INR (INR (INR (INL (ctx, n, cs)))) =>
       3 * list_size (option_size src_expr_size) cs
   | INR (INR (INR (INR (INL (ctx, n, e))))) => 3 * src_expr_size e + 1
   | INR (INR (INR (INR (INR (INL (ctx, n, e)))))) => 3 * src_expr_size e + 2
   | INR (INR (INR (INR (INR (INR (ctx, n, es)))))) => 3 * list_size src_expr_size es)’ >>
  conj_tac >- simp[prim_recTheory.WF_measure] >>
  rpt conj_tac >>
  rw[prim_recTheory.measure_thm, solidityImportTheory.src_expr_size_def,
     listTheory.list_size_def,
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
 * and write as a word. A constant of such a type is read before the block,
 * as an expression reads it.
 *)
Definition elab_assembly_reference_def:
  (elab_assembly_reference ctx n (SrcAssemblyValue x) =
    case ALOOKUP ctx.variables x of
      SOME ty =>
        if assembly_value_type ty then SOME (([], AssemblyLocal (AstId x) ty), n)
        else NONE
    | NONE =>
      case ALOOKUP ctx.constants x of
        SOME (ty, w) =>
          if assembly_value_type ty then
            let p = if ctx.mode = CheckedArithmetic then x else w in
            let (ss, a) = bind_value n ty (InternalCallOperation (AstId p) []) in
            SOME ((ss, AssemblyConstant a ty), n + 1)
          else NONE
      | NONE => NONE) ∧
  (elab_assembly_reference ctx n (SrcAssemblySlot x) =
    if IS_SOME (ALOOKUP ctx.state x) then SOME (([], AssemblySlot (AstId x)), n)
    else NONE) ∧
  (elab_assembly_reference ctx n (SrcAssemblyOffset x) =
    if IS_SOME (ALOOKUP ctx.state x) then SOME (([], AssemblyOffset (AstId x)), n)
    else NONE)
End

Definition elab_assembly_references_def:
  (elab_assembly_references ctx n [] = SOME (([], []), n)) ∧
  (elab_assembly_references ctx n ((name, r) :: refs) =
    case elab_assembly_reference ctx n r of
      SOME ((ss, r'), n1) =>
        (case elab_assembly_references ctx n1 refs of
           SOME ((ss', rs), n2) => SOME ((ss ++ ss', (name, r') :: rs), n2)
         | NONE => NONE)
    | NONE => NONE)
End

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
        (case default_operation ty of
           SOME op =>
             SOME (([DefineStmt (AstId v.var_info.node_id) (SingleType ty) op],
                    ctx with variables := (v.var_info.node_id, ty) :: ctx.variables), n)
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
  (elab_stmt ctx n (SrcPlaceholder _) =
    case ctx.placeholder of
      SOME (next, ps) =>
        let (ss, n1) = placeholder_call n next ps ctx.returns in
        SOME ((ss, ctx), n1)
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
  (elab_stmt ctx n (SrcEmit _ ev args order) =
    case ALOOKUP ctx.events ev of
      NONE => NONE
    | SOME e =>
        case all_some (MAP event_parameter e.event_parameters) of
          NONE => NONE
        | SOME ps =>
            case OPTION_BIND (elab_arg_values ctx n args)
                   (λ((ss, vs), next). OPTION_MAP (λvs'. ((ss, vs'), next))
                                         (arrange order vs)) of
              SOME ((ss, vs), next) =>
                (case coerce_abi_values next (MAP FST ps) vs of
                   SOME (cs, as, n1) =>
                     SOME ((ss ++ cs ++ [EmitStmt (event_topic e) (emit_arguments ps as)],
                            ctx), n1)
                 | NONE => NONE)
            | NONE => NONE) ∧
  (* Arguments are coerced to the error's parameter types, which must be
     elementary for the revert data's ABI encoding. *)
  (elab_stmt ctx n (SrcRevertError _ err args order) =
    case all_some (MAP variable_type err.error_parameters) of
      NONE => NONE
    | SOME params =>
        if ¬EVERY is_elementary_type params then NONE else
        case elab_args ctx n order params args of
          SOME ((ss, as), n1) =>
            SOME ((ss ++ [RevertErrorStmt err.error_selector params as], ctx), n1)
        | NONE => NONE) ∧
  (* A constructor, and the modifiers it runs, may not halt from assembly:
   * the source installs no runtime code from the returned bytes. *)
  (elab_stmt ctx n (SrcInlineAssembly _ code refs) =
    if ¬assembly_stmts_ok (if ctx.creation then YReturn :: YStop :: assembly_unsupported
                           else assembly_unsupported) code ∨
       ¬assembly_memory_ok code then NONE else
    case elab_assembly_references ctx n refs of
      SOME ((ss, rs), n1) => SOME ((ss ++ [AssemblyStmt code rs], ctx), n1)
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
  (elab_modifier_args ctx n [] [] = SOME ([], n)) ∧
  (elab_modifier_args ctx n ((x, ty) :: ps) (e :: es) =
    case elab_args ctx n [] [ty] [e] of
      SOME ((ss, as), n1) =>
        (case elab_modifier_args ctx n1 ps es of
           SOME (ss', n2) =>
             SOME (ss ++ define_parameters [(x, ty)] as ++ ss', n2)
         | NONE => NONE)
    | NONE => NONE) ∧
  (elab_modifier_args ctx n _ _ = NONE)
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
 *)
Definition elab_levels_def:
  (elab_levels ctx modifiers ps rs x n [] ss =
    let (ds, n0) = return_defaults n rs in
    case elab_stmts ctx n0 ss of
      SOME ((code, _), n1) =>
        SOME ([<| procedure_id := AstId x; parameters := core_bindings ps;
                  return_bindings := core_bindings rs; body := ds ++ code |>], n1)
    | NONE => NONE) ∧
  (elab_levels ctx modifiers ps rs x n ((m, args) :: ms) ss =
    case ALOOKUP modifiers m of
      NONE => NONE
    | SOME (md : src_modifier) =>
        case (all_some (MAP variable_binding md.modifier_parameters),
              md.modifier_body) of
          (SOME mps, SrcBlock _ mss) =>
            if static_memory_returns rs then NONE else
            (case elab_modifier_args ctx (n + 1) mps args of
               SOME (sa, n1) =>
                 (case elab_stmts (ctx with <| supers := []; variables := mps;
                                               placeholder := SOME (n, ps) |>)
                         n1 mss of
                    SOME ((code, _), n2) =>
                      (case elab_levels ctx modifiers ps rs n n2 ms ss of
                         SOME (levels, n3) =>
                           SOME (<| procedure_id := AstId x;
                                    parameters := core_bindings ps;
                                    return_bindings := core_bindings rs;
                                    body := sa ++ code |> :: levels, n3)
                       | NONE => NONE)
                  | NONE => NONE)
             | NONE => NONE)
        | _ => NONE)
End

(* A function's procedures, checked arithmetic by default; parameters and
 * returns keep their declaration ids.
 *)
Definition elab_function_def:
  elab_function structs events functions fs bases modifiers state immutables
                constants n
                (f : src_function) =
    case (all_some (MAP variable_binding f.fn_parameters),
          all_some (MAP variable_binding f.fn_returns), f.fn_body,
          super_table fs bases f) of
      (SOME ps, SOME rs, SrcBlock _ ss, SOME supers) =>
        elab_levels <| functions := functions; supers := supers; structs := structs;
                       events := events; variables := ps ++ rs;
                       state := state; immutables := immutables;
                       constants := constants;
                       returns := rs; placeholder := NONE;
                       mode := CheckedArithmetic;
                       creation := (f.fn_kind = "constructor") |>
          modifiers ps rs f.fn_info.node_id n f.fn_modifiers ss
    | _ => NONE
End

Definition elab_functions_def:
  (elab_functions structs events functions all bases modifiers state immutables
     constants n [] =
    SOME ([], n)) ∧
  (elab_functions structs events functions all bases modifiers state immutables
     constants n (f :: fs) =
    case elab_function structs events functions all bases modifiers state
           immutables constants n f of
      SOME (ps, n1) =>
        (case elab_functions structs events functions all bases modifiers state
                immutables constants n1 fs of
           SOME (ps', n2) => SOME (ps ++ ps', n2)
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
      NONE => NONE
    | SOME ((cs, a'), n2) => SOME ((ns ++ rs ++ cs, a'), n2)
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
      SOME ((ss, a, vt), n1) =>
        (case coerce n1 ty a vt of
           SOME ((cs, a'), n2) =>
             SOME (<| procedure_id := AstId p; parameters := [];
                      return_bindings := [(AstId n2, ty)];
                      body := ss ++ cs ++ [ReturnStmt [a']] |>, n2 + 1)
         | NONE => NONE)
    | NONE => NONE
End

Definition elab_constant_def:
  elab_constant ctx n ((v : src_variable), e) =
    case ALOOKUP ctx.constants v.var_info.node_id of
      SOME (ty, w) =>
        (case constant_procedure (ctx with mode := CheckedArithmetic) n
                v.var_info.node_id ty e of
           SOME (checked, n1) =>
             (case constant_procedure (ctx with mode := UncheckedArithmetic) n1 w ty e of
                SOME (wrapping, n2) => SOME ([checked; wrapping], n2)
              | NONE => NONE)
         | NONE => NONE)
    | NONE => NONE
End

Definition elab_constants_def:
  (elab_constants ctx n [] = SOME ([], n)) ∧
  (elab_constants ctx n (c :: cs) =
    case elab_constant ctx n c of
      SOME (ps, n1) =>
        (case elab_constants ctx n1 cs of
           SOME (ps', n2) => SOME (ps ++ ps', n2)
         | NONE => NONE)
    | NONE => NONE)
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
Definition elab_base_arguments_def:
  (elab_base_arguments ctx fs n [] = SOME ([], n)) ∧
  (elab_base_arguments ctx fs n ((x, b, args) :: rest) =
    case (constructor_parameters x fs, constructor_parameters b fs) of
      (SOME xps, SOME bps) =>
        (case elab_args (ctx with variables := xps) n [] (MAP SND bps) args of
           SOME ((ss, atoms), n1) =>
             (case elab_base_arguments ctx fs n1 rest of
                SOME (ss', n2) => SOME (ss ++ define_parameters bps atoms ++ ss', n2)
              | NONE => NONE)
         | NONE => NONE)
    | _ => NONE)
End

Definition variable_with_id_def:
  (variable_with_id y [] = NONE) ∧
  (variable_with_id y ((v : src_variable) :: vs) =
    if v.var_info.node_id = y then SOME v else variable_with_id y vs)
End

(* The initializers of the state variables and immutables vs that base x
 * declares, in declaration order. *)
Definition elab_initializers_def:
  (elab_initializers ctx n x vs [] = SOME ([], n)) ∧
  (elab_initializers ctx n x vs ((y, e) :: inits) =
    case variable_with_id y vs of
      NONE => NONE
    | SOME v =>
        if v.var_scope ≠ x then elab_initializers ctx n x vs inits else
        case elab_expr ctx n
               (SrcAssignment v.var_info "="
                  (SrcIdentifier v.var_info v.var_name v.var_info.node_id
                     v.var_type_id) e v.var_type_id) of
          SOME ((ss, _, _), n1) =>
            (case elab_initializers ctx n1 x vs inits of
               SOME (ss', n2) => SOME (ss ++ ss', n2)
             | NONE => NONE)
        | NONE => NONE)
End

(* Bases, base first. *)
Definition elab_constructors_def:
  (elab_constructors ctx (c : src_contract) n [] = SOME ([], n)) ∧
  (elab_constructors ctx c n (x :: xs) =
    case elab_initializers ctx n x
           (c.contract_state_variables ++ c.contract_immutables)
           c.contract_initializers of
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
 * node ids; the first live function or getter is the entry procedure, or the creation
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
        (case (all_some (MAP (state_variable c.contract_bases) c.contract_state_variables),
               constant_table c, immutable_table c) of
           (SOME state, SOME table, SOME immutables) =>
             let constants = number_constants (MAX_LIST (unit_ids u) + 1) table in
             (case (elab_type_declarations c.contract_enums c.contract_structs,
                   elab_struct_layouts c.contract_structs,
                   core_state_variables state c.contract_storage,
                   elab_functions c.contract_structs
                     (MAP (λe. (e.event_info.node_id, e)) c.contract_events)
                     (call_table (c.contract_functions ++
                                  c.contract_library_functions))
                     c.contract_functions c.contract_bases
                     (MAP (λm. (m.modifier_info.node_id, m)) c.contract_modifiers)
                     state immutables constants
                     (MAX_LIST (unit_ids u) + 1 + LENGTH table)
                     (checked_functions c.contract_functions c.contract_bases ++
                      c.contract_library_functions)) of
               (SOME decls, SOME layouts, SOME cvs, SOME (fps, n0)) =>
                 (case elab_getters c.contract_structs state immutables n0
                         (FILTER (λx. IS_SOME (ALOOKUP (state ++ immutables) x))
                            (MAP FST c.contract_getters)) of
                    NONE => NONE
                  | SOME (gps, n1) =>
                 case elab_constants
                        <| functions := []; supers := [];
                           structs := c.contract_structs; events := [];
                           variables := []; state := []; immutables := [];
                           constants := constants;
                           returns := []; placeholder := NONE;
                           mode := CheckedArithmetic; creation := F |>
                        n1 c.contract_constants of
                   NONE => NONE
                 | SOME (cps, n) =>
                 let ps = fps ++ gps ++ cps in
                 (case elab_creation
                         <| functions := call_table (c.contract_functions ++
                                                     c.contract_library_functions);
                            supers := [];
                            structs := c.contract_structs;
                            events := MAP (λe. (e.event_info.node_id, e))
                                        c.contract_events;
                            variables := []; state := state;
                            immutables := immutables;
                            constants := constants; returns := [];
                            placeholder := NONE; mode := CheckedArithmetic;
                            creation := T |> c n of
                    NONE => NONE
                  | SOME (creation, _) =>
                 SOME <| procedures := ps ++ [creation]; state_variables := cvs;
                         immutables := MAP (λ(x, ty). (AstId x, ty)) immutables;
                         struct_layouts := layouts; type_declarations := decls;
                         entry_procedure :=
                           (case ps of
                              p :: _ => p.procedure_id
                            | [] => creation.procedure_id);
                         external_functions :=
                           external_functions fs ++
                           MAP (λ(x, selector).
                                  <| selector := selector;
                                     external_procedure := AstId x;
                                     payable := F |>) c.contract_getters;
                         receive_procedure := OPTION_MAP FST
                           (special_function "receive" fs);
                         fallback_procedure :=
                           special_function "fallback" fs;
                         creation_procedure :=
                           SOME (creation.procedure_id, creation_payable c) |>))
              | _ => NONE)
         | _ => NONE)
    | _ => NONE
End

(* cv translation, so that units are elaborated by cv_eval. The mutually
 * recursive elaborators terminate on scaled cv sizes of their syntax.
 *)

val () = cv_auto_trans bind_value_def;
val () = cv_auto_trans default_operation_def;
val () = cv_auto_trans coerce_def;
val () = cv_auto_trans snapshot_def;
val () = cv_auto_trans store_target_def;
val () = cv_auto_trans assign_local_def;
val () = cv_auto_trans variable_destination_def;
val () = cv_auto_trans destination_type_def;
val () = cv_auto_trans read_value_type_def;
val () = cv_auto_trans read_destination_def;
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

val coerce_values_pre_def =
  cv_auto_trans_pre "coerce_values_pre" coerce_values_def;

Theorem coerce_values_pre[cv_pre,local]:
  ∀n tys vs. coerce_values_pre n tys vs
Proof
  ho_match_mp_tac coerce_values_ind >> rpt strip_tac >>
  simp[Once coerce_values_pre_def] >> rw[] >> fs[]
QED

val coerce_abi_values_pre_def =
  cv_auto_trans_pre "coerce_abi_values_pre" coerce_abi_values_def;

Theorem coerce_abi_values_pre[cv_pre,local]:
  ∀n tys vs. coerce_abi_values_pre n tys vs
Proof
  ho_match_mp_tac coerce_abi_values_ind >> rpt strip_tac >>
  simp[Once coerce_abi_values_pre_def] >> rw[] >> fs[]
QED

val () = cv_auto_trans abi_argument_def;
val () = cv_auto_trans abi_arguments_def;
val () = cv_auto_trans abi_encoding_def;
val () = cv_auto_trans arrange_def;

val elab_expr_pre_def = cv_auto_trans_pre_rec
  "elab_expr_pre elab_args_pre elab_values_pre elab_components_pre elab_location_pre elab_destination_pre elab_arg_values_pre"
  elab_expr_def (
  WF_REL_TAC ‘measure (λx. case x of
     INL (ctx, n, e) => 3 * cv_size e + 2
   | INR (INL (ctx, n, order, tys, es)) => 3 * cv_size es + 1
   | INR (INR (INL (ctx, n, e))) => 3 * cv_size e + 3
   | INR (INR (INR (INL (ctx, n, cs)))) => 3 * cv_size cs
   | INR (INR (INR (INR (INL (ctx, n, e))))) => 3 * cv_size e + 1
   | INR (INR (INR (INR (INR (INL (ctx, n, e)))))) => 3 * cv_size e + 2
   | INR (INR (INR (INR (INR (INR (ctx, n, es)))))) => 3 * cv_size es)’ >>
  cv_termination_tac
);

Theorem elab_pre_bounded[local]:
  !b.
  (!ctx n e. 3 * src_expr_size e + 2 < b ==> elab_expr_pre ctx n e) /\
  (!ctx n order tys es. 3 * list_size src_expr_size es + 1 < b ==>
     elab_args_pre ctx n order tys es) /\
  (!ctx n e. 3 * src_expr_size e + 3 < b ==> elab_values_pre ctx n e) /\
  (!ctx n cs. 3 * list_size (option_size src_expr_size) cs < b ==>
     elab_components_pre ctx n cs) /\
  (!ctx n e. 3 * src_expr_size e + 1 < b ==> elab_location_pre ctx n e) /\
  (!ctx n e. 3 * src_expr_size e + 2 < b ==> elab_destination_pre ctx n e) /\
  (!ctx n es. 3 * list_size src_expr_size es < b ==> elab_arg_values_pre ctx n es)
Proof
  completeInduct_on ‘b’ >> rpt conj_tac >> rpt gen_tac >> disch_tac >>
  qpat_x_assum ‘!m. m < b ==> _’ (drule_then strip_assume_tac)
  >~ [‘elab_expr_pre ctx n e’] >-
    (Cases_on ‘e’ >> simp_tac std_ss [Once elab_expr_pre_def] >>
     simp[src_expr_distinct, src_expr_11, solidityImportTheory.src_expr_size_def])
  >~ [‘elab_location_pre ctx n e’] >-
    (Cases_on ‘e’ >> simp_tac std_ss [Once elab_expr_pre_def] >>
     simp[src_expr_distinct, src_expr_11, solidityImportTheory.src_expr_size_def])
  >~ [‘elab_args_pre ctx n order tys es’] >-
    (Cases_on ‘es’ >> simp_tac std_ss [Once elab_expr_pre_def] >>
     simp[listTheory.list_size_def])
  >~ [‘elab_arg_values_pre ctx n es’] >-
    (Cases_on ‘es’ >> simp_tac std_ss [Once elab_expr_pre_def] >>
     simp[listTheory.list_size_def])
  >~ [‘elab_components_pre ctx n cs’] >-
    (Cases_on ‘cs’ >> simp_tac std_ss [Once elab_expr_pre_def] >>
     simp[listTheory.list_size_def, basicSizeTheory.option_size_def]) >>
  simp_tac std_ss [Once elab_expr_pre_def] >>
  simp[solidityImportTheory.src_expr_size_def]
QED

Theorem elab_expr_pre[cv_pre,local]:
  (∀ctx n v. elab_expr_pre ctx n v) ∧
  (∀ctx n order tys es. elab_args_pre ctx n order tys es) ∧
  (∀ctx n e. elab_values_pre ctx n e) ∧
  (∀ctx n cs. elab_components_pre ctx n cs) ∧
  (∀ctx n e. elab_location_pre ctx n e) ∧
  (∀ctx n e. elab_destination_pre ctx n e)
Proof
  conj_tac >-
    (rpt gen_tac >> irule (cj 1 elab_pre_bounded) >>
     qexists_tac ‘3 * src_expr_size v + 3’ >> simp[]) >>
  conj_tac >-
    (rpt gen_tac >> irule (cj 2 elab_pre_bounded) >>
     qexists_tac ‘3 * list_size src_expr_size es + 2’ >> simp[]) >>
  conj_tac >-
    (rpt gen_tac >> irule (cj 3 elab_pre_bounded) >>
     qexists_tac ‘3 * src_expr_size e + 4’ >> simp[]) >>
  conj_tac >-
    (rpt gen_tac >> irule (cj 4 elab_pre_bounded) >>
     qexists_tac ‘3 * list_size (option_size src_expr_size) cs + 1’ >> simp[]) >>
  conj_tac >-
    (rpt gen_tac >> irule (cj 5 elab_pre_bounded) >>
     qexists_tac ‘3 * src_expr_size e + 2’ >> simp[]) >>
  rpt gen_tac >> irule (cj 6 elab_pre_bounded) >>
  qexists_tac ‘3 * src_expr_size e + 3’ >> simp[]
QED

Theorem elab_arg_values_pre[cv_pre,local]:
  ∀ctx n es. elab_arg_values_pre ctx n es
Proof
  rpt gen_tac >> irule (cj 7 elab_pre_bounded) >>
  qexists_tac ‘3 * list_size src_expr_size es + 1’ >> simp[]
QED

val () = cv_auto_trans elab_condition_def;
val () = cv_auto_trans
  (REWRITE_RULE [GSYM byteTheory.word_of_bytes_be_def] event_topic_def);
val () = cv_auto_trans event_parameter_def;
val () = cv_auto_trans emit_arguments_def;

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
val () = cv_auto_trans elab_assembly_reference_def;
val elab_assembly_references_pre_def =
  cv_auto_trans_pre "elab_assembly_references_pre" elab_assembly_references_def;

Theorem elab_assembly_references_pre[cv_pre,local]:
  ∀ctx n refs. elab_assembly_references_pre ctx n refs
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
val () = cv_auto_trans define_parameters_def;
val elab_modifier_args_pre_def =
  cv_auto_trans_pre "elab_modifier_args_pre" elab_modifier_args_def;

Theorem elab_modifier_args_pre[cv_pre,local]:
  ∀ctx n tys es. elab_modifier_args_pre ctx n tys es
Proof
  ho_match_mp_tac elab_modifier_args_ind >> rpt strip_tac >>
  simp[Once elab_modifier_args_pre_def]
QED
val elab_levels_pre_def = cv_auto_trans_pre "elab_levels_pre" elab_levels_def;

Theorem elab_levels_pre[cv_pre,local]:
  ∀ctx modifiers ps rs x n ms ss. elab_levels_pre ctx modifiers ps rs x n ms ss
Proof
  ho_match_mp_tac elab_levels_ind >> rpt strip_tac >>
  simp[Once elab_levels_pre_def] >> rw[] >> fs[] >>
  (* the record update appears as a case on the context *)
  Cases_on ‘ctx’ >> gvs[fetch "-" "elab_ctx_fn_updates"]
QED

val () = cv_auto_trans elab_function_def;
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
val () = cv_auto_trans elaborate_unit_def;
