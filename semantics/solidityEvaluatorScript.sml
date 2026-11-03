(* Evaluator: locals, value-type state variables, control flow and internal
 * calls over the core, fuel-indexed by recursive depth.
 *
 * Fuel: statement-list traversal is structural and siblings reuse the bound;
 * invoke_source decrements on entry and a while loop decrements on its back
 * edge, so straight-line code and a loop's first iteration need none. No step
 * counter is threaded through the state.
 *
 * Scopes: an if branch and each loop iteration run in a pushed scope, and
 * leaving pops only that scope, so writes to enclosing bindings survive. A
 * procedure runs in a fresh scope and target map; the caller's are restored
 * afterwards, since the pure fragment has no references through which a callee
 * could reach them. Within a procedure, capturing a target overwrites it.
 *
 * Storage: a state variable lives in the storage of the executing account,
 * frame.self_address, in the world's verifereum accounts, at the slot and
 * byte offset of the program's layout. Reads and writes go straight to that
 * world, so a write is seen by everything after it, callers and callees
 * included; restoring the world on revert is the frame's job
 * (finish_source_frame). Access sets and original values, which only matter
 * to gas, are not tracked.
 *
 * Gas evidence is passed through unchanged; the EVM boundary is out of scope.
 * Unsupported statements and operations, and anything the checker would reject,
 * end in InvalidCompletion.
 *)
Theory solidityEvaluator
Ancestors
  solidityMemory solidityABI externalCall
Libs
  cv_transLib wordsLib intLib

(* Scopes and targets *)

Definition ast_key_def:
  ast_key (AstId n) = n
End

Definition lookup_binding_def:
  (lookup_binding x [] = NONE) ∧
  (lookup_binding x (scope :: scopes) =
    case FLOOKUP scope (ast_key x) of
      SOME b => SOME b
    | NONE => lookup_binding x scopes)
End

(* Writes the binding in the innermost scope that holds it. *)
Definition update_binding_def:
  (update_binding x v [] = NONE) ∧
  (update_binding x v (scope :: scopes) =
    case FLOOKUP scope (ast_key x) of
      SOME b =>
        SOME ((scope |+ (ast_key x, b with binding_value := v)) :: scopes)
    | NONE =>
        (case update_binding x v scopes of
           SOME scopes' => SOME (scope :: scopes')
         | NONE => NONE))
End

Definition bind_local_def:
  (bind_local x b [] = [FEMPTY |+ (ast_key x, b)]) ∧
  (bind_local x b (scope :: scopes) = (scope |+ (ast_key x, b)) :: scopes)
End

Definition set_target_def:
  set_target t target targets = targets |+ (ast_key t, target)
End

Definition push_scope_def:
  push_scope (st : source_state) = st with scopes := FEMPTY :: st.scopes
End

Definition pop_scopes_def:
  (pop_scopes [] = []) ∧
  (pop_scopes (_ :: scopes) = scopes)
End

(* Results *)

Definition normal_result_def:
  normal_result st gas =
    <| completion := NormalCompletion; state := st;
       unused_gas_evidence := gas |>
End

Definition abrupt_result_def:
  abrupt_result c st gas =
    <| completion := c; state := st; unused_gas_evidence := gas |>
End

Definition pop_result_def:
  pop_result (r : source_result) =
    r with state := (r.state with scopes := pop_scopes r.state.scopes)
End

(* Atoms and pure operations *)

Definition eval_atom_def:
  (eval_atom scopes (ConstantAtom s) = SOME (ScalarValue s)) ∧
  (eval_atom scopes (BoundAtom x) =
    case lookup_binding x scopes of
      SOME b => SOME b.binding_value
    | NONE => NONE)
End

Definition eval_atoms_def:
  (eval_atoms scopes [] = SOME []) ∧
  (eval_atoms scopes (a :: atoms) =
    case (eval_atom scopes a, eval_atoms scopes atoms) of
      (SOME v, SOME vs) => SOME (v :: vs)
    | _ => NONE)
End

Definition scalar_values_def:
  (scalar_values [] = SOME []) ∧
  (scalar_values (ScalarValue s :: vs) =
    case scalar_values vs of SOME ss => SOME (s :: ss) | NONE => NONE) ∧
  (scalar_values (_ :: _) = NONE)
End

(* The source type of a conversion: a binding's declared type, or the target
 * type for a constant (the literal/default-initialisation form).
 *)
Definition conversion_source_type_def:
  (conversion_source_type scopes ty (ConstantAtom _) = SOME ty) ∧
  (conversion_source_type scopes ty (BoundAtom x) =
    case lookup_binding x scopes of
      SOME b =>
        (case b.binding_type of SingleType src => SOME src | _ => NONE)
    | NONE => NONE)
End

Definition scalar_outcome_value_def:
  scalar_outcome_value (ScalarOk s) = ValueOk (ScalarValue s) ∧
  scalar_outcome_value (ScalarPanic code) = ValueAbrupt (PanicCompletion code) ∧
  scalar_outcome_value ScalarInvalid =
    ValueAbrupt (InvalidCompletion "ill-typed scalar operands")
End

(* Operations over scalar values and tuples, without storage access. *)
Definition eval_pure_operation_def:
  eval_pure_operation env scopes op =
    case op of
      ScalarOperation ty mode oper atoms =>
        (case eval_atoms scopes atoms of
           NONE => ValueAbrupt (InvalidCompletion "unbound atom")
         | SOME vs =>
             (case scalar_values vs of
                NONE => ValueAbrupt (InvalidCompletion "non-scalar operand")
              | SOME ss =>
                  scalar_outcome_value
                    (eval_scalar_operation env ty mode oper ss)))
    | ConvertOperation ty a =>
        (case (conversion_source_type scopes ty a, eval_atom scopes a) of
           (SOME src, SOME (ScalarValue s)) =>
             scalar_outcome_value (eval_conversion env src ty s)
         | (SOME src, SOME (ReferenceValue r)) => convert_byte_reference src ty r
         | _ => ValueAbrupt (InvalidCompletion "ill-typed conversion"))
    | TupleOperation atoms =>
        (case eval_atoms scopes atoms of
           SOME vs => ValueOk (TupleValue vs)
         | NONE => ValueAbrupt (InvalidCompletion "unbound atom"))
    | TupleComponentOperation n a =>
        (case eval_atom scopes a of
           SOME (TupleValue vs) =>
             (case oEL n vs of
                SOME v => ValueOk v
              | NONE => ValueAbrupt (InvalidCompletion "tuple index"))
         | _ => ValueAbrupt (InvalidCompletion "not a tuple"))
    | _ => ValueAbrupt (InvalidCompletion "unsupported operation")
End

(* msg, this, tx and block reads, from the frame. *)
(* The numeric fields are unbounded in the frame; the EVM reads each as a
 * word, so as a uint256 it wraps.
 *)
Definition environment_value_def:
  environment_value (fr : source_frame) f =
    case f of
      MsgData => ReferenceValue (CalldataReference 0 (LENGTH fr.call_data) BytesT)
    | MsgSender => ScalarValue (AddressValue fr.sender_address)
    | MsgValue =>
        ScalarValue (IntegerValue (wrap_integer F 256 (&fr.call_value)))
    | SelfAddress => ScalarValue (AddressValue fr.self_address)
    | TxOrigin => ScalarValue (AddressValue fr.tx_params.origin)
    | TxGasPrice =>
        ScalarValue (IntegerValue (wrap_integer F 256 (&fr.tx_params.gasPrice)))
    | BlockNumber =>
        ScalarValue (IntegerValue (wrap_integer F 256 (&fr.tx_params.blockNumber)))
    | BlockTimestamp =>
        ScalarValue (IntegerValue (wrap_integer F 256 (&fr.tx_params.blockTimeStamp)))
    | BlockChainId =>
        ScalarValue (IntegerValue (wrap_integer F 256 (&fr.tx_params.chainId)))
    | BlockCoinbase => ScalarValue (AddressValue fr.tx_params.blockCoinBase)
    | BlockBaseFee =>
        ScalarValue (IntegerValue (wrap_integer F 256 (&fr.tx_params.baseFeePerGas)))
    | BlockGasLimit =>
        ScalarValue (IntegerValue (wrap_integer F 256 (&fr.tx_params.blockGasLimit)))
End

(* Pure operations; calls and array mutations are handled by statements. *)
Definition eval_operation_def:
  eval_operation env (st : source_state) op =
    case op of
      DefaultBytesOperation element =>
        if byte_sequence_type element then
          ValueOk (ReferenceValue (MemoryReference (HeapId 0) 0 element))
        else ValueAbrupt (InvalidCompletion "bad default byte type")
    | StateReferenceOperation x =>
        (case state_reference env st.frame.self_address x of
           SOME r => ValueOk (ReferenceValue r)
         | _ => ValueAbrupt (InvalidCompletion "bad state reference"))
    | ReadOperation ty a =>
        (case eval_atom st.scopes a of
           SOME (ReferenceValue (MemoryReference h i rty)) =>
             read_memory_reference st ty (MemoryReference h i rty)
         | SOME (ReferenceValue r) => read_storage_reference st.world.accounts ty r
         | _ => ValueAbrupt (InvalidCompletion "bad storage reference"))
    | ByteIndexOperation a index =>
        (case (eval_atom st.scopes a, eval_atom st.scopes index) of
           (SOME (ReferenceValue r), SOME (ScalarValue (IntegerValue i))) =>
             (case r of
                StorageReference _ _ _ _ _ _ =>
                  (case navigate_storage env st.world.accounts r (IntegerValue i) of
                     ValueOk (ReferenceValue element) =>
                       read_storage_reference st.world.accounts (FixedBytesT 1) element
                   | ValueAbrupt c => ValueAbrupt c
                   | _ => ValueAbrupt (InvalidCompletion "bad storage byte reference"))
              | _ => case byte_contents st r of
                INL bs =>
                  if i < 0 ∨ &(LENGTH bs) ≤ i then ValueAbrupt (PanicCompletion 50)
                  else (case oEL (Num i) bs of
                          SOME b => ValueOk (ScalarValue (BytesValue [b]))
                        | NONE => ValueAbrupt (InvalidCompletion "bad byte index"))
              | INR c => ValueAbrupt c)
         | _ => ValueAbrupt (InvalidCompletion "bad byte index operands"))
    | ArrayLengthOperation a =>
        (case eval_atom st.scopes a of
           SOME (ReferenceValue r) =>
             (case r of
                StorageReference _ _ _ _ _ _ => storage_array_length st.world.accounts r
              | _ => case reference_bytes st r of
                       SOME bs => ValueOk (ScalarValue (IntegerValue (&(LENGTH bs))))
                     | NONE => ValueAbrupt (InvalidCompletion "bad byte sequence reference"))
         | _ => ValueAbrupt (InvalidCompletion "bad array reference"))
    | NavigateOperation ty root_expr (FieldNavigation member_id) =>
        (case eval_atom st.scopes root_expr of
           SOME (ReferenceValue r) => navigate_storage_field env r member_id
         | _ => ValueAbrupt (InvalidCompletion "bad struct reference"))
    | NavigateOperation ty root_expr (IndexNavigation index) =>
        (case (eval_atom st.scopes root_expr, eval_atom st.scopes index) of
           (SOME (ReferenceValue (MemoryReference h offset rty)),
            SOME (ScalarValue (IntegerValue i))) =>
             navigate_memory_byte st (MemoryReference h offset rty) i
         | (SOME (ReferenceValue r), SOME (ScalarValue s)) =>
             navigate_storage env st.world.accounts r s
         | _ => ValueAbrupt (InvalidCompletion "bad index operands"))
    | EnvironmentOperation f =>
        ValueOk (environment_value st.frame f)
    | _ => eval_pure_operation env st.scopes op
End

(* Procedures *)

Definition default_elementary_def:
  default_elementary ty =
    case ty of
      BoolT => SOME (BoolValue F)
    | UintT _ => SOME (IntegerValue 0)
    | IntT _ => SOME (IntegerValue 0)
    | AddressT _ => SOME (AddressValue 0w)
    | FixedBytesT n => SOME (BytesValue (REPLICATE n 0w))
    | _ => NONE
End

Definition default_scalar_def:
  default_scalar env ty =
    case ty of
      EnumT _ => SOME (IntegerValue 0)
    | UserValueT id =>
        (case lookup_user_value env id of
           SOME u => default_elementary u
         | NONE => NONE)
    | _ => default_elementary ty
End

Definition single_binding_def:
  single_binding ty v = <| binding_type := SingleType ty; binding_value := v |>
End

Definition bind_parameters_def:
  (bind_parameters [] [] = SOME FEMPTY) ∧
  (bind_parameters ((x, ty) :: params) (v :: vs) =
    case bind_parameters params vs of
      SOME scope => SOME (scope |+ (ast_key x, single_binding ty v))
    | NONE => NONE) ∧
  (bind_parameters _ _ = NONE)
End

Definition default_runtime_value_def:
  default_runtime_value env ty =
    case ty of
      LocatedT MemoryLoc element =>
        if byte_sequence_type element then
          SOME (ReferenceValue (MemoryReference (HeapId 0) 0 element))
        else NONE
    | LocatedT CalldataLoc element =>
        if byte_sequence_type element then
          SOME (ReferenceValue (CalldataReference 0 0 element))
        else NONE
    | LocatedT StorageLoc element =>
        if byte_sequence_type element then
          SOME (ReferenceValue
            (StorageReference PersistentStorage 0w 0w 0 element (LayoutId 0)))
        else NONE
    | _ => OPTION_MAP ScalarValue (default_scalar env ty)
End

Definition bind_defaults_def:
  (bind_defaults env [] = SOME FEMPTY) ∧
  (bind_defaults env ((x, ty) :: rets) =
    case (default_runtime_value env ty, bind_defaults env rets) of
      (SOME s, SOME scope) =>
        SOME (scope |+ (ast_key x, single_binding ty s))
    | _ => NONE)
End

(* Parameters bound to arguments, return bindings default-initialised. *)
Definition entry_scope_def:
  entry_scope env (p : core_procedure) args =
    case (bind_parameters p.parameters args, bind_defaults env p.return_bindings)
    of
      (SOME params, SOME rets) => SOME (FUNION params rets)
    | _ => NONE
End

Definition read_returns_def:
  (read_returns scopes [] = SOME []) ∧
  (read_returns scopes ((x, _) :: rets) =
    case (lookup_binding x scopes, read_returns scopes rets) of
      (SOME b, SOME vs) => SOME (b.binding_value :: vs)
    | _ => NONE)
End

(* A call's value, following call_result_type: nothing, one value, or a tuple. *)
Definition pack_results_def:
  (pack_results [] = TupleValue []) ∧
  (pack_results [v] = v) ∧
  (pack_results vs = TupleValue vs)
End

(* Statements that do not run nested code *)

Definition define_binding_def:
  define_binding x ty v (st : source_state) =
    st with scopes :=
      bind_local x <| binding_type := ty; binding_value := v |> st.scopes
End

(* A storage write in a static frame fails; the EVM would halt exceptionally,
 * which no source completion models yet.
 *)
Definition write_target_def:
  write_target t a (st : source_state) =
    case (FLOOKUP st.targets (ast_key t), eval_atom st.scopes a) of
      (SOME (BindTarget x), SOME v) =>
        (case update_binding x v st.scopes of
           SOME scopes => SOME (st with scopes := scopes)
         | NONE => NONE)
    | (SOME (ValueTarget (MemoryReference h i ty)), SOME (ScalarValue s)) =>
        write_memory_byte (MemoryReference h i ty) s st
    | (SOME (ValueTarget (StorageReference PersistentStorage addr slot offset
                            ty _)), SOME (ScalarValue s)) =>
        if st.frame.static_context then NONE else
        (case write_storage st.world.accounts addr slot offset ty s of
           SOME accounts =>
             SOME (st with world := st.world with accounts := accounts)
         | NONE => NONE)
    | _ => NONE
End

(* The pinned profile checks push against 2^64, independently of source
 * arithmetic mode. push() preserves existing bytes at the appended location.
 * Update length before the value write, including in the presence of slot
 * collisions; pop clears the scalar before updating length. *)
Definition push_storage_array_def:
  push_storage_array env x annotation a value (st : source_state) gas =
    if st.frame.static_context then
      abrupt_result (InvalidCompletion "array push in static frame") st gas
    else case eval_atom st.scopes a of
      SOME (ReferenceValue
        (StorageReference PersistentStorage addr slot 0 (ArrayT element NONE) layout)) =>
        let old_length = w2n (lookup_storage slot
              (lookup_account addr st.world.accounts).storage) in
        if 2 ** 64 ≤ old_length then abrupt_result (PanicCompletion 65) st gas else
        (case fixed_array_element env addr (mapping_slot [] slot) element
                (old_length + 1) layout (&old_length) of
           ValueOk (ReferenceValue
             (StorageReference PersistentStorage _ data_slot offset _ _)) =>
             (case write_storage st.world.accounts addr slot 0 (UintT 256)
                     (IntegerValue (&(old_length + 1))) of
                SOME accounts =>
                  let updated =
                    case value of
                      NONE => SOME accounts
                    | SOME v =>
                        (case eval_atom st.scopes v of
                           SOME (ScalarValue s) =>
                             write_storage accounts addr data_slot offset element s
                         | _ => NONE) in
                  (case updated of
                     SOME accounts' =>
                       normal_result
                         (define_binding x annotation
                           (ReferenceValue (StorageReference PersistentStorage addr
                              data_slot offset element layout))
                           (st with world := st.world with accounts := accounts')) gas
                   | NONE => abrupt_result (InvalidCompletion "bad array push value") st gas)
              | NONE => abrupt_result (InvalidCompletion "bad array length write") st gas)
         | _ => abrupt_result (InvalidCompletion "bad array push element") st gas)
    | _ => abrupt_result (InvalidCompletion "bad dynamic array reference") st gas
End

Definition pop_storage_array_def:
  pop_storage_array env x annotation a (st : source_state) gas =
    if st.frame.static_context then
      abrupt_result (InvalidCompletion "array pop in static frame") st gas
    else case eval_atom st.scopes a of
      SOME (ReferenceValue
        (StorageReference PersistentStorage addr slot 0 (ArrayT element NONE) layout)) =>
        let old_length = w2n (lookup_storage slot
              (lookup_account addr st.world.accounts).storage) in
        if old_length = 0 then abrupt_result (PanicCompletion 49) st gas else
        (case (fixed_array_element env addr (mapping_slot [] slot) element
                 old_length layout (&(old_length - 1)), default_scalar env element) of
           (ValueOk (ReferenceValue
             (StorageReference PersistentStorage _ data_slot offset _ _)), SOME scalar_zero) =>
             (case write_storage st.world.accounts addr data_slot offset element scalar_zero of
                SOME accounts =>
                  (case write_storage accounts addr slot 0 (UintT 256)
                          (IntegerValue (&(old_length - 1))) of
                     SOME accounts' =>
                       normal_result
                         (define_binding x annotation (TupleValue [])
                           (st with world := st.world with accounts := accounts')) gas
                   | NONE => abrupt_result (InvalidCompletion "bad array length write") st gas)
              | NONE => abrupt_result (InvalidCompletion "bad array element clear") st gas)
         | _ => abrupt_result (InvalidCompletion "bad array pop element") st gas)
    | _ => abrupt_result (InvalidCompletion "bad dynamic array reference") st gas
End

Definition eval_event_args_def:
  (eval_event_args scopes [] = SOME []) ∧
  (eval_event_args scopes ((ty, indexed, a) :: args) =
    case (eval_atom scopes a, eval_event_args scopes args) of
      (SOME v, SOME vs) => SOME ((ty, indexed, v) :: vs)
    | _ => NONE)
End

(* A log of the executing account, appended to the world's logs, so a revert
 * of the frame discards it with the rest of the world. As with storage
 * writes, an emit in a static frame fails.
 *)
Definition emit_event_def:
  emit_event topic args (st : source_state) gas =
    if st.frame.static_context then
      abrupt_result (InvalidCompletion "emit in static frame") st gas
    else case eval_event_args st.scopes args of
      NONE => abrupt_result (InvalidCompletion "unbound atom") st gas
    | SOME vs =>
        case event_log st.frame.self_address topic vs of
          SOME e =>
            normal_result
              (st with world := st.world with logs := st.world.logs ++ [e]) gas
        | NONE => abrupt_result (InvalidCompletion "bad event arguments") st gas
End

(* The gas a high-level call gives its callee. The source does not track gas,
 * where the bytecode passes all but a 64th of what it has left.
 *)
Definition external_call_gas_def:
  external_call_gas = 10000000n
End

(* A high-level call, as the compiler's code makes it: arguments ABI-encoded
 * after the selector; a call that expects no return data reverts on a target
 * without code; a failed call reverts with the callee's revert data; return
 * data the decoder rejects reverts with none. A successful call leaves the
 * world the callee left, with its logs after the caller's.
 *)
Definition call_external_def:
  call_external x ty kind selector params rets target value args
                (st : source_state) gas =
    case (eval_atom st.scopes target, eval_atom st.scopes value,
          eval_atoms st.scopes args) of
      (SOME (ScalarValue (AddressValue callee)),
       SOME (ScalarValue (IntegerValue v)), SOME vs) =>
        (case encoded_values params vs of
           NONE => abrupt_result (InvalidCompletion "bad call arguments") st gas
         | SOME data =>
           let static = (kind = ExternalStaticCall ∨ st.frame.static_context) in
           if rets = [] ∧ (lookup_account callee st.world.accounts).code = []
           then abrupt_result (RevertCompletion []) st gas
           else if static ∧ v ≠ 0 then
             abrupt_result (InvalidCompletion "value in static frame") st gas
           else
             case run_external_call st.frame.self_address callee
                    (selector ++ data) (Num v) static external_call_gas
                    st.world.accounts st.world.transient st.frame.tx_params of
               NONE =>
                 abrupt_result (InvalidCompletion "call outside the model") st gas
             | SOME r =>
               if ¬r.call_success then
                 abrupt_result (RevertCompletion r.call_return) st gas
               else
                 let st' = st with world :=
                       <| accounts := r.call_accounts;
                          transient := r.call_transient;
                          logs := st.world.logs ++ r.call_logs |> in
                 case decode_arguments rets r.call_return of
                   SOME rvs =>
                     normal_result (define_binding x ty (pack_results rvs) st') gas
                 | NONE => abrupt_result (RevertCompletion []) st' gas)
    | _ => abrupt_result (InvalidCompletion "bad call operands") st gas
End

(* Every statement except internal calls, if and while. *)
Definition simple_stmt_def:
  simple_stmt env s st gas =
    case s of
      DefineStmt x ty (BytesLiteralOperation element bs) =>
        let (v, st') = allocate_bytes element bs st in
        normal_result (define_binding x ty v st') gas
    | DefineStmt x ty (AllocateBytesOperation element length) =>
        (case eval_atom st.scopes length of
           SOME (ScalarValue (IntegerValue n)) =>
             if n < 0 then abrupt_result (InvalidCompletion "negative byte allocation") st gas
             else if 2 ** 64 ≤ Num n then abrupt_result (PanicCompletion 65) st gas
             else let (v, st') = allocate_bytes element (REPLICATE (Num n) 0w) st in
                  normal_result (define_binding x ty v st') gas
         | _ => abrupt_result (InvalidCompletion "bad byte allocation length") st gas)
    | DefineStmt x ty (ArrayPushOperation a value) =>
        push_storage_array env x ty a value st gas
    | DefineStmt x ty (ArrayPopOperation a) =>
        pop_storage_array env x ty a st gas
    | DefineStmt x ty (ExternalCallOperation kind selector params rets target
                         value args) =>
        call_external x ty kind selector params rets target value args st gas
    | DefineStmt x ty op =>
        (case eval_operation env st op of
           ValueOk v => normal_result (define_binding x ty v st) gas
         | ValueAbrupt c => abrupt_result c st gas)
    | CaptureBindingStmt t x =>
        normal_result
          (st with targets := set_target t (BindTarget x) st.targets) gas
    | CaptureValueStmt t a =>
        (case eval_atom st.scopes a of
           SOME (ReferenceValue r) =>
             normal_result
               (st with targets := set_target t (ValueTarget r) st.targets) gas
         | _ => abrupt_result (InvalidCompletion "bad captured reference") st gas)
    | BindReferenceStmt t _ a =>
        (case write_target t a st of
           SOME st' => normal_result st' gas
         | NONE => abrupt_result (InvalidCompletion "bad reference binding") st gas)
    | CopyContentsStmt _ _ a b =>
        (case (eval_atom st.scopes a, eval_atom st.scopes b) of
           (SOME (ReferenceValue src), SOME (ReferenceValue dst)) =>
             (case copy_byte_contents src dst st of
                INL st' => normal_result st' gas
              | INR c => abrupt_result c st gas)
         | _ => abrupt_result (InvalidCompletion "bad byte sequence copy") st gas)
    | WriteScalarStmt t ty a =>
        (case write_target t a st of
           SOME st' => normal_result st' gas
         | NONE => abrupt_result (InvalidCompletion "bad scalar write") st gas)
    | ReturnStmt atoms =>
        (case eval_atoms st.scopes atoms of
           SOME vs => abrupt_result (ReturnCompletion vs) st gas
         | NONE => abrupt_result (InvalidCompletion "unbound atom") st gas)
    | BreakStmt => abrupt_result BreakCompletion st gas
    | ContinueStmt => abrupt_result ContinueCompletion st gas
    | PanicStmt code => abrupt_result (PanicCompletion code) st gas
    | EmitStmt topic args => emit_event topic args st gas
    | RevertErrorStmt selector params args =>
        (case eval_atoms st.scopes args of
           SOME vs =>
             (case encoded_values params vs of
                SOME data => abrupt_result (RevertCompletion (selector ++ data)) st gas
              | NONE => abrupt_result (InvalidCompletion "bad error arguments") st gas)
         | NONE => abrupt_result (InvalidCompletion "unbound atom") st gas)
    | RevertStmt a =>
        (case eval_atom st.scopes a of
           SOME (ScalarValue (BytesValue data)) =>
             abrupt_result (RevertCompletion data) st gas
         | _ => abrupt_result (InvalidCompletion "bad revert payload") st gas)
    | _ => abrupt_result (InvalidCompletion "unsupported statement") st gas
End

(* Pieces of the recursive cases *)

Definition branch_of_def:
  branch_of (st : source_state) c =
    case eval_atom st.scopes c of
      SOME (ScalarValue (BoolValue b)) => SOME b
    | _ => NONE
End

(* A call's returned values, packed per call_result_type, bound to x. *)
Definition bind_call_result_def:
  bind_call_result x ty (r : source_result) =
    case r.completion of
      ReturnCompletion vs =>
        normal_result (define_binding x ty (pack_results vs) r.state)
          r.unused_gas_evidence
    | _ => r
End

Datatype:
  loop_step = LoopExit | LoopNext | LoopStop
End

(* After a loop body: break leaves the loop normally, normal completion and
 * continue go round again, anything else propagates.
 *)
Definition loop_after_body_def:
  loop_after_body c =
    case c of
      BreakCompletion => LoopExit
    | NormalCompletion => LoopNext
    | ContinueCompletion => LoopNext
    | _ => LoopStop
End

Definition enter_procedure_def:
  enter_procedure (st : source_state) scope =
    st with <| scopes := [scope]; targets := FEMPTY |>
End

Definition restore_caller_def:
  restore_caller (caller : source_state) (callee : source_state) =
    callee with <| scopes := caller.scopes; targets := caller.targets |>
End

(* A body's completion as the call's: falling through returns the current
 * return bindings, and break/continue cannot escape a procedure.
 *)
Definition procedure_completion_def:
  procedure_completion (p : core_procedure) (r : source_result) =
    case r.completion of
      NormalCompletion =>
        (case read_returns r.state.scopes p.return_bindings of
           SOME vs => ReturnCompletion vs
         | NONE => InvalidCompletion "missing return binding")
    | BreakCompletion => InvalidCompletion "break escaped procedure"
    | ContinueCompletion => InvalidCompletion "continue escaped procedure"
    | c => c
End

(* The evaluator *)

Definition eval_block_def:
  (eval_block (n : num) env [] st gas = normal_result st gas) ∧
  (eval_block n env (s :: ss) st gas =
    let r = eval_stmt n env s st gas in
    if r.completion = NormalCompletion
    then eval_block n env ss r.state r.unused_gas_evidence
    else r) ∧
  (eval_stmt n env (DefineStmt x ty (InternalCallOperation f atoms)) st gas =
    case eval_atoms st.scopes atoms of
      SOME args => bind_call_result x ty (invoke_source n env f args st gas)
    | NONE => abrupt_result (InvalidCompletion "unbound atom") st gas) ∧
  (eval_stmt n env (IfStmt c ts es) st gas =
    case branch_of st c of
      SOME T => pop_result (eval_block n env ts (push_scope st) gas)
    | SOME F => pop_result (eval_block n env es (push_scope st) gas)
    | NONE =>
        abrupt_result (InvalidCompletion "non-boolean condition") st gas) ∧
  (eval_stmt n env (WhileStmt prelude c body) st gas =
    eval_loop n env prelude c body st gas) ∧
  (eval_stmt n env s st gas = simple_stmt env s st gas) ∧
  (* One iteration in a pushed scope; fuel is spent on the back edge. *)
  (eval_loop n env prelude c body st gas =
    let r1 = eval_block n env prelude (push_scope st) gas in
    if r1.completion ≠ NormalCompletion then pop_result r1 else
    case branch_of r1.state c of
      NONE =>
        pop_result
          (r1 with completion := InvalidCompletion "non-boolean condition")
    | SOME b =>
        if ¬b then pop_result r1 else
        let r2 = pop_result (eval_block n env body r1.state
                               r1.unused_gas_evidence) in
        case loop_after_body r2.completion of
          LoopExit => r2 with completion := NormalCompletion
        | LoopStop => r2
        | LoopNext =>
            if n = 0 then r2 with completion := FuelExhausted
            else eval_loop (n - 1) env prelude c body r2.state
                   r2.unused_gas_evidence) ∧
  (* A successful call completes with ReturnCompletion of the returned values,
   * whether the body returned explicitly or fell through.
   *)
  (invoke_source n env f args st gas =
    if n = 0 then abrupt_result FuelExhausted st gas else
    case lookup_procedure env f of
      NONE => abrupt_result (InvalidCompletion "unknown procedure") st gas
    | SOME p =>
        case entry_scope env p args of
          NONE => abrupt_result (InvalidCompletion "bad arguments") st gas
        | SOME scope =>
            let r = eval_block (n - 1) env p.body (enter_procedure st scope)
                      gas in
            abrupt_result (procedure_completion p r)
              (restore_caller st r.state) r.unused_gas_evidence)
Termination
  WF_REL_TAC ‘inv_image ($< LEX $<)
    (λx. case x of
           INL (n, env, ss, st, gas) => (n, list_size core_stmt_size ss)
         | INR (INL (n, env, s, st, gas)) => (n, core_stmt_size s)
         | INR (INR (INL (n, env, pre, c, bd, st, gas))) =>
             (n, list_size core_stmt_size pre +
                 list_size core_stmt_size bd + 1)
         | INR (INR (INR (n, env, f, args, st, gas))) => (n, 0))’ >>
  rw[solidityCoreTheory.core_stmt_size_def, listTheory.list_size_def] >>
  rename1 ‘core_atom_size a’ >> Cases_on ‘a’ >>
  simp[solidityCoreTheory.core_atom_size_def]
End

(* cv translation, so core programs run under cv_compute. Termination of the
 * translated evaluator follows a scaled (fuel, size) order on the cv encodings,
 * strictly decreasing on every cv input.
 *)

val () = cv_auto_trans simple_stmt_def;
val () = cv_auto_trans bind_call_result_def;
val () = cv_auto_trans procedure_completion_def;

val () = cv_auto_trans_rec eval_block_def (
  WF_REL_TAC ‘inv_image ($< LEX $<)
    (λx. case x of
           INL (n, env, ss, st, gas) => (cv$c2n n, 2 * cv_size ss)
         | INR (INL (n, env, s, st, gas)) => (cv$c2n n, 2 * cv_size s + 1)
         | INR (INR (INL (n, env, pre, c, bd, st, gas))) =>
             (cv$c2n n, 2 * (cv_size pre + cv_size bd) + 1)
         | INR (INR (INR (n, env, f, args, st, gas))) => (cv$c2n n, 0))’ >>
  cv_termination_tac >>
  (* a while statement's prelude and body against its encoding *)
  rename1 ‘cv_snd (cv_snd x)’ >> Cases_on ‘x’ >> gvs[] >>
  rename1 ‘cv_snd y’ >> Cases_on ‘y’ >> gvs[]
);
