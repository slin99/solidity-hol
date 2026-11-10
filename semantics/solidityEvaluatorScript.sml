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
  solidityMemory solidityABI externalCall yulEvaluator
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
         | (SOME src, SOME (ReferenceValue r)) =>
             if src = ty then ValueOk (ReferenceValue r)
             else convert_byte_reference src ty r
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

(* A call's value, following call_result_type: nothing, one value, or a tuple. *)
Definition pack_results_def:
  (pack_results [] = TupleValue []) ∧
  (pack_results [v] = v) ∧
  (pack_results vs = TupleValue vs)
End

(* Pure operations; calls and array mutations are handled by statements. *)
Definition eval_operation_def:
  eval_operation env (st : source_state) op =
    case op of
      NullMemoryOperation ty =>
        ValueOk (ReferenceValue (MemoryReference (HeapId 0) 0 ty))
    | StateReferenceOperation x =>
        (case state_reference env st.frame.self_address x of
           SOME r => ValueOk (ReferenceValue r)
         | _ => ValueAbrupt (InvalidCompletion "bad state reference"))
    | ImmutableReferenceOperation x =>
        if IS_SOME (ALOOKUP env.immutables x)
        then ValueOk (ReferenceValue (ImmutableReference x))
        else ValueAbrupt (InvalidCompletion "bad immutable reference")
    | ReadOperation ty a =>
        (case eval_atom st.scopes a of
           SOME (ReferenceValue (MemoryReference h i rty)) =>
             read_memory_reference st ty (MemoryReference h i rty)
         | SOME (ReferenceValue (ImmutableReference x)) =>
             (case FLOOKUP st.immutables (ast_key x) of
                SOME s => ValueOk (ScalarValue s)
              | NONE =>
                  case default_elementary ty of
                    SOME s => ValueOk (ScalarValue s)
                  | NONE => ValueAbrupt (InvalidCompletion "bad immutable type"))
         | SOME (ReferenceValue r) => read_storage_reference env st.world.accounts ty r
         | _ => ValueAbrupt (InvalidCompletion "bad storage reference"))
    | ByteIndexOperation a index =>
        (case (eval_atom st.scopes a, eval_atom st.scopes index) of
           (SOME (ReferenceValue r), SOME (ScalarValue (IntegerValue i))) =>
             (case r of
                StorageReference _ _ _ _ _ _ =>
                  (case navigate_storage env st.world.accounts r (IntegerValue i) of
                     ValueOk (ReferenceValue element) =>
                       read_storage_reference env st.world.accounts (FixedBytesT 1) element
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
    | ArrayIndexOperation a index =>
        (case (eval_atom st.scopes a, eval_atom st.scopes index) of
           (SOME (ReferenceValue (CalldataReference data n (ArrayT element _))),
            SOME (ScalarValue (IntegerValue i))) =>
             if i < 0 ∨ &n ≤ i then ValueAbrupt (PanicCompletion 50) else
             (case calldata_element st.frame.call_data element data (Num i) of
                INL v => ValueOk v
              | INR c => ValueAbrupt c)
         | (SOME (ReferenceValue r), SOME (ScalarValue (IntegerValue i))) =>
             (case r of
                StorageReference _ _ _ _ (ArrayT element _) _ =>
                  (case navigate_storage env st.world.accounts r (IntegerValue i) of
                     ValueOk (ReferenceValue r') =>
                       read_storage_reference env st.world.accounts element r'
                   | ValueOk _ => ValueAbrupt (InvalidCompletion "bad storage array element")
                   | ValueAbrupt c => ValueAbrupt c)
              | _ =>
                case memory_array_element st r i of
                  INL (_, _, _, v) => ValueOk v
                | INR c => ValueAbrupt c)
         | _ => ValueAbrupt (InvalidCompletion "bad array index operands"))
    | CodeLengthOperation a =>
        (case eval_atom st.scopes a of
           SOME (ScalarValue (AddressValue address)) =>
             ValueOk (ScalarValue (IntegerValue
               (&(LENGTH (lookup_account address st.world.accounts).code))))
         | _ => ValueAbrupt (InvalidCompletion "bad code length operand"))
    | Keccak256Operation a =>
        (case eval_atom st.scopes a of
           SOME (ReferenceValue r) =>
             (case byte_contents st r of
                INL bs => ValueOk (ScalarValue (BytesValue (num_to_bytes 32
                            (w2n (word_of_bytes_be (Keccak_256_w64 bs) : bytes32)))))
              | INR c => ValueAbrupt c)
         | _ => ValueAbrupt (InvalidCompletion "bad keccak256 operand"))
    (* The precompile at address 1, as the compiler calls it: an invalid
     * signature returns nothing, which reads as address(0). *)
    | EcrecoverOperation h v r s =>
        (case (eval_atom st.scopes h, eval_atom st.scopes v,
               eval_atom st.scopes r, eval_atom st.scopes s) of
           (SOME (ScalarValue (BytesValue hb)), SOME (ScalarValue (IntegerValue vi)),
            SOME (ScalarValue (BytesValue rb)), SOME (ScalarValue (BytesValue sb))) =>
             ValueOk (ScalarValue (AddressValue
               (case ecrecover (word_of_bytes_be hb) (Num vi)
                       (num_of_be_bytes rb) (num_of_be_bytes sb) of
                  SOME a => a
                | NONE => 0w)))
         | _ => ValueAbrupt (InvalidCompletion "bad ecrecover operands"))
    (* The compiler's decoder from memory: short data, or a value outside its
     * type, reverts with no data; data after the encoding is ignored. *)
    | AbiDecodeOperation tys a =>
        (case eval_atom st.scopes a of
           SOME (ReferenceValue r) =>
             (case byte_contents st r of
                INL bs =>
                  (case decode_arguments env tys bs 0 (memory_free_pointer st) of
                     INL vs => ValueOk (pack_results vs)
                   | INR c => ValueAbrupt c)
              | INR c => ValueAbrupt c)
         | _ => ValueAbrupt (InvalidCompletion "bad abi.decode operand"))
    | ArrayLengthOperation a =>
        (case eval_atom st.scopes a of
           SOME (ReferenceValue r) =>
             (case r of
                StorageReference _ _ _ _ _ _ => storage_array_length st.world.accounts r
              | MemoryReference _ _ (ArrayT _ _) =>
                  (case memory_array_length st r of
                     SOME n => ValueOk (ScalarValue (IntegerValue (&n)))
                   | NONE => ValueAbrupt (InvalidCompletion "bad memory array reference"))
              | CalldataReference _ n _ => ValueOk (ScalarValue (IntegerValue (&n)))
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

(* A static memory array return binding starts at object zero too; the
 * elaborated body allocates its zero value before running. The compiler
 * rejects reading a calldata return binding before it is assigned, so its
 * default is never observed. *)
Definition default_runtime_value_def:
  default_runtime_value env ty =
    case ty of
      LocatedT MemoryLoc element =>
        if memory_object_type element then
          SOME (ReferenceValue (MemoryReference (HeapId 0) 0 element))
        else NONE
    | LocatedT CalldataLoc element =>
        if calldata_object_type element then
          SOME (ReferenceValue (CalldataReference 0
            (case element of ArrayT _ (SOME n) => n | _ => 0) element))
        else NONE
    | LocatedT StorageLoc element =>
        if storage_object_type element then
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
    | (SOME (ReferenceFieldTarget (HeapId id) i _), SOME v) =>
        write_memory_element id i v st
    | (SOME (ValueTarget (ImmutableReference x)), SOME (ScalarValue s)) =>
        SOME (st with immutables := st.immutables |+ (ast_key x, s))
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
  emit_event env topic args (st : source_state) gas =
    case eval_event_args st.scopes args of
      NONE => abrupt_result (InvalidCompletion "unbound atom") st gas
    | SOME vs =>
        case event_log env st st.frame.self_address topic vs of
          INL e =>
            if st.frame.static_context then
              abrupt_result (InvalidCompletion "emit in static frame") st gas
            else normal_result
              (st with world := st.world with logs := st.world.logs ++ [e]) gas
        | INR c => abrupt_result c st gas
End

(* The gas a high-level call gives its callee. The source does not track gas,
 * where the bytecode passes all but a 64th of what it has left.
 *)
Definition external_call_gas_def:
  external_call_gas = 10000000n
End

(* The gas a call gives its callee with its gas option: the option, capped at
 * external_call_gas as the CALL opcode caps it at the gas left. *)
Definition callee_gas_def:
  (callee_gas scopes NONE = SOME external_call_gas) ∧
  (callee_gas scopes (SOME g) =
    case eval_atom scopes g of
      SOME (ScalarValue (IntegerValue n)) => SOME (MIN (Num n) external_call_gas)
    | _ => NONE)
End

(* A high-level call, as the compiler's code makes it: arguments ABI-encoded
 * after the selector; a call that expects no return data reverts on a target
 * without code; a failed call reverts with the callee's revert data; return
 * data the decoder rejects reverts with none. A successful call leaves the
 * world the callee left, with its logs after the caller's.
 *)
(* The unused success fields of a failed try call still have their declared
 * scalar types. *)
Definition default_call_results_def:
  (default_call_results [] = SOME []) ∧
  (default_call_results (ty :: rets) =
    case (default_elementary ty, default_call_results rets) of
      (SOME v, SOME vs) => SOME (v :: vs)
    | _ => NONE)
End

Definition call_external_mode_def:
  call_external_mode catching env x ty kind selector params rets target value
                g args (st : source_state) gas =
    case (eval_atom st.scopes target, eval_atom st.scopes value,
          callee_gas st.scopes g, eval_atoms st.scopes args) of
      (SOME (ScalarValue (AddressValue callee)),
       SOME (ScalarValue (IntegerValue v)), SOME limit, SOME vs) =>
        if rets = [] ∧ (lookup_account callee st.world.accounts).code = []
        then abrupt_result (RevertCompletion []) st gas
        else (case encoded_runtime_values env st params vs of
           INR c => abrupt_result c st gas
         | INL data =>
           let static = (kind = ExternalStaticCall ∨ st.frame.static_context) in
           if static ∧ v ≠ 0 then
             abrupt_result (InvalidCompletion "value in static frame") st gas
           else
             case run_external_call st.frame.self_address callee
                    (selector ++ data) (Num v) static limit
                    st.world.accounts st.world.transient st.frame.tx_params of
               NONE =>
                 abrupt_result (InvalidCompletion "call outside the model") st gas
             | SOME r =>
               if ¬r.call_success then
                 if ¬catching then abrupt_result (RevertCompletion r.call_return) st gas
                 else
                   (case default_call_results rets of
                      NONE => abrupt_result (InvalidCompletion "bad try return types") st gas
                    | SOME defaults =>
                        let values = ScalarValue (BoolValue F) :: MAP ScalarValue defaults in
                        if r.call_return = [] then
                          normal_result (define_binding x ty
                            (TupleValue (values ++ [ReferenceValue
                              (MemoryReference (HeapId 0) 0 BytesT)])) st) gas
                        else if 2 ** 64 ≤ 128 + st.memory_allocated +
                                32 + 32 * ((LENGTH r.call_return + 31) DIV 32) then
                          abrupt_result (PanicCompletion 65) st gas
                        else
                          let (data, st1) = allocate_bytes F BytesT r.call_return st in
                          normal_result (define_binding x ty
                            (TupleValue (values ++ [data])) st1) gas)
               else
                 let st' = st with world :=
                       <| accounts := r.call_accounts;
                          transient := r.call_transient;
                          logs := st.world.logs ++ r.call_logs |> in
                 let reserved = if EXISTS (λty. is_dynamic (abi_type ty)) rets then
                       LENGTH r.call_return
                     else MIN (head_lengths (MAP abi_type rets) 0)
                            (LENGTH r.call_return) in
                 let st1 = st' with memory_allocated := st'.memory_allocated +
                       32 * ((reserved + 31) DIV 32) in
                 case decode_arguments env rets r.call_return 0 (memory_free_pointer st1) of
                   INL rvs =>
                     (case materialize_arguments rets rvs st1 of
                        SOME (values, st2) =>
                          let result = if catching then
                                TupleValue (ScalarValue (BoolValue T) :: values ++
                                  [ReferenceValue (MemoryReference (HeapId 0) 0 BytesT)])
                              else pack_results values in
                          normal_result (define_binding x ty result st2) gas
                      | NONE => abrupt_result (InvalidCompletion "bad call results") st' gas)
                 | INR c => abrupt_result c st' gas)
    | _ => abrupt_result (InvalidCompletion "bad call operands") st gas
End

Definition call_external_def:
  call_external env x ty kind selector params rets target value g args st gas =
    call_external_mode F env x ty kind selector params rets target value g args
      st gas
End

(* A low-level target.call(data), target.staticcall(data) or
 * target.delegatecall(data), as the compiler makes it: the data passed where
 * it is, no check that the target has code, and a failure returned rather
 * than reverted. A delegate call runs the target's code in this contract's
 * account, with this frame's sender and value. No return data is the empty
 * array at 0x60; other return data is copied to a new memory bytes.
 *)
Definition call_low_level_def:
  call_low_level x ty kind target value g data (st : source_state) gas =
    case (eval_atom st.scopes target, eval_atom st.scopes value,
          callee_gas st.scopes g, eval_atom st.scopes data) of
      (SOME (ScalarValue (AddressValue callee)),
       SOME (ScalarValue (IntegerValue v)), SOME limit, SOME d) =>
        (case (case d of
                 ScalarValue (BytesValue bs) => INL bs
               | ReferenceValue r => byte_contents st r
               | _ => INR (InvalidCompletion "bad call data")) of
           INR c => abrupt_result c st gas
         | INL bs =>
           let static = (kind = ExternalStaticCall ∨ st.frame.static_context) in
           if static ∧ v ≠ 0 then
             abrupt_result (InvalidCompletion "value in static frame") st gas
           else
           case (if kind = ExternalDelegateCall then
                   run_delegate_call st.frame.self_address st.frame.sender_address
                     st.frame.call_value callee bs static limit
                     st.world.accounts st.world.transient st.frame.tx_params
                 else
                   run_external_call st.frame.self_address callee bs (Num v)
                     static limit st.world.accounts st.world.transient
                     st.frame.tx_params) of
             NONE => abrupt_result (InvalidCompletion "call outside the model") st gas
           | SOME res =>
             let st' = if res.call_success then
                   st with world :=
                     <| accounts := res.call_accounts;
                        transient := res.call_transient;
                        logs := st.world.logs ++ res.call_logs |>
                 else st in
             let success = ScalarValue (BoolValue res.call_success) in
             if res.call_return = [] then
               normal_result (define_binding x ty
                 (TupleValue [success; ReferenceValue (MemoryReference (HeapId 0) 0 BytesT)])
                 st') gas
             else if 2 ** 64 ≤ 128 + st'.memory_allocated + 32 +
                               32 * ((LENGTH res.call_return + 31) DIV 32)
             then abrupt_result (PanicCompletion 65) st' gas
             else
               let (v, st1) = allocate_bytes F BytesT res.call_return st' in
               normal_result (define_binding x ty (TupleValue [success; v]) st1) gas)
    | _ => abrupt_result (InvalidCompletion "bad low-level call operands") st gas
End

(* The selector an ABI encoding starts with: none, or four bytes. *)
Definition selector_bytes_def:
  selector_bytes scopes selector =
    case selector of
      NONE => SOME []
    | SOME s =>
        case eval_atom scopes s of
          SOME (ScalarValue (BytesValue bs)) => if LENGTH bs = 4 then SOME bs else NONE
        | _ => NONE
End

(* An ABI encoding as a new memory bytes, or string (string.concat),
 * allocated as the compiler does: Panic(0x41) when the free memory pointer
 * would pass 2^64. *)
Definition allocate_encoding_def:
  allocate_encoding x ty bs st gas =
    if 2 ** 64 ≤ 128 + st.memory_allocated + 32 + 32 * ((LENGTH bs + 31) DIV 32)
    then abrupt_result (PanicCompletion 65) st gas
    else let element = if ty = SingleType (LocatedT MemoryLoc StringT) then StringT
                       else BytesT in
         let (v, st') = allocate_bytes T element bs st in
         normal_result (define_binding x ty v st') gas
End

Definition abi_encode_def:
  abi_encode env x ty selector tys args st gas =
    case (selector_bytes st.scopes selector, eval_atoms st.scopes args) of
      (SOME prefix, SOME vs) =>
        (case encoded_runtime_values env st tys vs of
           INL bs => allocate_encoding x ty (prefix ++ bs) st gas
         | INR c => abrupt_result c st gas)
    | _ => abrupt_result (InvalidCompletion "bad abi.encode operands") st gas
End

Definition abi_encode_packed_def:
  abi_encode_packed x ty tys args st gas =
    case eval_atoms st.scopes args of
      SOME vs =>
        (case packed_values st tys vs of
           INL bs => allocate_encoding x ty bs st gas
         | INR c => abrupt_result c st gas)
    | NONE => abrupt_result (InvalidCompletion "bad abi.encodePacked operands") st gas
End

(* Every statement except internal calls, if and while. *)
Definition simple_stmt_def:
  simple_stmt env s st gas =
    case s of
      DefineStmt x ty (BytesLiteralOperation element bs) =>
        let (v, st') = allocate_bytes T element bs st in
        normal_result (define_binding x ty v st') gas
    | DefineStmt x ty (DefaultMemoryOperation element) =>
        (case default_memory_value element st of
           INL (v, st') => normal_result (define_binding x ty v st') gas
         | INR c => abrupt_result c st gas)
    | DefineStmt x ty (AllocateMemoryOperation element length) =>
        (case eval_atom st.scopes length of
           SOME (ScalarValue (IntegerValue n)) =>
             if n < 0 then abrupt_result (InvalidCompletion "negative allocation") st gas
             else if 2 ** 64 ≤ Num n then abrupt_result (PanicCompletion 65) st gas
             else if byte_sequence_type element then
               if 2 ** 64 ≤ 128 + st.memory_allocated + 32 + 32 * ((Num n + 31) DIV 32)
               then abrupt_result (PanicCompletion 65) st gas else
               let (v, st') = allocate_bytes T element (REPLICATE (Num n) 0w) st in
               normal_result (define_binding x ty v st') gas
             else
               (case zero_array element (Num n) st of
                  INL (v, st') => normal_result (define_binding x ty v st') gas
                | INR c => abrupt_result c st gas)
         | _ => abrupt_result (InvalidCompletion "bad allocation length") st gas)
    | DefineStmt x ty (CopyToMemoryOperation a) =>
        (case eval_atom st.scopes a of
           SOME (ReferenceValue (CalldataReference data n rty)) =>
             (case copy_calldata_array st.frame.call_data rty data n
                     (memory_free_pointer st) of
                INL v =>
                  (case materialize_value rty v st of
                     SOME (v', st') => normal_result (define_binding x ty v' st') gas
                   | NONE => abrupt_result (InvalidCompletion "bad calldata array copy") st gas)
              | INR c => abrupt_result c st gas)
         | SOME (ReferenceValue (StorageReference PersistentStorage addr slot 0 rty _)) =>
             (case storage_array_value env st.world.accounts addr slot rty of
                INL v =>
                  if 2 ** 64 ≤ memory_free_pointer st + memory_value_size rty v then
                    abrupt_result (PanicCompletion 65) st gas
                  else
                    (case materialize_value rty v st of
                       SOME (v', st') => normal_result (define_binding x ty v' st') gas
                     | NONE => abrupt_result (InvalidCompletion "bad storage array copy") st gas)
              | INR c => abrupt_result c st gas)
         | _ => abrupt_result (InvalidCompletion "bad array copy") st gas)
    | DefineStmt x ty (AbiEncodeOperation selector tys args) =>
        abi_encode env x ty selector tys args st gas
    | DefineStmt x ty (AbiEncodePackedOperation tys args) =>
        abi_encode_packed x ty tys args st gas
    | DefineStmt x ty (ArrayPushOperation a value) =>
        push_storage_array env x ty a value st gas
    | DefineStmt x ty (ArrayPopOperation a) =>
        pop_storage_array env x ty a st gas
    | DefineStmt x ty (ExternalCallOperation kind selector params rets target
                         value g args) =>
        call_external env x ty kind selector params rets target value g args st gas
    | DefineStmt x ty (LowLevelCallOperation kind target value g data) =>
        call_low_level x ty kind target value g data st gas
    | DefineStmt x ty (TryExternalCallOperation kind selector params rets target
                         value g args) =>
        call_external_mode T env x ty kind selector params rets target value g
          args st gas
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
    | CaptureReferenceFieldStmt t a (IndexNavigation index) =>
        (case (eval_atom st.scopes a, eval_atom st.scopes index) of
           (SOME (ReferenceValue r), SOME (ScalarValue (IntegerValue i))) =>
             (case r of
                MemoryReference _ _ BytesT =>
                  (case navigate_memory_byte st r i of
                     ValueOk (ReferenceValue ref) =>
                       normal_result (st with targets := set_target t
                         (ValueTarget ref) st.targets) gas
                   | ValueOk _ => abrupt_result (InvalidCompletion "bad byte capture") st gas
                   | ValueAbrupt c => abrupt_result c st gas)
              | _ => case memory_array_element st r i of
                INL (id, k, element, _) =>
                  normal_result (st with targets := set_target t
                    (ReferenceFieldTarget (HeapId id) k element) st.targets) gas
              | INR c => abrupt_result c st gas)
         | _ => abrupt_result (InvalidCompletion "bad array element capture") st gas)
    | BindReferenceStmt t _ a =>
        (case write_target t a st of
           SOME st' => normal_result st' gas
         | NONE => abrupt_result (InvalidCompletion "bad reference binding") st gas)
    | CopyContentsStmt src_ty _ a b =>
        (case (eval_atom st.scopes a, eval_atom st.scopes b) of
           (SOME (ReferenceValue src), SOME (ReferenceValue dst)) =>
             (case src_ty of
                LocatedT _ (ArrayT element length) =>
                  (* The compiler's storage-to-storage copy returns at once
                   * when the source is the destination. *)
                  if (case (src, dst) of
                        (StorageReference PersistentStorage src_addr src_slot 0 _ _,
                         StorageReference PersistentStorage dst_addr dst_slot 0 _ _) =>
                          src_addr = dst_addr ∧ src_slot = dst_slot
                      | _ => F)
                  then normal_result st gas else
                  (case array_copy_value env st (ArrayT element length) src of
                     INL v =>
                       (case copy_to_storage env st.world.accounts (ArrayT element length) v
                               dst st.frame.static_context of
                          INL accounts =>
                            normal_result (st with world := st.world with accounts := accounts) gas
                        | INR c => abrupt_result c st gas)
                   | INR c => abrupt_result c st gas)
              | _ =>
                case copy_byte_contents src dst st of
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
    | EmitStmt topic args => emit_event env topic args st gas
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

(* Inline assembly. A block runs in the Yul evaluator on a machine built from
 * the source state: the world, the frame, a scope binding each referenced
 * declaration's Yul name to its word, and a memory holding the free memory
 * pointer at 0x40 and each memory byte sequence (bytes, string) where the
 * compiler keeps it: its length word at the object's address, then its bytes.
 * Nothing else of the source heap has a byte image, and the evaluator fails a
 * read of memory the block was not given. On normal exit the referenced
 * locals are written back, cleaned per type as the compiler cleans a value on
 * every Solidity read, and each byte sequence's bytes are read back from
 * memory; writes outside the scratch space [0, 0x40), the byte sequences'
 * data words and the memory from the free memory pointer up fail closed, and
 * so do writes to a length word or the free memory pointer. The memory from
 * the free memory pointer up is the temporary memory the Solidity docs let a
 * memory-safe block use: the source keeps nothing there, and the block's
 * writes there are dropped. In a static frame, a block that names a builtin changing
 * the world (call included) fails closed, whether or not it would run it.
 *
 * A call and staticcall run the callee as the source's own calls do
 * (run_external_call), with the machine's gas budget the one every call from
 * the source gets: gas() stands for it, and the static checks admit gas()
 * only as a call's gas argument, so the budget is never a value the block
 * sees. The return data buffer starts empty, and the static checks admit
 * returndatasize and returndatacopy only after a call of the block's own.
 *
 * Non-canonical words and storage bytes are outside the model (InvalidCompletion).
 *)

(* A value-type scalar as the stack word the compiler keeps it in: integers
 * in two's complement, fixed bytes left-aligned. *)
Definition assembly_word_def:
  assembly_word ty s =
    case ty of
      FixedBytesT k =>
        OPTION_MAP (λn. n * 2 ** (8 * (32 - k))) (stored_number k s)
    | _ => stored_number 32 s
End

(* The value of type ty a word written to a local stands for. *)
Definition assembly_value_def:
  assembly_value ty (w : num) =
    case ty of
      BoolT => SOME (BoolValue (w ≠ 0))
    | FixedBytesT k => stored_value ty (w DIV 2 ** (8 * (32 - k)))
    | _ =>
        case storage_bytes ty of
          SOME b => stored_value ty (w MOD 2 ** (8 * b))
        | NONE => NONE
End

Definition assembly_reference_word_def:
  assembly_reference_word env (st : source_state) r =
    case r of
      AssemblyLocal x ty =>
        (case lookup_binding x st.scopes of
           SOME b =>
             (case b.binding_value of
                ScalarValue s => assembly_word ty s
              | _ => NONE)
         | NONE => NONE)
    | AssemblySlot x =>
        OPTION_MAP (λv. w2n v.state_slot) (lookup_state_variable env x)
    | AssemblyOffset x =>
        OPTION_MAP (λv. v.state_offset) (lookup_state_variable env x)
    | AssemblyConstant a ty =>
        (case eval_atom st.scopes a of
           SOME (ScalarValue s) => assembly_word ty s
         | _ => NONE)
    (* the shared empty byte sequence is the compiler's zero slot, 0x60 *)
    | AssemblyMemory x ty =>
        (case lookup_binding x st.scopes of
           SOME b =>
             (case b.binding_value of
                ReferenceValue (MemoryReference (HeapId id) 0 _) =>
                  if id = 0 then SOME 0x60
                  else OPTION_MAP (λobj. obj.object_address) (FLOOKUP st.heap id)
              | _ => NONE)
         | NONE => NONE)
End

(* The words of a block's references: the locals' as the block's initial
 * scope, and the read-only ones' by name, for the code to hold as literals. *)
Definition assembly_inputs_def:
  (assembly_inputs env st [] =
    SOME (FEMPTY : string |-> bytes32, [] : (string # bytes32) list)) ∧
  (assembly_inputs env st ((name, r) :: refs) =
    case (assembly_reference_word env st r, assembly_inputs env st refs) of
      (SOME w, SOME (scope, literals)) =>
        (case r of
           AssemblyLocal _ _ => SOME (scope |+ (name, n2w w), literals)
         | _ => SOME (scope, (name, n2w w) :: literals))
    | _ => NONE)
End

(* The code with each name in sub read as its word, as the compiler puts the
 * values of x.slot, x.offset and constants in the code. A Yul function's
 * parameters and results may reuse a name for its body; a let may not.
 * Nested function definitions aren't imported, so a body's narrowed sub never
 * reaches an inner function, where the compiler would see the block's names.
 * Each builtin call becomes a checked one, whose memory reads the evaluator
 * holds to the memory the block was given. *)
Definition yul_substitute_expr_def:
  (yul_substitute_expr sub (YulLit l) = YulLit l) ∧
  (yul_substitute_expr sub (YulName x) =
    case ALOOKUP sub x of
      SOME w => YulLit (LitNumber w)
    | NONE => YulName x) ∧
  (yul_substitute_expr sub (YulBuiltin b es) =
    YulCheckedBuiltin b (yul_substitute_exprs sub es)) ∧
  (yul_substitute_expr sub (YulCheckedBuiltin b es) =
    YulCheckedBuiltin b (yul_substitute_exprs sub es)) ∧
  (yul_substitute_expr sub (YulApply f es) =
    YulApply f (yul_substitute_exprs sub es)) ∧
  (yul_substitute_exprs sub [] = []) ∧
  (yul_substitute_exprs sub (e :: es) =
    yul_substitute_expr sub e :: yul_substitute_exprs sub es)
End

(* sub without the names in xs. *)
Definition yul_unbind_def:
  (yul_unbind xs [] = ([] : (string # bytes32) list)) ∧
  (yul_unbind xs ((x, w) :: sub) =
    if MEM x xs then yul_unbind xs sub else (x, w) :: yul_unbind xs sub)
End

Definition yul_substitute_stmt_def:
  (yul_substitute_stmt sub (YulBlock ss) = YulBlock (yul_substitute_stmts sub ss)) ∧
  (yul_substitute_stmt sub (YulFunction f params results body) =
    YulFunction f params results
      (yul_substitute_stmts (yul_unbind (params ++ results) sub) body)) ∧
  (yul_substitute_stmt sub (YulLet xs NONE) = YulLet xs NONE) ∧
  (yul_substitute_stmt sub (YulLet xs (SOME e)) =
    YulLet xs (SOME (yul_substitute_expr sub e))) ∧
  (yul_substitute_stmt sub (YulAssign xs e) =
    YulAssign xs (yul_substitute_expr sub e)) ∧
  (yul_substitute_stmt sub (YulIf e body) =
    YulIf (yul_substitute_expr sub e) (yul_substitute_stmts sub body)) ∧
  (yul_substitute_stmt sub (YulSwitch e cases default) =
    YulSwitch (yul_substitute_expr sub e) (yul_substitute_cases sub cases)
      (yul_substitute_stmts sub default)) ∧
  (yul_substitute_stmt sub (YulFor pre c post body) =
    YulFor (yul_substitute_stmts sub pre) (yul_substitute_expr sub c)
      (yul_substitute_stmts sub post) (yul_substitute_stmts sub body)) ∧
  (yul_substitute_stmt sub YulBreak = YulBreak) ∧
  (yul_substitute_stmt sub YulContinue = YulContinue) ∧
  (yul_substitute_stmt sub YulLeave = YulLeave) ∧
  (yul_substitute_stmt sub (YulExprStmt e) =
    YulExprStmt (yul_substitute_expr sub e)) ∧
  (yul_substitute_stmts sub [] = []) ∧
  (yul_substitute_stmts sub (s :: ss) =
    yul_substitute_stmt sub s :: yul_substitute_stmts sub ss) ∧
  (yul_substitute_cases sub [] = []) ∧
  (yul_substitute_cases sub ((l, body) :: cases) =
    (l, yul_substitute_stmts sub body) :: yul_substitute_cases sub cases)
End

(* m with the byte sequence objects with ids 1 to i written into memory, each
 * as its length word and its data, zero-padded to whole words where the
 * compiler's memory holds the zeros (object_padded), the memory solc
 * allocates for it. Padding the compiler leaves as it was stays unwritten,
 * so a block reading it fails closed. *)
Definition assembly_project_def:
  (assembly_project heap 0 (m : yul_machine) = SOME m) ∧
  (assembly_project heap (SUC i) m =
    case FLOOKUP heap (SUC i) of
      SOME obj =>
        if byte_sequence_type obj.object_type then
          case heap_bytes obj 0 obj.object_length of
            SOME bs =>
              assembly_project heap i
                (yul_memory_write m obj.object_address
                   (word_to_bytes_be (n2w obj.object_length : bytes32) ++ bs ++
                    (if obj.object_padded then
                       REPLICATE (32 * ((obj.object_length + 31) DIV 32) -
                                  obj.object_length) 0w
                     else [])))
          | NONE => NONE
        else assembly_project heap i m
    | NONE => assembly_project heap i m)
End

Definition assembly_machine_def:
  assembly_machine (st : source_state) scope =
    assembly_project st.heap st.next_heap_id
      (yul_memory_write
         <| accounts := st.world.accounts; transient := st.world.transient;
            logs := st.world.logs; self_address := st.frame.self_address;
            caller_address := st.frame.sender_address;
            call_value := n2w st.frame.call_value;
            call_data := st.frame.call_data; return_data := [];
            code := []; objects := FEMPTY; immutable_offsets := FEMPTY;
            immutables := FEMPTY; memory := FEMPTY; memory_size := 0;
            gas_limit := external_call_gas; scopes := [scope];
            transaction_parameters := st.frame.tx_params |>
         0x40 (word_to_bytes_be (n2w (memory_free_pointer st) : bytes32)))
End

(* The memory a block may change and still exit normally, as (start, length)
 * ranges: the scratch space, and the data of each byte sequence object with
 * id 1 to i in whole words (a 32-byte mstore at its last byte is in bounds),
 * not its length word. *)
Definition assembly_writable_def:
  (assembly_writable heap 0 = [(0, 64)]) ∧
  (assembly_writable heap (SUC i) =
    case FLOOKUP heap (SUC i) of
      SOME obj =>
        if byte_sequence_type obj.object_type then
          (obj.object_address + 32, 32 * ((obj.object_length + 31) DIV 32)) ::
          assembly_writable heap i
        else assembly_writable heap i
    | NONE => assembly_writable heap i)
End

(* Memory with the n bytes from a, and then the ranges rs, removed. *)
Definition without_range_def:
  (without_range a 0 (mem : num |-> word8) = mem) ∧
  (without_range a (SUC n) mem = without_range (a + 1) n (mem \\ a))
End

Definition without_ranges_def:
  (without_ranges [] (mem : num |-> word8) = mem) ∧
  (without_ranges ((a, n) :: rs) mem = without_ranges rs (without_range a n mem))
End

(* The n bytes from a are all written, and zero. *)
Definition memory_zeros_def:
  (memory_zeros (mem : num |-> word8) a 0 ⇔ T) ∧
  (memory_zeros mem a (SUC n) ⇔
     FLOOKUP mem a = SOME 0w ∧ memory_zeros mem (a + 1) n)
End

(* The heap with the bytes of each byte sequence object with id 1 to i read
 * back from the block's final memory, and whether its padding is zero. *)
Definition assembly_read_back_def:
  (assembly_read_back heap 0 (m : yul_machine) = heap) ∧
  (assembly_read_back heap (SUC i) m =
    assembly_read_back
      (case FLOOKUP heap (SUC i) of
         SOME obj =>
           if byte_sequence_type obj.object_type then
             heap |+ (SUC i, obj with <|
               object_cells := byte_cells
                 (yul_memory_read m (obj.object_address + 32) obj.object_length);
               object_padded := memory_zeros m.memory
                 (obj.object_address + 32 + obj.object_length)
                 (32 * ((obj.object_length + 31) DIV 32) - obj.object_length) |>)
           else heap
       | NONE => heap) i m)
End

Definition assembly_world_def:
  assembly_world (m : yul_machine) =
    (<| accounts := m.accounts; transient := m.transient; logs := m.logs |>
       : source_world)
End

(* Writes a referenced local back from the block's final scopes; a location
 * or constant reference has nothing to write. *)
Definition assembly_write_one_def:
  assembly_write_one (name, r) scopes (yscopes : (string |-> bytes32) list) =
    case r of
      AssemblyLocal x ty =>
        (case yul_lookup name yscopes of
           NONE => NONE
         | SOME w =>
             case assembly_value ty (w2n w) of
               NONE => NONE
             | SOME s =>
                 if assembly_word ty s = SOME (w2n w) then
                   update_binding x (ScalarValue s) scopes
                 else NONE)
    | _ => SOME scopes
End

Definition assembly_write_back_def:
  (assembly_write_back [] scopes yscopes = SOME scopes) ∧
  (assembly_write_back (r :: refs) scopes yscopes =
    case assembly_write_one r scopes yscopes of
      NONE => NONE
    | SOME scopes' => assembly_write_back refs scopes' yscopes)
End

Definition assembly_result_def:
  assembly_result refs (st : source_state) m0 (r : yul_result) gas =
    let world = assembly_world r.machine in
    case r.completion of
      YulNormal =>
        let free = memory_free_pointer st in
        let writable = (free, r.machine.memory_size - free) ::
                       assembly_writable st.heap st.next_heap_id in
        if without_ranges writable r.machine.memory ≠
           without_ranges writable m0.memory then
          abrupt_result
            (InvalidCompletion "assembly wrote memory outside the scratch space and byte sequence data")
            st gas
        else
          (case assembly_write_back refs st.scopes r.machine.scopes of
             SOME scopes =>
               normal_result (st with <| world := world; scopes := scopes;
                   heap := assembly_read_back st.heap st.next_heap_id r.machine |>) gas
           | NONE =>
               abrupt_result (InvalidCompletion "assembly write-back failed")
                 st gas)
    | YulReturn data =>
        abrupt_result (HaltCompletion data) (st with world := world) gas
    | YulRevert data => abrupt_result (RevertCompletion data) st gas
    | YulInvalid reason => abrupt_result (InvalidCompletion reason) st gas
    | YulOutOfFuel => abrupt_result FuelExhausted st gas
    | _ =>
        abrupt_result (InvalidCompletion "assembly control escaped its block")
          st gas
End

Definition eval_assembly_def:
  eval_assembly n env code refs (st : source_state) gas =
    let bad = if st.frame.static_context
              then assembly_unsupported ++ assembly_state_writes
              else assembly_unsupported in
    if ¬assembly_stmts_ok bad code then
      abrupt_result (InvalidCompletion "unsupported assembly builtin") st gas
    else
    case assembly_inputs env st refs of
      NONE => abrupt_result (InvalidCompletion "bad assembly reference") st gas
    | SOME (scope, literals) =>
        case assembly_machine st scope of
          NONE => abrupt_result (InvalidCompletion "bad memory object") st gas
        | SOME m0 =>
            assembly_result refs st m0
              (run_yul n (yul_substitute_stmts literals code) m0) gas
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
  (eval_stmt n env (AssemblyStmt code refs) st gas =
    eval_assembly n env code refs st gas) ∧
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

val () = cv_auto_trans abi_encode_def;
val () = cv_auto_trans abi_encode_packed_def;
val () = cv_auto_trans simple_stmt_def;
val () = cv_auto_trans assembly_word_def;
val () = cv_auto_trans assembly_value_def;
val () = cv_auto_trans assembly_reference_word_def;
val () = cv_auto_trans assembly_inputs_def;
val () = cv_auto_trans yul_substitute_expr_def;
val () = cv_auto_trans yul_unbind_def;
val () = cv_auto_trans yul_substitute_stmt_def;
val () = cv_auto_trans assembly_project_def;
val () = cv_auto_trans assembly_machine_def;
val () = cv_auto_trans assembly_writable_def;
val () = cv_auto_trans without_range_def;
val () = cv_auto_trans without_ranges_def;
val () = cv_auto_trans memory_zeros_def;
val () = cv_auto_trans assembly_read_back_def;
val () = cv_auto_trans assembly_world_def;
val () = cv_auto_trans assembly_write_one_def;
val () = cv_auto_trans assembly_write_back_def;
val () = cv_auto_trans assembly_result_def;
val () = cv_auto_trans eval_assembly_def;
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
