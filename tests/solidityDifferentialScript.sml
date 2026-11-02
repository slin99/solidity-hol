(* Differential runs of a source unit of the admitted subset on concrete
 * transactions: its deployed bytecode from the pinned compiler, called in
 * Verifereum, and its elaborated core, entered through its dispatcher
 * (solidityEntry) with the same calldata, sender and value.
 *
 * Both runs start from the same storage of the contract account, given as
 * slot/value pairs, and of a peer contract, if any, that the contract can
 * call: code from the same compiler at peer_address. They are observed by their outcome, by the contract's
 * complete committed storage, including unlisted hashed slots, and by the
 * logs. Listed slots
 * from the layout/initial/expected storage are retained for diagnostics and
 * the existing observation interface; agreement additionally checks exact
 * storage-function equality through Verifereum's sparse cv representation.
 *
 * Encoding convention: both runs are observed as ABI-encoded data. A return
 * is the encoding of the declared return types; a panic is the revert data
 * Panic(uint256), selector 0x4e487b71; any other revert is its raw data.
 * A call is either raw calldata or a named function with inputs written as
 * integers, booleans or byte strings, typed by the function's parameters and
 * encoded after its selector; an input outside its type is a diagnostic, not
 * a call. Raw calldata declares no return types. Account balances are not
 * observed; the evaluator's world is the one after the value transfer, as
 * Verifereum gives the contract's frame.
 *
 * Diagnostics are never agreement: an unknown function, an input or result
 * that cannot be encoded, fuel exhaustion, an invalid completion, an
 * exceptional halt of the bytecode and an invalid transaction are distinct
 * outcomes, and a comparison involving one is inconclusive. Import rejection,
 * elaboration rejection and an invalid core are reported per unit by
 * solidityDifferentialLib before any call is made.
 *)
Theory solidityDifferential
Ancestors
  solidityElaborate solidityEntry contractABI keccak vfmCompute
Libs
  cv_transLib wordsLib intLib

(* Inputs *)

Datatype:
  argument = IntArg int | BoolArg bool | BytesArg (byte list)
End

Definition argument_scalar_def:
  (argument_scalar (IntArg i) = IntegerValue i) ∧
  (argument_scalar (BoolArg b) = BoolValue b) ∧
  (argument_scalar (BytesArg bs) = BytesValue bs)
End

(* An address is written as an integer or as 20 bytes. *)
Definition argument_value_def:
  (argument_value (AddressT _) (IntArg i) =
    if 0 ≤ i ∧ i < &(2 ** 160) then
      SOME (ScalarValue (AddressValue (n2w (Num i))))
    else NONE) ∧
  (argument_value (AddressT _) (BytesArg bs) =
    if LENGTH bs = 20 then
      SOME (ScalarValue (AddressValue (n2w (num_of_be_bytes bs))))
    else NONE) ∧
  (argument_value ty a =
    if elementary_scalar_has_type ty (argument_scalar a) then
      SOME (ScalarValue (argument_scalar a))
    else NONE)
End

Definition argument_values_def:
  (argument_values [] [] = SOME []) ∧
  (argument_values (ty :: tys) (a :: as) =
    case (argument_value ty a, argument_values tys as) of
      (SOME v, SOME vs) => SOME (v :: vs)
    | _ => NONE) ∧
  (argument_values _ _ = NONE)
End

(* Outcomes *)

Datatype:
  diagnostic =
    UnknownFunction
  | UnencodableArguments
  | UnencodableResult
  | OutOfFuel
  | InvalidCompletion
  | ExceptionalHalt
  | InvalidTransaction
End

Datatype:
  call_outcome = Returned (byte list) | Reverted (byte list) | Diagnostic diagnostic
End

Definition is_diagnostic_def:
  (is_diagnostic (Diagnostic _) ⇔ T) ∧
  (is_diagnostic _ ⇔ F)
End

Definition returned_def:
  returned tys vs = Returned (enc (Tuple tys) (ListV vs))
End

(* Functions of the unit's contract *)

Definition unit_function_def:
  unit_function u name =
    case u.unit_contracts of
      c :: _ =>
        (case FILTER (λf. f.fn_name = name) c.contract_functions of
           f :: _ => SOME f
         | [] => NONE)
    | [] => NONE
End

Definition function_types_def:
  function_types u name =
    case unit_function u name of
      SOME f => callee_types f
    | NONE => NONE
End

(* Storage *)

Definition contract_address_def:
  contract_address = 0x1000w : address
End

Definition peer_address_def:
  peer_address = 0x5000w : address
End

Definition seed_storage_def:
  (seed_storage [] = empty_storage) ∧
  (seed_storage ((k, v) :: kvs) =
    update_storage (n2w k) (n2w v) (seed_storage kvs))
End

(* The contract, with its code and initial storage, and no other account. *)
Definition contract_accounts_def:
  contract_accounts code storage =
    update_account contract_address
      (empty_account_state with <| code := code;
                                   storage := seed_storage storage |>)
      empty_accounts
End

(* The contract and a sender funded for the value it sends. *)
Definition differential_accounts_def:
  differential_accounts code storage sender =
    update_account sender (empty_account_state with balance := 2 ** 128)
      (contract_accounts code storage)
End

Definition observed_slots_def:
  observed_slots (prog : core_program) storage final =
    nub
      (MAP (λv. w2n v.state_slot) prog.state_variables ++ MAP FST storage ++
       MAP FST final)
End

Definition storage_values_def:
  storage_values st slots = MAP (λk. (k, w2n (lookup_storage (n2w k) st))) slots
End

(* A projection for diagnostics and the retained listed-slot interface. *)
Definition project_observation_def:
  project_observation slots (outcome, st, logs : event list) =
    (outcome, case st of NONE => [] | SOME store => storage_values store slots)
End

(* A listed slot ends with its listed value, any other with its initial one. *)
Definition expected_storage_def:
  expected_storage storage final slots =
    MAP (λk. (k, case ALOOKUP final k of
                   SOME v => v
                 | NONE => (case ALOOKUP storage k of SOME v => v | NONE => 0)))
      slots
End

(* The contract and the sender, with the peer's code and storage. *)
Definition case_accounts_def:
  case_accounts code storage sender peer_code peer_storage =
    update_account peer_address
      (empty_account_state with <| code := peer_code;
                                   storage := seed_storage peer_storage |>)
      (differential_accounts code storage sender)
End

(* Cases *)

(* A call to the deployed contract, or its creation from initcode with
 * constructor arguments, given as values or as raw bytes. *)
Datatype:
  call_input =
    NamedCall string (argument list)
  | RawCall (byte list)
  | Deploy (byte list) (argument list + byte list)
End

Datatype:
  expectation =
    ExpectReturn (argument list) | ExpectPanic num | ExpectRevert (byte list)
End

(* A transaction from the sender to the contract, from the initial storage
 * of the contract and of the peer (no code for none), with its expected
 * outcome, final storage entries and logs, each log given by its logger,
 * topics and data.
 *)
Datatype:
  differential_case = <|
    case_sender : address;
    case_value : num;
    case_input : call_input;
    case_storage : (num # num) list;
    case_peer_code : byte list;
    case_peer_storage : (num # num) list;
    case_expect : expectation;
    case_final : (num # num) list;
    case_logs : (address # bytes32 list # byte list) list
  |>
End

Definition call_data_def:
  call_data name params vs =
    case encoded_values params vs of
      SOME bs => SOME (function_selector name (MAP abi_type params) ++ bs)
    | NONE => NONE
End

Definition constructor_types_def:
  constructor_types u =
    case u.unit_contracts of
      c :: _ =>
        (case contract_constructor c.contract_info.node_id c.contract_functions of
           SOME f => callee_types f
         | NONE => SOME ([], []))
    | [] => NONE
End

(* The calldata and the declared return types of a call; for a creation, the
 * encoded constructor arguments, which follow the initcode in the
 * transaction's data. *)
Definition input_call_def:
  (input_call u (NamedCall name args) =
    case function_types u name of
      NONE => INL UnknownFunction
    | SOME (params, rets) =>
        case argument_values params args of
          NONE => INL UnencodableArguments
        | SOME vs =>
            case call_data name params vs of
              NONE => INL UnencodableArguments
            | SOME data => INR (data, rets)) ∧
  (input_call u (RawCall data) = INR (data, [])) ∧
  (input_call u (Deploy code (INR data)) = INR (data, [])) ∧
  (input_call u (Deploy code (INL args)) =
    case constructor_types u of
      NONE => INL UnknownFunction
    | SOME (params, _) =>
        case argument_values params args of
          NONE => INL UnencodableArguments
        | SOME vs =>
            case encoded_values params vs of
              NONE => INL UnencodableArguments
            | SOME data => INR (data, []))
End

Definition expected_logs_def:
  (expected_logs [] = []) ∧
  (expected_logs ((logger, topics, data) :: logs) =
    <| logger := logger; topics := topics; data := data |> ::
    expected_logs logs)
End

(* The transaction *)

(* Distinct values for each field a contract can read, so that reading the
 * wrong one shows up as a mismatch.
 *)
Definition differential_chain_id_def:
  differential_chain_id = 5n
End

Definition differential_block_def:
  differential_block = <|
    baseFeePerGas := 7; excessBlobGas := 0; gasUsed := 0; blobGasUsed := 0;
    number := 11; timeStamp := 1700000000; coinBase := 0xC0FFEEw;
    gasLimit := 30000000;
    prevRandao := 0w; hash := 0w; parentBeaconBlockRoot := 0w;
    stateRoot := 0w; transactions := []; withdrawals := [];
    requestsHash := 0w; withdrawalsRoot := 0w; rlpSize := 0
  |>
End

Definition differential_tx_def:
  differential_tx sender value data = <|
    from := sender; to := SOME contract_address; data := data; nonce := 0;
    value := value; gasLimit := 10000000; gasPrice := 9; accessList := [];
    blobVersionedHashes := []; maxFeePerBlobGas := NONE; maxFeePerGas := NONE;
    authorizationList := []
  |>
End

(* The account a case observes: the contract, or the one its creation
 * transaction makes. *)
Definition case_address_def:
  case_address c =
    case c.case_input of
      Deploy _ _ => address_for_create c.case_sender 0
    | _ => contract_address
End

Definition case_tx_def:
  case_tx c data =
    case c.case_input of
      Deploy code _ =>
        differential_tx c.case_sender c.case_value (code ++ data) with to := NONE
    | _ => differential_tx c.case_sender c.case_value data
End

(* The evaluator run *)

(* The contract's frame, with the transaction parameters Verifereum gives
 * the same transaction.
 *)
Definition differential_frame_def:
  differential_frame sender value data = <|
    self_address := contract_address; code_address := contract_address;
    sender_address := sender; call_value := value; call_data := data;
    static_context := F;
    tx_params := initial_tx_params differential_chain_id [] differential_block
                   (differential_tx sender value data) 0
  |>
End

Definition differential_world_def:
  differential_world accounts =
    <| accounts := accounts; transient := empty_transient_storage; logs := [] |>
End

(* The outcome, complete committed contract storage and logs of a run. *)
Definition contract_observation_def:
  contract_observation a r =
    case r of
      ContractReturned data w =>
        (Returned data, SOME (lookup_account a w.accounts).storage, w.logs)
    | ContractReverted data w =>
        (Reverted data, SOME (lookup_account a w.accounts).storage, w.logs)
    | ContractInvalid _ => (Diagnostic InvalidCompletion, NONE, [])
    | ContractOutOfFuel => (Diagnostic OutOfFuel, NONE, [])
End

Definition source_execution_def:
  source_execution code u prog fuel c =
    case input_call u c.case_input of
      INL d => (Diagnostic d, NONE, [])
    | INR (data, _) =>
        let a = case_address c in
        let fr = differential_frame c.case_sender c.case_value data with
                   <| self_address := a; code_address := a |> in
        let w = differential_world
                  (transfer_value c.case_sender a c.case_value
                     (case_accounts code c.case_storage c.case_sender
                        c.case_peer_code c.case_peer_storage)) in
        contract_observation a
          (case c.case_input of
             Deploy _ _ => deploy_contract fuel prog fr w
           | _ => call_contract fuel prog fr w)
End

Definition source_observation_def:
  source_observation code u prog fuel c slots =
    project_observation slots (source_execution code u prog fuel c)
End

(* The bytecode run *)

Definition evm_execution_def:
  evm_execution code u c =
    case input_call u c.case_input of
      INL d => (Diagnostic d, NONE, [])
    | INR (data, _) =>
        case run_transaction (Collect empty_domain) F differential_chain_id []
               differential_block
               (case_accounts code c.case_storage c.case_sender c.case_peer_code
                  c.case_peer_storage)
               (case_tx c data) of
          SOME (r, accounts) =>
            (let st = SOME (lookup_account (case_address c) accounts).storage in
             case r.result of
               NONE =>
                 (case c.case_input of
                    Deploy _ _ => (Returned [], st, r.logs)
                  | _ => (Returned r.output, st, r.logs))
             | SOME Reverted => (Reverted r.output, st, r.logs)
             | SOME _ => (Diagnostic ExceptionalHalt, NONE, []))
        | NONE => (Diagnostic InvalidTransaction, NONE, [])
End

Definition evm_observation_def:
  evm_observation code u c slots =
    project_observation slots (evm_execution code u c)
End

(* Expected outcomes *)

Definition expected_outcome_def:
  expected_outcome u input e =
    case e of
      ExpectReturn results =>
        (case input_call u input of
           INL d => Diagnostic d
         | INR (_, rets) =>
             case argument_values rets results of
               NONE => Diagnostic UnencodableResult
             | SOME vs =>
                 case encoded_values rets vs of
                   SOME bs => Returned bs
                 | NONE => Diagnostic UnencodableResult)
    | ExpectPanic n => Reverted (panic_data n)
    | ExpectRevert bs => Reverted bs
End

(* Comparison *)

Datatype:
  verdict =
    Agree call_outcome
    (* bytecode, source *)
  | Mismatch call_outcome call_outcome
    (* the outcome both runs agree on, the expected one *)
  | Unexpected call_outcome call_outcome
    (* bytecode, source, at least one a diagnostic *)
  | Inconclusive call_outcome call_outcome
    (* final storage: bytecode, source *)
  | StorageMismatch ((num # num) list) ((num # num) list)
    (* final storage: the one both runs agree on, the expected one *)
  | StorageUnexpected ((num # num) list) ((num # num) list)
    (* logs: bytecode, source *)
  | LogMismatch (event list) (event list)
    (* logs: the ones both runs agree on, the expected ones *)
  | LogUnexpected (event list) (event list)
End

Definition compare_observations_def:
  compare_observations (expected, expected_st) (evm, evm_st) (src, src_st) =
    if is_diagnostic evm ∨ is_diagnostic src then Inconclusive evm src
    else if evm ≠ src then Mismatch evm src
    else if evm ≠ expected then Unexpected evm expected
    else if evm_st ≠ src_st then StorageMismatch evm_st src_st
    else if evm_st ≠ expected_st then StorageUnexpected evm_st expected_st
    else Agree evm
End

Definition differential_verdict_def:
  differential_verdict code u prog fuel c =
    let slots = observed_slots prog c.case_storage c.case_final in
    let evm_run = evm_execution code u c in
    let src_run = source_execution code u prog fuel c in
    let evm = project_observation slots evm_run in
    let src = project_observation slots src_run in
    case compare_observations
      (expected_outcome u c.case_input c.case_expect,
       expected_storage c.case_storage c.case_final slots) evm src of
      Agree outcome =>
        if FST (SND evm_run) ≠ FST (SND src_run) then
          StorageMismatch (SND evm) (SND src)
        else if FST (SND evm_run) ≠
                SOME (seed_storage (c.case_final ++ c.case_storage)) then
          StorageUnexpected (SND evm)
            (expected_storage c.case_storage c.case_final slots)
        else if SND (SND evm_run) ≠ SND (SND src_run) then
          LogMismatch (SND (SND evm_run)) (SND (SND src_run))
        else if SND (SND evm_run) ≠ expected_logs c.case_logs then
          LogUnexpected (SND (SND evm_run)) (expected_logs c.case_logs)
        else Agree outcome
    | other => other
End

Definition is_agreement_def:
  (is_agreement (Agree _) ⇔ T) ∧
  (is_agreement _ ⇔ F)
End

Definition differential_agrees_def:
  differential_agrees code u prog fuel c ⇔
    is_agreement (differential_verdict code u prog fuel c)
End

Theorem compare_observations_agree:
  is_agreement (compare_observations x y z) ⇒
  ¬is_diagnostic (FST x) ∧ y = x ∧ z = x
Proof
  PairCases_on ‘x’ >> PairCases_on ‘y’ >> PairCases_on ‘z’ >>
  simp[compare_observations_def] >> rpt IF_CASES_TAC >>
  gvs[is_agreement_def]
QED

Theorem complete_check_agreement[local]:
  is_agreement
    (case verdict of
       Agree outcome =>
         if b1 then StorageMismatch s1 s2
         else if b2 then StorageUnexpected s3 s4
         else if b3 then LogMismatch l1 l2
         else if b4 then LogUnexpected l3 l4
         else Agree outcome
     | other => other) ⇒
  is_agreement verdict
Proof
  Cases_on ‘verdict’ >> simp[is_agreement_def] >>
  rpt IF_CASES_TAC >> simp[is_agreement_def]
QED

(* What an agreement establishes: both runs produce the expected outcome,
 * which is a return or a revert, never a diagnostic, and the expected final
 * storage at the observed slots.
 *)
Theorem differential_agrees_outcomes:
  differential_agrees code u prog fuel c ∧
  slots = observed_slots prog c.case_storage c.case_final ⇒
  ¬is_diagnostic (expected_outcome u c.case_input c.case_expect) ∧
  evm_observation code u c slots =
    (expected_outcome u c.case_input c.case_expect,
     expected_storage c.case_storage c.case_final slots) ∧
  source_observation code u prog fuel c slots =
    (expected_outcome u c.case_input c.case_expect,
     expected_storage c.case_storage c.case_final slots)
Proof
  rw[differential_agrees_def, differential_verdict_def,
     evm_observation_def, source_observation_def] >>
  drule complete_check_agreement >> strip_tac >>
  drule compare_observations_agree >> simp[]
QED

(* Full committed storage, including slots absent from diagnostics. *)
Theorem differential_agrees_storage:
  differential_agrees code u prog fuel c ⇒
  FST (SND (evm_execution code u c)) =
    SOME (seed_storage (c.case_final ++ c.case_storage)) ∧
  FST (SND (source_execution code u prog fuel c)) =
    SOME (seed_storage (c.case_final ++ c.case_storage))
Proof
  rw[differential_agrees_def, differential_verdict_def] >>
  BasicProvers.every_case_tac >> gvs[is_agreement_def]
QED

Theorem differential_agrees_logs:
  differential_agrees code u prog fuel c ⇒
  SND (SND (evm_execution code u c)) = expected_logs c.case_logs ∧
  SND (SND (source_execution code u prog fuel c)) = expected_logs c.case_logs
Proof
  rw[differential_agrees_def, differential_verdict_def] >>
  BasicProvers.every_case_tac >> gvs[is_agreement_def]
QED

val () = cv_auto_trans argument_scalar_def;
val () = cv_auto_trans solidityCoreWfTheory.elementary_scalar_has_type_def;
val () = cv_auto_trans argument_value_def;
val () = cv_auto_trans argument_values_def;
val () = cv_auto_trans is_diagnostic_def;
val () = cv_auto_trans returned_def;
val () = cv_auto_trans unit_function_def;
val () = cv_auto_trans function_types_def;
val () = cv_auto_trans seed_storage_def;
val () = cv_auto_trans contract_accounts_def;
val () = cv_auto_trans differential_accounts_def;
val () = cv_auto_trans case_accounts_def;
val () = cv_auto_trans listTheory.nub_def;
val () = cv_auto_trans observed_slots_def;
val () = cv_auto_trans storage_values_def;
val () = cv_auto_trans project_observation_def;
val () = cv_auto_trans expected_storage_def;
val () = cv_auto_trans call_data_def;
val () = cv_auto_trans constructor_types_def;
val () = cv_auto_trans input_call_def;
val () = cv_auto_trans expected_logs_def;
val () = cv_auto_trans differential_tx_def;
val () = cv_auto_trans case_address_def;
val () = cv_auto_trans case_tx_def;
val () = cv_auto_trans differential_frame_def;
val () = cv_auto_trans differential_world_def;
val () = cv_auto_trans contract_observation_def;
val () = cv_auto_trans source_execution_def;
val () = cv_auto_trans source_observation_def;
val () = cv_auto_trans evm_execution_def;
val () = cv_auto_trans evm_observation_def;
val () = cv_auto_trans expected_outcome_def;
val () = cv_auto_trans compare_observations_def;
val () = cv_auto_trans differential_verdict_def;
val () = cv_auto_trans is_agreement_def;
val () = cv_auto_trans differential_agrees_def;
