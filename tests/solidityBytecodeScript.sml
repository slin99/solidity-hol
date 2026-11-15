(* Concrete EVM execution and observations shared by the differential tests.
 * This layer depends only on Verifereum, independently of source elaboration.
 *)
Theory solidityBytecode
Ancestors contractABI keccak vfmCompute
Libs cv_transLib wordsLib intLib

Datatype:
  argument = IntArg int | BoolArg bool | BytesArg (byte list)
End

Datatype:
  diagnostic =
    UnknownFunction
  | UnencodableArguments
  | UnencodableResult
  | OutOfFuel
  | InvalidCompletion
  | ExceptionalHalt
  | InvalidTransaction
  | InvalidGasEvidence
End

Datatype:
  call_outcome = Returned (byte list) | Reverted (byte list) | Aborted | Diagnostic diagnostic
End

Definition is_diagnostic_def:
  (is_diagnostic (Diagnostic _) ⇔ T) ∧
  (is_diagnostic _ ⇔ F)
End

Definition returned_def:
  returned tys vs = Returned (enc (Tuple tys) (ListV vs))
End

Definition patch_word_def:
  patch_word w code i = TAKE i code ++ w ++ DROP (i + LENGTH w) code
End

Definition patch_immutables_def:
  (patch_immutables refs [] code = code) ∧
  (patch_immutables refs ((x, _, w) :: vs) code =
    patch_immutables refs vs
      (FOLDL (patch_word w) code
         (case ALOOKUP refs x of SOME offsets => offsets | NONE => [])))
End

Definition code_immutable_words_def:
  code_immutable_words refs code =
    FLAT (MAP (λ(_, offsets).
                 case offsets of i :: _ => TAKE 32 (DROP i code) | [] => [])
              refs)
End

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

Definition contract_accounts_def:
  contract_accounts code storage =
    update_account contract_address
      (empty_account_state with <| code := code;
                                   storage := seed_storage storage |>)
      empty_accounts
End

Definition differential_accounts_def:
  differential_accounts code storage sender =
    update_account sender (empty_account_state with balance := 2 ** 128)
      (contract_accounts code storage)
End

Definition storage_values_def:
  storage_values st slots = MAP (λk. (k, w2n (lookup_storage (n2w k) st))) slots
End

Definition project_observation_def:
  project_observation slots (outcome, st, logs : event list) =
    (outcome, case st of NONE => [] | SOME store => storage_values store slots)
End

Definition expected_storage_def:
  expected_storage storage final slots =
    MAP (λk. (k, case ALOOKUP final k of
                   SOME v => v
                 | NONE => (case ALOOKUP storage k of SOME v => v | NONE => 0)))
      slots
End

Definition seed_libraries_def:
  (seed_libraries [] accounts = accounts) ∧
  (seed_libraries ((addr, library_code) :: libraries) accounts =
    seed_libraries libraries
      (update_account addr (empty_account_state with code := library_code) accounts))
End

Theorem seed_libraries_foldl:
  ∀libraries accounts.
    seed_libraries libraries accounts =
    FOLDL (λaccounts (addr, library_code).
      update_account addr (empty_account_state with code := library_code) accounts)
      accounts libraries
Proof
  Induct >> simp[seed_libraries_def] >>
  Cases_on ‘h’ >> simp[seed_libraries_def]
QED

Definition case_accounts_def:
  case_accounts code storage sender peer_code peer_storage libraries =
    seed_libraries libraries (update_account peer_address
      (empty_account_state with <| code := peer_code;
                                   storage := seed_storage peer_storage |>)
      (differential_accounts code storage sender))
End

Datatype:
  call_input =
    NamedCall string (argument list)
  | RawCall (byte list)
  | Deploy (byte list) (argument list + byte list)
End

Datatype:
  expectation =
    ExpectReturn (argument list) | ExpectRawReturn (byte list)
  | ExpectPanic num | ExpectRevert (byte list) | ExpectAbort
End

Datatype:
  differential_case = <|
    case_sender : address;
    case_value : num;
    case_gas : num list;
    case_input : call_input;
    case_immutables : (num # argument) list;
    case_immutable_refs : (num # num list) list;
    case_storage : (num # num) list;
    case_peer_code : byte list;
    case_peer_storage : (num # num) list;
    case_libraries : (address # byte list) list;
    case_expect : expectation;
    case_final : (num # num) list;
    case_logs : (address # bytes32 list # byte list) list
  |>
End

Definition expected_logs_def:
  (expected_logs [] = []) ∧
  (expected_logs ((logger, topics, data) :: logs) =
    <| logger := logger; topics := topics; data := data |> ::
    expected_logs logs)
End

Definition differential_chain_id_def:
  differential_chain_id = 5n
End

(* Distinct values for the fields a contract can read expose field mix-ups. *)
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

(* Observe the called account, or the newly created account's immutable words. *)
Definition bytecode_execution_def:
  bytecode_execution (accounts, tx, refs) =
    case run_transaction (Collect empty_domain) F differential_chain_id []
           differential_block accounts tx of
      SOME (r, accounts) =>
        (let a = case tx.to of
                   NONE => address_for_create tx.from tx.nonce
                 | SOME address => address in
         let account = lookup_account a accounts in
         let st = SOME account.storage in
         case r.result of
           NONE =>
             (case tx.to of
                NONE => (Returned (code_immutable_words refs account.code), st, r.logs)
              | SOME _ => (Returned r.output, st, r.logs))
         | SOME Reverted => (Reverted r.output, st, r.logs)
         | SOME InvalidOpcode => (Aborted, st, r.logs)
         | SOME _ => (Diagnostic ExceptionalHalt, NONE, []))
    | NONE => (Diagnostic InvalidTransaction, NONE, [])
End

(* Track a GAS word through stack shuffles to a call's budget operand.
 * Dup of that word also exposes it as a value, so it is an observation. *)
Definition is_call_budget_gas_def:
  (is_call_budget_gas 0 parsed pc depth ⇔ F) ∧
  (is_call_budget_gas (SUC fuel) parsed pc depth ⇔
    case FLOOKUP parsed pc of
      NONE => F
    | SOME op =>
        let next_pc = pc + LENGTH (opcode op) in
        case op of
          Call => depth = 0
        | StaticCall => depth = 0
        | DelegateCall => depth = 0
        | CallCode => depth = 0
        | Push _ _ => is_call_budget_gas fuel parsed next_pc (depth + 1)
        | Dup n =>
            if depth = n then F
            else is_call_budget_gas fuel parsed next_pc (depth + 1)
        | Swap n =>
            let depth' = if depth = 0 then n + 1
                         else if depth = n + 1 then 0 else depth in
            is_call_budget_gas fuel parsed next_pc depth'
        | _ => F)
End

Definition observes_gas_def:
  observes_gas (s : execution_state) ⇔
    case s.contexts of
      [(ctxt, _)] =>
        FLOOKUP ctxt.msgParams.parsed ctxt.pc = SOME Gas ∧
        ¬is_call_budget_gas 16 ctxt.msgParams.parsed (ctxt.pc + 1) 0
    | _ => F
End

(* Read the value actually pushed by Verifereum's GAS step. The bound only
 * limits this diagnostic replay; exhaustion cannot establish agreement. *)
Definition trace_top_gas_def:
  (trace_top_gas 0 s = NONE) ∧
  (trace_top_gas (SUC fuel) s =
    let (result, next) = step s in
    case result of
      INR e => if vfm_abort e then NONE else SOME []
    | INL () =>
        if observes_gas s then
          (case next.contexts of
             [(ctxt, _)] =>
               (case ctxt.stack of
                  w :: _ => OPTION_MAP (CONS (w2n w)) (trace_top_gas fuel next)
                | [] => NONE)
           | _ => NONE)
        else trace_top_gas fuel next)
End

Definition bytecode_gas_observations_def:
  bytecode_gas_observations (accounts, tx, refs : (num # num list) list) =
    case run_create (Collect empty_domain) F differential_chain_id []
           differential_block accounts tx of
      SOME (INL _) => SOME []
    | SOME (INR (_, s, precomp)) =>
        (case precomp of
           SOME _ => SOME []
         | NONE => trace_top_gas (SUC tx.gasLimit) s)
    | NONE => NONE
End

val () = cv_auto_trans is_call_budget_gas_def;
val () = cv_auto_trans observes_gas_def;
val () = cv_auto_trans trace_top_gas_def;
val () = cv_auto_trans bytecode_gas_observations_def;
val () = cv_auto_trans is_diagnostic_def;
val () = cv_auto_trans returned_def;
val () = cv_auto_trans patch_word_def;
val () = cv_auto_trans (INST_TYPE [beta |-> “:num”] patch_immutables_def);
val () = cv_auto_trans code_immutable_words_def;
val () = cv_auto_trans seed_storage_def;
val () = cv_auto_trans contract_accounts_def;
val () = cv_auto_trans differential_accounts_def;
val () = cv_auto_trans storage_values_def;
val () = cv_auto_trans project_observation_def;
val () = cv_auto_trans (INST_TYPE [alpha |-> “:num”] expected_storage_def);
val seed_libraries_pre_def = cv_auto_trans_pre_rec
  "seed_libraries_pre" seed_libraries_def (
  WF_REL_TAC ‘measure (cv_size o FST)’ >> cv_termination_tac
);

Theorem seed_libraries_pre[cv_pre,local]:
  ∀libraries accounts. seed_libraries_pre libraries accounts
Proof
  Induct_on ‘libraries’ >- simp[Once seed_libraries_pre_def] >>
  Cases_on ‘h’ >> simp[Once seed_libraries_pre_def]
QED

val () = cv_auto_trans case_accounts_def;
val () = cv_auto_trans expected_logs_def;
val () = cv_auto_trans differential_tx_def;
val () = cv_auto_trans case_address_def;
val () = cv_auto_trans case_tx_def;
val () = cv_auto_trans bytecode_execution_def;
