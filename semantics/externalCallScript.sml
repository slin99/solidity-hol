(* An external call run on Verifereum: one message call from a caller account
 * to a callee, on a fresh one-frame execution state, returning the callee's
 * outcome and the world it leaves. The caller's own execution is the
 * source's (or the Yul frame's): only the callee runs as EVM code, so a call
 * back into the caller runs the caller's bytecode.
 *
 * As the CALL and STATICCALL opcodes do, value moves before the callee runs,
 * a value the caller cannot pay fails the call without running it, and a
 * failed call (revert, exceptional halt or that) leaves the accounts and
 * transient storage as they were, with no logs. Gas is a fixed budget given
 * by the caller: the source does not track gas, so a callee that runs out of
 * it fails here where the bytecode might not.
 *
 * The callee's frame is fresh rather than nested in the caller's: its access
 * set holds only the caller and callee, and its depth is one. Its original
 * accounts are the transaction's, which the caller passes in (original): the
 * world at the transaction's start, with each account created since marked
 * empty, as Verifereum's CREATE marks it. That is what SELFDESTRUCT reads to
 * tell an account created in this transaction (EIP-6780), so the caller must
 * thread it from call to call. A successful call hands back the original
 * accounts it leaves and the accounts it left pending deletion (to_delete),
 * which the caller keeps until the transaction settles; a failed call leaves
 * both as they were.
 *
 * A delegate call runs the target's code in the caller's own account, with
 * the caller frame's sender and value, and moves no value.
 *
 * The construction follows vyper-hol's concrete external calls.
 *)
Theory externalCall
Ancestors
  vfmCompute
Libs
  cv_transLib

Datatype:
  call_outcome = <|
    call_success : bool;
    call_return : byte list;
    call_accounts : evm_accounts;
    call_transient : transient_storage;
    call_logs : event list;
    call_original : evm_accounts;
    call_to_delete : address list
  |>
End

(* The callee's message, as the caller's CALL would make it: a stipend comes
 * with value, the value has moved before the callee's code runs, and a
 * delegated account runs its delegate's code. *)
Definition external_call_state_def:
  external_call_state caller callee calldata value static gas accounts
                      original transient tx_params =
    let gas_limit = gas + (if value = 0 then 0 else call_stipend) in
    let tx = <| from := caller; to := SOME callee; data := calldata;
                nonce := 0; value := value; gasLimit := gas_limit;
                gasPrice := 0; accessList := []; blobVersionedHashes := [];
                maxFeePerBlobGas := NONE; maxFeePerGas := NONE;
                authorizationList := [] |> in
    let code = case get_delegate (lookup_account callee accounts).code of
                 NONE => (lookup_account callee accounts).code
               | SOME d => (lookup_account d accounts).code in
    let ctxt = initial_context callee code static empty_return_destination tx in
    let accounts' = transfer_value caller callee value accounts in
    let rollback = <| accounts := accounts'; tStorage := transient;
                      accesses := <| addresses := fINSERT caller
                                                    (fINSERT callee fEMPTY);
                                     storageKeys := fEMPTY |>;
                      toDelete := [] |> in
    <| contexts := [(ctxt, rollback)]; txParams := tx_params;
       rollback := rollback; originalAccounts := original;
       msdomain := Collect empty_domain |>
End

(* The finished frame's outcome; NONE if it did not finish in one frame or
 * stopped outside the model. *)
Definition external_call_result_def:
  external_call_result accounts original transient
    (result : unit + exception option, final : execution_state) =
    case final.contexts of
      [(ctxt, _)] =>
        (case result of
           INR NONE =>
             SOME <| call_success := T; call_return := ctxt.returnData;
                     call_accounts := final.rollback.accounts;
                     call_transient := final.rollback.tStorage;
                     call_logs := ctxt.logs;
                     call_original := final.originalAccounts;
                     call_to_delete := final.rollback.toDelete |>
         | INR (SOME Reverted) =>
             SOME <| call_success := F; call_return := ctxt.returnData;
                     call_accounts := accounts; call_transient := transient;
                     call_logs := []; call_original := original;
                     call_to_delete := [] |>
         | INR e =>
             if vfm_abort e then NONE
             else SOME <| call_success := F; call_return := [];
                          call_accounts := accounts;
                          call_transient := transient; call_logs := [];
                          call_original := original; call_to_delete := [] |>
         | INL _ => NONE)
    | _ => NONE
End

(* NONE where the call leaves the model: a recipient balance overflow, a run
 * outside the domain, or one external_call_result rejects. *)
Definition run_external_call_def:
  run_external_call caller callee calldata value static gas accounts original
                    transient tx_params =
    if (lookup_account caller accounts).balance < value then
      SOME <| call_success := F; call_return := []; call_accounts := accounts;
              call_transient := transient; call_logs := [];
              call_original := original; call_to_delete := [] |>
    else if caller ≠ callee ∧
            2 ** 256 ≤ (lookup_account callee accounts).balance + value then
      NONE
    else
      let s0 = external_call_state caller callee calldata value static gas
                 accounts original transient tx_params in
      if fIN callee precompile_addresses then
        external_call_result accounts original transient
          (dispatch_precompiles callee s0)
      else
        case run_call s0 of
          SOME outcome => external_call_result accounts original transient outcome
        | NONE => NONE
End

(* The callee's message for DELEGATECALL, as Verifereum's proceed_call makes
 * it: the target's code (or its delegate's) runs as the caller, at its
 * address on its storage and balance, with the sender and value of the
 * caller's own frame. No value moves, so no stipend comes with it. *)
Definition delegate_call_state_def:
  delegate_call_state self sender value target calldata static gas accounts
                      original transient tx_params =
    let tx = <| from := sender; to := SOME self; data := calldata;
                nonce := 0; value := value; gasLimit := gas;
                gasPrice := 0; accessList := []; blobVersionedHashes := [];
                maxFeePerBlobGas := NONE; maxFeePerGas := NONE;
                authorizationList := [] |> in
    let code = case get_delegate (lookup_account target accounts).code of
                 NONE => (lookup_account target accounts).code
               | SOME d => (lookup_account d accounts).code in
    let ctxt = initial_context self code static empty_return_destination tx in
    let rollback = <| accounts := accounts; tStorage := transient;
                      accesses := <| addresses := fINSERT self
                                                    (fINSERT target fEMPTY);
                                     storageKeys := fEMPTY |>;
                      toDelete := [] |> in
    <| contexts := [(ctxt, rollback)]; txParams := tx_params;
       rollback := rollback; originalAccounts := original;
       msdomain := Collect empty_domain |>
End

(* A delegate call from the frame of self (called by sender with value) to
 * the code at target: a precompile target runs as the precompile. *)
Definition run_delegate_call_def:
  run_delegate_call self sender value target calldata static gas accounts
                    original transient tx_params =
    let s0 = delegate_call_state self sender value target calldata static gas
               accounts original transient tx_params in
    if fIN target precompile_addresses then
      external_call_result accounts original transient
        (dispatch_precompiles target s0)
    else
      case run_call s0 of
        SOME outcome => external_call_result accounts original transient outcome
      | NONE => NONE
End

val () = cv_auto_trans external_call_state_def;
val () = cv_auto_trans external_call_result_def;
val () = cv_auto_trans run_external_call_def;

Datatype:
  create_outcome = <|
    create_address : address option;
    create_return : byte list;
    create_accounts : evm_accounts;
    create_transient : transient_storage;
    create_logs : event list;
    create_original : evm_accounts;
    create_to_delete : address list
  |>
End

(* The saved world retains the creator's nonce bump, before clearing the
 * target or moving value. The target is empty in the transaction's original
 * accounts from here on, as Verifereum's CREATE marks it: its original
 * storage is zero, and a SELFDESTRUCT of it later in the transaction deletes
 * it. *)
Definition create_call_state_def:
  create_call_state caller addr initcode value gas accounts original transient
                    tx_params =
    let tx = <| from := caller; to := SOME addr; data := []; nonce := 0;
                value := value; gasLimit := gas; gasPrice := 0; accessList := [];
                blobVersionedHashes := []; maxFeePerBlobGas := NONE;
                maxFeePerGas := NONE; authorizationList := [] |> in
    let ctxt = initial_context addr initcode F (Code addr) tx in
    let saved = <| accounts := accounts; tStorage := transient;
                   accesses := <| addresses := fINSERT caller (fINSERT addr fEMPTY);
                                  storageKeys := fEMPTY |>; toDelete := [] |> in
    let post = (transfer_value caller addr value o increment_nonce addr o
                clear_storage addr) accounts in
    <| contexts := [(ctxt, saved)]; txParams := tx_params;
       rollback := saved with accounts := post;
       originalAccounts := update_account addr empty_account_state original;
       msdomain := Collect empty_domain |>
End

(* run_call's handle_create has already checked and installed runtime code.
 * Successful CREATE clears returndata; only constructor REVERT exposes bytes. *)
Definition create_call_result_def:
  create_call_result addr accounts original transient
    (result : unit + exception option, final : execution_state) =
    case final.contexts of
      [(ctxt, _)] =>
        (case result of
           INR NONE =>
             SOME <| create_address := SOME addr; create_return := [];
                     create_accounts := final.rollback.accounts;
                     create_transient := final.rollback.tStorage;
                     create_logs := ctxt.logs;
                     create_original := final.originalAccounts;
                     create_to_delete := final.rollback.toDelete |>
         | INR e =>
             if vfm_abort e then NONE else
             SOME <| create_address := NONE;
                     create_return := if e = SOME Reverted then ctxt.returnData else [];
                     create_accounts := accounts; create_transient := transient;
                     create_logs := []; create_original := original;
                     create_to_delete := [] |>
         | INL _ => NONE)
    | _ => NONE
End

(* CREATE/CREATE2's prelude, followed by one concrete initcode frame. Size
 * and recipient overflow leave the model, as at the external-call boundary. *)
Definition run_create_call_def:
  run_create_call caller salt initcode value gas accounts original transient
                  tx_params =
    let nonce = (lookup_account caller accounts).nonce in
    let addr = case salt of
                 NONE => address_for_create caller nonce
               | SOME s => address_for_create2 caller s initcode in
    if LENGTH initcode > 2 * max_code_size ∨
       caller ≠ addr ∧ 2 ** 256 ≤ (lookup_account addr accounts).balance + value
    then NONE else
    if (lookup_account caller accounts).balance < value ∨ SUC nonce ≥ 2 ** 64
    then SOME <| create_address := NONE; create_return := [];
                 create_accounts := accounts; create_transient := transient;
                 create_logs := []; create_original := original;
                 create_to_delete := [] |> else
    let accounts1 = increment_nonce caller accounts in
    if account_already_created (lookup_account addr accounts)
    then SOME <| create_address := NONE; create_return := [];
                 create_accounts := accounts1; create_transient := transient;
                 create_logs := []; create_original := original;
                 create_to_delete := [] |> else
    case run_call (create_call_state caller addr initcode value gas accounts1
                    original transient tx_params) of
      SOME outcome => create_call_result addr accounts1 original transient outcome
    | NONE => NONE
End

val () = cv_auto_trans create_call_state_def;
val () = cv_auto_trans create_call_result_def;
val () = cv_auto_trans run_create_call_def;
val () = cv_auto_trans delegate_call_state_def;
val () = cv_auto_trans run_delegate_call_def;
