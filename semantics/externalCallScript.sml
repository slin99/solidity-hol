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
 * The callee's frame is fresh rather than nested in the caller's: its
 * original accounts are the world after the value transfer, its access set
 * holds only the caller and callee, and its depth is one. A call that leaves
 * accounts pending deletion is outside the model (NONE), since a fresh frame
 * cannot hand them back to the caller's transaction.
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
    call_logs : event list
  |>
End

(* The callee's message, as the caller's CALL would make it: a stipend comes
 * with value, the value has moved before the callee's code runs, and a
 * delegated account runs its delegate's code. *)
Definition external_call_state_def:
  external_call_state caller callee calldata value static gas accounts
                      transient tx_params =
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
       rollback := rollback; originalAccounts := accounts';
       msdomain := Collect empty_domain |>
End

(* The finished frame's outcome; NONE if it did not finish in one frame,
 * stopped outside the model or left accounts pending deletion. *)
Definition external_call_result_def:
  external_call_result accounts transient
    (result : unit + exception option, final : execution_state) =
    case final.contexts of
      [(ctxt, _)] =>
        (case result of
           INR NONE =>
             if final.rollback.toDelete ≠ [] then NONE else
             SOME <| call_success := T; call_return := ctxt.returnData;
                     call_accounts := final.rollback.accounts;
                     call_transient := final.rollback.tStorage;
                     call_logs := ctxt.logs |>
         | INR (SOME Reverted) =>
             SOME <| call_success := F; call_return := ctxt.returnData;
                     call_accounts := accounts; call_transient := transient;
                     call_logs := [] |>
         | INR e =>
             if vfm_abort e then NONE
             else SOME <| call_success := F; call_return := [];
                          call_accounts := accounts;
                          call_transient := transient; call_logs := [] |>
         | INL _ => NONE)
    | _ => NONE
End

(* NONE where the call leaves the model: a recipient balance overflow, a run
 * outside the domain, or one external_call_result rejects. *)
Definition run_external_call_def:
  run_external_call caller callee calldata value static gas accounts transient
                    tx_params =
    if (lookup_account caller accounts).balance < value then
      SOME <| call_success := F; call_return := []; call_accounts := accounts;
              call_transient := transient; call_logs := [] |>
    else if caller ≠ callee ∧
            2 ** 256 ≤ (lookup_account callee accounts).balance + value then
      NONE
    else
      let s0 = external_call_state caller callee calldata value static gas
                 accounts transient tx_params in
      if fIN callee precompile_addresses then
        external_call_result accounts transient (dispatch_precompiles callee s0)
      else
        case run_call s0 of
          SOME outcome => external_call_result accounts transient outcome
        | NONE => NONE
End

(* The callee's message for DELEGATECALL, as Verifereum's proceed_call makes
 * it: the target's code (or its delegate's) runs as the caller, at its
 * address on its storage and balance, with the sender and value of the
 * caller's own frame. No value moves, so no stipend comes with it. *)
Definition delegate_call_state_def:
  delegate_call_state self sender value target calldata static gas accounts
                      transient tx_params =
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
       rollback := rollback; originalAccounts := accounts;
       msdomain := Collect empty_domain |>
End

(* A delegate call from the frame of self (called by sender with value) to
 * the code at target: a precompile target runs as the precompile. *)
Definition run_delegate_call_def:
  run_delegate_call self sender value target calldata static gas accounts
                    transient tx_params =
    let s0 = delegate_call_state self sender value target calldata static gas
               accounts transient tx_params in
    if fIN target precompile_addresses then
      external_call_result accounts transient (dispatch_precompiles target s0)
    else
      case run_call s0 of
        SOME outcome => external_call_result accounts transient outcome
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
    create_logs : event list
  |>
End

(* The saved world retains the creator's nonce bump, before clearing the
 * target or moving value. Transaction-original storage at the target is zero. *)
Definition create_call_state_def:
  create_call_state caller addr initcode value gas accounts transient tx_params =
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
       originalAccounts := update_account addr empty_account_state accounts;
       msdomain := Collect empty_domain |>
End

(* run_call's handle_create has already checked and installed runtime code.
 * Successful CREATE clears returndata; only constructor REVERT exposes bytes. *)
Definition create_call_result_def:
  create_call_result addr accounts transient
    (result : unit + exception option, final : execution_state) =
    case final.contexts of
      [(ctxt, _)] =>
        (case result of
           INR NONE =>
             if final.rollback.toDelete ≠ [] then NONE else
             SOME <| create_address := SOME addr; create_return := [];
                     create_accounts := final.rollback.accounts;
                     create_transient := final.rollback.tStorage;
                     create_logs := ctxt.logs |>
         | INR e =>
             if vfm_abort e then NONE else
             SOME <| create_address := NONE;
                     create_return := if e = SOME Reverted then ctxt.returnData else [];
                     create_accounts := accounts; create_transient := transient;
                     create_logs := [] |>
         | INL _ => NONE)
    | _ => NONE
End

(* CREATE/CREATE2's prelude, followed by one concrete initcode frame. Size
 * and recipient overflow leave the model, as at the external-call boundary. *)
Definition run_create_call_def:
  run_create_call caller salt initcode value gas accounts transient tx_params =
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
                 create_logs := [] |> else
    let accounts1 = increment_nonce caller accounts in
    if account_already_created (lookup_account addr accounts)
    then SOME <| create_address := NONE; create_return := [];
                 create_accounts := accounts1; create_transient := transient;
                 create_logs := [] |> else
    case run_call (create_call_state caller addr initcode value gas accounts1
                    transient tx_params) of
      SOME outcome => create_call_result addr accounts1 transient outcome
    | NONE => NONE
End

val () = cv_auto_trans create_call_state_def;
val () = cv_auto_trans create_call_result_def;
val () = cv_auto_trans run_create_call_def;
val () = cv_auto_trans delegate_call_state_def;
val () = cv_auto_trans run_delegate_call_def;
