Theory solidityCreateCallTest
Ancestors
  externalCall solidityEVMCreateTest
Libs
  cv_transLib wordsLib

(* Finite observations distinguish soft failure from collision/revert. *)
Definition create_adapter_summary_def:
  create_adapter_summary salt code value accounts =
    let addr = case salt of NONE => address_for_create 0x1001w
                                     (lookup_account 0x1001w accounts).nonce
                         | SOME s => address_for_create2 0x1001w s code in
    case run_create_call 0x1001w salt code value 200000 accounts
           empty_transient_storage fixture_tx_params of
      NONE => NONE
    | SOME r => SOME
        (r.create_address = SOME addr, r.create_return,
         (lookup_account 0x1001w r.create_accounts).nonce,
         (lookup_account 0x1001w r.create_accounts).balance,
         (lookup_account addr r.create_accounts).nonce,
         (lookup_account addr r.create_accounts).balance,
         (lookup_account addr r.create_accounts).code,
         lookup_storage 0w (lookup_account addr r.create_accounts).storage,
         lookup_storage 1w (lookup_account addr r.create_accounts).storage,
         r.create_logs)
End

Definition create_adapter_accounts_def:
  create_adapter_accounts =
    update_account 0x1001w (empty_account_state with balance := 1000)
      empty_accounts
End

Definition create_adapter_code_def:
  create_adapter_code : byte list =
    [0x60w; 42w; 0x60w; 0w; 0x55w;
     0x60w; 0w; 0x60w; 0w; 0x53w;
     0x60w; 1w; 0x60w; 0w; 0xf3w]
End

val () = cv_auto_trans create_adapter_summary_def;
val () = cv_auto_trans create_adapter_accounts_def;
val () = cv_auto_trans create_adapter_code_def;

Theorem creation_adapter_installs_code_and_transfers_value:
  create_adapter_summary NONE create_adapter_code 7 create_adapter_accounts =
    SOME (T, [], 1, 993, 1, 7, [0w], 42w, 0w, [])
Proof
  CONV_TAC cv_eval
QED

Theorem creation_adapter_salt_address:
  create_adapter_summary (SOME 42w) create_adapter_code 7 create_adapter_accounts =
    SOME (T, [], 1, 993, 1, 7, [0w], 42w, 0w, [])
Proof
  CONV_TAC cv_eval
QED

Theorem creation_adapter_insufficient_balance_keeps_nonce:
  create_adapter_summary NONE [] 1001 create_adapter_accounts =
    SOME (F, [], 0, 1000, 0, 0, [], 0w, 0w, [])
Proof
  CONV_TAC cv_eval
QED

Theorem creation_adapter_collision_bumps_nonce:
  create_adapter_summary NONE [] 7
    (update_account (address_for_create 0x1001w 0)
      (empty_account_state with nonce := 1) create_adapter_accounts) =
    SOME (F, [], 1, 1000, 1, 0, [], 0w, 0w, [])
Proof
  CONV_TAC cv_eval
QED

Theorem creation_adapter_revert_restores_world_and_keeps_data:
  create_adapter_summary NONE
    [0x60w; 42w; 0x60w; 0w; 0x55w;
     0x60w; 0w; 0x60w; 0w; 0xa0w;
     0x60w; 0xabw; 0x60w; 0w; 0x53w;
     0x60w; 1w; 0x60w; 0w; 0xfdw]
    7 create_adapter_accounts =
    SOME (F, [0xabw], 1, 1000, 0, 0, [], 0w, 0w, [])
Proof
  CONV_TAC cv_eval
QED

Theorem creation_adapter_exception_clears_data:
  create_adapter_summary NONE [0xfew] 7 create_adapter_accounts =
    SOME (F, [], 1, 1000, 0, 0, [], 0w, 0w, [])
Proof
  CONV_TAC cv_eval
QED

Theorem creation_adapter_rejects_ef_runtime:
  create_adapter_summary NONE
    [0x60w; 0xefw; 0x60w; 0w; 0x53w;
     0x60w; 1w; 0x60w; 0w; 0xf3w] 7 create_adapter_accounts =
    SOME (F, [], 1, 1000, 0, 0, [], 0w, 0w, [])
Proof
  CONV_TAC cv_eval
QED

Theorem creation_adapter_clears_target_storage_preserving_balance:
  create_adapter_summary NONE create_adapter_code 7
    (update_account (address_for_create 0x1001w 0)
      (empty_account_state with <| balance := 23;
        storage := update_storage 1w 99w empty_storage |>)
      create_adapter_accounts) =
    SOME (T, [], 1, 993, 1, 30, [0w], 42w, 0w, [])
Proof
  CONV_TAC cv_eval
QED

Theorem creation_adapter_nonce_limit_keeps_nonce:
  create_adapter_summary NONE [] 0
    (update_account 0x1001w
      (empty_account_state with <| balance := 1000; nonce := 2 ** 64 - 1 |>)
      empty_accounts) =
    SOME (F, [], 2 ** 64 - 1, 1000, 0, 0, [], 0w, 0w, [])
Proof
  CONV_TAC cv_eval
QED

Theorem creation_adapter_overflow_outside_model:
  run_create_call 0x1001w NONE [] 7 200000
    (update_account (address_for_create 0x1001w 0)
      (empty_account_state with balance := 2 ** 256 - 1) create_adapter_accounts)
    empty_transient_storage fixture_tx_params = NONE
Proof
  CONV_TAC cv_eval
QED
