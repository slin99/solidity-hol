(* The external entry of a contract: one call frame of the contract's code,
 * from its calldata to its return or revert data, following the dispatcher
 * of the pinned profile (solc-0.8.37-via-ir-osaka):
 *  - calldata of at least 4 bytes whose selector names an external function
 *    calls it: a nonpayable function given value reverts, then the arguments
 *    are ABI-decoded, reverting on data the decoder rejects;
 *  - otherwise empty calldata calls receive, if any, and any other calldata
 *    the fallback, which reverts on value unless payable;
 *  - with neither, the call reverts.
 * Compiler-generated reverts carry no data. A return is the ABI encoding of
 * the return values, and a panic the revert data Panic(uint256).
 *
 * The frame starts from the world at frame entry: value transfer, nonces,
 * gas and the transaction around the call are Verifereum's. A revert or panic
 * restores that world, including its logs.
 *)
Theory solidityEntry
Ancestors
  solidityEvaluator
Libs
  cv_transLib

Datatype:
  contract_result
  = ContractReturned (byte list) source_world
  | ContractReverted (byte list) source_world
  | ContractInvalid string
  | ContractOutOfFuel
End

Datatype:
  dispatch_result
  = DispatchCall core_procedure (runtime_value list)
  | DispatchRevert
  | DispatchInvalid string
End

Definition lookup_external_def:
  (lookup_external sel [] = NONE) ∧
  (lookup_external sel (e :: es) =
    if e.selector = sel then SOME e else lookup_external sel es)
End

Definition dispatch_procedure_def:
  dispatch_procedure env f args =
    case lookup_procedure env f of
      SOME p => DispatchCall p args
    | NONE => DispatchInvalid "unknown procedure"
End

Definition dispatch_def:
  dispatch env (prog : core_program) (fr : source_frame) =
    let data = fr.call_data in
    case (if 4 ≤ LENGTH data
          then lookup_external (TAKE 4 data) prog.external_functions
          else NONE) of
      SOME e =>
        if ¬e.payable ∧ fr.call_value ≠ 0 then DispatchRevert else
        (case lookup_procedure env e.external_procedure of
           NONE => DispatchInvalid "unknown procedure"
         | SOME p =>
             case decode_arguments (MAP SND p.parameters) (DROP 4 data) of
               SOME args => DispatchCall p args
             | NONE => DispatchRevert)
    | NONE =>
        case (data, prog.receive_procedure, prog.fallback_procedure) of
          ([], SOME f, _) => dispatch_procedure env f []
        | (_, _, SOME (f, payable)) =>
            if ¬payable ∧ fr.call_value ≠ 0 then DispatchRevert
            else dispatch_procedure env f []
        | _ => DispatchRevert
End

(* One frame running procedure p on its arguments. *)
Definition run_entry_def:
  run_entry fuel env p args (fr : source_frame) (w : source_world) =
    let st = <| world := w; frame := fr; scopes := []; heap := FEMPTY;
                next_heap_id := 0; targets := FEMPTY |> in
    let r = invoke_source fuel env p.procedure_id args st [] in
    case finish_source_frame w r.state.world r.completion of
      FrameSuccess vs w' =>
        (case encoded_values (MAP SND p.return_bindings) vs of
           SOME data => ContractReturned data w'
         | NONE => ContractInvalid "unencodable return values")
    | FrameRevert data w' => ContractReverted data w'
    | FramePanic code w' => ContractReverted (panic_data code) w'
    | FrameInvalid reason => ContractInvalid reason
    | FrameResourceLimit => ContractOutOfFuel
End

Definition call_contract_def:
  call_contract fuel (prog : core_program) (fr : source_frame)
                (w : source_world) =
    let env = core_program_environment prog in
    case dispatch env prog fr of
      DispatchRevert => ContractReverted [] w
    | DispatchInvalid reason => ContractInvalid reason
    | DispatchCall p args => run_entry fuel env p args fr w
End

(* The creation transaction's frame of a contract, from a world in which its
 * account exists with no storage and holds the value sent. The constructor's
 * arguments are the frame's calldata, without selector; a creation sent
 * value reverts unless the constructor is payable, and arguments the decoder
 * rejects revert. A successful creation returns no data: the deployed code
 * is the compiler's.
 *)
Definition deploy_contract_def:
  deploy_contract fuel (prog : core_program) (fr : source_frame)
                  (w : source_world) =
    let env = core_program_environment prog in
    case prog.creation_procedure of
      NONE => ContractInvalid "no creation procedure"
    | SOME (f, payable) =>
        if ¬payable ∧ fr.call_value ≠ 0 then ContractReverted [] w else
        case lookup_procedure env f of
          NONE => ContractInvalid "unknown procedure"
        | SOME p =>
            case decode_arguments (MAP SND p.parameters) fr.call_data of
              NONE => ContractReverted [] w
            | SOME args => run_entry fuel env p args fr w
End

Theorem call_contract_revert_restores_world:
  call_contract fuel prog fr w = ContractReverted data w' ⇒ w' = w
Proof
  rw[call_contract_def, run_entry_def,
     solidityStateTheory.finish_source_frame_def, AllCaseEqs()] >> simp[]
QED

val () = cv_auto_trans lookup_external_def;
val () = cv_auto_trans dispatch_procedure_def;
val () = cv_auto_trans dispatch_def;
val () = cv_auto_trans run_entry_def;
val () = cv_auto_trans call_contract_def;
val () = cv_auto_trans deploy_contract_def;
