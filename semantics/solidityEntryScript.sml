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

(* A creation that succeeds yields the values of the contract's immutables:
 * the deployed code is the compiler's, with those values in it. *)
Datatype:
  contract_result
  = ContractReturned (byte list) source_world
  | ContractCreated (num |-> scalar) source_world
  | ContractReverted (byte list) source_world
  | ContractInvalid string
  | ContractOutOfFuel
End

Datatype:
  dispatch_result
  = DispatchCall core_procedure (runtime_value list)
  | DispatchRevert
  | DispatchPanic num
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
             case decode_arguments env (MAP SND p.parameters) (DROP 4 data) 4 128 of
               INL args => DispatchCall p args
             | INR (PanicCompletion n) => DispatchPanic n
             | INR _ => DispatchRevert)
    | NONE =>
        case (data, prog.receive_procedure, prog.fallback_procedure) of
          ([], SOME f, _) => dispatch_procedure env f []
        | (_, _, SOME (f, payable)) =>
            if ¬payable ∧ fr.call_value ≠ 0 then DispatchRevert
            else dispatch_procedure env f []
        | _ => DispatchRevert
End

(* One frame running procedure p on its arguments, with the values imm of
 * the immutables. An inline assembly halt returns its bytes as the frame's
 * data; in a creation frame those bytes would be the deployed code, which the
 * source does not model, so a halt there fails closed. A creation frame
 * yields the immutables' final values.
 *)
Definition run_entry_def:
  run_entry fuel env p args (fr : source_frame) (w : source_world) imm reserved
            creating =
    let st = <| world := w; frame := fr; immutables := imm; scopes := [];
                heap := FEMPTY; next_heap_id := 0; memory_allocated := reserved;
                targets := FEMPTY |> in
    let r = case materialize_arguments (MAP SND p.parameters) args st of
      SOME (values, st1) => invoke_source fuel env p.procedure_id values st1 []
    | NONE => abrupt_result (InvalidCompletion "bad entry arguments") st [] in
    case finish_source_frame w r.state.world r.completion of
      FrameSuccess vs w' =>
        (case encoded_runtime_values env r.state (MAP SND p.return_bindings) vs of
           INL data =>
             if creating then ContractCreated r.state.immutables w'
             else ContractReturned data w'
         | INR (PanicCompletion code) => ContractReverted (panic_data code) w
         | INR (RevertCompletion data) => ContractReverted data w
         | INR _ => ContractInvalid "unencodable return values")
    | FrameRevert data w' => ContractReverted data w'
    | FrameHalt data w' =>
        if creating then ContractInvalid "assembly halt in a creation frame"
        else ContractReturned data w'
    | FramePanic code w' => ContractReverted (panic_data code) w'
    | FrameInvalid reason => ContractInvalid reason
    | FrameResourceLimit => ContractOutOfFuel
End

(* A call of the deployed contract, whose immutables have the values imm. *)
Definition call_contract_def:
  call_contract fuel (prog : core_program) imm (fr : source_frame)
                (w : source_world) =
    let env = core_program_environment prog in
    case dispatch env prog fr of
      DispatchRevert => ContractReverted [] w
    | DispatchPanic n => ContractReverted (panic_data n) w
    | DispatchInvalid reason => ContractInvalid reason
    | DispatchCall p args => run_entry fuel env p args fr w imm 0 F
End

(* The creation transaction's frame of a contract, from a world in which its
 * account exists with no storage and holds the value sent. The constructor's
 * encoded arguments are supplied in the input frame and decoded before its
 * call_data is cleared: creation reads arguments from initcode, while msg.data
 * is empty. A creation sent value reverts unless the constructor is payable,
 * and arguments the decoder rejects revert. The immutables start at zero, and
 * a successful creation yields their values. Memory above the scratch space
 * holds a word for each immutable, then the copied arguments, so both the
 * decoder and the constructor allocate above them.
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
            let reserved = 32 * LENGTH prog.immutables +
                           32 * ((LENGTH fr.call_data + 31) DIV 32) in
            case decode_arguments env (MAP SND p.parameters) fr.call_data 0
              (128 + reserved) of
              INR (PanicCompletion n) => ContractReverted (panic_data n) w
            | INR _ => ContractReverted [] w
            | INL args => run_entry fuel env p args (fr with call_data := []) w
                FEMPTY reserved T
End

Theorem call_contract_revert_restores_world:
  call_contract fuel prog imm fr w = ContractReverted data w' ⇒ w' = w
Proof
  rw[call_contract_def, run_entry_def,
     solidityStateTheory.finish_source_frame_def, AllCaseEqs()] >> simp[]
QED

(* An external call of an unsupported function, one the program does not
 * model, is refused: the call is invalid, never a return or a revert. *)
Theorem call_contract_unsupported:
  wf_core_program (core_program_environment prog) prog ∧
  4 ≤ LENGTH fr.call_data ∧
  lookup_external (TAKE 4 fr.call_data) prog.external_functions = SOME e ∧
  MEM e.external_procedure prog.unsupported_procedures ∧
  (e.payable ∨ fr.call_value = 0) ⇒
  call_contract fuel prog imm fr w = ContractInvalid "unknown procedure"
Proof
  rw[solidityCoreWfTheory.wf_core_program_def, listTheory.EVERY_MEM] >> first_x_assum drule >>
  rw[call_contract_def, dispatch_def]
QED

val () = cv_auto_trans lookup_external_def;
val () = cv_auto_trans dispatch_procedure_def;
val () = cv_auto_trans dispatch_def;
val () = cv_auto_trans run_entry_def;
val () = cv_auto_trans call_contract_def;
val () = cv_auto_trans deploy_contract_def;
