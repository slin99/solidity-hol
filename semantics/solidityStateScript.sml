(* Source-facing state blueprint. EVM correspondence beyond this observable
 * projection is deliberately not claimed; see docs/implementation-blueprint.md.
 *)
Theory solidityState
Ancestors
  solidityCore finite_map

Datatype:
  source_world = <|
    accounts : evm_accounts;
    transient : transient_storage;
    logs : event list
  |>
End

(* Any single-typed binding may be captured and written (the checker's
 * convention), so a binding records no assignability.
 *)
Datatype:
  source_binding = <|
    binding_type : core_value_type;
    binding_value : runtime_value
  |>
End

(* Addressable heap objects: references carry identity and a captured offset.
 * Byte sequences use the length and byte cells; other heap values are deferred.
 *)
Datatype:
  heap_object = <|
    object_type : sol_type;
    object_length : num;
    object_cells : num |-> runtime_value
  |>
End

Datatype:
  source_frame = <|
    self_address : address;
    code_address : address;
    sender_address : address;
    call_value : num;
    call_data : byte list;
    static_context : bool;
    tx_params : transaction_parameters
  |>
End

(* Scopes, heap and targets are num-keyed finite maps (scopes and targets keyed
 * by the ast_id's number), which cv encodes as sptrees. Scopes are innermost
 * first. The immutables are the values of the contract's immutables, keyed by
 * their declarations: those the deployed code holds, or, during creation, those
 * the constructor has assigned so far; one not there is zero.
 *)
Datatype:
  source_state = <|
    world : source_world;
    frame : source_frame;
    immutables : num |-> scalar;
    scopes : (num |-> source_binding) list;
    heap : num |-> heap_object;
    next_heap_id : num;
    memory_allocated : num;
    targets : num |-> captured_target
  |>
End

(* Execution evidence is separate from persistent world and rollback state.
 * These tags reserve query-specific observations; call/create meanings are NOT
 * settled. An authoritative gas projection must follow Vyper-HOL issue #98.
 *)
Datatype:
  gas_observation
  = GasLeftObservation num
  | CallGasObservation num
  | CreateGasObservation num
End

Datatype:
  source_result = <|
    completion : source_completion;
    state : source_state;
    unused_gas_evidence : gas_observation list
  |>
End

(* Requested gas is a source operand, not an oracle replacement. Available gas
 * and concrete CALL overhead remain adapter/simulation obligations.
 *)
Datatype:
  bytecode_request
  = CallRequest external_kind address (byte list) num (num option)
  | CreateRequest (byte list) num (num option) (bytes32 option)
End

Definition project_evm_world_def:
  project_evm_world (es : execution_state) =
    case es.contexts of
      [] => NONE
    | (ctxt, checkpoint)::rest => SOME <|
        accounts := es.rollback.accounts;
        transient := es.rollback.tStorage;
        logs := ctxt.logs
      |>
End

(* Raw results retain provisional state. Commit policy does not treat invalid
 * input/fuel exhaustion as either success or a Solidity revert.
 *)
Datatype:
  frame_observation
  = FrameSuccess (runtime_value list) source_world
  | FrameRevert (byte list) source_world
  | FrameHalt (byte list) source_world
  | FramePanic num source_world
  | FrameInvalid string
  | FrameResourceLimit
End

Definition finish_source_frame_def:
  finish_source_frame initial final completion =
    case completion of
      NormalCompletion => FrameSuccess [] final
    | ReturnCompletion values => FrameSuccess values final
    | RevertCompletion data => FrameRevert data initial
    | HaltCompletion data => FrameHalt data final
    | PanicCompletion code => FramePanic code initial
    | FuelExhausted => FrameResourceLimit
    | InvalidCompletion reason => FrameInvalid reason
    | BreakCompletion => FrameInvalid "break escaped frame"
    | ContinueCompletion => FrameInvalid "continue escaped frame"
End

Theorem source_revert_restores_world:
  finish_source_frame initial final (RevertCompletion data) =
    FrameRevert data initial
Proof
  simp[finish_source_frame_def]
QED

Theorem source_exhaustion_does_not_commit:
  finish_source_frame initial final FuelExhausted = FrameResourceLimit
Proof
  simp[finish_source_frame_def]
QED
