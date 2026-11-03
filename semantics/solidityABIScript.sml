(* The ABI at the contract boundary, for scalars and bytes/string values:
 * calldata arguments, return data, Panic(uint256) revert data and event logs, over
 * Verifereum's contractABI encoding.
 *)
Theory solidityABI
Ancestors
  contractABI
  (* for its cv encodings of runtime values and events, so that every
   * descendant sees one encoding *)
  solidityMemory
Libs
  cv_transLib wordsLib intLib

Definition abi_type_def:
  (abi_type (UintT n) = Uint n) ∧
  (abi_type (IntT n) = Int n) ∧
  (abi_type BoolT = Bool) ∧
  (abi_type (AddressT _) = Address) ∧
  (abi_type (FixedBytesT n) = Bytes (SOME n)) ∧
  (abi_type BytesT = Bytes NONE) ∧
  (abi_type StringT = String) ∧
  (abi_type (LocatedT _ ty) = abi_type ty) ∧
  (abi_type _ = Tuple [])
End

Definition abi_value_def:
  (abi_value (UintT _) (ScalarValue (IntegerValue i)) = SOME (NumV (Num i))) ∧
  (abi_value (IntT _) (ScalarValue (IntegerValue i)) = SOME (IntV i)) ∧
  (abi_value BoolT (ScalarValue (BoolValue b)) =
    SOME (NumV (if b then 1 else 0))) ∧
  (abi_value (AddressT _) (ScalarValue (AddressValue a)) =
    SOME (NumV (w2n a))) ∧
  (abi_value (FixedBytesT _) (ScalarValue (BytesValue bs)) = SOME (BytesV bs)) ∧
  (abi_value BytesT (ScalarValue (BytesValue bs)) = SOME (BytesV bs)) ∧
  (abi_value StringT (ScalarValue (BytesValue bs)) = SOME (BytesV bs)) ∧
  (abi_value (LocatedT _ ty) v = abi_value ty v) ∧
  (abi_value _ _ = NONE)
End

Definition abi_values_def:
  (abi_values [] [] = SOME []) ∧
  (abi_values (ty :: tys) (v :: vs) =
    case (abi_value ty v, abi_values tys vs) of
      (SOME a, SOME as) => SOME (a :: as)
    | _ => NONE) ∧
  (abi_values _ _ = NONE)
End

(* The encoding of values as a tuple of their types: return data. *)
Definition encoded_values_def:
  encoded_values tys vs =
    case abi_values tys vs of
      SOME avs => SOME (enc (Tuple (MAP abi_type tys)) (ListV avs))
    | NONE => NONE
End

(* Runtime references are read from the current frame and heap before encoding. *)
Definition runtime_abi_value_def:
  runtime_abi_value st ty v =
    case v of
      ReferenceValue r =>
        (case reference_bytes st r of
           SOME bs => abi_value ty (ScalarValue (BytesValue bs))
         | NONE => NONE)
    | _ => abi_value ty v
End

Definition runtime_abi_values_def:
  (runtime_abi_values st [] [] = SOME []) ∧
  (runtime_abi_values st (ty :: tys) (v :: vs) =
    case (runtime_abi_value st ty v, runtime_abi_values st tys vs) of
      (SOME a, SOME avs) => SOME (a :: avs)
    | _ => NONE) ∧
  (runtime_abi_values _ _ _ = NONE)
End

Definition encoded_runtime_values_def:
  encoded_runtime_values st tys vs =
    OPTION_MAP (λavs. enc (Tuple (MAP abi_type tys)) (ListV avs))
      (runtime_abi_values st tys vs)
End

(* Inverse of abi_value on values valid_enc accepts. *)
Definition abi_runtime_value_def:
  (abi_runtime_value (UintT _) (NumV n) = SOME (ScalarValue (IntegerValue (&n)))) ∧
  (abi_runtime_value (IntT _) (IntV i) = SOME (ScalarValue (IntegerValue i))) ∧
  (abi_runtime_value BoolT (NumV n) = SOME (ScalarValue (BoolValue (n = 1)))) ∧
  (abi_runtime_value (AddressT _) (NumV n) =
    SOME (ScalarValue (AddressValue (n2w n)))) ∧
  (abi_runtime_value (FixedBytesT _) (BytesV bs) =
    SOME (ScalarValue (BytesValue bs))) ∧
  (abi_runtime_value _ _ = NONE)
End

Definition abi_runtime_values_def:
  (abi_runtime_values [] [] = SOME []) ∧
  (abi_runtime_values (ty :: tys) (a :: as) =
    case (abi_runtime_value ty a, abi_runtime_values tys as) of
      (SOME v, SOME vs) => SOME (v :: vs)
    | _ => NONE) ∧
  (abi_runtime_values _ _ = NONE)
End

(* The source heap tracks allocations; an external call also reserves its
 * returndata buffer before decoding dynamic return values. *)
Definition memory_free_pointer_def:
  memory_free_pointer st = 128 + st.memory_allocated
End

(* Scalar cleanliness uses contractABI. Dynamic byte tails follow the pinned
 * decoder: offsets need not be aligned, tails may overlap, and padding is
 * ignored. Memory allocation overflow is checked before the data span. *)
Definition decode_abi_argument_def:
  decode_abi_argument ty bs head base free =
    if head + 32 > LENGTH bs then INR (RevertCompletion []) else
    if byte_sequence_value_type ty then
      let offset = num_of_be_bytes (TAKE 32 (DROP head bs)) in
      if 2 ** 64 ≤ offset ∨ offset + 32 > LENGTH bs then
        INR (RevertCompletion []) else
      let length = num_of_be_bytes (TAKE 32 (DROP offset bs)) in
      let allocated = free + 32 + 32 * ((length + 31) DIV 32) in
      let memory = (case ty of LocatedT MemoryLoc _ => T | _ => F) in
      if memory ∧ (2 ** 64 ≤ length ∨ 2 ** 64 ≤ allocated) then
        INR (PanicCompletion 65)
      else if 2 ** 64 ≤ length ∨ offset + 32 + length > LENGTH bs then
        INR (RevertCompletion [])
      else case ty of
        LocatedT CalldataLoc element =>
          INL (ReferenceValue (CalldataReference (base + offset + 32) length element), free)
      | LocatedT MemoryLoc element =>
          INL (ScalarValue (BytesValue (TAKE length (DROP (offset + 32) bs))), allocated)
      | _ => INR (InvalidCompletion "bad ABI byte location")
    else
      let data = TAKE 32 (DROP head bs) in
      if ¬valid_enc (abi_type ty) data then INR (RevertCompletion []) else
      case abi_runtime_value ty (dec (abi_type ty) data) of
        SOME v => INL (v, free)
      | NONE => INR (InvalidCompletion "bad ABI scalar type")
End

Definition decode_abi_arguments_def:
  (decode_abi_arguments [] bs head base free = INL []) ∧
  (decode_abi_arguments (ty :: tys) bs head base free =
    case decode_abi_argument ty bs head base free of
      INR c => INR c
    | INL (v, next) =>
        case decode_abi_arguments tys bs (head + 32) base next of
          INL vs => INL (v :: vs)
        | INR c => INR c)
End

Definition decode_arguments_def:
  decode_arguments tys bs base free =
    if LENGTH tys * 32 > LENGTH bs then INR (RevertCompletion [])
    else decode_abi_arguments tys bs 0 base free
End

(* Decoded memory payloads become heap objects before a procedure sees them.
 * Calldata payloads retain slices into the frame's original call_data. *)
Definition materialize_arguments_def:
  (materialize_arguments [] [] st = SOME ([], st)) ∧
  (materialize_arguments (ty :: tys) (v :: vs) st =
    let (value, st1) =
      case (ty, v) of
        (LocatedT MemoryLoc element, ScalarValue (BytesValue bs)) =>
          allocate_bytes element bs st
      | _ => (v, st) in
    case materialize_arguments tys vs st1 of
      SOME (values, st2) => SOME (value :: values, st2)
    | NONE => NONE) ∧
  (materialize_arguments _ _ _ = NONE)
End

(* Revert data of Panic(uint256), selector 0x4e487b71. *)
Definition panic_data_def:
  panic_data n = [0x4Ew; 0x48w; 0x7Bw; 0x71w] ++ enc (Uint 256) (NumV n)
End

(* Event arguments split into the topics of the indexed ones, each the
 * value's ABI word, and the types and values of the rest, which form the
 * log's data.
 *)
Definition event_parts_def:
  (event_parts st [] = SOME ([], [], [])) ∧
  (event_parts st ((ty, indexed, v) :: args) =
    case (runtime_abi_value st ty v, event_parts st args) of
      (SOME a, SOME (topics, tys, avs)) =>
        if indexed then
          SOME ((case a of
                   BytesV bs => if byte_sequence_value_type ty then
                     word_of_bytes_be (Keccak_256_w64 bs)
                     else word_of_bytes T (0w : bytes32) (enc (abi_type ty) a)
                 | _ => word_of_bytes T (0w : bytes32) (enc (abi_type ty) a)) :: topics,
                tys, avs)
        else SOME (topics, abi_type ty :: tys, a :: avs)
    | _ => NONE)
End

Definition event_log_def:
  event_log st logger topic0 args =
    case event_parts st args of
      SOME (topics, tys, avs) =>
        SOME <| logger := logger;
                topics := (case topic0 of SOME t => t :: topics | NONE => topics);
                data := enc (Tuple tys) (ListV avs) |>
    | NONE => NONE
End

val () = cv_auto_trans abi_type_def;
val () = cv_auto_trans abi_value_def;
val () = cv_auto_trans abi_values_def;
val () = cv_auto_trans encoded_values_def;
val () = cv_auto_trans abi_runtime_value_def;
val () = cv_auto_trans abi_runtime_values_def;
val () = cv_auto_trans runtime_abi_value_def;
val () = cv_auto_trans runtime_abi_values_def;
val () = cv_auto_trans encoded_runtime_values_def;
val () = cv_auto_trans memory_free_pointer_def;
val () = cv_auto_trans decode_abi_argument_def;
val () = cv_auto_trans decode_abi_arguments_def;
val () = cv_auto_trans decode_arguments_def;
val materialize_arguments_pre_def =
  cv_auto_trans_pre "materialize_arguments_pre" materialize_arguments_def;

Theorem materialize_arguments_pre[cv_pre]:
  ∀tys vs st. materialize_arguments_pre tys vs st
Proof
  ho_match_mp_tac materialize_arguments_ind >> rpt strip_tac >>
  simp[Once materialize_arguments_pre_def] >> rw[] >> fs[]
QED
val () = cv_auto_trans panic_data_def;
val () = cv_auto_trans
  (REWRITE_RULE [GSYM byteTheory.word_of_bytes_be_def] event_parts_def);
val () = cv_auto_trans event_log_def;
