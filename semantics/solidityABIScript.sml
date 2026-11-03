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

(* Keep both the logical value (for indexed hashes) and its encoded body.
 * Storage encoders copy complete data words, retaining unused dirty bytes. *)
Definition runtime_abi_value_def:
  runtime_abi_value st ty v =
    let contents = case v of
          ReferenceValue r => byte_contents st r
        | ScalarValue (BytesValue bs) => INL bs
        | _ => INL [] in
    case contents of
      INR c => INR c
    | INL bs =>
      case abi_value ty (case v of ReferenceValue _ => ScalarValue (BytesValue bs)
                                | _ => v) of
        NONE => INR (InvalidCompletion "bad ABI value")
      | SOME a =>
        let encoded = enc (abi_type ty) a in
        case v of
          ReferenceValue (StorageReference PersistentStorage addr slot 0 element _) =>
            if byte_sequence_type element then
              let length = LENGTH bs in
              let padded = storage_byte_range st.world.accounts addr slot length 0
                             (32 * ((length + 31) DIV 32)) in
              let data = if 0 < length ∧ length < 32 then TAKE 31 padded ++ [0w]
                         else padded in
              INL (a, enc (Uint 256) (NumV length) ++ data)
            else INL (a, encoded)
        | _ => INL (a, encoded)
End

(* The tuple head/tail layout, using already encoded component bodies. *)
Definition encoded_abi_parts_def:
  (encoded_abi_parts hl tl [] = ([], [])) ∧
  (encoded_abi_parts hl tl ((ty, encoded_body) :: parts) =
    let dynamic = is_dynamic ty in
    let tail = if dynamic then encoded_body else [] in
    let head = if dynamic then enc (Uint 256) (NumV (hl + tl)) else encoded_body in
    let (heads, tails) = encoded_abi_parts hl (tl + LENGTH tail) parts in
    (head ++ heads, tail ++ tails))
End

Definition encoded_abi_tuple_def:
  encoded_abi_tuple parts =
    let (heads, tails) = encoded_abi_parts (head_lengths (MAP FST parts) 0) 0 parts in
    heads ++ tails
End

Definition runtime_abi_values_def:
  (runtime_abi_values (st : source_state) [] [] =
     (INL [] : (contractABI$abi_type # byte list) list + source_completion)) ∧
  (runtime_abi_values st (ty :: tys) (v :: vs) =
    case runtime_abi_value st ty v of
      INR c => INR c
    | INL (a, encoded_body) =>
      (case runtime_abi_values st tys vs of
         INL encoded => INL ((abi_type ty, encoded_body) :: encoded)
       | INR c => INR c)) ∧
  (runtime_abi_values _ _ _ = INR (InvalidCompletion "bad ABI arguments"))
End

Definition encoded_runtime_values_def:
  encoded_runtime_values st tys vs =
    case runtime_abi_values st tys vs of
      INL parts => INL (encoded_abi_tuple parts)
    | INR c => INR c
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
  (event_parts st [] = INL ([], [])) ∧
  (event_parts st ((ty, indexed, v) :: args) =
    case runtime_abi_value st ty v of
      INR c => INR c
    | INL (a, encoded_body) =>
      (case event_parts st args of
         INR c => INR c
       | INL (topics, parts) =>
        if indexed then
          INL ((case a of
                   BytesV bs => if byte_sequence_value_type ty then
                     word_of_bytes_be (Keccak_256_w64 bs)
                     else word_of_bytes T (0w : bytes32) encoded_body
                 | _ => word_of_bytes T (0w : bytes32) encoded_body) :: topics, parts)
        else INL (topics, (abi_type ty, encoded_body) :: parts)))
End

Definition event_log_def:
  event_log st logger topic0 args =
    case event_parts st args of
      INL (topics, parts) =>
        INL <| logger := logger;
               topics := (case topic0 of SOME t => t :: topics | NONE => topics);
               data := encoded_abi_tuple parts |>
    | INR c => INR c
End

val () = cv_auto_trans abi_type_def;
val () = cv_auto_trans abi_value_def;
val () = cv_auto_trans abi_values_def;
val () = cv_auto_trans encoded_values_def;
val () = cv_auto_trans abi_runtime_value_def;
val () = cv_auto_trans abi_runtime_values_def;
val () = cv_auto_trans runtime_abi_value_def;
val () = cv_auto_trans encoded_abi_parts_def;
val () = cv_auto_trans encoded_abi_tuple_def;
val runtime_abi_values_pre_def =
  cv_auto_trans_pre "runtime_abi_values_pre" runtime_abi_values_def;

Theorem runtime_abi_values_pre[cv_pre,local]:
  ∀st tys vs. runtime_abi_values_pre st tys vs
Proof
  ho_match_mp_tac runtime_abi_values_ind >> rpt strip_tac >>
  simp[Once runtime_abi_values_pre_def] >> rw[] >> gvs[]
QED

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
val event_parts_pre_def = cv_auto_trans_pre "event_parts_pre"
  (REWRITE_RULE [GSYM byteTheory.word_of_bytes_be_def] event_parts_def);

Theorem event_parts_pre[cv_pre,local]:
  ∀st args. event_parts_pre st args
Proof
  ho_match_mp_tac event_parts_ind >> rpt strip_tac >>
  simp[Once event_parts_pre_def] >> rw[] >> gvs[]
QED

val () = cv_auto_trans event_log_def;
