(* The ABI at the contract boundary, for scalars, bytes/string values and
 * memory arrays:
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
  (abi_type (ArrayT ty length) = Array length (abi_type ty)) ∧
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

(* The ABI value of a memory object of type ty, or of an element value. *)
Definition memory_abi_value_def:
  (memory_abi_value (st : source_state) ty v =
    case ty of
      ArrayT element length =>
        (case v of
           ReferenceValue (MemoryReference (HeapId id) 0 rty) =>
             if rty ≠ ty then NONE
             else if id = 0 then
               (if length = NONE then SOME (ListV []) else NONE)
             else
               (case FLOOKUP st.heap id of
                  SOME obj =>
                    if obj.object_type ≠ ty then NONE else
                    OPTION_MAP ListV
                      (memory_abi_cells st element obj 0 obj.object_length)
                | NONE => NONE)
         | _ => NONE)
    | _ =>
        (case v of
           ReferenceValue r =>
             (case reference_bytes st r of
                SOME bs => abi_value ty (ScalarValue (BytesValue bs))
              | NONE => NONE)
         | _ => abi_value ty v)) ∧
  (memory_abi_cells st element obj i n =
    if n = 0 then SOME [] else
    case (memory_abi_value st element (memory_cell obj element i),
          memory_abi_cells st element obj (i + 1) (n - 1)) of
      (SOME a, SOME as) => SOME (a :: as)
    | _ => NONE)
Termination
  WF_REL_TAC ‘inv_image ($< LEX $<) (λx. case x of
    INL (st, ty, v) => (sol_type_size ty, 0)
  | INR (st, element, obj, i, n) => (sol_type_size element, n + 1))’ >>
  rw[solidityASTTheory.sol_type_size_def]
End

(* Keep both the logical value (for indexed hashes) and its encoded body.
 * Storage encoders copy complete data words, retaining unused dirty bytes. *)
Definition runtime_abi_value_def:
  runtime_abi_value st ty v =
    case ty of
      LocatedT MemoryLoc (ArrayT element length) =>
        (case memory_abi_value st (ArrayT element length) v of
           SOME a => INL (a, enc (abi_type ty) a)
         | NONE => INR (InvalidCompletion "bad ABI value"))
    | _ =>
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

Definition abi_word_def:
  abi_word bs pos = num_of_be_bytes (TAKE 32 (DROP pos bs))
End

(* The bytes an element takes in its array's encoding. *)
Definition abi_stride_def:
  abi_stride ty =
    if is_dynamic (abi_type ty) then 32 else static_length (abi_type ty)
End

(* A memory value decoded at pos, as the pinned decoder does: a scalar
 * validated in place; a byte sequence or array whose encoding starts at pos
 * in range, its length below 2^64 and its memory allocated (Panic(0x41) when
 * the free memory pointer would pass 2^64) before its data span is checked;
 * then each element, a dynamic one at an offset below 2^64 from the start of
 * the array's data. Offsets need not be aligned, tails may overlap, and
 * padding is ignored. Byte sequences decode to their bytes and arrays to the
 * tuple of their elements; free is the free memory pointer. *)
Definition decode_memory_value_def:
  (decode_memory_value ty bs pos free =
    if byte_sequence_type ty ∨ (case ty of ArrayT _ _ => T | _ => F) then
      if pos + 32 > LENGTH bs then INR (RevertCompletion []) else
      let (length, data, size) =
        case ty of
          ArrayT element (SOME n) => (n, pos, 32 * n)
        | ArrayT element NONE =>
            let n = abi_word bs pos in (n, pos + 32, 32 + 32 * n)
        | _ => let n = abi_word bs pos in (n, pos + 32, 32 + 32 * ((n + 31) DIV 32)) in
      if 2 ** 64 ≤ length ∨ 2 ** 64 ≤ free + size then INR (PanicCompletion 65) else
      case ty of
        ArrayT element _ =>
          if data + length * abi_stride element > LENGTH bs then
            INR (RevertCompletion [])
          else
            (case decode_memory_elements element bs data 0 length (free + size) of
               INL (vs, next) => INL (TupleValue vs, next)
             | INR c => INR c)
      | _ =>
          if data + length > LENGTH bs then INR (RevertCompletion [])
          else INL (ScalarValue (BytesValue (TAKE length (DROP data bs))), free + size)
    else
      let word = TAKE 32 (DROP pos bs) in
      if pos + 32 > LENGTH bs ∨ ¬valid_enc (abi_type ty) word then
        INR (RevertCompletion [])
      else
        case abi_runtime_value ty (dec (abi_type ty) word) of
          SOME v => INL (v, free)
        | NONE => INR (InvalidCompletion "bad ABI scalar type")) ∧
  (decode_memory_elements element bs data i n free =
    if n = 0 then INL ([], free) else
    let src = data + i * abi_stride element in
    let decoded =
      if is_dynamic (abi_type element) then
        let offset = abi_word bs src in
        if 2 ** 64 ≤ offset then INR (RevertCompletion [])
        else decode_memory_value element bs (data + offset) free
      else decode_memory_value element bs src free in
    case decoded of
      INR c => INR c
    | INL (v, next) =>
        case decode_memory_elements element bs data (i + 1) (n - 1) next of
          INL (vs, last) => INL (v :: vs, last)
        | INR c => INR c)
Termination
  WF_REL_TAC ‘inv_image ($< LEX $<) (λx. case x of
    INL (ty, bs, pos, free) => (sol_type_size ty, 0)
  | INR (element, bs, data, i, n, free) => (sol_type_size element, n + 1))’ >>
  rw[solidityASTTheory.sol_type_size_def]
End

(* An argument at head: a scalar or static array in place, any other value at
 * the offset the head holds. A calldata byte sequence stays in the calldata. *)
Definition decode_abi_argument_def:
  decode_abi_argument ty bs head base free =
    if head + 32 > LENGTH bs then INR (RevertCompletion []) else
    case ty of
      LocatedT CalldataLoc element =>
        let offset = abi_word bs head in
        if 2 ** 64 ≤ offset ∨ offset + 32 > LENGTH bs then
          INR (RevertCompletion []) else
        let length = abi_word bs offset in
        if 2 ** 64 ≤ length ∨ offset + 32 + length > LENGTH bs then
          INR (RevertCompletion [])
        else if byte_sequence_type element then
          INL (ReferenceValue (CalldataReference (base + offset + 32) length element), free)
        else INR (InvalidCompletion "bad ABI calldata type")
    | LocatedT MemoryLoc element =>
        if is_dynamic (abi_type element) then
          let offset = abi_word bs head in
          if 2 ** 64 ≤ offset then INR (RevertCompletion [])
          else decode_memory_value element bs offset free
        else decode_memory_value element bs head free
    | _ => decode_memory_value ty bs head free
End

Definition decode_abi_arguments_def:
  (decode_abi_arguments [] bs head base free = INL []) ∧
  (decode_abi_arguments (ty :: tys) bs head base free =
    case decode_abi_argument ty bs head base free of
      INR c => INR c
    | INL (v, next) =>
        case decode_abi_arguments tys bs (head + abi_stride ty) base next of
          INL vs => INL (v :: vs)
        | INR c => INR c)
End

Definition decode_arguments_def:
  decode_arguments tys bs base free =
    if head_lengths (MAP abi_type tys) 0 > LENGTH bs then INR (RevertCompletion [])
    else decode_abi_arguments tys bs 0 base free
End

(* A decoded memory value as heap objects, allocated in decoding order: an
 * array before its elements. *)
Definition materialize_value_def:
  (materialize_value ty v (st : source_state) =
    case (ty, v) of
      (ArrayT element length, TupleValue vs) =>
        let n = LENGTH vs in
        let id = st.next_heap_id + 1 in
        let obj = <| object_type := ty; object_length := n;
                     object_cells := FEMPTY |> in
        let st1 = st with <| heap := st.heap |+ (id, obj); next_heap_id := id;
                     memory_allocated := st.memory_allocated +
                       (if length = NONE then 32 else 0) + 32 * n |> in
        (case materialize_values element 0 vs FEMPTY st1 of
           SOME (cells, st2) =>
             SOME (ReferenceValue (MemoryReference (HeapId id) 0 ty),
                   st2 with heap := st2.heap |+ (id, obj with object_cells := cells))
         | NONE => NONE)
    | (_, ScalarValue (BytesValue bs)) =>
        if byte_sequence_type ty then SOME (allocate_bytes ty bs st)
        else SOME (v, st)
    | (_, ScalarValue _) => SOME (v, st)
    | _ => NONE) ∧
  (materialize_values element i [] cells st = SOME (cells, st)) ∧
  (materialize_values element i (v :: vs) cells st =
    case materialize_value element v st of
      SOME (value, st1) =>
        materialize_values element (i + 1) vs (cells |+ (i, value)) st1
    | NONE => NONE)
Termination
  WF_REL_TAC ‘measure (λx. case x of
    INL (ty, v, st) => runtime_value_size v
  | INR (element, i, vs, cells, st) => list_size runtime_value_size vs)’ >>
  rw[solidityCoreTheory.runtime_value_size_def, listTheory.list_size_def]
End

(* Decoded memory payloads become heap objects before a procedure sees them.
 * Calldata payloads retain slices into the frame's original call_data. *)
Definition materialize_arguments_def:
  (materialize_arguments [] [] st = SOME ([], st)) ∧
  (materialize_arguments (ty :: tys) (v :: vs) st =
    case (case ty of
            LocatedT MemoryLoc element => materialize_value element v st
          | _ => SOME (v, st)) of
      SOME (value, st1) =>
        (case materialize_arguments tys vs st1 of
           SOME (values, st2) => SOME (value :: values, st2)
         | NONE => NONE)
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
val memory_abi_value_pre_def = cv_auto_trans_pre_rec "memory_abi_value_pre memory_abi_cells_pre" memory_abi_value_def (
  WF_REL_TAC ‘inv_image ($< LEX $<) (λx. case x of
    INL (st, ty, v) => (cv_size ty, 0)
  | INR (st, element, obj, i, n) => (cv_size element, cv$c2n n + 1))’ >>
  cv_termination_tac
);

Theorem memory_abi_value_pre[cv_pre]:
  (∀st ty v. memory_abi_value_pre st ty v) ∧
  (∀st element obj i n. memory_abi_cells_pre st element obj i n)
Proof
  ho_match_mp_tac memory_abi_value_ind >> rpt strip_tac >>
  simp[Once memory_abi_value_pre_def] >> rw[] >> gvs[]
QED
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
val () = cv_auto_trans abi_word_def;
val () = cv_auto_trans abi_stride_def;
val decode_memory_value_pre_def = cv_auto_trans_pre_rec "decode_memory_value_pre decode_memory_elements_pre" decode_memory_value_def (
  WF_REL_TAC ‘inv_image ($< LEX $<) (λx. case x of
    INL (ty, bs, pos, free) => (cv_size ty, 0)
  | INR (element, bs, data, i, n, free) => (cv_size element, cv$c2n n + 1))’ >>
  cv_termination_tac
);

Theorem decode_memory_value_pre[cv_pre]:
  (∀ty bs pos free. decode_memory_value_pre ty bs pos free) ∧
  (∀element bs data i n free. decode_memory_elements_pre element bs data i n free)
Proof
  ho_match_mp_tac decode_memory_value_ind >> rpt strip_tac >>
  simp[Once decode_memory_value_pre_def] >> rw[] >> gvs[]
QED
val () = cv_auto_trans decode_abi_argument_def;
val () = cv_auto_trans decode_abi_arguments_def;
val () = cv_auto_trans decode_arguments_def;
val materialize_value_pre_def = cv_auto_trans_pre_rec "materialize_value_pre materialize_values_pre" materialize_value_def (
  WF_REL_TAC ‘measure (λx. case x of
    INL (ty, v, st) => cv_size v
  | INR (element, i, vs, cells, st) => cv_size vs)’ >>
  cv_termination_tac
);

Theorem materialize_value_pre[cv_pre]:
  (∀ty v st. materialize_value_pre ty v st) ∧
  (∀element i vs cells st. materialize_values_pre element i vs cells st)
Proof
  ho_match_mp_tac materialize_value_ind >> rpt strip_tac >>
  simp[Once materialize_value_pre_def] >> rw[] >> gvs[] >>
  (* record updates appear as cases on the state *)
  Cases_on ‘st’ >>
  gvs[solidityStateTheory.source_state_fn_updates, solidityMemoryTheory.heap_object_literal]
QED
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
