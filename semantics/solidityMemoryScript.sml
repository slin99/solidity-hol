(* Byte sequences in the source heap. Object zero denotes the empty default
 * memory value; allocations use positive identities so later allocations
 * cannot change a default-initialised return binding. *)
Theory solidityMemory
Ancestors
  solidityStorage
Libs
  cv_transLib wordsLib intLib

Definition byte_cells_def:
  byte_cells bs =
    FEMPTY |++ ZIP (COUNT_LIST (LENGTH bs), MAP (λb. ScalarValue (BytesValue [b])) bs)
End

Definition allocate_bytes_def:
  allocate_bytes ty bs (st : source_state) =
    let id = st.next_heap_id + 1 in
    let obj = <| object_type := ty; object_length := LENGTH bs;
                 object_cells := byte_cells bs |> in
    (ReferenceValue (MemoryReference (HeapId id) 0 ty),
     st with <| heap := st.heap |+ (id, obj); next_heap_id := id |>)
End

Definition memory_byte_def:
  memory_byte obj i =
    case FLOOKUP obj.object_cells i of
      NONE => SOME (0w : byte)
    | SOME (ScalarValue (BytesValue [b])) => SOME b
    | _ => NONE
End

Definition heap_bytes_def:
  (heap_bytes obj i 0 = SOME []) ∧
  (heap_bytes obj i (SUC n) =
    case (memory_byte obj i, heap_bytes obj (i + 1) n) of
      (SOME b, SOME bs) => SOME (b :: bs)
    | _ => NONE)
End

Definition memory_bytes_def:
  memory_bytes (st : source_state) (HeapId id) ty =
    if ¬byte_sequence_type ty then NONE else
    if id = 0 then SOME [] else
    case FLOOKUP st.heap id of
      SOME obj =>
        if byte_sequence_type obj.object_type then
          heap_bytes obj 0 obj.object_length
        else NONE
    | NONE => NONE
End

Definition reference_bytes_def:
  reference_bytes (st : source_state) r =
    case r of
      StorageReference PersistentStorage _ _ _ _ _ =>
        (case storage_byte_contents st.world.accounts r of
           INL bs => SOME bs
         | INR _ => NONE)
    | MemoryReference id 0 ty => memory_bytes st id ty
    | CalldataReference offset length ty =>
        if byte_sequence_type ty ∧ offset + length ≤ LENGTH st.frame.call_data then
          SOME (TAKE length (DROP offset st.frame.call_data))
        else NONE
    | _ => NONE
End

Definition read_memory_reference_def:
  read_memory_reference (st : source_state) ty r =
    case r of
      MemoryReference (HeapId id) offset rty =>
        if ty ≠ FixedBytesT 1 ∨ rty ≠ ty then
          ValueAbrupt (InvalidCompletion "bad memory read type")
        else (case FLOOKUP st.heap id of
          SOME obj =>
            if ¬byte_sequence_type obj.object_type ∨ obj.object_length ≤ offset then
              ValueAbrupt (InvalidCompletion "bad memory byte reference")
            else (case memory_byte obj offset of
              SOME b => ValueOk (ScalarValue (BytesValue [b]))
            | NONE => ValueAbrupt (InvalidCompletion "bad memory byte cell"))
        | NONE => ValueAbrupt (InvalidCompletion "missing memory object"))
    | _ => ValueAbrupt (InvalidCompletion "bad memory reference")
End

Definition navigate_memory_byte_def:
  navigate_memory_byte (st : source_state) r i =
    case r of
      MemoryReference id 0 BytesT =>
        (case memory_bytes st id BytesT of
           SOME bs =>
             if i < 0 ∨ &(LENGTH bs) ≤ i then ValueAbrupt (PanicCompletion 50)
             else ValueOk (ReferenceValue (MemoryReference id (Num i) (FixedBytesT 1)))
         | NONE => ValueAbrupt (InvalidCompletion "bad memory byte array"))
    | _ => ValueAbrupt (InvalidCompletion "bad memory byte array")
End

Definition write_memory_byte_def:
  write_memory_byte r s (st : source_state) =
    case (r, s) of
      (MemoryReference (HeapId id) i ty, BytesValue [b]) =>
        if ty ≠ FixedBytesT 1 then NONE else
        (case FLOOKUP st.heap id of
           SOME obj =>
             if byte_sequence_type obj.object_type ∧ i < obj.object_length then
               SOME (st with heap := st.heap |+ (id,
                 obj with object_cells := obj.object_cells |+
                   (i, ScalarValue (BytesValue [b]))))
             else NONE
         | NONE => NONE)
    | _ => NONE
End

Definition copy_memory_bytes_def:
  copy_memory_bytes src dst (st : source_state) =
    case (reference_bytes st src, dst) of
      (SOME bs, MemoryReference (HeapId id) 0 ty) =>
        (case FLOOKUP st.heap id of
           SOME obj =>
             if byte_sequence_type ty ∧ byte_sequence_type obj.object_type ∧
                obj.object_length = LENGTH bs then
               SOME (st with heap := st.heap |+ (id, obj with object_cells := byte_cells bs))
             else NONE
         | NONE => NONE)
    | _ => NONE
End

(* Byte access and copies propagate malformed storage-header panics. *)
Definition byte_contents_def:
  byte_contents st r =
    case r of
      StorageReference _ _ _ _ _ _ => storage_byte_contents st.world.accounts r
    | _ => case reference_bytes st r of
        SOME bs => INL bs
      | NONE => INR (InvalidCompletion "bad byte sequence reference")
End

Definition copy_byte_contents_def:
  copy_byte_contents src dst st =
    case dst of
      StorageReference PersistentStorage _ _ _ _ _ =>
        (case src of
           StorageReference PersistentStorage _ _ _ _ _ =>
             (case copy_storage_bytes st.world.accounts src dst st.frame.static_context of
                INL accounts => INL (st with world := st.world with accounts := accounts)
              | INR c => INR c)
         | _ => case byte_contents st src of
             INR c => INR c
           | INL bs => case store_storage_bytes st.world.accounts dst bs st.frame.static_context of
               INL accounts => INL (st with world := st.world with accounts := accounts)
             | INR c => INR c)
    | _ => (case byte_contents st src of
        INR c => INR c
      | INL bs => case copy_memory_bytes src dst st of
          SOME st' => INL st'
        | NONE => INR (InvalidCompletion "bad memory byte copy"))
End

(* Reference conversion preserves identity and location; copying is a statement. *)
Definition convert_byte_reference_def:
  convert_byte_reference src dst r =
    case (src, dst, r) of
      (LocatedT MemoryLoc a, LocatedT MemoryLoc b, MemoryReference id 0 c) =>
        if a = c ∧ byte_sequence_type a ∧ byte_sequence_type b then
          ValueOk (ReferenceValue (MemoryReference id 0 b))
        else ValueAbrupt (InvalidCompletion "bad byte reference conversion")
    | (LocatedT CalldataLoc a, LocatedT CalldataLoc b, CalldataReference off len c) =>
        if a = c ∧ byte_sequence_type a ∧ byte_sequence_type b then
          ValueOk (ReferenceValue (CalldataReference off len b))
        else ValueAbrupt (InvalidCompletion "bad byte reference conversion")
    | (LocatedT StorageLoc a, LocatedT StorageLoc b,
       StorageReference PersistentStorage addr slot 0 c layout) =>
        if a = c ∧ byte_sequence_type a ∧ byte_sequence_type b then
          ValueOk (ReferenceValue
            (StorageReference PersistentStorage addr slot 0 b layout))
        else ValueAbrupt (InvalidCompletion "bad byte reference conversion")
    | _ => ValueAbrupt (InvalidCompletion "bad byte reference conversion")
End

val () = cv_auto_trans byte_cells_def;
val () = cv_auto_trans allocate_bytes_def;
val () = cv_auto_trans memory_byte_def;
val () = cv_auto_trans heap_bytes_def;
val () = cv_auto_trans memory_bytes_def;
val () = cv_auto_trans reference_bytes_def;
val () = cv_auto_trans read_memory_reference_def;
val () = cv_auto_trans navigate_memory_byte_def;
val () = cv_auto_trans write_memory_byte_def;
val () = cv_auto_trans copy_memory_bytes_def;

val () = cv_auto_trans byte_contents_def;
val () = cv_auto_trans copy_byte_contents_def;
val () = cv_auto_trans convert_byte_reference_def;
