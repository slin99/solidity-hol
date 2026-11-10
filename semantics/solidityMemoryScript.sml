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
                 object_cells := byte_cells bs;
                 object_address := 128 + st.memory_allocated |> in
    (ReferenceValue (MemoryReference (HeapId id) 0 ty),
     st with <| heap := st.heap |+ (id, obj); next_heap_id := id;
               memory_allocated := st.memory_allocated +
                 32 + 32 * ((LENGTH bs + 31) DIV 32) |>)
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

(* A calldata byte sequence reads zeros past the end of the calldata, as
 * calldatacopy does; its offset and length were checked when decoded. *)
Definition reference_bytes_def:
  reference_bytes (st : source_state) r =
    case r of
      StorageReference PersistentStorage _ _ _ _ _ =>
        (case storage_byte_contents st.world.accounts r of
           INL bs => SOME bs
         | INR _ => NONE)
    | MemoryReference id 0 ty => memory_bytes st id ty
    | CalldataReference offset length ty =>
        if byte_sequence_type ty then
          SOME (TAKE length (DROP offset st.frame.call_data ++ REPLICATE length 0w))
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

(* Memory arrays: an object of type ArrayT element length holds one cell per
 * element, a value or a pointer to another object, as the compiler's memory
 * layout does. A cell never written holds the element's zero, a pointer to the
 * empty object zero for a byte sequence or dynamic array; static array
 * elements are allocated with their array. Object zero is also the empty
 * dynamic array. *)

Definition default_elementary_def:
  default_elementary ty =
    case ty of
      BoolT => SOME (BoolValue F)
    | UintT _ => SOME (IntegerValue 0)
    | IntT _ => SOME (IntegerValue 0)
    | AddressT _ => SOME (AddressValue 0w)
    | FixedBytesT n => SOME (BytesValue (REPLICATE n 0w))
    | EnumT _ => SOME (IntegerValue 0)
    | FunctionT InternalFn _ _ _ => SOME (InternalFunctionValue NONE)
    | _ => NONE
End

Definition memory_cell_def:
  memory_cell obj element i =
    case FLOOKUP obj.object_cells i of
      SOME v => v
    | NONE =>
        case default_elementary element of
          SOME s => ScalarValue s
        | NONE => ReferenceValue (MemoryReference (HeapId 0) 0 element)
End

(* A zeroed array of n elements, after the compiler's allocation: the length
 * word of a dynamic array and a word per element, Panic(0x41) when the free
 * memory pointer would pass 2^64; then each static array element, in order. *)
Definition zero_array_def:
  (zero_array ty n (st : source_state) =
    case ty of
      ArrayT element length =>
        let size = (if length = NONE then 32 else 0) + 32 * n in
        if 2 ** 64 ≤ 128 + st.memory_allocated + size then
          INR (PanicCompletion 65)
        else
          let id = st.next_heap_id + 1 in
          let obj = <| object_type := ty; object_length := n;
                       object_cells := FEMPTY;
                       object_address := 128 + st.memory_allocated |> in
          let st1 = st with <| heap := st.heap |+ (id, obj); next_heap_id := id;
                               memory_allocated := st.memory_allocated + size |> in
          let r = ReferenceValue (MemoryReference (HeapId id) 0 ty) in
          (case element of
             ArrayT _ (SOME k) =>
               (case zero_arrays element k 0 n FEMPTY st1 of
                  INL (cells, st2) =>
                    INL (r, st2 with heap :=
                              st2.heap |+ (id, obj with object_cells := cells))
                | INR c => INR c)
           | _ => INL (r, st1))
    | _ => INR (InvalidCompletion "bad memory array type")) ∧
  (zero_arrays element k i m cells st =
    if m = 0 then INL (cells, st) else
    case zero_array element k st of
      INL (v, st1) => zero_arrays element k (i + 1) (m - 1) (cells |+ (i, v)) st1
    | INR c => INR c)
Termination
  WF_REL_TAC ‘inv_image ($< LEX $<) (λx. case x of
    INL (ty, n, st) => (sol_type_size ty, 0)
  | INR (element, k, i, m, cells, st) => (sol_type_size element, m + 1))’ >>
  rw[solidityASTTheory.sol_type_size_def]
End

(* The value of a memory variable before any assignment. *)
Definition default_memory_value_def:
  default_memory_value ty (st : source_state) =
    case ty of
      ArrayT _ (SOME n) => zero_array ty n st
    | _ => INL (ReferenceValue (MemoryReference (HeapId 0) 0 ty), st)
End

Definition memory_array_length_def:
  memory_array_length (st : source_state) r =
    case r of
      MemoryReference (HeapId id) 0 (ArrayT element length) =>
        if id = 0 then SOME 0 else
        (case FLOOKUP st.heap id of
           SOME obj =>
             if obj.object_type = ArrayT element length then SOME obj.object_length
             else NONE
         | NONE => NONE)
    | _ => NONE
End

(* Element i of a memory array, which must exist: Panic(0x32) otherwise. *)
Definition memory_array_element_def:
  memory_array_element (st : source_state) r (i : int) =
    case (r, memory_array_length st r) of
      (MemoryReference (HeapId id) _ (ArrayT element _), SOME n) =>
        if i < 0 ∨ &n ≤ i then INR (PanicCompletion 50) else
        (case FLOOKUP st.heap id of
           SOME obj => INL (id, Num i, element, memory_cell obj element (Num i))
         | NONE => INR (InvalidCompletion "missing memory object"))
    | _ => INR (InvalidCompletion "bad memory array reference")
End

Definition write_memory_element_def:
  write_memory_element id i v (st : source_state) =
    case FLOOKUP st.heap id of
      SOME obj =>
        (case obj.object_type of
           ArrayT _ _ =>
             if i < obj.object_length then
               SOME (st with heap := st.heap |+ (id,
                 obj with object_cells := obj.object_cells |+ (i, v)))
             else NONE
         | _ => NONE)
    | NONE => NONE
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

(* The value of a memory array, as a copy reads it: the tuple of its
 * elements, byte sequences as their bytes. *)
Definition memory_array_value_def:
  (memory_array_value (st : source_state) ty v =
    case (ty, v) of
      (ArrayT element length, ReferenceValue (MemoryReference (HeapId id) 0 rty)) =>
        if rty ≠ ty then INR (InvalidCompletion "bad memory array reference")
        else if id = 0 then
          (if length = NONE then INL (TupleValue [])
           else INR (InvalidCompletion "bad memory array reference"))
        else
          (case FLOOKUP st.heap id of
             SOME obj =>
               if obj.object_type ≠ ty then
                 INR (InvalidCompletion "bad memory array reference")
               else
                 (case memory_array_cells st element obj 0 obj.object_length of
                    INL vs => INL (TupleValue vs)
                  | INR c => INR c)
           | NONE => INR (InvalidCompletion "missing memory object"))
    | (_, ReferenceValue r) =>
        (case byte_contents st r of
           INL bs => INL (ScalarValue (BytesValue bs))
         | INR c => INR c)
    | (_, ScalarValue _) => INL v
    | _ => INR (InvalidCompletion "bad memory array value")) ∧
  (memory_array_cells st element obj i n =
    if n = 0 then INL [] else
    case memory_array_value st element (memory_cell obj element i) of
      INR c => INR c
    | INL v =>
        case memory_array_cells st element obj (i + 1) (n - 1) of
          INL vs => INL (v :: vs)
        | INR c => INR c)
Termination
  WF_REL_TAC ‘inv_image ($< LEX $<) (λx. case x of
    INL (st, ty, v) => (sol_type_size ty, 0)
  | INR (st, element, obj, i, n) => (sol_type_size element, n + 1))’ >>
  rw[solidityASTTheory.sol_type_size_def]
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
    | _ =>
      (* The compiler's calldata-to-memory conversion reverts when the data,
       * added as a word, ends past the calldata; its other readers pad. *)
      if (case src of
            CalldataReference offset length _ =>
              LENGTH st.frame.call_data < (offset + length) MOD 2 ** 256
          | _ => F)
      then INR (RevertCompletion []) else
      (case byte_contents st src of
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

val () = cv_auto_trans default_elementary_def;
val () = cv_auto_trans memory_cell_def;
(* How cv's precondition presents a heap object record. *)
Theorem heap_object_literal:
  <| object_type := a; object_length := b; object_cells := c;
     object_address := d |> = heap_object a b c d
Proof
  simp[solidityStateTheory.heap_object_component_equality]
QED

val zero_array_pre_def = cv_auto_trans_pre_rec "zero_array_pre zero_arrays_pre" zero_array_def (
  WF_REL_TAC ‘inv_image ($< LEX $<) (λx. case x of
    INL (ty, n, st) => (cv_size ty, 0)
  | INR (element, k, i, m, cells, st) => (cv_size element, cv$c2n m + 1))’ >>
  cv_termination_tac
);

Theorem zero_array_pre[cv_pre]:
  (∀ty n st. zero_array_pre ty n st) ∧
  (∀element k i m cells st. zero_arrays_pre element k i m cells st)
Proof
  ho_match_mp_tac zero_array_ind >> rpt strip_tac >>
  simp[Once zero_array_pre_def] >> rw[] >> gvs[] >>
  (* record updates appear as cases on the state *)
  Cases_on ‘st’ >> gvs[solidityStateTheory.source_state_fn_updates, heap_object_literal]
QED
val () = cv_auto_trans default_memory_value_def;
val () = cv_auto_trans memory_array_length_def;
val () = cv_auto_trans memory_array_element_def;
val () = cv_auto_trans write_memory_element_def;

val () = cv_auto_trans byte_contents_def;
val memory_array_value_pre_def = cv_auto_trans_pre_rec
  "memory_array_value_pre memory_array_cells_pre" memory_array_value_def (
  WF_REL_TAC ‘inv_image ($< LEX $<) (λx. case x of
    INL (st, ty, v) => (cv_size ty, 0)
  | INR (st, element, obj, i, n) => (cv_size element, cv$c2n n + 1))’ >>
  cv_termination_tac
);

Theorem memory_array_value_pre[cv_pre]:
  (∀st ty v. memory_array_value_pre st ty v) ∧
  (∀st element obj i n. memory_array_cells_pre st element obj i n)
Proof
  ho_match_mp_tac memory_array_value_ind >> rpt strip_tac >>
  simp[Once memory_array_value_pre_def] >> rw[] >> gvs[]
QED

val () = cv_auto_trans copy_byte_contents_def;
val () = cv_auto_trans convert_byte_reference_def;
