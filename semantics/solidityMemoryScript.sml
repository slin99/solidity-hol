(* Byte sequences in the source heap. Object zero denotes the empty default
 * memory value; allocations use positive identities so later allocations
 * cannot change a default-initialised return binding. *)
Theory solidityMemory
Ancestors
  solidityStorage
Libs
  cv_transLib wordsLib intLib

(* The cells of the bytes bs from index i, added to cells. *)
Definition byte_cells_from_def:
  (byte_cells_from (cells : num |-> runtime_value) i [] = cells) ∧
  (byte_cells_from cells i (b :: bs) =
     byte_cells_from (cells |+ (i, ScalarValue (BytesValue [b]))) (i + 1) bs)
End

Definition byte_cells_def:
  byte_cells bs = byte_cells_from FEMPTY 0 bs
End

Theorem byte_cells_from_zip[local]:
  ∀bs cells i.
    byte_cells_from cells i bs =
    cells |++ ZIP (GENLIST (λj. i + j) (LENGTH bs),
                   MAP (λb. ScalarValue (BytesValue [b])) bs)
Proof
  Induct >- simp [byte_cells_from_def, finite_mapTheory.FUPDATE_LIST_THM] >>
  rpt gen_tac >>
  REWRITE_TAC [byte_cells_from_def, listTheory.LENGTH, listTheory.GENLIST_CONS,
               listTheory.MAP, listTheory.ZIP, finite_mapTheory.FUPDATE_LIST_THM] >>
  simp [combinTheory.o_DEF] >>
  rpt AP_TERM_TAC >> simp [listTheory.GENLIST_FUN_EQ]
QED

Theorem byte_cells_zip:
  byte_cells bs =
    FEMPTY |++ ZIP (COUNT_LIST (LENGTH bs), MAP (λb. ScalarValue (BytesValue [b])) bs)
Proof
  simp [byte_cells_def, byte_cells_from_zip, rich_listTheory.COUNT_LIST_GENLIST] >>
  rpt AP_TERM_TAC >> simp [listTheory.GENLIST_FUN_EQ]
QED

Definition allocate_bytes_def:
  allocate_bytes padded ty bs (st : source_state) =
    let id = st.next_heap_id + 1 in
    let obj = <| object_type := ty; object_length := LENGTH bs;
                 object_cells := byte_cells bs;
                 object_address := 128 + st.memory_allocated;
                 object_padded := padded |> in
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

(* The component a navigated memory reference denotes: byte offset of a
 * byte sequence, read as a bytes1, or cell offset of a struct, read as its
 * field type ty (a reference field located in memory). *)
Definition read_memory_reference_def:
  read_memory_reference (st : source_state) ty r =
    case r of
      MemoryReference (HeapId id) offset rty =>
        (case FLOOKUP st.heap id of
           SOME obj =>
             (case obj.object_type of
                StructT _ =>
                  if (case ty of LocatedT MemoryLoc t => t | t => t) ≠ rty ∨
                     obj.object_length ≤ offset
                  then ValueAbrupt (InvalidCompletion "bad memory field reference")
                  else ValueOk (memory_cell obj rty offset)
              | _ =>
                if ty ≠ FixedBytesT 1 ∨ rty ≠ ty then
                  ValueAbrupt (InvalidCompletion "bad memory read type")
                else if ¬byte_sequence_type obj.object_type ∨ obj.object_length ≤ offset then
                  ValueAbrupt (InvalidCompletion "bad memory byte reference")
                else (case memory_byte obj offset of
                  SOME b => ValueOk (ScalarValue (BytesValue [b]))
                | NONE => ValueAbrupt (InvalidCompletion "bad memory byte cell")))
         | NONE => ValueAbrupt (InvalidCompletion "missing memory object"))
    | _ => ValueAbrupt (InvalidCompletion "bad memory reference")
End

(* A new memory object of size bytes with no cells written, after the
 * compiler's allocation: NONE when the free memory pointer would pass 2^64. *)
Definition allocate_object_def:
  allocate_object ty length size (st : source_state) =
    if 2 ** 64 ≤ 128 + st.memory_allocated + size then NONE else
    let id = st.next_heap_id + 1 in
    let obj = <| object_type := ty; object_length := length;
                 object_cells := FEMPTY;
                 object_address := 128 + st.memory_allocated;
                 object_padded := T |> in
    SOME (id, st with <| heap := st.heap |+ (id, obj); next_heap_id := id;
                         memory_allocated := st.memory_allocated + size |>)
End

Definition fill_object_def:
  fill_object id ty result =
    case result of
      INL (cells, st : source_state) =>
        (case FLOOKUP st.heap id of
           SOME obj =>
             INL (ReferenceValue (MemoryReference (HeapId id) 0 ty),
                  st with heap := st.heap |+ (id, obj with object_cells := cells))
         | NONE => INR (InvalidCompletion "missing memory object"))
    | INR c => INR c
End

(* A zeroed memory object: for an array of n elements its length word if
 * dynamic and a word per element, for a struct a word per field, Panic(0x41)
 * when the free memory pointer would pass 2^64; then each struct or static
 * array element or field, in order, as the compiler allocates them. A byte
 * sequence or dynamic array member points to the empty object zero. The fuel
 * bounds the struct nesting. *)
Definition zero_object_def:
  (zero_object env (fuel : num) ty n (st : source_state) =
    case ty of
      ArrayT element length =>
        (case allocate_object ty n ((if length = NONE then 32 else 0) + 32 * n) st of
           SOME (id, st1) => fill_object id ty (zero_elements env fuel element 0 n FEMPTY st1)
         | NONE => INR (PanicCompletion 65))
    | StructT s =>
        (case lookup_struct env s of
           SOME fields =>
             if fuel = 0 then INR (InvalidCompletion "struct nesting") else
             (case allocate_object ty (LENGTH fields) (32 * LENGTH fields) st of
                SOME (id, st1) =>
                  fill_object id ty (zero_fields env (fuel - 1) (MAP SND fields) 0 FEMPTY st1)
              | NONE => INR (PanicCompletion 65))
         | NONE => INR (InvalidCompletion "unknown struct"))
    | _ => INR (InvalidCompletion "bad memory object type")) ∧
  (zero_elements env fuel element i m cells st =
    if m = 0 then INL (cells, st) else
    case (case element of
            ArrayT _ (SOME k) => SOME k
          | StructT _ => SOME 0
          | _ => NONE) of
      NONE => INL (cells, st)
    | SOME k =>
        case zero_object env fuel element k st of
          INL (v, st1) => zero_elements env fuel element (i + 1) (m - 1) (cells |+ (i, v)) st1
        | INR c => INR c) ∧
  (zero_fields env fuel [] i cells st = INL (cells, st)) ∧
  (zero_fields env fuel (ty :: tys) i cells st =
    case (case ty of
            ArrayT _ (SOME k) => SOME k
          | StructT _ => SOME 0
          | _ => NONE) of
      NONE => zero_fields env fuel tys (i + 1) cells st
    | SOME k =>
        case zero_object env fuel ty k st of
          INL (v, st1) => zero_fields env fuel tys (i + 1) (cells |+ (i, v)) st1
        | INR c => INR c)
Termination
  WF_REL_TAC ‘inv_image ($< LEX $< LEX $<) (λx. case x of
    INL (env, fuel, ty, n, st) => (fuel, sol_type_size ty, 0)
  | INR (INL (env, fuel, element, i, m, cells, st)) => (fuel, sol_type_size element, m + 1)
  | INR (INR (env, fuel, tys, i, cells, st)) => (fuel, list_size sol_type_size tys, 1))’ >>
  rw[solidityASTTheory.sol_type_size_def, listTheory.list_size_def]
End

(* The value of a memory variable before any assignment. *)
Definition default_memory_value_def:
  default_memory_value env ty (st : source_state) =
    case ty of
      ArrayT _ (SOME n) => zero_object env (LENGTH env.type_declarations) ty n st
    | StructT _ => zero_object env (LENGTH env.type_declarations) ty 0 st
    | _ => INL (ReferenceValue (MemoryReference (HeapId 0) 0 ty), st)
End

Definition memory_array_length_def:
  memory_array_length (st : source_state) r =
    case r of
      MemoryReference (HeapId id) 0 (ArrayT element length) =>
        if id = 0 then (if length = NONE then SOME 0 else NONE) else
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

(* The position and type of field f among a struct's fields. *)
Definition field_position_def:
  (field_position (f : ast_id) [] = NONE) ∧
  (field_position f ((g, ty) :: fields) =
    if f = g then SOME (0n, ty : sol_type) else
    case field_position f fields of
      SOME (k, ty') => SOME (k + 1, ty')
    | NONE => NONE)
End

(* Field f of the memory struct r: its object, cell index, type and value. *)
Definition memory_struct_field_def:
  memory_struct_field env (st : source_state) r f =
    case r of
      MemoryReference (HeapId id) 0 (StructT s) =>
        (case (lookup_struct env s, FLOOKUP st.heap id) of
           (SOME fields, SOME obj) =>
             if obj.object_type ≠ StructT s then
               INR (InvalidCompletion "bad memory struct reference")
             else
               (case field_position f fields of
                  SOME (k, ty) => INL (id, k, ty, memory_cell obj ty k)
                | NONE => INR (InvalidCompletion "unknown struct field"))
         | _ => INR (InvalidCompletion "missing memory struct"))
    | _ => INR (InvalidCompletion "bad memory struct reference")
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
         | StructT _ =>
             if i < obj.object_length then
               SOME (st with heap := st.heap |+ (id,
                 obj with object_cells := obj.object_cells |+ (i, v)))
             else NONE
         | _ => NONE)
    | NONE => NONE
End

(* A write through a navigated memory reference: a struct cell, or a byte of
 * a byte sequence written as a bytes1. *)
Definition write_memory_reference_def:
  write_memory_reference r v (st : source_state) =
    case r of
      MemoryReference (HeapId id) i ty =>
        (case FLOOKUP st.heap id of
           SOME obj =>
             (case obj.object_type of
                StructT _ => write_memory_element id i v st
              | _ =>
                (case v of
                   ScalarValue (BytesValue [b]) =>
                     if ty = FixedBytesT 1 ∧ byte_sequence_type obj.object_type ∧
                        i < obj.object_length
                     then SOME (st with heap := st.heap |+ (id,
                            obj with object_cells := obj.object_cells |+
                              (i, ScalarValue (BytesValue [b]))))
                     else NONE
                 | _ => NONE))
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

(* The value of a memory array or struct, as a copy reads it: the tuple of
 * its elements or fields, byte sequences as their bytes. The fuel bounds the
 * struct nesting. *)
Definition memory_array_value_def:
  (memory_array_value env (fuel : num) (st : source_state) ty v =
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
                 (case memory_array_cells env fuel st element obj 0 obj.object_length of
                    INL vs => INL (TupleValue vs)
                  | INR c => INR c)
           | NONE => INR (InvalidCompletion "missing memory object"))
    | (StructT s, ReferenceValue (MemoryReference (HeapId id) 0 rty)) =>
        if rty ≠ ty then INR (InvalidCompletion "bad memory struct reference") else
        (case (lookup_struct env s, FLOOKUP st.heap id) of
           (SOME fields, SOME obj) =>
             if obj.object_type ≠ ty then
               INR (InvalidCompletion "bad memory struct reference")
             else if fuel = 0 then INR (InvalidCompletion "struct nesting")
             else
               (case memory_struct_cells env (fuel - 1) st (MAP SND fields) obj 0 of
                  INL vs => INL (TupleValue vs)
                | INR c => INR c)
         | _ => INR (InvalidCompletion "missing memory struct"))
    | (_, ReferenceValue r) =>
        (case byte_contents st r of
           INL bs => INL (ScalarValue (BytesValue bs))
         | INR c => INR c)
    | (_, ScalarValue _) => INL v
    | _ => INR (InvalidCompletion "bad memory array value")) ∧
  (memory_array_cells env fuel st element obj i n =
    if n = 0 then INL [] else
    case memory_array_value env fuel st element (memory_cell obj element i) of
      INR c => INR c
    | INL v =>
        case memory_array_cells env fuel st element obj (i + 1) (n - 1) of
          INL vs => INL (v :: vs)
        | INR c => INR c) ∧
  (memory_struct_cells env fuel st [] obj i = INL []) ∧
  (memory_struct_cells env fuel st (ty :: tys) obj i =
    case memory_array_value env fuel st ty (memory_cell obj ty i) of
      INR c => INR c
    | INL v =>
        case memory_struct_cells env fuel st tys obj (i + 1) of
          INL vs => INL (v :: vs)
        | INR c => INR c)
Termination
  WF_REL_TAC ‘inv_image ($< LEX $< LEX $<) (λx. case x of
    INL (env, fuel, st, ty, v) => (fuel, sol_type_size ty, 0)
  | INR (INL (env, fuel, st, element, obj, i, n)) => (fuel, sol_type_size element, n + 1)
  | INR (INR (env, fuel, st, tys, obj, i)) => (fuel, list_size sol_type_size tys, 1))’ >>
  rw[solidityASTTheory.sol_type_size_def, listTheory.list_size_def]
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
    | _ => INR (InvalidCompletion "bad storage byte copy")
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

val () = cv_auto_trans byte_cells_from_def;
val () = cv_auto_trans byte_cells_def;
val () = cv_auto_trans allocate_bytes_def;
val () = cv_auto_trans memory_byte_def;
val () = cv_auto_trans heap_bytes_def;
val () = cv_auto_trans memory_bytes_def;
val () = cv_auto_trans reference_bytes_def;
val () = cv_auto_trans navigate_memory_byte_def;


val () = cv_auto_trans default_elementary_def;
val () = cv_auto_trans memory_cell_def;
val () = cv_auto_trans read_memory_reference_def;
(* How cv's precondition presents a heap object record. *)
Theorem heap_object_literal:
  <| object_type := a; object_length := b; object_cells := c;
     object_address := d; object_padded := e |> = heap_object a b c d e
Proof
  simp[solidityStateTheory.heap_object_component_equality]
QED

val () = cv_auto_trans allocate_object_def;
val () = cv_auto_trans fill_object_def;
val zero_object_pre_def = cv_auto_trans_pre_rec
  "zero_object_pre zero_elements_pre zero_fields_pre" zero_object_def (
  WF_REL_TAC ‘inv_image ($< LEX $< LEX $<) (λx. case x of
    INL (env, fuel, ty, n, st) => (cv$c2n fuel, cv_size ty, 0)
  | INR (INL (env, fuel, element, i, m, cells, st)) =>
      (cv$c2n fuel, cv_size element, cv$c2n m + 1)
  | INR (INR (env, fuel, tys, i, cells, st)) => (cv$c2n fuel, cv_size tys, 1))’ >>
  cv_termination_tac
);

Theorem zero_object_pre[cv_pre]:
  (∀env fuel ty n st. zero_object_pre env fuel ty n st) ∧
  (∀env fuel element i m cells st. zero_elements_pre env fuel element i m cells st) ∧
  (∀env fuel tys i cells st. zero_fields_pre env fuel tys i cells st)
Proof
  ho_match_mp_tac zero_object_ind >> rpt strip_tac >>
  simp[Once zero_object_pre_def] >> rw[] >> gvs[]
QED
val () = cv_auto_trans default_memory_value_def;
val () = cv_auto_trans memory_array_length_def;
val () = cv_auto_trans memory_array_element_def;
val () = cv_auto_trans field_position_def;
val () = cv_auto_trans memory_struct_field_def;
val () = cv_auto_trans write_memory_element_def;
val () = cv_auto_trans write_memory_reference_def;

val () = cv_auto_trans byte_contents_def;
val memory_array_value_pre_def = cv_auto_trans_pre_rec
  "memory_array_value_pre memory_array_cells_pre memory_struct_cells_pre" memory_array_value_def (
  WF_REL_TAC ‘inv_image ($< LEX $< LEX $<) (λx. case x of
    INL (env, fuel, st, ty, v) => (cv$c2n fuel, cv_size ty, 0)
  | INR (INL (env, fuel, st, element, obj, i, n)) =>
      (cv$c2n fuel, cv_size element, cv$c2n n + 1)
  | INR (INR (env, fuel, st, tys, obj, i)) => (cv$c2n fuel, cv_size tys, 1))’ >>
  cv_termination_tac
);

Theorem memory_array_value_pre[cv_pre]:
  (∀env fuel st ty v. memory_array_value_pre env fuel st ty v) ∧
  (∀env fuel st element obj i n. memory_array_cells_pre env fuel st element obj i n) ∧
  (∀env fuel st tys obj i. memory_struct_cells_pre env fuel st tys obj i)
Proof
  ho_match_mp_tac memory_array_value_ind >> rpt strip_tac >>
  simp[Once memory_array_value_pre_def] >> rw[] >> gvs[]
QED

val () = cv_auto_trans copy_byte_contents_def;
val () = cv_auto_trans convert_byte_reference_def;
