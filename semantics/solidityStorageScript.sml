(* Concrete storage interfaces shared by execution and observation. *)
Theory solidityStorage
Ancestors
  solidityState solidityScalar vfmCompute keccak
Libs
  cv_transLib wordsLib intLib

Datatype:
  value_outcome = ValueOk runtime_value | ValueAbrupt source_completion
End

(* Storage *)

(* A value as the number held in its b storage bytes: integers in two's
 * complement, fixed bytes big-endian.
 *)
Definition stored_number_def:
  stored_number b s =
    case s of
      BoolValue v => SOME (if v then 1 else 0)
    | IntegerValue i => SOME (Num (wrap_integer F (8 * b) i))
    | AddressValue a => SOME (w2n a)
    | BytesValue bs => SOME (num_of_be_bytes bs)
    | _ => NONE
End

(* The value of type ty held as the number n < 256 ** storage_bytes ty. *)
Definition stored_value_def:
  stored_value ty (n : num) =
    case ty of
      BoolT => SOME (BoolValue (n ≠ 0))
    | UintT _ => SOME (IntegerValue (&n))
    | IntT w => SOME (IntegerValue (wrap_integer T w (&n)))
    | AddressT _ => SOME (AddressValue (n2w n))
    | FixedBytesT k => SOME (BytesValue (num_to_bytes k n))
    | _ => NONE
End

(* The bytes of a value of type ty at a byte offset from the low-order end of
 * a slot of an account. Reading keeps only those bytes, as the compiler's
 * storage cleanup does; writing replaces only them.
 *)
Definition read_storage_def:
  read_storage accounts addr slot offset ty =
    case storage_bytes ty of
      SOME b =>
        stored_value ty
          ((w2n (lookup_storage slot (lookup_account addr accounts).storage)
            DIV 2 ** (8 * offset)) MOD 2 ** (8 * b))
    | NONE => NONE
End

Definition write_storage_def:
  write_storage accounts addr slot offset ty s =
    case storage_bytes ty of
      NONE => NONE
    | SOME b =>
        case stored_number b s of
          NONE => NONE
        | SOME v =>
            let account = lookup_account addr accounts in
            let w = w2n (lookup_storage slot account.storage) in
            let lo = 2 ** (8 * offset) in
            let hi = 2 ** (8 * (offset + b)) in
            let w' = w DIV hi * hi + v MOD 2 ** (8 * b) * lo + w MOD lo in
            SOME (update_account addr
                    (account with storage :=
                       update_storage slot (n2w w') account.storage)
                    accounts)
End

(* A declaration's concrete location in the executing account. *)
Definition state_reference_def:
  state_reference env addr (AstId x) =
    case lookup_state_variable env (AstId x) of
      SOME v => SOME (StorageReference PersistentStorage addr
        v.state_slot v.state_offset v.state_type (LayoutId x))
    | NONE => NONE
End

(* Solidity mapping keys occupy one 32-byte word: integers are extended to
 * 256 bits, addresses and booleans are zero padded, bytesN are right padded.
 *)
Definition mapping_key_bytes_def:
  mapping_key_bytes key s =
    if ¬elementary_storage_type_ok key ∨ ¬elementary_scalar_has_type key s then NONE
    else case s of
      BytesValue bs => SOME (bs ++ REPLICATE (32 - LENGTH bs) 0w)
    | _ => OPTION_MAP (num_to_bytes 32) (stored_number 32 s)
End

Definition mapping_slot_def:
  mapping_slot key_bytes (slot : bytes32) : bytes32 =
    word_of_bytes_be (Keccak_256_w64 (key_bytes ++ num_to_bytes 32 (w2n slot)))
End

(* Short bytes share the root word with a low-byte length tag; long bytes
 * start at keccak256(root). Invalid length tags panic before any access. *)
Definition storage_byte_length_def:
  storage_byte_length accounts addr slot =
    let n = w2n (lookup_storage slot (lookup_account addr accounts).storage) in
    let long = (n MOD 2 = 1) in
    let length = if long then n DIV 2 else (n DIV 2) MOD 128 in
    if long = (length < 32) then INR (PanicCompletion 34) else INL length
End

Definition storage_byte_location_def:
  storage_byte_location slot (length : num) (i : num) =
    if length < 32 then (slot, 31 - i)
    else (mapping_slot [] slot + n2w (i DIV 32), 31 - i MOD 32)
End

Definition navigate_storage_byte_def:
  navigate_storage_byte accounts addr slot layout i =
    case storage_byte_length accounts addr slot of
      INR c => ValueAbrupt c
    | INL length =>
        if i < 0 ∨ &length ≤ i then ValueAbrupt (PanicCompletion 50) else
        let (data_slot, offset) = storage_byte_location slot length (Num i) in
        ValueOk (ReferenceValue (StorageReference PersistentStorage addr
          data_slot offset (FixedBytesT 1) layout))
End

Definition storage_byte_range_def:
  (storage_byte_range accounts addr slot length i 0 = []) ∧
  (storage_byte_range accounts addr slot length i (SUC n) =
    let (data_slot, offset) = storage_byte_location slot length i in
    let data = w2n (lookup_storage data_slot (lookup_account addr accounts).storage) in
    (n2w (data DIV 2 ** (8 * offset)) : byte) ::
      storage_byte_range accounts addr slot length (i + 1) n)
End

Definition storage_byte_contents_def:
  storage_byte_contents accounts r =
    case r of
      StorageReference PersistentStorage addr slot 0 ty _ =>
        if ¬byte_sequence_type ty then INR (InvalidCompletion "not storage bytes")
        else (case storage_byte_length accounts addr slot of
          INR c => INR c
        | INL length =>
            if 2 ** 64 ≤ length then INR (PanicCompletion 65)
            else INL (storage_byte_range accounts addr slot length 0 length))
    | _ => INR (InvalidCompletion "not storage bytes")
End

Definition set_storage_word_def:
  set_storage_word accounts addr slot value =
    let account = lookup_account addr accounts in
    update_account addr
      (account with storage := update_storage slot value account.storage) accounts
End

Definition clear_byte_slots_def:
  (clear_byte_slots 0 accounts addr slot = accounts) ∧
  (clear_byte_slots (SUC n) accounts addr slot =
    clear_byte_slots n (set_storage_word accounts addr slot 0w) addr (slot + 1w))
End

Definition store_byte_chunks_def:
  (store_byte_chunks 0 accounts addr slot (bs : byte list) = accounts) ∧
  (store_byte_chunks (SUC n) accounts addr slot bs =
    let chunk = TAKE 32 bs in
    let value = n2w (num_of_be_bytes (chunk ++ REPLICATE (32 - LENGTH chunk) 0w)) in
    store_byte_chunks n (set_storage_word accounts addr slot value)
      addr (slot + 1w) (DROP 32 bs))
End

(* Memory and calldata sources are independent of the destination storage. *)
Definition store_storage_bytes_def:
  store_storage_bytes accounts r (bs : byte list) static =
    case r of
      StorageReference PersistentStorage addr slot 0 ty _ =>
        if ¬byte_sequence_type ty then INR (InvalidCompletion "not storage bytes")
        else if 2 ** 64 ≤ LENGTH bs then INR (PanicCompletion 65)
        else (case storage_byte_length accounts addr slot of
          INR c => INR c
        | INL old_length =>
            if static then INR (InvalidCompletion "byte copy in static frame") else
            let length = LENGTH bs in
            let old_slots = if old_length < 32 then 0 else (old_length + 31) DIV 32 in
            let new_slots = if length < 32 then 0 else (length + 31) DIV 32 in
            let data_slot = mapping_slot [] slot in
            let cleared = clear_byte_slots (old_slots - new_slots) accounts addr
                            (data_slot + n2w new_slots) in
            if length < 32 then
              INL (set_storage_word cleared addr slot
                (n2w (num_of_be_bytes (bs ++ REPLICATE (31 - length) 0w ++
                    [n2w (2 * length)]))))
            else
              INL (set_storage_word
                (store_byte_chunks new_slots cleared addr data_slot bs)
                addr slot (n2w (2 * length + 1))))
    | _ => INR (InvalidCompletion "not storage bytes")
End

(* Storage copies read each source word after clearing obsolete destination
 * slots, and after earlier destination writes. Array indices can alias these
 * locations without any hash collision. *)
Definition copy_storage_byte_chunks_def:
  (copy_storage_byte_chunks 0 remaining accounts src_addr src_slot dst_addr dst_slot = accounts) ∧
  (copy_storage_byte_chunks (SUC n) remaining accounts src_addr src_slot dst_addr dst_slot =
    let used = MIN 32 remaining in
    let shift = 2 ** (8 * (32 - used)) in
    let value = w2n (lookup_storage src_slot (lookup_account src_addr accounts).storage) in
    let updated = set_storage_word accounts dst_addr dst_slot (n2w ((value DIV shift) * shift)) in
    copy_storage_byte_chunks n (remaining - used) updated
      src_addr (src_slot + 1w) dst_addr (dst_slot + 1w))
End

Definition copy_storage_bytes_def:
  copy_storage_bytes accounts src dst static =
    case (src, dst) of
      (StorageReference PersistentStorage src_addr src_slot 0 src_ty _,
       StorageReference PersistentStorage dst_addr dst_slot 0 dst_ty _) =>
        if ¬byte_sequence_type src_ty ∨ ¬byte_sequence_type dst_ty then
          INR (InvalidCompletion "not storage bytes")
        else if src_addr = dst_addr ∧ src_slot = dst_slot then INL accounts
        else (case storage_byte_length accounts src_addr src_slot of
          INR c => INR c
        | INL length =>
            if 2 ** 64 ≤ length then INR (PanicCompletion 65) else
            case storage_byte_length accounts dst_addr dst_slot of
              INR c => INR c
            | INL old_length =>
                if static then INR (InvalidCompletion "byte copy in static frame") else
                let old_slots = if old_length < 32 then 0 else (old_length + 31) DIV 32 in
                let new_slots = if length < 32 then 0 else (length + 31) DIV 32 in
                let data_slot = mapping_slot [] dst_slot in
                let cleared = clear_byte_slots (old_slots - new_slots) accounts dst_addr
                                (data_slot + n2w new_slots) in
                if length < 32 then
                  let value = if length = 0 then 0 else
                    w2n (lookup_storage src_slot (lookup_account src_addr cleared).storage) in
                  let shift = 2 ** (8 * (32 - length)) in
                  INL (set_storage_word cleared dst_addr dst_slot
                    (n2w ((value DIV shift) * shift + 2 * length)))
                else
                  INL (set_storage_word
                    (copy_storage_byte_chunks new_slots length cleared src_addr
                      (mapping_slot [] src_slot) dst_addr data_slot)
                    dst_addr dst_slot (n2w (2 * length + 1))))
    | _ => INR (InvalidCompletion "not storage bytes")
End

(* The slot and byte offset of element i of an array whose data starts at
 * data: scalars pack from the low-order end without straddling slots, other
 * elements start on a fresh slot. Slot arithmetic wraps at the word width. *)
Definition storage_element_location_def:
  storage_element_location env (data : bytes32) element (i : num) =
    case storage_bytes element of
      SOME b =>
        if b = 0 ∨ 32 < b then NONE else
        let per_slot = 32 DIV b in
        SOME (n2w (w2n data + i DIV per_slot) : bytes32, b * (i MOD per_slot))
    | NONE =>
        OPTION_MAP (λslots. (n2w (w2n data + i * slots) : bytes32, 0))
          (fixed_storage_slots env element)
End

(* One new index from a captured fixed-array reference. The caller has already
 * evaluated the index. *)
Definition fixed_array_element_def:
  fixed_array_element env addr slot element length layout (i : int) =
    if i < 0 ∨ &length ≤ i then ValueAbrupt (PanicCompletion 50) else
    case storage_element_location env slot element (Num i) of
      SOME (s, offset) =>
        ValueOk (ReferenceValue
          (StorageReference PersistentStorage addr s offset element layout))
    | NONE => ValueAbrupt (InvalidCompletion "bad array element type")
End

(* The length of a storage array at slot and the slot its elements start
 * at: a fixed-size array's own slot, a dynamic one's keccak256(slot). *)
Definition storage_array_data_def:
  storage_array_data accounts addr slot ty =
    case ty of
      ArrayT _ (SOME n) => (n, slot)
    | _ => (w2n (lookup_storage slot (lookup_account addr accounts).storage),
            mapping_slot [] slot)
End

(* The value of a storage array, as a copy reads it: arrays as the tuple of
 * their elements, byte sequences as their bytes and scalars cleaned. A length
 * of 2^64 or more panics with 0x41, as the compiler's copies do. *)
Definition storage_array_value_def:
  (storage_array_value env accounts addr slot ty =
    if byte_sequence_type ty then
      (case storage_byte_length accounts addr slot of
         INR c => INR c
       | INL length =>
           if 2 ** 64 ≤ length then INR (PanicCompletion 65)
           else INL (ScalarValue (BytesValue
                  (storage_byte_range accounts addr slot length 0 length))))
    else case ty of
      ArrayT element l =>
        (case storage_array_data accounts addr slot ty of
           (length, data) =>
             if 2 ** 64 ≤ length then INR (PanicCompletion 65) else
             case storage_array_elements env accounts addr data element 0 length of
               INL vs => INL (TupleValue vs)
             | INR c => INR c)
    | _ => INR (InvalidCompletion "bad storage array type")) ∧
  (storage_array_elements env accounts addr data element i n =
    if n = 0 then INL [] else
    case storage_element_location env data element i of
      NONE => INR (InvalidCompletion "bad array element type")
    | SOME (s, offset) =>
        let value =
          if is_elementary_type element then
            (case read_storage accounts addr s offset element of
               SOME v => INL (ScalarValue v)
             | NONE => INR (InvalidCompletion "bad storage read"))
          else storage_array_value env accounts addr s element in
        case value of
          INR c => INR c
        | INL v =>
            case storage_array_elements env accounts addr data element (i + 1) (n - 1) of
              INL vs => INL (v :: vs)
            | INR c => INR c)
Termination
  WF_REL_TAC ‘inv_image ($< LEX $<) (λx. case x of
    INL (env, accounts, addr, slot, ty) => (sol_type_size ty, 0)
  | INR (env, accounts, addr, data, element, i, n) => (sol_type_size element, n + 1))’ >>
  rw[solidityASTTheory.sol_type_size_def]
End

(* Storage a storage array or byte sequence occupies, cleared as the
 * compiler's delete does: the length, every element, and a long byte
 * sequence's data. A dynamic length of 2^64 or more cannot be cleared within
 * any gas limit. *)
Definition clear_storage_value_def:
  (clear_storage_value env accounts addr slot ty =
    if byte_sequence_type ty then
      (case storage_byte_length accounts addr slot of
         INR c => INR c
       | INL length =>
           (* An empty one is left as it is, as resizing it to zero does. *)
           if length = 0 then INL accounts else
           let slots = if length < 32 then 0 else (length + 31) DIV 32 in
           INL (set_storage_word
                  (clear_byte_slots slots accounts addr (mapping_slot [] slot))
                  addr slot 0w))
    else case ty of
      ArrayT element l =>
        (case storage_array_data accounts addr slot ty of
           (length, data) =>
             if 2 ** 64 ≤ length then INR FuelExhausted else
             let accounts1 = if l = NONE then set_storage_word accounts addr slot 0w
                             else accounts in
             if is_elementary_type element then
               (case fixed_storage_slots env (ArrayT element (SOME length)) of
                  SOME slots => INL (clear_byte_slots slots accounts1 addr data)
                | NONE => INL accounts1)
             else clear_storage_elements env accounts1 addr data element 0 length)
    | _ => INR (InvalidCompletion "bad storage array type")) ∧
  (clear_storage_elements env accounts addr data element i n =
    if n = 0 then INL accounts else
    case storage_element_location env data element i of
      NONE => INR (InvalidCompletion "bad array element type")
    | SOME (s, _) =>
        case clear_storage_value env accounts addr s element of
          INR c => INR c
        | INL accounts' =>
            clear_storage_elements env accounts' addr data element (i + 1) (n - 1))
Termination
  WF_REL_TAC ‘inv_image ($< LEX $<) (λx. case x of
    INL (env, accounts, addr, slot, ty) => (sol_type_size ty, 0)
  | INR (env, accounts, addr, data, element, i, n) => (sol_type_size element, n + 1))’ >>
  rw[solidityASTTheory.sol_type_size_def]
End

(* Writes the value of a src array into cleared storage of type dst, each
 * scalar converted as an implicit conversion does. Past the cleared length,
 * slots may hold stale data, which the compiler's copy overwrites: the slots
 * of scalar elements are zeroed first, as the compiler writes each packed
 * slot as a whole word built from zero, and each nested array or byte
 * sequence is first cleared, as resizing it does. *)
Definition store_storage_value_def:
  (store_storage_value env accounts addr slot src dst v =
    if byte_sequence_type dst then
      (case v of
         ScalarValue (BytesValue bs) =>
           let length = LENGTH bs in
           if length < 32 then
             INL (set_storage_word accounts addr slot
               (n2w (num_of_be_bytes (bs ++ REPLICATE (31 - length) 0w ++
                  [n2w (2 * length)]))))
           else
             INL (set_storage_word
               (store_byte_chunks ((length + 31) DIV 32) accounts addr
                  (mapping_slot [] slot) bs)
               addr slot (n2w (2 * length + 1)))
       | _ => INR (InvalidCompletion "bad stored byte sequence"))
    else case (src, dst, v) of
      (ArrayT e _, ArrayT e' l, TupleValue vs) =>
        let accounts1 = if l = NONE then
                          set_storage_word accounts addr slot (n2w (LENGTH vs))
                        else accounts in
        let data = if l = NONE then mapping_slot [] slot else slot in
        let accounts2 =
          if is_elementary_type e' then
            (case fixed_storage_slots env (ArrayT e' (SOME (LENGTH vs))) of
               SOME slots => clear_byte_slots slots accounts1 addr data
             | NONE => accounts1)
          else accounts1 in
        store_storage_elements env accounts2 addr data e e' 0 vs
    | _ => INR (InvalidCompletion "bad stored array")) ∧
  (store_storage_elements env accounts addr data src dst i [] = INL accounts) ∧
  (store_storage_elements env accounts addr data src dst i (v :: vs) =
    case storage_element_location env data dst i of
      NONE => INR (InvalidCompletion "bad array element type")
    | SOME (s, offset) =>
        let stored =
          if is_elementary_type dst then
            (case v of
               ScalarValue x =>
                 (case eval_conversion env src dst x of
                    ScalarOk y =>
                      (case write_storage accounts addr s offset dst y of
                         SOME accounts' => INL accounts'
                       | NONE => INR (InvalidCompletion "bad storage write"))
                  | _ => INR (InvalidCompletion "bad element conversion"))
             | _ => INR (InvalidCompletion "bad stored element"))
          else
            (case clear_storage_value env accounts addr s dst of
               INR c => INR c
             | INL cleared => store_storage_value env cleared addr s src dst v) in
        case stored of
          INR c => INR c
        | INL accounts' =>
            store_storage_elements env accounts' addr data src dst (i + 1) vs)
Termination
  WF_REL_TAC ‘measure (λx. case x of
    INL (env, accounts, addr, slot, src, dst, v) => runtime_value_size v
  | INR (env, accounts, addr, data, src, dst, i, vs) => list_size runtime_value_size vs)’ >>
  rw[solidityCoreTheory.runtime_value_size_def, listTheory.list_size_def]
End

(* A copy of the value of a src array into the storage array dst refers to:
 * its old contents cleared, then the value written. The value is read before
 * any write, so a copy from the destination itself leaves it unchanged. *)
Definition copy_to_storage_def:
  copy_to_storage env accounts src v dst static =
    case dst of
      StorageReference PersistentStorage addr slot 0 ty _ =>
        if static then INR (InvalidCompletion "array copy in static frame") else
        (case clear_storage_value env accounts addr slot ty of
           INR c => INR c
         | INL cleared => store_storage_value env cleared addr slot src ty v)
    | _ => INR (InvalidCompletion "bad storage array reference")
End

(* Navigation consumes already evaluated atoms and returns a concrete location.
 * A nested mapping starts at the preceding mapping's hashed slot.
 *)
Definition navigate_storage_def:
  navigate_storage env accounts r s =
    case r of
      StorageReference PersistentStorage addr slot 0 (MappingT key value) layout =>
        (case mapping_key_bytes key s of
           SOME bs =>
             ValueOk (ReferenceValue
               (StorageReference PersistentStorage addr (mapping_slot bs slot)
                  0 value layout))
         | NONE => ValueAbrupt (InvalidCompletion "bad mapping key"))
    | StorageReference PersistentStorage addr slot 0
        (ArrayT element (SOME length)) layout =>
        (case s of
           IntegerValue i => fixed_array_element env addr slot element length layout i
         | _ => ValueAbrupt (InvalidCompletion "bad array index"))
    | StorageReference PersistentStorage addr slot 0 (ArrayT element NONE) layout =>
        (case s of
           IntegerValue i =>
             fixed_array_element env addr (mapping_slot [] slot) element
               (w2n (lookup_storage slot (lookup_account addr accounts).storage)) layout i
         | _ => ValueAbrupt (InvalidCompletion "bad array index"))
    | StorageReference PersistentStorage addr slot 0 BytesT layout =>
        (case s of
           IntegerValue i => navigate_storage_byte accounts addr slot layout i
         | _ => ValueAbrupt (InvalidCompletion "bad byte index"))
    | _ => ValueAbrupt (InvalidCompletion "unsupported storage navigation")
End

(* Access and navigation consume concrete references, independently of atoms,
 * bindings, scopes and evaluator control flow.
 *)
Definition read_storage_reference_def:
  read_storage_reference accounts ty r =
    case r of
      StorageReference PersistentStorage addr slot offset rty _ =>
        if rty ≠ ty then ValueAbrupt (InvalidCompletion "bad read type")
        else if offset = 0 ∧ memory_object_type ty then ValueOk (ReferenceValue r)
        else (case read_storage accounts addr slot offset ty of
                SOME scalar => ValueOk (ScalarValue scalar)
              | NONE => ValueAbrupt (InvalidCompletion "bad storage read"))
    | _ => ValueAbrupt (InvalidCompletion "bad storage reference")
End

Definition storage_array_length_def:
  storage_array_length accounts r =
    case r of
      StorageReference PersistentStorage addr slot 0 (ArrayT _ NONE) _ =>
        ValueOk (ScalarValue (IntegerValue
          (&(w2n (lookup_storage slot (lookup_account addr accounts).storage)))))
    | StorageReference PersistentStorage addr slot 0 ty _ =>
        if ¬byte_sequence_type ty then
          ValueAbrupt (InvalidCompletion "bad byte sequence length")
        else (case storage_byte_length accounts addr slot of
          INL length => ValueOk (ScalarValue (IntegerValue (&length)))
        | INR c => ValueAbrupt c)
    | _ => ValueAbrupt (InvalidCompletion "bad dynamic array reference")
End

Definition navigate_storage_field_def:
  navigate_storage_field env r member_id =
    case r of
      StorageReference PersistentStorage addr slot 0 (StructT id) layout =>
        (case lookup_struct_layout env id of
           SOME s =>
             (case ALOOKUP (MAP (λv. (v.state_id, v)) s.struct_fields) member_id of
                SOME v => ValueOk (ReferenceValue
                  (StorageReference PersistentStorage addr (slot + v.state_slot)
                    v.state_offset v.state_type layout))
              | NONE => ValueAbrupt (InvalidCompletion "unknown struct field"))
         | NONE => ValueAbrupt (InvalidCompletion "missing struct layout"))
    | _ => ValueAbrupt (InvalidCompletion "bad struct reference")
End

val () = cv_auto_trans read_storage_def;
val () = cv_auto_trans write_storage_def;
val () = cv_auto_trans state_reference_def;
val () = cv_auto_trans storage_byte_length_def;
val () = cv_auto_trans storage_byte_location_def;
val () = cv_auto_trans navigate_storage_byte_def;
val () = cv_auto_trans storage_byte_range_def;
val () = cv_auto_trans storage_byte_contents_def;
val () = cv_auto_trans set_storage_word_def;
val () = cv_auto_trans clear_byte_slots_def;
val () = cv_auto_trans store_byte_chunks_def;
val () = cv_auto_trans store_storage_bytes_def;
val () = cv_auto_trans copy_storage_byte_chunks_def;
val () = cv_auto_trans copy_storage_bytes_def;
val () = cv_auto_trans storage_element_location_def;
val () = cv_auto_trans fixed_array_element_def;
val () = cv_auto_trans storage_array_data_def;

val storage_array_value_pre_def = cv_auto_trans_pre_rec
  "storage_array_value_pre storage_array_elements_pre" storage_array_value_def (
  WF_REL_TAC ‘inv_image ($< LEX $<) (λx. case x of
    INL (env, accounts, addr, slot, ty) => (cv_size ty, 0)
  | INR (env, accounts, addr, data, element, i, n) => (cv_size element, cv$c2n n + 1))’ >>
  cv_termination_tac
);

Theorem storage_array_value_pre[cv_pre]:
  (∀env accounts addr slot ty. storage_array_value_pre env accounts addr slot ty) ∧
  (∀env accounts addr data element i n.
     storage_array_elements_pre env accounts addr data element i n)
Proof
  ho_match_mp_tac storage_array_value_ind >> rpt strip_tac >>
  simp[Once storage_array_value_pre_def] >> rw[] >> gvs[]
QED

val clear_storage_value_pre_def = cv_auto_trans_pre_rec
  "clear_storage_value_pre clear_storage_elements_pre" clear_storage_value_def (
  WF_REL_TAC ‘inv_image ($< LEX $<) (λx. case x of
    INL (env, accounts, addr, slot, ty) => (cv_size ty, 0)
  | INR (env, accounts, addr, data, element, i, n) => (cv_size element, cv$c2n n + 1))’ >>
  cv_termination_tac
);

Theorem clear_storage_value_pre[cv_pre]:
  (∀env accounts addr slot ty. clear_storage_value_pre env accounts addr slot ty) ∧
  (∀env accounts addr data element i n.
     clear_storage_elements_pre env accounts addr data element i n)
Proof
  ho_match_mp_tac clear_storage_value_ind >> rpt strip_tac >>
  simp[Once clear_storage_value_pre_def] >> rw[] >> gvs[]
QED

val store_storage_value_pre_def = cv_auto_trans_pre_rec
  "store_storage_value_pre store_storage_elements_pre" store_storage_value_def (
  WF_REL_TAC ‘measure (λx. case x of
    INL (env, accounts, addr, slot, src, dst, v) => cv_size v
  | INR (env, accounts, addr, data, src, dst, i, vs) => cv_size vs)’ >>
  cv_termination_tac
);

Theorem store_storage_value_pre[cv_pre]:
  (∀env accounts addr slot src dst v.
     store_storage_value_pre env accounts addr slot src dst v) ∧
  (∀env accounts addr data src dst i vs.
     store_storage_elements_pre env accounts addr data src dst i vs)
Proof
  ho_match_mp_tac store_storage_value_ind >> rpt strip_tac >>
  simp[Once store_storage_value_pre_def] >> rw[] >> gvs[]
QED

val () = cv_auto_trans copy_to_storage_def;
val () = cv_auto_trans navigate_storage_def;
val () = cv_auto_trans read_storage_reference_def;
val () = cv_auto_trans storage_array_length_def;
val () = cv_auto_trans navigate_storage_field_def;
