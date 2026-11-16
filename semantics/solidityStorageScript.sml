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
      BoolT => if n < 2 then SOME (BoolValue (n = 1)) else NONE
    | UintT _ => SOME (IntegerValue (&n))
    | IntT w => SOME (IntegerValue (wrap_integer T w (&n)))
    | AddressT _ => SOME (AddressValue (n2w n))
    | FixedBytesT k => SOME (BytesValue (num_to_bytes k n))
    (* read_storage_word checks enum membership against the environment *)
    | EnumT _ => SOME (IntegerValue (&n))
    | _ => NONE
End

(* The bytes of a value of type ty at a byte offset from the low-order end of
 * a slot of an account. Reading keeps only those bytes, as the compiler's
 * storage cleanup does; writing replaces only them.
 *)
Definition read_storage_word_def:
  read_storage_word env (word : bytes32) offset ty =
    case storage_bytes ty of
      SOME b =>
        (case stored_value ty
          ((w2n word DIV 2 ** (8 * offset)) MOD 2 ** (8 * b)) of
           SOME v => if scalar_has_type env ty v then SOME v else NONE
         | NONE => NONE)
    | NONE => NONE
End

Definition read_storage_def:
  read_storage env accounts addr slot offset ty =
    read_storage_word env
      (lookup_storage slot (lookup_account addr accounts).storage) offset ty
End

Definition write_storage_word_def:
  write_storage_word (word : bytes32) offset ty s =
    case storage_bytes ty of
      NONE => NONE
    | SOME b =>
        case stored_number b s of
          NONE => NONE
        | SOME v =>
            let w = w2n word in
            let lo = 2 ** (8 * offset) in
            let hi = 2 ** (8 * (offset + b)) in
            let w' = w DIV hi * hi + v MOD 2 ** (8 * b) * lo + w MOD lo in
            SOME (n2w w' : bytes32)
End

Definition write_storage_def:
  write_storage accounts addr slot offset ty s =
    let account = lookup_account addr accounts in
    OPTION_MAP (λword. update_account addr
      (account with storage := update_storage slot word account.storage) accounts)
      (write_storage_word (lookup_storage slot account.storage) offset ty s)
End

(* A declaration's concrete location in the executing account. *)
Definition state_reference_def:
  state_reference env addr (AstId x) =
    case lookup_state_variable env (AstId x) of
      SOME v => SOME (StorageReference v.state_backend addr
        v.state_slot v.state_offset v.state_type (LayoutId x))
    | NONE => NONE
End

(* Solidity mapping keys occupy one 32-byte word: integers are extended to
 * 256 bits, addresses and booleans are zero padded, bytesN are right padded.
 *)
Definition mapping_key_bytes_def:
  mapping_key_bytes key s =
    if byte_sequence_type key then (case s of BytesValue bs => SOME bs | _ => NONE)
    else if ¬elementary_storage_type_ok key ∨ ¬elementary_scalar_has_type key s then NONE
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

(* Replace a byte sequence, clearing only obsolete long-data slots. *)
Definition replace_storage_bytes_def:
  replace_storage_bytes accounts addr slot (bs : byte list) static =
    if 2 ** 64 ≤ LENGTH bs then INR (PanicCompletion 65)
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
End

(* Memory and calldata sources are independent of the destination storage. *)
Definition store_storage_bytes_def:
  store_storage_bytes accounts r (bs : byte list) static =
    case r of
      StorageReference PersistentStorage addr slot 0 ty _ =>
        if ¬byte_sequence_type ty then INR (InvalidCompletion "not storage bytes")
        else replace_storage_bytes accounts addr slot bs static
    | _ => INR (InvalidCompletion "not storage bytes")
End

(* The first k bytes of a word, the rest zeroed. *)
Definition word_prefix_def:
  word_prefix (w : bytes32) k = w && ¬(¬0w >>> (8 * k))
End

(* The length update of push(b) as solc 0.8.37 emits it, which push(b) then
 * follows with a write of b at the returned location: a short sequence's
 * length tag rises by 2; at 31 bytes the root word, its tag byte cleared,
 * moves to the data area; a long sequence's length rises by one. solc's
 * push() also clears a short root word past the new length; its own writes
 * keep those bytes zero, so push() shares this update. *)
Definition push_storage_bytes_def:
  push_storage_bytes accounts addr slot =
    case storage_byte_length accounts addr slot of
      INR c => INR c
    | INL length =>
        if 2 ** 64 ≤ length then INR (PanicCompletion 65) else
        let root = lookup_storage slot (lookup_account addr accounts).storage in
        let accounts' =
          if length < 31 then set_storage_word accounts addr slot (root + 2w)
          else if length = 31 then
            set_storage_word
              (set_storage_word accounts addr (mapping_slot [] slot) (word_prefix root 31))
              addr slot 65w
          else set_storage_word accounts addr slot (n2w (2 * (length + 1) + 1)) in
        INL (accounts', storage_byte_location slot (length + 1) length)
End

(* pop() as solc 0.8.37 emits it: a sequence of at most 32 bytes keeps its
 * first length - 1 bytes in a short root word, clearing the data area's
 * first word at 32; a longer one clears its last byte and updates its
 * length. *)
Definition pop_storage_bytes_def:
  pop_storage_bytes accounts addr slot =
    case storage_byte_length accounts addr slot of
      INR c => INR c
    | INL length =>
        if length = 0 then INR (PanicCompletion 49) else
        let storage = (lookup_account addr accounts).storage in
        let data_slot = mapping_slot [] slot in
        if length = 32 then
          INL (set_storage_word
            (set_storage_word accounts addr slot
               (word_prefix (lookup_storage data_slot storage) 31 + 62w))
            addr data_slot 0w)
        else if length < 32 then
          INL (set_storage_word accounts addr slot
            (word_prefix (lookup_storage slot storage) (length - 1) +
             n2w (2 * (length - 1))))
        else
          let (byte_slot, offset) = storage_byte_location slot length (length - 1) in
          let cleared = set_storage_word accounts addr byte_slot
                (lookup_storage byte_slot storage && ¬(255w << (8 * offset))) in
          INL (set_storage_word cleared addr slot (n2w (2 * (length - 1) + 1)))
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

(* The value of a storage array or struct, as a copy reads it: arrays as the
 * tuple of their elements, structs as the tuple of their fields in
 * declaration order, byte sequences as their bytes and canonical scalars. A
 * length of 2^64 or more panics with 0x41, as the compiler's copies do. The
 * fuel bounds the struct nesting. *)
Definition storage_array_value_def:
  (storage_array_value env (fuel : num) accounts addr slot ty =
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
             case storage_array_elements env fuel accounts addr data element 0 length of
               INL vs => INL (TupleValue vs)
             | INR c => INR c)
    | StructT s =>
        (case (lookup_struct env s, lookup_struct_layout env s) of
           (SOME fields, SOME layout) =>
             if fuel = 0 then INR (InvalidCompletion "struct nesting") else
             (case storage_struct_fields env (fuel - 1) accounts addr slot
                     layout.struct_fields fields of
                INL vs => INL (TupleValue vs)
              | INR c => INR c)
         | _ => INR (InvalidCompletion "missing struct layout"))
    | _ => INR (InvalidCompletion "bad storage array type")) ∧
  (storage_array_elements env fuel accounts addr data element i n =
    if n = 0 then INL [] else
    case storage_element_location env data element i of
      NONE => INR (InvalidCompletion "bad array element type")
    | SOME (s, offset) =>
        let value =
          if is_stored_scalar_type element then
            (case read_storage env accounts addr s offset element of
               SOME v => INL (ScalarValue v)
             | NONE => INR (InvalidCompletion "bad storage read"))
          else storage_array_value env fuel accounts addr s element in
        case value of
          INR c => INR c
        | INL v =>
            case storage_array_elements env fuel accounts addr data element (i + 1) (n - 1) of
              INL vs => INL (v :: vs)
            | INR c => INR c) ∧
  (storage_struct_fields env fuel accounts addr slot layout [] = INL []) ∧
  (storage_struct_fields env fuel accounts addr slot layout ((f, ty) :: fields) =
    case ALOOKUP (MAP (λv. (v.state_id, v)) layout) f of
      NONE => INR (InvalidCompletion "missing field layout")
    | SOME v =>
        let s = slot + v.state_slot in
        let value =
          if is_stored_scalar_type ty then
            (case read_storage env accounts addr s v.state_offset ty of
               SOME x => INL (ScalarValue x)
             | NONE => INR (InvalidCompletion "bad storage read"))
          else storage_array_value env fuel accounts addr s ty in
        case value of
          INR c => INR c
        | INL x =>
            case storage_struct_fields env fuel accounts addr slot layout fields of
              INL xs => INL (x :: xs)
            | INR c => INR c)
Termination
  WF_REL_TAC ‘inv_image ($< LEX $< LEX $<) (λx. case x of
    INL (env, fuel, accounts, addr, slot, ty) => (fuel, sol_type_size ty, 0)
  | INR (INL (env, fuel, accounts, addr, data, element, i, n)) =>
      (fuel, sol_type_size element, n + 1)
  | INR (INR (env, fuel, accounts, addr, slot, layout, fields)) =>
      (fuel, list_size (sol_type_size o SND) fields, 1))’ >>
  rw[solidityASTTheory.sol_type_size_def, listTheory.list_size_def]
End

(* Storage a storage array, struct or byte sequence occupies, cleared as the
 * compiler's delete does: the length, every element, a long byte sequence's
 * data, and each field of a struct but a mapping. Struct scalar fields
 * clear their whole slots; a directly targeted scalar clears only its bytes.
 * A dynamic length of 2^64 or more cannot be cleared within any gas
 * limit. The fuel bounds the struct nesting. *)
Definition clear_storage_value_def:
  (clear_storage_value env (fuel : num) accounts addr slot offset ty =
    if is_stored_scalar_type ty then
      (case write_storage accounts addr slot offset ty (IntegerValue 0) of
         SOME accounts' => INL accounts'
       | NONE => INR (InvalidCompletion "bad storage clear"))
    else if offset ≠ 0 then INR (InvalidCompletion "unaligned storage clear")
    else if byte_sequence_type ty then
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
             if is_stored_scalar_type element then
               (case fixed_storage_slots env (ArrayT element (SOME length)) of
                  SOME slots => INL (clear_byte_slots slots accounts1 addr data)
                | NONE => INL accounts1)
             else clear_storage_elements env fuel accounts1 addr data element 0 length)
    | StructT s =>
        (case (lookup_struct env s, lookup_struct_layout env s) of
           (SOME fields, SOME layout) =>
             if fuel = 0 then INR FuelExhausted else
             clear_storage_fields env (fuel - 1) accounts addr slot layout.struct_fields fields
         | _ => INR (InvalidCompletion "missing struct layout"))
    | MappingT _ _ => INL accounts
    | _ => INR (InvalidCompletion "bad storage clear type")) ∧
  (clear_storage_elements env fuel accounts addr data element i n =
    if n = 0 then INL accounts else
    case storage_element_location env data element i of
      NONE => INR (InvalidCompletion "bad array element type")
    | SOME (s, offset) =>
        case clear_storage_value env fuel accounts addr s offset element of
          INR c => INR c
        | INL accounts' =>
            clear_storage_elements env fuel accounts' addr data element (i + 1) (n - 1)) ∧
  (clear_storage_fields env fuel accounts addr slot layout [] = INL accounts) ∧
  (clear_storage_fields env fuel accounts addr slot layout ((f, ty) :: fields) =
    case ALOOKUP (MAP (λv. (v.state_id, v)) layout) f of
      NONE => INR (InvalidCompletion "missing field layout")
    | SOME v =>
        let s = slot + v.state_slot in
        let cleared =
          if is_stored_scalar_type ty then INL (set_storage_word accounts addr s 0w)
          else clear_storage_value env fuel accounts addr s v.state_offset ty in
        case cleared of
          INR c => INR c
        | INL accounts' =>
            clear_storage_fields env fuel accounts' addr slot layout fields)
Termination
  WF_REL_TAC ‘inv_image ($< LEX $< LEX $<) (λx. case x of
    INL (env, fuel, accounts, addr, slot, offset, ty) => (fuel, sol_type_size ty, 0)
  | INR (INL (env, fuel, accounts, addr, data, element, i, n)) =>
      (fuel, sol_type_size element, n + 1)
  | INR (INR (env, fuel, accounts, addr, slot, layout, fields)) =>
      (fuel, list_size (sol_type_size o SND) fields, 1))’ >>
  rw[solidityASTTheory.sol_type_size_def, listTheory.list_size_def]
End

Theorem clear_storage_fuel_stable:
  (∀env fuel accounts addr slot offset ty m.
     clear_storage_value env fuel accounts addr slot offset ty ≠ INR FuelExhausted ∧
     fuel ≤ m ⇒
     clear_storage_value env m accounts addr slot offset ty =
       clear_storage_value env fuel accounts addr slot offset ty) ∧
  (∀env fuel accounts addr data element i n m.
     clear_storage_elements env fuel accounts addr data element i n ≠ INR FuelExhausted ∧
     fuel ≤ m ⇒
     clear_storage_elements env m accounts addr data element i n =
       clear_storage_elements env fuel accounts addr data element i n) ∧
  (∀env fuel accounts addr slot layout fields m.
     clear_storage_fields env fuel accounts addr slot layout fields ≠ INR FuelExhausted ∧
     fuel ≤ m ⇒
     clear_storage_fields env m accounts addr slot layout fields =
       clear_storage_fields env fuel accounts addr slot layout fields)
Proof
  ho_match_mp_tac clear_storage_value_ind >> rpt strip_tac >>
  qpat_x_assum ‘_ <> INR FuelExhausted’ mp_tac
  >~ [‘clear_storage_value env m accounts addr slot offset ty = _’] >-
   (Cases_on ‘is_stored_scalar_type ty’
    >- (once_rewrite_tac[clear_storage_value_def] >> simp[]) >>
    Cases_on ‘offset <> 0’
    >- (once_rewrite_tac[clear_storage_value_def] >> simp[]) >>
    Cases_on ‘byte_sequence_type ty’
    >- (once_rewrite_tac[clear_storage_value_def] >> simp[]) >>
    Cases_on ‘ty’ >> once_rewrite_tac[clear_storage_value_def] >>
    simp[]
    >~ [‘ArrayT element len’] >-
     (Cases_on ‘storage_array_data accounts addr slot (ArrayT element len)’ >>
      gvs[] >> Cases_on ‘2 ** 64 <= q’ >> simp[] >>
      Cases_on ‘is_stored_scalar_type element’ >> simp[] >>
      metis_tac[]) >>
    Cases_on ‘lookup_struct env a’ >> simp[] >>
    Cases_on ‘lookup_struct_layout env a’ >> simp[] >>
    Cases_on ‘m = 0’ >> simp[] >>
    ‘m' <> 0 /\ m - 1 <= m' - 1’ by decide_tac >>
    gvs[] >> metis_tac[])
  >~ [‘clear_storage_elements env m accounts addr data element i n = _’] >-
   (Cases_on ‘n = 0’
    >- (once_rewrite_tac[clear_storage_value_def] >> simp[]) >>
    Cases_on ‘storage_element_location env data element i’
    >- (once_rewrite_tac[clear_storage_value_def] >> simp[]) >>
    rename1 ‘storage_element_location env data element i = SOME loc’ >>
    PairCases_on ‘loc’ >>
    once_rewrite_tac[clear_storage_value_def] >> simp[] >>
    Cases_on ‘clear_storage_value env m accounts addr loc0 loc1 element’ >>
    simp[]) >>
  once_rewrite_tac[clear_storage_value_def] >> simp[] >>
  Cases_on ‘ALOOKUP (MAP (\v. (v.state_id, v)) layout) f’ >> simp[] >>
  Cases_on ‘is_stored_scalar_type ty’ >> gvs[] >>
  Cases_on ‘clear_storage_value env fuel accounts addr
              (slot + x.state_slot) x.state_offset ty’ >>
  gvs[]
QED

(* Replace storage contents using each element's layout: scalar arrays write
 * complete packed slots; aggregate arrays clear only removed elements, and
 * retained structs overwrite members while preserving scalar-slot padding.
 * The fuel bounds recursive clearing. *)
Definition store_storage_value_def:
  (store_storage_value env fuel accounts addr slot src dst v =
    if byte_sequence_type dst then
      (case v of
         ScalarValue (BytesValue bs) => replace_storage_bytes accounts addr slot bs F
       | _ => INR (InvalidCompletion "bad stored byte sequence"))
    else case (src, dst, v) of
      (ArrayT e _, ArrayT e' l, TupleValue vs) =>
        (case storage_array_data accounts addr slot (ArrayT e' l) of
           (old_length, data) =>
             if 2 ** 64 ≤ old_length then INR FuelExhausted else
             let length = LENGTH vs in
             let accounts1 = if l = NONE then
                               set_storage_word accounts addr slot (n2w length)
                             else accounts in
             let resized =
               if is_stored_scalar_type e' then
                 (case fixed_storage_slots env (ArrayT e' (SOME (MAX old_length length))) of
                    SOME slots => INL (clear_byte_slots slots accounts1 addr data)
                  | NONE => INL accounts1)
               else clear_storage_elements env fuel accounts1 addr data e'
                      length (old_length - length) in
             case resized of
               INR c => INR c
             | INL accounts2 =>
                 store_storage_elements env fuel accounts2 addr data e e' 0 vs)
    | (StructT _, StructT s, TupleValue vs) =>
        (case (lookup_struct env s, lookup_struct_layout env s) of
           (SOME fields, SOME layout) =>
             store_storage_fields env fuel accounts addr slot layout.struct_fields fields vs
         | _ => INR (InvalidCompletion "missing struct layout"))
    | _ => INR (InvalidCompletion "bad stored array")) ∧
  (store_storage_elements env fuel accounts addr data src dst i [] = INL accounts) ∧
  (store_storage_elements env fuel accounts addr data src dst i (v :: vs) =
    case storage_element_location env data dst i of
      NONE => INR (InvalidCompletion "bad array element type")
    | SOME (s, offset) =>
        let stored =
          if is_stored_scalar_type dst then
            (case v of
               ScalarValue x =>
                 (case eval_conversion env src dst x of
                    ScalarOk y =>
                      (case write_storage accounts addr s offset dst y of
                         SOME accounts' => INL accounts'
                       | NONE => INR (InvalidCompletion "bad storage write"))
                  | _ => INR (InvalidCompletion "bad element conversion"))
             | _ => INR (InvalidCompletion "bad stored element"))
          else store_storage_value env fuel accounts addr s src dst v in
        case stored of
          INR c => INR c
        | INL accounts' =>
            store_storage_elements env fuel accounts' addr data src dst (i + 1) vs) ∧
  (store_storage_fields env fuel accounts addr slot layout [] vs = INL accounts) ∧
  (store_storage_fields env fuel accounts addr slot layout ((f, ty) :: fields) [] =
    INR (InvalidCompletion "bad stored struct")) ∧
  (store_storage_fields env fuel accounts addr slot layout ((f, ty) :: fields) (v :: vs) =
    case ALOOKUP (MAP (λv. (v.state_id, v)) layout) f of
      NONE => INR (InvalidCompletion "missing field layout")
    | SOME l =>
        let s = slot + l.state_slot in
        let stored =
          if is_stored_scalar_type ty then
            (case v of
               ScalarValue x =>
                 (case write_storage accounts addr s l.state_offset ty x of
                    SOME accounts' => INL accounts'
                  | NONE => INR (InvalidCompletion "bad storage write"))
             | _ => INR (InvalidCompletion "bad stored field"))
          else case ty of
            MappingT _ _ => INL accounts
          | _ => store_storage_value env fuel accounts addr s ty ty v in
        case stored of
          INR c => INR c
        | INL accounts' =>
            store_storage_fields env fuel accounts' addr slot layout fields vs)
Termination
  WF_REL_TAC ‘measure (λx. case x of
    INL (env, fuel, accounts, addr, slot, src, dst, v) => runtime_value_size v
  | INR (INL (env, fuel, accounts, addr, data, src, dst, i, vs)) =>
      list_size runtime_value_size vs
  | INR (INR (env, fuel, accounts, addr, slot, layout, fields, vs)) =>
      list_size runtime_value_size vs)’ >>
  rw[solidityCoreTheory.runtime_value_size_def, listTheory.list_size_def]
End

(* Copy into storage after reading the source. Arrays and byte sequences
 * replace their old contents; structs overwrite fields in place, preserving
 * scalar-slot padding and mappings. *)
Definition copy_to_storage_def:
  copy_to_storage env accounts src v dst static =
    case dst of
      StorageReference PersistentStorage addr slot 0 ty _ =>
        if static then INR (InvalidCompletion "array copy in static frame") else
        store_storage_value env (LENGTH env.type_declarations) accounts addr slot src ty v
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
  read_storage_reference env world ty r =
    case r of
      StorageReference backend addr slot offset rty _ =>
        if rty ≠ ty then ValueAbrupt (InvalidCompletion "bad read type")
        else if backend = PersistentStorage ∧ offset = 0 ∧ located_object_shape StorageLoc ty
        then ValueOk (ReferenceValue r)
        else (case read_storage_word env
                (lookup_storage slot (case backend of
                   PersistentStorage => (lookup_account addr world.accounts).storage
                 | TransientStorage => lookup_transient_storage addr world.transient)) offset ty of
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

val () = cv_auto_trans read_storage_word_def;
val () = cv_auto_trans read_storage_def;
val () = cv_auto_trans write_storage_word_def;
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
val () = cv_auto_trans replace_storage_bytes_def;
val () = cv_auto_trans store_storage_bytes_def;
val () = cv_auto_trans word_prefix_def;
val () = cv_auto_trans push_storage_bytes_def;
val () = cv_auto_trans pop_storage_bytes_def;
val () = cv_auto_trans copy_storage_byte_chunks_def;
val () = cv_auto_trans copy_storage_bytes_def;
val () = cv_auto_trans storage_element_location_def;
val () = cv_auto_trans fixed_array_element_def;
val () = cv_auto_trans storage_array_data_def;

val storage_array_value_pre_def = cv_auto_trans_pre_rec
  "storage_array_value_pre storage_array_elements_pre storage_struct_fields_pre" storage_array_value_def (
  WF_REL_TAC ‘inv_image ($< LEX $< LEX $<) (λx. case x of
    INL (env, fuel, accounts, addr, slot, ty) => (cv$c2n fuel, cv_size ty, 0)
  | INR (INL (env, fuel, accounts, addr, data, element, i, n)) =>
      (cv$c2n fuel, cv_size element, cv$c2n n + 1)
  | INR (INR (env, fuel, accounts, addr, slot, layout, fields)) =>
      (cv$c2n fuel, cv_size fields, 1))’ >>
  cv_termination_tac
);

Theorem storage_array_value_pre[cv_pre]:
  (∀env fuel accounts addr slot ty. storage_array_value_pre env fuel accounts addr slot ty) ∧
  (∀env fuel accounts addr data element i n.
     storage_array_elements_pre env fuel accounts addr data element i n) ∧
  (∀env fuel accounts addr slot layout fields.
     storage_struct_fields_pre env fuel accounts addr slot layout fields)
Proof
  ho_match_mp_tac storage_array_value_ind >> rpt strip_tac >>
  simp[Once storage_array_value_pre_def] >> rw[] >> gvs[]
QED

val clear_storage_value_pre_def = cv_auto_trans_pre_rec
  "clear_storage_value_pre clear_storage_elements_pre clear_storage_fields_pre" clear_storage_value_def (
  WF_REL_TAC ‘inv_image ($< LEX $< LEX $<) (λx. case x of
    INL (env, fuel, accounts, addr, slot, offset, ty) => (cv$c2n fuel, cv_size ty, 0)
  | INR (INL (env, fuel, accounts, addr, data, element, i, n)) =>
      (cv$c2n fuel, cv_size element, cv$c2n n + 1)
  | INR (INR (env, fuel, accounts, addr, slot, layout, fields)) =>
      (cv$c2n fuel, cv_size fields, 1))’ >>
  cv_termination_tac
);

Theorem clear_storage_value_pre[cv_pre]:
  (∀env fuel accounts addr slot offset ty. clear_storage_value_pre env fuel accounts addr slot offset ty) ∧
  (∀env fuel accounts addr data element i n.
     clear_storage_elements_pre env fuel accounts addr data element i n) ∧
  (∀env fuel accounts addr slot layout fields.
     clear_storage_fields_pre env fuel accounts addr slot layout fields)
Proof
  ho_match_mp_tac clear_storage_value_ind >> rpt strip_tac >>
  simp[Once clear_storage_value_pre_def] >> rw[] >> gvs[]
QED

val store_storage_value_pre_def = cv_auto_trans_pre_rec
  "store_storage_value_pre store_storage_elements_pre store_storage_fields_pre" store_storage_value_def (
  WF_REL_TAC ‘measure (λx. case x of
    INL (env, fuel, accounts, addr, slot, src, dst, v) => cv_size v
  | INR (INL (env, fuel, accounts, addr, data, src, dst, i, vs)) => cv_size vs
  | INR (INR (env, fuel, accounts, addr, slot, layout, fields, vs)) => cv_size vs)’ >>
  cv_termination_tac
);

Theorem store_storage_value_pre[cv_pre]:
  (∀env fuel accounts addr slot src dst v.
     store_storage_value_pre env fuel accounts addr slot src dst v) ∧
  (∀env fuel accounts addr data src dst i vs.
     store_storage_elements_pre env fuel accounts addr data src dst i vs) ∧
  (∀env fuel accounts addr slot layout fields vs.
     store_storage_fields_pre env fuel accounts addr slot layout fields vs)
Proof
  ho_match_mp_tac store_storage_value_ind >> rpt strip_tac >>
  simp[Once store_storage_value_pre_def] >> rw[] >> gvs[]
QED

val () = cv_auto_trans copy_to_storage_def;
val () = cv_auto_trans navigate_storage_def;
val () = cv_auto_trans read_storage_reference_def;
val () = cv_auto_trans storage_array_length_def;
val () = cv_auto_trans navigate_storage_field_def;
