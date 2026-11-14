(* The ABI at the contract boundary, for every ABI type (scalars, byte
 * sequences, arrays and structs) wherever its value is: calldata arguments,
 * return data, abi.encode and abi.decode, revert data and event logs, over
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

(* The ABI type of ty, each struct the tuple of its fields' types. The fuel
 * bounds the struct nesting; callers pass the number of type declarations,
 * which a struct the ABI admits nests within. *)
Definition abi_type_def:
  (abi_type env (fuel : num) ty =
    case ty of
      UintT n => Uint n
    | IntT n => Int n
    | BoolT => Bool
    | AddressT _ => Address
    | FixedBytesT n => Bytes (SOME n)
    | EnumT _ => Uint 8
    | BytesT => Bytes NONE
    | StringT => String
    | ArrayT element length => Array length (abi_type env fuel element)
    | StructT s =>
        (case lookup_struct env s of
           SOME fields =>
             if fuel = 0 then Tuple []
             else Tuple (abi_types env (fuel - 1) (MAP SND fields))
         | NONE => Tuple [])
    | LocatedT _ ty' => abi_type env fuel ty'
    | _ => Tuple []) ∧
  (abi_types env fuel [] = []) ∧
  (abi_types env fuel (ty :: tys) = abi_type env fuel ty :: abi_types env fuel tys)
Termination
  WF_REL_TAC ‘inv_image ($< LEX $<) (λx. case x of
    INL (env, fuel, ty) => (fuel, sol_type_size ty)
  | INR (env, fuel, tys) => (fuel, list_size sol_type_size tys))’ >>
  rw[solidityASTTheory.sol_type_size_def, listTheory.list_size_def]
End

Definition abi_value_def:
  (abi_value (UintT _) (ScalarValue (IntegerValue i)) = SOME (NumV (Num i))) ∧
  (abi_value (IntT _) (ScalarValue (IntegerValue i)) = SOME (IntV i)) ∧
  (abi_value BoolT (ScalarValue (BoolValue b)) =
    SOME (NumV (if b then 1 else 0))) ∧
  (abi_value (AddressT _) (ScalarValue (AddressValue a)) =
    SOME (NumV (w2n a))) ∧
  (abi_value (FixedBytesT _) (ScalarValue (BytesValue bs)) = SOME (BytesV bs)) ∧
  (abi_value (EnumT _) (ScalarValue (IntegerValue i)) = SOME (NumV (Num i))) ∧
  (abi_value BytesT (ScalarValue (BytesValue bs)) = SOME (BytesV bs)) ∧
  (abi_value StringT (ScalarValue (BytesValue bs)) = SOME (BytesV bs)) ∧
  (abi_value (LocatedT _ ty) v = abi_value ty v) ∧
  (abi_value _ _ = NONE)
End

(* The ABI value of a value tree: an array's elements or a struct's fields in
 * order, as a list. *)
Definition value_abi_value_def:
  (value_abi_value env ty v =
    case (ty, v) of
      (ArrayT element _, TupleValue vs) =>
        OPTION_MAP ListV (values_abi_value env element vs)
    | (ArrayT _ _, _) => NONE
    | (StructT s, TupleValue vs) =>
        (case lookup_struct env s of
           SOME fields => OPTION_MAP ListV (fields_abi_value env (MAP SND fields) vs)
         | NONE => NONE)
    | (StructT _, _) => NONE
    | _ => abi_value ty v) ∧
  (values_abi_value env element [] = SOME []) ∧
  (values_abi_value env element (v :: vs) =
    case (value_abi_value env element v, values_abi_value env element vs) of
      (SOME a, SOME as) => SOME (a :: as)
    | _ => NONE) ∧
  (fields_abi_value env [] [] = SOME []) ∧
  (fields_abi_value env (ty :: tys) (v :: vs) =
    case (value_abi_value env ty v, fields_abi_value env tys vs) of
      (SOME a, SOME as) => SOME (a :: as)
    | _ => NONE) ∧
  (fields_abi_value env _ _ = NONE)
Termination
  WF_REL_TAC ‘measure (λx. case x of
    INL (env, ty, v) => runtime_value_size v
  | INR (INL (env, element, vs)) => list_size runtime_value_size vs
  | INR (INR (env, tys, vs)) => list_size runtime_value_size vs)’ >>
  rw[solidityCoreTheory.runtime_value_size_def, listTheory.list_size_def]
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
  (* a uint8, which dispatch checks against the enum's members *)
  (abi_runtime_value (EnumT _) (NumV n) = SOME (ScalarValue (IntegerValue (&n)))) ∧
  (abi_runtime_value _ _ = NONE)
End

Definition abi_word_def:
  abi_word bs pos = num_of_be_bytes (TAKE 32 (DROP pos bs))
End

(* The bytes an element or field takes in the head of its array or struct. *)
Definition abi_stride_def:
  abi_stride env ty =
    let a = abi_type env (LENGTH env.type_declarations) ty in
    if is_dynamic a then 32 else static_length a
End

(* The bytes the heads of a value of ABI type a take: a tuple's or fixed
 * array's components' heads, else a word. A dynamic struct or fixed array in
 * calldata needs this much calldata where it starts. *)
Definition abi_head_size_def:
  abi_head_size a =
    case a of
      Tuple ts => head_lengths ts 0
    | Array (SOME n) t => head_lengths (REPLICATE n t) 0
    | _ => 32
End

(* The length a calldata reference to a value of type ty records: a fixed
 * array's length, else 0; a dynamic array's comes from the calldata. *)
Definition calldata_length_def:
  calldata_length ty = case ty of ArrayT _ (SOME n) => n | _ => 0
End

(* The calldata word at pos, zero past the end, as CALLDATALOAD reads it. *)
Definition calldata_word_def:
  calldata_word (cd : byte list) pos =
    num_of_be_bytes (TAKE 32 (DROP pos cd ++ REPLICATE 32 0w))
End

(* The calldata position an offset at ptr, relative to base, leads to, as the
 * pinned compiler's calldata accessors check it: the offset, a signed word, is
 * below the calldata left after base less needed - 1, needed being the bytes
 * the value's head or length word takes. Addresses wrap at 2^256. *)
Definition calldata_offset_def:
  calldata_offset cd base ptr needed =
    let size : 256 word = n2w (LENGTH cd) in
    let rel : 256 word = n2w (calldata_word cd ptr) in
    if rel < size - n2w base - n2w (needed - 1) then SOME (n2w base + rel : 256 word)
    else NONE
End

(* A byte sequence or dynamic array in calldata, reached through the offset
 * at ptr: its length there is below 2^64, and its data of stride bytes per
 * element ends within the calldata, compared as signed words. The data's
 * position and the length. *)
Definition calldata_tail_def:
  calldata_tail cd base ptr stride =
    case calldata_offset cd base ptr 32 of
      NONE => INR (RevertCompletion [])
    | SOME addr =>
      let size : 256 word = n2w (LENGTH cd) in
      let length = calldata_word cd (w2n addr) in
      if 2 ** 64 ≤ length then INR (RevertCompletion []) else
      let data = addr + 32w in
      if size - n2w (length * stride) < data then INR (RevertCompletion [])
      else INL (w2n data, length)
End

(* The element or field of a calldata array or struct whose head is at head,
 * as the pinned compiler's calldata accessors read it: a scalar read and
 * validated in place (an enum outside its members reverts), a static array or
 * struct in place, and any other value through the offset there, relative to
 * base, the start of the array's data or of the struct. *)
Definition calldata_part_def:
  calldata_part env cd ty base head =
    let a = abi_type env (LENGTH env.type_declarations) ty in
    if is_stored_scalar_type ty then
      let word = TAKE 32 (DROP head cd ++ REPLICATE 32 0w) in
      if ¬valid_enc a word then INR (RevertCompletion []) else
      (case abi_runtime_value ty (dec a word) of
         SOME (ScalarValue v) =>
           if (case ty of EnumT _ => ¬scalar_has_type env ty v | _ => F) then
             INR (RevertCompletion [])
           else INL (ScalarValue v)
       | _ => INR (InvalidCompletion "bad calldata element type"))
    else if ¬is_dynamic a then
      INL (ReferenceValue (CalldataReference head (calldata_length ty) ty))
    else if byte_sequence_type ty ∨ (case ty of ArrayT _ NONE => T | _ => F) then
      let stride = case ty of ArrayT inner NONE => abi_stride env inner | _ => 1 in
      (case calldata_tail cd base head stride of
         INL (pos, length) => INL (ReferenceValue (CalldataReference pos length ty))
       | INR c => INR c)
    else
      case calldata_offset cd base head (abi_head_size a) of
        SOME addr =>
          INL (ReferenceValue (CalldataReference (w2n addr) (calldata_length ty) ty))
      | NONE => INR (RevertCompletion [])
End

(* Field f of the calldata struct of type s at pos: a scalar field as a
 * reference to its head, read and validated when the field is read; any other
 * field as calldata_part reaches it. *)
Definition calldata_struct_field_def:
  calldata_struct_field env cd s pos f =
    case lookup_struct env s of
      NONE => INR (InvalidCompletion "unknown struct")
    | SOME fields =>
      case field_position f fields of
        NONE => INR (InvalidCompletion "unknown struct field")
      | SOME (k, ty) =>
        let head = pos + head_lengths (abi_types env (LENGTH env.type_declarations)
                                         (TAKE k (MAP SND fields))) 0 in
        if is_stored_scalar_type ty then
          INL (ReferenceValue (CalldataReference head 0 ty))
        else calldata_part env cd ty pos head
End

(* The value of a calldata array, struct or byte sequence at data, read part
 * by part through the pinned compiler's calldata accessors, so an invalid
 * element or offset reverts: an array or struct as the tuple of its elements
 * or fields, a byte sequence as its bytes. The encoder and the copies to
 * storage read calldata this way. The fuel bounds the struct nesting. *)
Definition calldata_value_def:
  (calldata_value env (fuel : num) cd ty data length =
    case ty of
      ArrayT element _ =>
        (case calldata_values env fuel cd element data 0 length of
           INL vs => INL (TupleValue vs)
         | INR c => INR c)
    | StructT s =>
        (case lookup_struct env s of
           SOME fields =>
             if fuel = 0 then INR (InvalidCompletion "struct nesting") else
             (case calldata_fields env (fuel - 1) cd (MAP SND fields) data data of
                INL vs => INL (TupleValue vs)
              | INR c => INR c)
         | NONE => INR (InvalidCompletion "unknown struct"))
    | _ => INL (ScalarValue (BytesValue
             (TAKE length (DROP data cd ++ REPLICATE length 0w))))) ∧
  (calldata_values env fuel cd element data i n =
    if n = 0 then INL [] else
    case calldata_part_value env fuel cd element data
           (data + i * abi_stride env element) of
      INR c => INR c
    | INL v =>
        case calldata_values env fuel cd element data (i + 1) (n - 1) of
          INL vs => INL (v :: vs)
        | INR c => INR c) ∧
  (calldata_fields env fuel cd [] base head = INL []) ∧
  (calldata_fields env fuel cd (ty :: tys) base head =
    case calldata_part_value env fuel cd ty base head of
      INR c => INR c
    | INL v =>
        case calldata_fields env fuel cd tys base (head + abi_stride env ty) of
          INL vs => INL (v :: vs)
        | INR c => INR c) ∧
  (calldata_part_value env fuel cd ty base head =
    case calldata_part env cd ty base head of
      INL (ReferenceValue (CalldataReference pos length _)) =>
        calldata_value env fuel cd ty pos length
    | result => result)
Termination
  WF_REL_TAC ‘inv_image ($< LEX $< LEX $<) (λx. case x of
    INL (_, fuel, _, ty, _, _) => (fuel, sol_type_size ty, 0)
  | INR (INL (_, fuel, _, element, _, _, n)) => (fuel, sol_type_size element, n + 2)
  | INR (INR (INL (_, fuel, _, tys, _, _))) => (fuel, list_size sol_type_size tys, 0)
  | INR (INR (INR (_, fuel, _, ty, _, _))) => (fuel, sol_type_size ty, 1))’ >>
  rw[solidityASTTheory.sol_type_size_def, listTheory.list_size_def]
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

(* A storage value encoded in place, as the pinned encoder does: its ABI
 * value and its encoding. Scalars are read cleaned; a byte sequence copies
 * whole data words, keeping unused dirty bytes, except the length byte of a
 * short one. A length of 2^64 or more panics with 0x41, as the memory for the
 * encoding cannot be allocated. The fuel bounds the struct nesting. *)
Definition storage_abi_value_def:
  (storage_abi_value env (fuel : num) accounts addr slot ty =
    if byte_sequence_type ty then
      (case storage_byte_length accounts addr slot of
         INR c => INR c
       | INL length =>
         let padded = storage_byte_range accounts addr slot length 0
                        (32 * ((length + 31) DIV 32)) in
         let data = if 0 < length ∧ length < 32 then TAKE 31 padded ++ [0w]
                    else padded in
         case abi_value ty (ScalarValue (BytesValue (TAKE length padded))) of
           SOME a => INL (a, enc (Uint 256) (NumV length) ++ data)
         | NONE => INR (InvalidCompletion "bad ABI value"))
    else case ty of
      ArrayT element l =>
        (case storage_array_data accounts addr slot ty of
           (length, data) =>
             if 2 ** 64 ≤ length then INR (PanicCompletion 65) else
             case storage_abi_elements env fuel accounts addr data element 0 length of
               INL parts =>
                 INL (ListV (MAP FST parts),
                      (if l = NONE then enc (Uint 256) (NumV length) else []) ++
                      encoded_abi_tuple
                        (MAP (λp. (abi_type env (LENGTH env.type_declarations) element,
                                   SND p)) parts))
             | INR c => INR c)
    | StructT s =>
        (case (lookup_struct env s, lookup_struct_layout env s) of
           (SOME fields, SOME layout) =>
             if fuel = 0 then INR (InvalidCompletion "struct nesting") else
             (case storage_abi_fields env (fuel - 1) accounts addr slot
                     layout.struct_fields fields of
                INL parts => INL (ListV (MAP FST parts), encoded_abi_tuple (MAP SND parts))
              | INR c => INR c)
         | _ => INR (InvalidCompletion "missing struct layout"))
    | _ => INR (InvalidCompletion "bad storage ABI type")) ∧
  (storage_abi_elements env fuel accounts addr data element i n =
    if n = 0 then INL [] else
    case storage_element_location env data element i of
      NONE => INR (InvalidCompletion "bad array element type")
    | SOME (s, offset) =>
        let value =
          if is_stored_scalar_type element then
            (case read_storage env accounts addr s offset element of
               SOME v =>
                 (case abi_value element (ScalarValue v) of
                    SOME a => INL (a, enc (abi_type env 0 element) a)
                  | NONE => INR (InvalidCompletion "bad ABI value"))
             | NONE => INR (InvalidCompletion "bad storage read"))
          else storage_abi_value env fuel accounts addr s element in
        case value of
          INR c => INR c
        | INL entry =>
            case storage_abi_elements env fuel accounts addr data element (i + 1) (n - 1) of
              INL entries => INL (entry :: entries)
            | INR c => INR c) ∧
  (storage_abi_fields env fuel accounts addr slot layout [] = INL []) ∧
  (storage_abi_fields env fuel accounts addr slot layout ((f, ty) :: fields) =
    case ALOOKUP (MAP (λv. (v.state_id, v)) layout) f of
      NONE => INR (InvalidCompletion "missing field layout")
    | SOME v =>
        let s = slot + v.state_slot in
        let value =
          if is_stored_scalar_type ty then
            (case read_storage env accounts addr s v.state_offset ty of
               SOME x =>
                 (case abi_value ty (ScalarValue x) of
                    SOME a => INL (a, enc (abi_type env 0 ty) a)
                  | NONE => INR (InvalidCompletion "bad ABI value"))
             | NONE => INR (InvalidCompletion "bad storage read"))
          else storage_abi_value env fuel accounts addr s ty in
        case value of
          INR c => INR c
        | INL (a, encoded) =>
            case storage_abi_fields env fuel accounts addr slot layout fields of
              INL parts =>
                INL ((a, (abi_type env (LENGTH env.type_declarations) ty, encoded)) :: parts)
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

(* The value tree of a memory, calldata or storage array, struct or byte
 * sequence of type ty, as a copy to storage and the encoder read it. Calldata
 * is read through the calldata accessors; a calldata array's own data span
 * was checked when it was decoded. *)
Definition array_copy_value_def:
  array_copy_value env (st : source_state) ty r =
    case r of
      MemoryReference _ _ _ =>
        memory_array_value env (LENGTH env.type_declarations) st ty (ReferenceValue r)
    | CalldataReference data n rty =>
        if rty ≠ ty then INR (InvalidCompletion "bad calldata array reference")
        else calldata_value env (LENGTH env.type_declarations) st.frame.call_data ty data n
    | StorageReference PersistentStorage addr slot 0 rty _ =>
        if rty ≠ ty then INR (InvalidCompletion "bad storage array reference")
        else storage_array_value env (LENGTH env.type_declarations)
               st.world.accounts addr slot ty
    | _ => INR (InvalidCompletion "bad array reference")
End

(* The ABI value of v, of type ty, and its encoding. A storage value is
 * encoded in place (storage_abi_value); any other reference is read into its
 * value tree, then encoded. *)
Definition runtime_abi_value_def:
  runtime_abi_value env st ty v =
    let ty' = case ty of LocatedT _ t => t | t => t in
    case v of
      ReferenceValue (StorageReference PersistentStorage addr slot 0 rty _) =>
        if rty ≠ ty' then INR (InvalidCompletion "bad ABI value")
        else storage_abi_value env (LENGTH env.type_declarations)
               st.world.accounts addr slot rty
    | _ =>
      case (case v of ReferenceValue r => array_copy_value env st ty' r | _ => INL v) of
        INR c => INR c
      | INL tree =>
        case value_abi_value env ty' tree of
          SOME a => INL (a, enc (abi_type env (LENGTH env.type_declarations) ty') a)
        | NONE => INR (InvalidCompletion "bad ABI value")
End

Definition runtime_abi_values_def:
  (runtime_abi_values env (st : source_state) [] [] =
     (INL [] : (contractABI$abi_type # byte list) list + source_completion)) ∧
  (runtime_abi_values env st (ty :: tys) (v :: vs) =
    case runtime_abi_value env st ty v of
      INR c => INR c
    | INL (a, encoded_body) =>
      (case runtime_abi_values env st tys vs of
         INL encoded =>
           INL ((abi_type env (LENGTH env.type_declarations) ty, encoded_body) :: encoded)
       | INR c => INR c)) ∧
  (runtime_abi_values _ _ _ _ = INR (InvalidCompletion "bad ABI arguments"))
End

Definition encoded_runtime_values_def:
  encoded_runtime_values env st tys vs =
    case runtime_abi_values env st tys vs of
      INL parts => INL (encoded_abi_tuple parts)
    | INR c => INR c
End

(* abi.encodePacked: a value in its own width, a bytesN left-aligned and the
 * others right-aligned in their word; a byte sequence as its contents,
 * wherever it is. *)
Definition packed_value_def:
  packed_value env st ty v =
    case ty of
      LocatedT _ (ArrayT element length) =>
        if ¬is_stored_scalar_type element then
          INR (InvalidCompletion "bad packed array")
        else
          (case runtime_abi_value env st ty v of
             INL (_, bs) => INL (case length of NONE => DROP 32 bs | SOME _ => bs)
           | INR c => INR c)
    | LocatedT _ _ =>
        (case v of
           ReferenceValue r => byte_contents st r
         | ScalarValue (BytesValue bs) => INL bs
         | _ => INR (InvalidCompletion "bad packed value"))
    | _ =>
      case (abi_value ty v, storage_bytes ty) of
        (SOME a, SOME width) =>
          let word = enc (abi_type env 0 ty) a in
          INL (case ty of
                 FixedBytesT _ => TAKE width word
               | _ => DROP (32 - width) word)
      | _ => INR (InvalidCompletion "bad packed value")
End

Definition packed_values_def:
  (packed_values env st [] [] = (INL [] : byte list + source_completion)) ∧
  (packed_values env st (ty :: tys) (v :: vs) =
    case packed_value env st ty v of
      INR c => INR c
    | INL bs =>
      case packed_values env st tys vs of
        INL rest => INL (bs ++ rest)
      | INR c => INR c) ∧
  (packed_values _ _ _ _ = INR (InvalidCompletion "bad packed values"))
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

(* A memory value decoded at pos, as the pinned decoder does: a scalar
 * validated in place (an enum outside its members reverts); a byte sequence
 * or array whose encoding starts at pos in range, its length below 2^64 and
 * its memory allocated (Panic(0x41) when the free memory pointer would pass
 * 2^64) before its data span is checked; a struct whose heads lie within the
 * data, allocated after that check; then each element or field, a dynamic
 * one at an offset below 2^64 from the start of the array's data or of the
 * struct. Offsets need not be aligned, tails may overlap, and padding is
 * ignored. Byte sequences decode to their bytes, and arrays and structs to
 * the tuple of their elements or fields; free is the free memory pointer.
 * The fuel bounds the struct nesting. *)
Definition decode_memory_value_def:
  (decode_memory_value env (fuel : num) ty bs pos free =
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
          if data + length * abi_stride env element > LENGTH bs then
            INR (RevertCompletion [])
          else
            (case decode_memory_elements env fuel element bs data 0 length (free + size) of
               INL (vs, next) => INL (TupleValue vs, next)
             | INR c => INR c)
      | _ =>
          if data + length > LENGTH bs then INR (RevertCompletion [])
          else INL (ScalarValue (BytesValue (TAKE length (DROP data bs))), free + size)
    else case ty of
      StructT s =>
        (case lookup_struct env s of
           SOME fields =>
             let tys = MAP SND fields in
             if pos + head_lengths (abi_types env (LENGTH env.type_declarations) tys) 0 >
                LENGTH bs
             then INR (RevertCompletion [])
             else if 2 ** 64 ≤ free + 32 * LENGTH tys then INR (PanicCompletion 65)
             else if fuel = 0 then INR (InvalidCompletion "struct nesting")
             else
               (case decode_memory_fields env (fuel - 1) tys bs pos pos
                       (free + 32 * LENGTH tys) of
                  INL (vs, next) => INL (TupleValue vs, next)
                | INR c => INR c)
         | NONE => INR (InvalidCompletion "unknown struct"))
    | _ =>
      let a = abi_type env 0 ty in
      let word = TAKE 32 (DROP pos bs) in
      if pos + 32 > LENGTH bs ∨ ¬valid_enc a word then
        INR (RevertCompletion [])
      else
        case abi_runtime_value ty (dec a word) of
          SOME (ScalarValue v) =>
            if (case ty of EnumT _ => ¬scalar_has_type env ty v | _ => F) then
              INR (RevertCompletion [])
            else INL (ScalarValue v, free)
        | _ => INR (InvalidCompletion "bad ABI scalar type")) ∧
  (decode_memory_elements env fuel element bs data i n free =
    if n = 0 then INL ([], free) else
    case decode_memory_part env fuel element bs data
           (data + i * abi_stride env element) free of
      INR c => INR c
    | INL (v, next) =>
        case decode_memory_elements env fuel element bs data (i + 1) (n - 1) next of
          INL (vs, last) => INL (v :: vs, last)
        | INR c => INR c) ∧
  (decode_memory_fields env fuel [] bs base src free = INL ([], free)) ∧
  (decode_memory_fields env fuel (ty :: tys) bs base src free =
    case decode_memory_part env fuel ty bs base src free of
      INR c => INR c
    | INL (v, next) =>
        case decode_memory_fields env fuel tys bs base (src + abi_stride env ty) next of
          INL (vs, last) => INL (v :: vs, last)
        | INR c => INR c) ∧
  (* An element or field whose head is at src: a dynamic one at the offset
   * there from base. *)
  (decode_memory_part env fuel ty bs base src free =
    if is_dynamic (abi_type env (LENGTH env.type_declarations) ty) then
      let offset = abi_word bs src in
      if 2 ** 64 ≤ offset then INR (RevertCompletion [])
      else decode_memory_value env fuel ty bs (base + offset) free
    else decode_memory_value env fuel ty bs src free)
Termination
  WF_REL_TAC ‘inv_image ($< LEX $< LEX $<) (λx. case x of
    INL (_, fuel, ty, _) => (fuel, sol_type_size ty, 1)
  | INR (INL (_, fuel, element, _, _, _, n, _)) =>
      (fuel, sol_type_size element, n + 3)
  | INR (INR (INL (_, fuel, tys, _))) =>
      (fuel, list_size sol_type_size tys, 0)
  | INR (INR (INR (_, fuel, ty, _))) =>
      (fuel, sol_type_size ty, 2))’ >>
  rw[solidityASTTheory.sol_type_size_def, listTheory.list_size_def]
End

(* A calldata object copied to memory: check allocation before its data span,
 * then read its value for materialization. Byte copies use word addition
 * for the span and calldatacopy's zero filling; an array is decoded as an ABI
 * argument after its span check, and a struct as an ABI argument is. *)
Definition copy_calldata_array_def:
  copy_calldata_array env cd ty data length free =
    if byte_sequence_type ty then
      let size = 32 + 32 * ((length + 31) DIV 32) in
      if 2 ** 64 ≤ length ∨ 2 ** 64 ≤ free + size then INR (PanicCompletion 65)
      else if LENGTH cd < (data + length) MOD 2 ** 256 then INR (RevertCompletion [])
      else INL (ScalarValue (BytesValue
             (TAKE length (DROP data cd ++ REPLICATE length 0w))))
    else case ty of
      ArrayT element l =>
        let size = (if l = NONE then 32 else 0) + 32 * length in
        if 2 ** 64 ≤ free + size then INR (PanicCompletion 65)
        else if data + length * abi_stride env element > LENGTH cd then
          INR (RevertCompletion [])
        else (case decode_memory_elements env (LENGTH env.type_declarations) element cd
                     data 0 length (free + size) of
                INL (vs, _) => INL (TupleValue vs)
              | INR c => INR c)
    | StructT _ =>
        (case decode_memory_value env (LENGTH env.type_declarations) ty cd data free of
           INL (v, _) => INL v
         | INR c => INR c)
    | _ => INR (InvalidCompletion "bad calldata copy")
End

(* The memory a value of type ty takes once materialized: each array's
 * elements and length word, each struct's fields, and each byte sequence's
 * length and data. *)
Definition memory_value_size_def:
  (memory_value_size env ty v =
    case (ty, v) of
      (ArrayT element length, TupleValue vs) =>
        (if length = NONE then 32 else 0) + 32 * LENGTH vs +
        memory_values_size env element vs
    | (StructT s, TupleValue vs) =>
        32 * LENGTH vs +
        (case lookup_struct env s of
           SOME fields => memory_fields_size env (MAP SND fields) vs
         | NONE => 0)
    | (_, ScalarValue (BytesValue bs)) =>
        if byte_sequence_type ty then 32 + 32 * ((LENGTH bs + 31) DIV 32) else 0
    | _ => 0) ∧
  (memory_values_size env element [] = 0) ∧
  (memory_values_size env element (v :: vs) =
    memory_value_size env element v + memory_values_size env element vs) ∧
  (memory_fields_size env (ty :: tys) (v :: vs) =
    memory_value_size env ty v + memory_fields_size env tys vs) ∧
  (memory_fields_size env _ _ = 0)
Termination
  WF_REL_TAC ‘measure (λx. case x of
    INL (env, ty, v) => runtime_value_size v
  | INR (INL (env, element, vs)) => list_size runtime_value_size vs
  | INR (INR (env, tys, vs)) => list_size runtime_value_size vs)’ >>
  rw[solidityCoreTheory.runtime_value_size_def, listTheory.list_size_def]
End

(* An argument at head: a scalar, static array or static struct in place, any
 * other value at the offset the head holds, below 2^64. A calldata argument
 * stays in the calldata: a byte sequence or dynamic array with its data in
 * range, any other dynamic value with its heads in range. *)
Definition decode_abi_argument_def:
  decode_abi_argument env ty bs head base free =
    if head + 32 > LENGTH bs then INR (RevertCompletion []) else
    case ty of
      LocatedT CalldataLoc element =>
        let a = abi_type env (LENGTH env.type_declarations) element in
        if ¬is_dynamic a then
          INL (ReferenceValue (CalldataReference (base + head) (calldata_length element)
                 element), free)
        else
        let offset = abi_word bs head in
        if byte_sequence_type element ∨ (case element of ArrayT _ NONE => T | _ => F) then
          if 2 ** 64 ≤ offset ∨ offset + 32 > LENGTH bs then
            INR (RevertCompletion []) else
          let length = abi_word bs offset in
          let stride = case element of ArrayT inner NONE => abi_stride env inner | _ => 1 in
          if 2 ** 64 ≤ length ∨ offset + 32 + length * stride > LENGTH bs then
            INR (RevertCompletion [])
          else INL (ReferenceValue (CalldataReference (base + offset + 32) length element),
                    free)
        else if 2 ** 64 ≤ offset ∨ offset + abi_head_size a > LENGTH bs then
          INR (RevertCompletion [])
        else INL (ReferenceValue (CalldataReference (base + offset)
                    (calldata_length element) element), free)
    | LocatedT MemoryLoc element =>
        decode_memory_part env (LENGTH env.type_declarations) element bs 0 head free
    | _ => decode_memory_value env (LENGTH env.type_declarations) ty bs head free
End

Definition decode_abi_arguments_def:
  (decode_abi_arguments env [] bs head base free = INL []) ∧
  (decode_abi_arguments env (ty :: tys) bs head base free =
    case decode_abi_argument env ty bs head base free of
      INR c => INR c
    | INL (v, next) =>
        case decode_abi_arguments env tys bs (head + abi_stride env ty) base next of
          INL vs => INL (v :: vs)
        | INR c => INR c)
End

Definition decode_arguments_def:
  decode_arguments env tys bs base free =
    if head_lengths (abi_types env (LENGTH env.type_declarations) tys) 0 > LENGTH bs then
      INR (RevertCompletion [])
    else decode_abi_arguments env tys bs 0 base free
End

(* A decoded memory value as heap objects, allocated in decoding order: an
 * array or struct before its elements or fields. Storage byte copies retain
 * unknown padding; calldata copies zero it. Keep the source location through
 * nested arrays and structs. *)
Definition materialize_value_def:
  (materialize_value env loc ty v (st : source_state) =
    case (ty, v) of
      (ArrayT element length, TupleValue vs) =>
        let n = LENGTH vs in
        let id = st.next_heap_id + 1 in
        let obj = <| object_type := ty; object_length := n;
                     object_cells := FEMPTY;
                     object_address := 128 + st.memory_allocated;
                     object_padded := T |> in
        let st1 = st with <| heap := st.heap |+ (id, obj); next_heap_id := id;
                     memory_allocated := st.memory_allocated +
                       (if length = NONE then 32 else 0) + 32 * n |> in
        (case materialize_values env loc element 0 vs FEMPTY st1 of
           SOME (cells, st2) =>
             SOME (ReferenceValue (MemoryReference (HeapId id) 0 ty),
                   st2 with heap := st2.heap |+ (id, obj with object_cells := cells))
         | NONE => NONE)
    | (StructT s, TupleValue vs) =>
        (case lookup_struct env s of
           SOME fields =>
             let n = LENGTH vs in
             let id = st.next_heap_id + 1 in
             let obj = <| object_type := ty; object_length := n;
                          object_cells := FEMPTY;
                          object_address := 128 + st.memory_allocated;
                          object_padded := T |> in
             let st1 = st with <| heap := st.heap |+ (id, obj); next_heap_id := id;
                          memory_allocated := st.memory_allocated + 32 * n |> in
             (case materialize_fields env loc (MAP SND fields) 0 vs FEMPTY st1 of
                SOME (cells, st2) =>
                  SOME (ReferenceValue (MemoryReference (HeapId id) 0 ty),
                        st2 with heap := st2.heap |+ (id, obj with object_cells := cells))
              | NONE => NONE)
         | NONE => NONE)
    | (_, ScalarValue (BytesValue bs)) =>
        if byte_sequence_type ty then SOME (allocate_bytes (loc ≠ StorageLoc) ty bs st)
        else SOME (v, st)
    | (_, ScalarValue _) => SOME (v, st)
    | _ => NONE) ∧
  (materialize_values env loc element i [] cells st = SOME (cells, st)) ∧
  (materialize_values env loc element i (v :: vs) cells st =
    case materialize_value env loc element v st of
      SOME (value, st1) =>
        materialize_values env loc element (i + 1) vs (cells |+ (i, value)) st1
    | NONE => NONE) ∧
  (materialize_fields env loc [] i [] cells st = SOME (cells, st)) ∧
  (materialize_fields env loc (ty :: tys) i (v :: vs) cells st =
    case materialize_value env loc ty v st of
      SOME (value, st1) =>
        materialize_fields env loc tys (i + 1) vs (cells |+ (i, value)) st1
    | NONE => NONE) ∧
  (materialize_fields env loc _ i _ cells st = NONE)
Termination
  WF_REL_TAC ‘measure (λx. case x of
    INL (env, loc, ty, v, st) => runtime_value_size v
  | INR (INL (env, loc, element, i, vs, cells, st)) => list_size runtime_value_size vs
  | INR (INR (env, loc, tys, i, vs, cells, st)) => list_size runtime_value_size vs)’ >>
  rw[solidityCoreTheory.runtime_value_size_def, listTheory.list_size_def]
End

(* Decoded memory payloads become heap objects before a procedure sees them.
 * Calldata payloads retain slices into the frame's original call_data. *)
Definition materialize_arguments_def:
  (materialize_arguments env [] [] st = SOME ([], st)) ∧
  (materialize_arguments env (ty :: tys) (v :: vs) st =
    case (case ty of
            LocatedT MemoryLoc element => materialize_value env CalldataLoc element v st
          | _ => SOME (v, st)) of
      SOME (value, st1) =>
        (case materialize_arguments env tys vs st1 of
           SOME (values, st2) => SOME (value :: values, st2)
         | NONE => NONE)
    | NONE => NONE) ∧
  (materialize_arguments _ _ _ _ = NONE)
End

(* Revert data of Panic(uint256), selector 0x4e487b71. *)
Definition panic_data_def:
  panic_data n = [0x4Ew; 0x48w; 0x7Bw; 0x71w] ++ enc (Uint 256) (NumV n)
End

(* The in-place encoding an indexed array or struct hashes: its elements or
 * fields concatenated, without lengths or offsets, a nested byte sequence
 * padded. Each part is taken from the part's encoded body (encoded), whose
 * words keep any dirty padding the storage encoder copied. *)
Definition indexed_data_def:
  (indexed_data t a (encoded : byte list) =
    case (t, a) of
      (Array length element, ListV vs) =>
        indexed_parts (REPLICATE (LENGTH vs) element) vs
          (if length = NONE then DROP 32 encoded else encoded) 0
    | (Tuple ts, ListV vs) => indexed_parts ts vs encoded 0
    | (_, BytesV bs) =>
        if is_dynamic t then SOME (TAKE (32 * ((LENGTH bs + 31) DIV 32)) (DROP 32 encoded))
        else SOME (TAKE 32 encoded)
    | _ => SOME (TAKE 32 encoded)) ∧
  (indexed_parts [] [] encoded pos = SOME []) ∧
  (indexed_parts (t :: ts) (v :: vs) encoded pos =
    let dynamic = is_dynamic t in
    let offset = if dynamic then abi_word encoded pos else pos in
    case (indexed_data t v (DROP offset encoded),
          indexed_parts ts vs encoded (pos + if dynamic then 32 else static_length t)) of
      (SOME bs, SOME rest) => SOME (bs ++ rest)
    | _ => NONE) ∧
  (indexed_parts _ _ encoded pos = NONE)
Termination
  WF_REL_TAC ‘measure (λx. case x of
    INL (t, a, encoded) => abi_value_size a
  | INR (ts, vs, encoded, pos) => list_size abi_value_size vs)’ >>
  rw[contractABITheory.abi_value_size_def, listTheory.list_size_def]
End

(* Event arguments split into indexed topics and data. An indexed array or
 * struct hashes its in-place encoding, a byte sequence its bytes; a scalar
 * topic is its ABI word. *)
Definition event_parts_def:
  (event_parts env st [] = INL ([], [])) ∧
  (event_parts env st ((ty, indexed, v) :: args) =
    case runtime_abi_value env st ty v of
      INR c => INR c
    | INL (a, encoded_body) =>
      (case event_parts env st args of
         INR c => INR c
       | INL (topics, parts) =>
        let t = abi_type env (LENGTH env.type_declarations) ty in
        if indexed then
          let topic =
            if (case t of Array _ _ => T | Tuple _ => T | _ => F) then
              OPTION_MAP (λbs. word_of_bytes_be (Keccak_256_w64 bs))
                (indexed_data t a encoded_body)
            else case a of
              BytesV bs =>
                SOME (if is_dynamic t then word_of_bytes_be (Keccak_256_w64 bs)
                      else word_of_bytes T (0w : bytes32) encoded_body)
            | _ => SOME (word_of_bytes T (0w : bytes32) encoded_body) in
          (case topic of
             SOME word => INL (word :: topics, parts)
           | NONE => INR (InvalidCompletion "bad indexed event argument"))
        else INL (topics, (t, encoded_body) :: parts)))
End

Definition event_log_def:
  event_log env st logger topic0 args =
    case event_parts env st args of
      INL (topics, parts) =>
        INL <| logger := logger;
               topics := (case topic0 of SOME t => t :: topics | NONE => topics);
               data := encoded_abi_tuple parts |>
    | INR c => INR c
End

val abi_type_pre_def = cv_auto_trans_pre_rec "abi_type_pre abi_types_pre" abi_type_def (
  WF_REL_TAC ‘inv_image ($< LEX $<) (λx. case x of
    INL (env, fuel, ty) => (cv$c2n fuel, cv_size ty)
  | INR (env, fuel, tys) => (cv$c2n fuel, cv_size tys))’ >>
  cv_termination_tac
);

Theorem abi_type_pre[cv_pre]:
  (∀env fuel ty. abi_type_pre env fuel ty) ∧
  (∀env fuel tys. abi_types_pre env fuel tys)
Proof
  ho_match_mp_tac abi_type_ind >> rpt strip_tac >>
  simp[Once abi_type_pre_def] >> rw[] >> gvs[]
QED
val () = cv_auto_trans abi_value_def;
val value_abi_value_pre_def = cv_auto_trans_pre_rec
  "value_abi_value_pre values_abi_value_pre fields_abi_value_pre" value_abi_value_def (
  WF_REL_TAC ‘measure (λx. case x of
    INL (env, ty, v) => cv_size v
  | INR (INL (env, element, vs)) => cv_size vs
  | INR (INR (env, tys, vs)) => cv_size vs)’ >>
  cv_termination_tac
);

Theorem value_abi_value_pre[cv_pre]:
  (∀env ty v. value_abi_value_pre env ty v) ∧
  (∀env element vs. values_abi_value_pre env element vs) ∧
  (∀env tys vs. fields_abi_value_pre env tys vs)
Proof
  ho_match_mp_tac value_abi_value_ind >> rpt strip_tac >>
  simp[Once value_abi_value_pre_def] >> rw[] >> gvs[]
QED
val () = cv_auto_trans abi_runtime_value_def;
val () = cv_auto_trans abi_runtime_values_def;
val () = cv_auto_trans abi_word_def;
val () = cv_auto_trans abi_stride_def;
val () = cv_auto_trans abi_head_size_def;
val () = cv_auto_trans calldata_length_def;
val () = cv_auto_trans calldata_word_def;
val () = cv_auto_trans calldata_offset_def;
val () = cv_auto_trans calldata_tail_def;
val () = cv_auto_trans calldata_part_def;
val () = cv_auto_trans calldata_struct_field_def;
val calldata_value_pre_def = cv_auto_trans_pre_rec
  "calldata_value_pre calldata_values_pre calldata_fields_pre calldata_part_value_pre"
  calldata_value_def (
  WF_REL_TAC ‘inv_image ($< LEX $< LEX $<) (λx. case x of
    INL (_, fuel, _, ty, _, _) => (cv$c2n fuel, cv_size ty, 0)
  | INR (INL (_, fuel, _, element, _, _, n)) =>
      (cv$c2n fuel, cv_size element, cv$c2n n + 2)
  | INR (INR (INL (_, fuel, _, tys, _, _))) => (cv$c2n fuel, cv_size tys, 0)
  | INR (INR (INR (_, fuel, _, ty, _, _))) => (cv$c2n fuel, cv_size ty, 1))’ >>
  cv_termination_tac
);

Theorem calldata_value_pre[cv_pre]:
  (∀env fuel cd ty data length. calldata_value_pre env fuel cd ty data length) ∧
  (∀env fuel cd element data i n. calldata_values_pre env fuel cd element data i n) ∧
  (∀env fuel cd tys base head. calldata_fields_pre env fuel cd tys base head) ∧
  (∀env fuel cd ty base head. calldata_part_value_pre env fuel cd ty base head)
Proof
  ho_match_mp_tac calldata_value_ind >> rpt strip_tac >>
  simp[Once calldata_value_pre_def] >> rw[] >> gvs[]
QED
val () = cv_auto_trans encoded_abi_parts_def;
val () = cv_auto_trans encoded_abi_tuple_def;
val storage_abi_value_pre_def = cv_auto_trans_pre_rec
  "storage_abi_value_pre storage_abi_elements_pre storage_abi_fields_pre"
  storage_abi_value_def (
  WF_REL_TAC ‘inv_image ($< LEX $< LEX $<) (λx. case x of
    INL (env, fuel, accounts, addr, slot, ty) => (cv$c2n fuel, cv_size ty, 0)
  | INR (INL (env, fuel, accounts, addr, data, element, i, n)) =>
      (cv$c2n fuel, cv_size element, cv$c2n n + 1)
  | INR (INR (env, fuel, accounts, addr, slot, layout, fields)) =>
      (cv$c2n fuel, cv_size fields, 1))’ >>
  cv_termination_tac
);

Theorem storage_abi_value_pre[cv_pre]:
  (∀env fuel accounts addr slot ty. storage_abi_value_pre env fuel accounts addr slot ty) ∧
  (∀env fuel accounts addr data element i n.
     storage_abi_elements_pre env fuel accounts addr data element i n) ∧
  (∀env fuel accounts addr slot layout fields.
     storage_abi_fields_pre env fuel accounts addr slot layout fields)
Proof
  ho_match_mp_tac storage_abi_value_ind >> rpt strip_tac >>
  simp[Once storage_abi_value_pre_def] >> rw[] >> gvs[]
QED
val () = cv_auto_trans array_copy_value_def;
val () = cv_auto_trans runtime_abi_value_def;
val runtime_abi_values_pre_def =
  cv_auto_trans_pre "runtime_abi_values_pre" runtime_abi_values_def;

Theorem runtime_abi_values_pre[cv_pre,local]:
  ∀env st tys vs. runtime_abi_values_pre env st tys vs
Proof
  ho_match_mp_tac runtime_abi_values_ind >> rpt strip_tac >>
  simp[Once runtime_abi_values_pre_def] >> rw[] >> gvs[]
QED

val () = cv_auto_trans encoded_runtime_values_def;
val () = cv_auto_trans packed_value_def;
val packed_values_pre_def =
  cv_auto_trans_pre "packed_values_pre" packed_values_def;

Theorem packed_values_pre[cv_pre]:
  ∀env st tys vs. packed_values_pre env st tys vs
Proof
  ho_match_mp_tac packed_values_ind >> rpt strip_tac >>
  simp[Once packed_values_pre_def] >> rw[] >> gvs[]
QED
val () = cv_auto_trans memory_free_pointer_def;
val decode_memory_value_pre_def = cv_auto_trans_pre_rec
  "decode_memory_value_pre decode_memory_elements_pre decode_memory_fields_pre decode_memory_part_pre"
  decode_memory_value_def (
  WF_REL_TAC ‘inv_image ($< LEX $< LEX $<) (λx. case x of
    INL (_, fuel, ty, _) => (cv$c2n fuel, cv_size ty, 1)
  | INR (INL (_, fuel, element, _, _, _, n, _)) =>
      (cv$c2n fuel, cv_size element, cv$c2n n + 3)
  | INR (INR (INL (_, fuel, tys, _))) =>
      (cv$c2n fuel, cv_size tys, 0)
  | INR (INR (INR (_, fuel, ty, _))) =>
      (cv$c2n fuel, cv_size ty, 2))’ >>
  cv_termination_tac
);

Theorem decode_memory_value_pre[cv_pre]:
  (∀env fuel ty bs pos free. decode_memory_value_pre env fuel ty bs pos free) ∧
  (∀env fuel element bs data i n free.
     decode_memory_elements_pre env fuel element bs data i n free) ∧
  (∀env fuel tys bs base src free. decode_memory_fields_pre env fuel tys bs base src free) ∧
  (∀env fuel ty bs base src free. decode_memory_part_pre env fuel ty bs base src free)
Proof
  ho_match_mp_tac decode_memory_value_ind >> rpt strip_tac >>
  simp[Once decode_memory_value_pre_def] >> rw[] >> gvs[]
QED
val () = cv_auto_trans copy_calldata_array_def;
val memory_value_size_pre_def = cv_auto_trans_pre_rec
  "memory_value_size_pre memory_values_size_pre memory_fields_size_pre" memory_value_size_def (
  WF_REL_TAC ‘measure (λx. case x of
    INL (env, ty, v) => cv_size v
  | INR (INL (env, element, vs)) => cv_size vs
  | INR (INR (env, tys, vs)) => cv_size vs)’ >>
  cv_termination_tac
);

Theorem memory_value_size_pre[cv_pre]:
  (∀env ty v. memory_value_size_pre env ty v) ∧
  (∀env element vs. memory_values_size_pre env element vs) ∧
  (∀env tys vs. memory_fields_size_pre env tys vs)
Proof
  ho_match_mp_tac memory_value_size_ind >> rpt strip_tac >>
  simp[Once memory_value_size_pre_def] >> rw[] >> gvs[]
QED

val () = cv_auto_trans decode_abi_argument_def;
val () = cv_auto_trans decode_abi_arguments_def;
val () = cv_auto_trans decode_arguments_def;
val materialize_value_pre_def = cv_auto_trans_pre_rec "materialize_value_pre materialize_values_pre materialize_fields_pre" materialize_value_def (
  WF_REL_TAC ‘measure (λx. case x of
    INL (env, loc, ty, v, st) => cv_size v
  | INR (INL (env, loc, element, i, vs, cells, st)) => cv_size vs
  | INR (INR (env, loc, tys, i, vs, cells, st)) => cv_size vs)’ >>
  cv_termination_tac
);

Theorem materialize_value_pre[cv_pre]:
  (∀env loc ty v st. materialize_value_pre env loc ty v st) ∧
  (∀env loc element i vs cells st. materialize_values_pre env loc element i vs cells st) ∧
  (∀env loc tys i vs cells st. materialize_fields_pre env loc tys i vs cells st)
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
  ∀env tys vs st. materialize_arguments_pre env tys vs st
Proof
  ho_match_mp_tac materialize_arguments_ind >> rpt strip_tac >>
  simp[Once materialize_arguments_pre_def] >> rw[] >> fs[]
QED
val () = cv_auto_trans panic_data_def;
val indexed_data_pre_def = cv_auto_trans_pre_rec
  "indexed_data_pre indexed_parts_pre" indexed_data_def (
  WF_REL_TAC ‘measure (λx. case x of
    INL (t, a, encoded) => cv_size a
  | INR (ts, vs, encoded, pos) => cv_size vs)’ >>
  cv_termination_tac
);

Theorem indexed_data_pre[cv_pre]:
  (∀t a encoded. indexed_data_pre t a encoded) ∧
  (∀ts vs encoded pos. indexed_parts_pre ts vs encoded pos)
Proof
  ho_match_mp_tac indexed_data_ind >> rpt strip_tac >>
  simp[Once indexed_data_pre_def] >> rw[] >> gvs[]
QED

val event_parts_pre_def = cv_auto_trans_pre "event_parts_pre"
  (REWRITE_RULE [GSYM byteTheory.word_of_bytes_be_def] event_parts_def);

Theorem event_parts_pre[cv_pre,local]:
  ∀env st args. event_parts_pre env st args
Proof
  ho_match_mp_tac event_parts_ind >> rpt strip_tac >>
  simp[Once event_parts_pre_def] >> rw[] >> gvs[]
QED

val () = cv_auto_trans event_log_def;
