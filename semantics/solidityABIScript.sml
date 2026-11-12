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
  (abi_type (EnumT _) = Uint 8) ∧
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
  (abi_value (EnumT _) (ScalarValue (IntegerValue i)) = SOME (NumV (Num i))) ∧
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

(* The ABI value of an array value read element by element: elements in
 * order, each array a list. *)
Definition value_abi_value_def:
  (value_abi_value ty v =
    case (ty, v) of
      (ArrayT element _, TupleValue vs) =>
        OPTION_MAP ListV (values_abi_value element vs)
    | (ArrayT _ _, _) => NONE
    | _ => abi_value ty v) ∧
  (values_abi_value element [] = SOME []) ∧
  (values_abi_value element (v :: vs) =
    case (value_abi_value element v, values_abi_value element vs) of
      (SOME a, SOME as) => SOME (a :: as)
    | _ => NONE)
Termination
  WF_REL_TAC ‘measure (λx. case x of
    INL (ty, v) => runtime_value_size v
  | INR (element, vs) => list_size runtime_value_size vs)’ >>
  rw[solidityCoreTheory.runtime_value_size_def, listTheory.list_size_def]
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

(* The bytes an element takes in its array's encoding. *)
Definition abi_stride_def:
  abi_stride ty =
    if is_dynamic (abi_type ty) then 32 else static_length (abi_type ty)
End

(* The calldata word at pos, zero past the end, as CALLDATALOAD reads it. *)
Definition calldata_word_def:
  calldata_word (cd : byte list) pos =
    num_of_be_bytes (TAKE 32 (DROP pos cd ++ REPLICATE 32 0w))
End

(* A dynamic element in calldata, reached as the pinned compiler does: the
 * offset at ptr, relative to base, is a signed word below the calldata left
 * after base; the length there is below 2^64; and its data of stride bytes per
 * element ends within the calldata, compared as signed words. Addresses wrap
 * at 2^256. The data's position and the length. *)
Definition calldata_tail_def:
  calldata_tail cd base ptr stride =
    let size : 256 word = n2w (LENGTH cd) in
    let rel : 256 word = n2w (calldata_word cd ptr) in
    if ¬(rel < size - n2w base - 31w) then INR (RevertCompletion []) else
    let addr = n2w base + rel in
    let length = calldata_word cd (w2n addr) in
    if 2 ** 64 ≤ length then INR (RevertCompletion []) else
    let data = addr + 32w in
    if size - n2w (length * stride) < data then INR (RevertCompletion [])
    else INL (w2n data, length)
End

(* Element i of a calldata array whose data starts at data: a scalar read and
 * validated in place, a static array in place, and a byte sequence or a
 * dynamic array through its offset. *)
Definition calldata_element_def:
  calldata_element cd element data i =
    if is_elementary_type element then
      let word = TAKE 32 (DROP (data + 32 * i) cd ++ REPLICATE 32 0w) in
      if ¬valid_enc (abi_type element) word then INR (RevertCompletion []) else
      (case abi_runtime_value element (dec (abi_type element) word) of
         SOME v => INL v
       | NONE => INR (InvalidCompletion "bad calldata element type"))
    else case element of
      ArrayT _ (SOME n) =>
        INL (ReferenceValue (CalldataReference
          (data + i * static_length (abi_type element)) n element))
    | _ =>
      let stride = case element of ArrayT inner NONE => abi_stride inner | _ => 1 in
      case calldata_tail cd data (data + 32 * i) stride of
        INL (pos, length) =>
          INL (ReferenceValue (CalldataReference pos length element))
      | INR c => INR c
End

(* The value of a calldata array or byte sequence of the given length at
 * data, read element by element through the pinned compiler's calldata
 * accessors, so an invalid element or offset reverts: an array as the tuple
 * of its elements, a byte sequence as its bytes. The encoder and a copy to
 * storage both read calldata this way. *)
Definition calldata_value_def:
  (calldata_value cd ty data length =
    case ty of
      ArrayT element _ =>
        (case calldata_values cd element data 0 length of
           INL vs => INL (TupleValue vs)
         | INR c => INR c)
    | _ => INL (ScalarValue (BytesValue
             (TAKE length (DROP data cd ++ REPLICATE length 0w))))) ∧
  (calldata_values cd element data i n =
    if n = 0 then INL [] else
    case calldata_element cd element data i of
      INR c => INR c
    | INL v =>
      let value =
        case v of
          ReferenceValue (CalldataReference pos length _) =>
            calldata_value cd element pos length
        | _ => INL v in
      case value of
        INR c => INR c
      | INL v' =>
        case calldata_values cd element data (i + 1) (n - 1) of
          INL vs => INL (v' :: vs)
        | INR c => INR c)
Termination
  WF_REL_TAC ‘inv_image ($< LEX $<) (λx. case x of
    INL (cd, ty, data, length) => (sol_type_size ty, 0)
  | INR (cd, element, data, i, n) => (sol_type_size element, n + 1))’ >>
  rw[solidityASTTheory.sol_type_size_def]
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

(* A storage array or byte sequence encoded in place, as the pinned encoder
 * does: its ABI value and its encoding. Scalar elements are read cleaned; a
 * byte sequence copies whole data words, keeping unused dirty bytes, except
 * the length byte of a short one. A length of 2^64 or more panics with 0x41,
 * as the memory for the encoding cannot be allocated. *)
Definition storage_abi_value_def:
  (storage_abi_value env accounts addr slot ty =
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
             case storage_abi_elements env accounts addr data element 0 length of
               INL parts =>
                 INL (ListV (MAP FST parts),
                      (if l = NONE then enc (Uint 256) (NumV length) else []) ++
                      encoded_abi_tuple (MAP (λp. (abi_type element, SND p)) parts))
             | INR c => INR c)
    | _ => INR (InvalidCompletion "bad storage array type")) ∧
  (storage_abi_elements env accounts addr data element i n =
    if n = 0 then INL [] else
    case storage_element_location env data element i of
      NONE => INR (InvalidCompletion "bad array element type")
    | SOME (s, offset) =>
        let value =
          if is_stored_scalar_type element then
            (case read_storage env accounts addr s offset element of
               SOME v =>
                 (case abi_value element (ScalarValue v) of
                    SOME a => INL (a, enc (abi_type element) a)
                  | NONE => INR (InvalidCompletion "bad ABI value"))
             | NONE => INR (InvalidCompletion "bad storage read"))
          else storage_abi_value env accounts addr s element in
        case value of
          INR c => INR c
        | INL entry =>
            case storage_abi_elements env accounts addr data element (i + 1) (n - 1) of
              INL entries => INL (entry :: entries)
            | INR c => INR c)
Termination
  WF_REL_TAC ‘inv_image ($< LEX $<) (λx. case x of
    INL (env, accounts, addr, slot, ty) => (sol_type_size ty, 0)
  | INR (env, accounts, addr, data, element, i, n) => (sol_type_size element, n + 1))’ >>
  rw[solidityASTTheory.sol_type_size_def]
End

(* Keep both the logical value (for indexed hashes) and its encoded body.
 * Storage encoders copy complete data words, retaining unused dirty bytes. *)
Definition runtime_abi_value_def:
  runtime_abi_value env st ty v =
    case ty of
      LocatedT _ (ArrayT element length) =>
        (case v of
           ReferenceValue (CalldataReference data n rty) =>
             if rty ≠ ArrayT element length then INR (InvalidCompletion "bad ABI value")
             else (case calldata_value st.frame.call_data rty data n of
                     INR c => INR c
                   | INL tree =>
                     case value_abi_value rty tree of
                       SOME a => INL (a, enc (abi_type ty) a)
                     | NONE => INR (InvalidCompletion "bad ABI value"))
         | ReferenceValue (StorageReference PersistentStorage addr slot 0 rty _) =>
             if rty ≠ ArrayT element length then INR (InvalidCompletion "bad ABI value")
             else storage_abi_value env st.world.accounts addr slot rty
         | _ =>
           case memory_abi_value st (ArrayT element length) v of
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

Definition runtime_abi_values_def:
  (runtime_abi_values env (st : source_state) [] [] =
     (INL [] : (contractABI$abi_type # byte list) list + source_completion)) ∧
  (runtime_abi_values env st (ty :: tys) (v :: vs) =
    case runtime_abi_value env st ty v of
      INR c => INR c
    | INL (a, encoded_body) =>
      (case runtime_abi_values env st tys vs of
         INL encoded => INL ((abi_type ty, encoded_body) :: encoded)
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
  packed_value st ty v =
    case ty of
      LocatedT _ _ =>
        (case v of
           ReferenceValue r => byte_contents st r
         | ScalarValue (BytesValue bs) => INL bs
         | _ => INR (InvalidCompletion "bad packed value"))
    | _ =>
      case (abi_value ty v, storage_bytes ty) of
        (SOME a, SOME width) =>
          let word = enc (abi_type ty) a in
          INL (case ty of
                 FixedBytesT _ => TAKE width word
               | _ => DROP (32 - width) word)
      | _ => INR (InvalidCompletion "bad packed value")
End

Definition packed_values_def:
  (packed_values st [] [] = (INL [] : byte list + source_completion)) ∧
  (packed_values st (ty :: tys) (v :: vs) =
    case packed_value st ty v of
      INR c => INR c
    | INL bs =>
      case packed_values st tys vs of
        INL rest => INL (bs ++ rest)
      | INR c => INR c) ∧
  (packed_values _ _ _ = INR (InvalidCompletion "bad packed values"))
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

(* A memory copy of a calldata array whose data starts at data, as the pinned
 * compiler converts one: allocated, its data span checked, then decoded as an
 * ABI argument is. *)
Definition copy_calldata_array_def:
  copy_calldata_array cd ty data length free =
    case ty of
      ArrayT element l =>
        let size = (if l = NONE then 32 else 0) + 32 * length in
        if 2 ** 64 ≤ free + size then INR (PanicCompletion 65)
        else if data + length * abi_stride element > LENGTH cd then
          INR (RevertCompletion [])
        else (case decode_memory_elements element cd data 0 length (free + size) of
                INL (vs, _) => INL (TupleValue vs)
              | INR c => INR c)
    | _ => INR (InvalidCompletion "bad calldata array copy")
End

(* The memory a value of type ty takes once materialized: each array's
 * elements and length word, and each byte sequence's length and data. *)
Definition memory_value_size_def:
  (memory_value_size ty v =
    case (ty, v) of
      (ArrayT element length, TupleValue vs) =>
        (if length = NONE then 32 else 0) + 32 * LENGTH vs +
        memory_values_size element vs
    | (_, ScalarValue (BytesValue bs)) =>
        if byte_sequence_type ty then 32 + 32 * ((LENGTH bs + 31) DIV 32) else 0
    | _ => 0) ∧
  (memory_values_size element [] = 0) ∧
  (memory_values_size element (v :: vs) =
    memory_value_size element v + memory_values_size element vs)
Termination
  WF_REL_TAC ‘measure (λx. case x of
    INL (ty, v) => runtime_value_size v
  | INR (element, vs) => list_size runtime_value_size vs)’ >>
  rw[solidityCoreTheory.runtime_value_size_def, listTheory.list_size_def]
End

(* The value of a memory, calldata or storage array of type ty, as a copy to
 * storage reads it. A calldata array is read through the calldata accessors;
 * its own data span was checked when it was decoded. *)
Definition array_copy_value_def:
  array_copy_value env (st : source_state) ty r =
    case r of
      MemoryReference _ _ _ => memory_array_value st ty (ReferenceValue r)
    | CalldataReference data n rty =>
        if rty ≠ ty then INR (InvalidCompletion "bad calldata array reference")
        else calldata_value st.frame.call_data ty data n
    | StorageReference PersistentStorage addr slot 0 rty _ =>
        if rty ≠ ty then INR (InvalidCompletion "bad storage array reference")
        else storage_array_value env st.world.accounts addr slot ty
    | _ => INR (InvalidCompletion "bad array reference")
End

(* An argument at head: a scalar or static array in place, any other value at
 * the offset the head holds. A calldata byte sequence stays in the calldata.
 * An enum outside its members reverts, as the pinned decoder's validator
 * does before it reads the next argument. *)
Definition decode_abi_argument_def:
  decode_abi_argument env ty bs head base free =
    if head + 32 > LENGTH bs then INR (RevertCompletion []) else
    case ty of
      LocatedT CalldataLoc (ArrayT element (SOME n)) =>
        INL (ReferenceValue (CalldataReference (base + head) n (ArrayT element (SOME n))), free)
    | LocatedT CalldataLoc element =>
        let offset = abi_word bs head in
        if 2 ** 64 ≤ offset ∨ offset + 32 > LENGTH bs then
          INR (RevertCompletion []) else
        let length = abi_word bs offset in
        let stride = case element of ArrayT inner NONE => abi_stride inner | _ => 1 in
        if 2 ** 64 ≤ length ∨ offset + 32 + length * stride > LENGTH bs then
          INR (RevertCompletion [])
        else INL (ReferenceValue (CalldataReference (base + offset + 32) length element), free)
    | LocatedT MemoryLoc element =>
        if is_dynamic (abi_type element) then
          let offset = abi_word bs head in
          if 2 ** 64 ≤ offset then INR (RevertCompletion [])
          else decode_memory_value element bs offset free
        else decode_memory_value element bs head free
    | EnumT _ =>
        (case decode_memory_value ty bs head free of
           INL (ScalarValue s, next) =>
             if scalar_has_type env ty s then INL (ScalarValue s, next)
             else INR (RevertCompletion [])
         | INL _ => INR (InvalidCompletion "bad ABI enum")
         | INR c => INR c)
    | _ => decode_memory_value ty bs head free
End

Definition decode_abi_arguments_def:
  (decode_abi_arguments env [] bs head base free = INL []) ∧
  (decode_abi_arguments env (ty :: tys) bs head base free =
    case decode_abi_argument env ty bs head base free of
      INR c => INR c
    | INL (v, next) =>
        case decode_abi_arguments env tys bs (head + abi_stride ty) base next of
          INL vs => INL (v :: vs)
        | INR c => INR c)
End

Definition decode_arguments_def:
  decode_arguments env tys bs base free =
    if head_lengths (MAP abi_type tys) 0 > LENGTH bs then INR (RevertCompletion [])
    else decode_abi_arguments env tys bs 0 base free
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
                     object_cells := FEMPTY;
                     object_address := 128 + st.memory_allocated;
                     object_padded := T |> in
        let st1 = st with <| heap := st.heap |+ (id, obj); next_heap_id := id;
                     memory_allocated := st.memory_allocated +
                       (if length = NONE then 32 else 0) + 32 * n |> in
        (case materialize_values element 0 vs FEMPTY st1 of
           SOME (cells, st2) =>
             SOME (ReferenceValue (MemoryReference (HeapId id) 0 ty),
                   st2 with heap := st2.heap |+ (id, obj with object_cells := cells))
         | NONE => NONE)
    | (_, ScalarValue (BytesValue bs)) =>
        if byte_sequence_type ty then SOME (allocate_bytes T ty bs st)
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

(* Indexed arrays concatenate their elements without lengths or offsets.
 * Byte/string elements retain whole padded words from the existing ABI body:
 * the storage encoder may have copied dirty padding into those words.
 *)
Definition indexed_array_data_def:
  (indexed_array_data ty a (encoded : byte list) =
    case (ty, a) of
      (ArrayT element length, ListV vs) =>
        indexed_array_elements element vs
          (if length = NONE then DROP 32 encoded else encoded) 0
    | (ArrayT _ _, _) => NONE
    | (_, BytesV bs) =>
        if byte_sequence_type ty then
          SOME (TAKE (32 * ((LENGTH bs + 31) DIV 32)) (DROP 32 encoded))
        else SOME (TAKE 32 encoded)
    | _ => SOME (TAKE 32 encoded)) ∧
  (indexed_array_elements element [] encoded pos = SOME []) ∧
  (indexed_array_elements element (v :: vs) encoded pos =
    let offset = if is_dynamic (abi_type element) then abi_word encoded pos else pos in
    case (indexed_array_data element v (DROP offset encoded),
          indexed_array_elements element vs encoded (pos + abi_stride element)) of
      (SOME bs, SOME rest) => SOME (bs ++ rest)
    | _ => NONE)
Termination
  WF_REL_TAC ‘measure (λx. case x of
    INL (ty, a, encoded) => abi_value_size a
  | INR (element, vs, encoded, pos) => list_size abi_value_size vs)’ >>
  rw[contractABITheory.abi_value_size_def, listTheory.list_size_def]
End

(* Event arguments split into indexed topics and data. Arrays and byte
 * sequences hash their in-place encoding; scalar topics are ABI words.
 *)
Definition event_parts_def:
  (event_parts env st [] = INL ([], [])) ∧
  (event_parts env st ((ty, indexed, v) :: args) =
    case runtime_abi_value env st ty v of
      INR c => INR c
    | INL (a, encoded_body) =>
      (case event_parts env st args of
         INR c => INR c
       | INL (topics, parts) =>
        if indexed then
          let topic = case ty of
            LocatedT _ (ArrayT element length) =>
              OPTION_MAP (λbs. word_of_bytes_be (Keccak_256_w64 bs))
                (indexed_array_data (ArrayT element length) a encoded_body)
          | _ => SOME (case a of
                   BytesV bs => if byte_sequence_value_type ty then
                     word_of_bytes_be (Keccak_256_w64 bs)
                     else word_of_bytes T (0w : bytes32) encoded_body
                 | _ => word_of_bytes T (0w : bytes32) encoded_body) in
          (case topic of
             SOME t => INL (t :: topics, parts)
           | NONE => INR (InvalidCompletion "bad indexed event argument"))
        else INL (topics, (abi_type ty, encoded_body) :: parts)))
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

val () = cv_auto_trans abi_type_def;
val () = cv_auto_trans abi_value_def;
val () = cv_auto_trans abi_values_def;
val value_abi_value_pre_def = cv_auto_trans_pre_rec
  "value_abi_value_pre values_abi_value_pre" value_abi_value_def (
  WF_REL_TAC ‘measure (λx. case x of
    INL (ty, v) => cv_size v
  | INR (element, vs) => cv_size vs)’ >>
  cv_termination_tac
);

Theorem value_abi_value_pre[cv_pre]:
  (∀ty v. value_abi_value_pre ty v) ∧
  (∀element vs. values_abi_value_pre element vs)
Proof
  ho_match_mp_tac value_abi_value_ind >> rpt strip_tac >>
  simp[Once value_abi_value_pre_def] >> rw[] >> gvs[]
QED
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
val () = cv_auto_trans abi_word_def;
val () = cv_auto_trans abi_stride_def;
val () = cv_auto_trans calldata_word_def;
val () = cv_auto_trans calldata_tail_def;
val () = cv_auto_trans calldata_element_def;
val calldata_value_pre_def = cv_auto_trans_pre_rec "calldata_value_pre calldata_values_pre" calldata_value_def (
  WF_REL_TAC ‘inv_image ($< LEX $<) (λx. case x of
    INL (cd, ty, data, length) => (cv_size ty, 0)
  | INR (cd, element, data, i, n) => (cv_size element, cv$c2n n + 1))’ >>
  cv_termination_tac
);

Theorem calldata_value_pre[cv_pre]:
  (∀cd ty data length. calldata_value_pre cd ty data length) ∧
  (∀cd element data i n. calldata_values_pre cd element data i n)
Proof
  ho_match_mp_tac calldata_value_ind >> rpt strip_tac >>
  simp[Once calldata_value_pre_def] >> rw[] >> gvs[]
QED
val () = cv_auto_trans encoded_abi_parts_def;
val () = cv_auto_trans encoded_abi_tuple_def;
val storage_abi_value_pre_def = cv_auto_trans_pre_rec
  "storage_abi_value_pre storage_abi_elements_pre" storage_abi_value_def (
  WF_REL_TAC ‘inv_image ($< LEX $<) (λx. case x of
    INL (env, accounts, addr, slot, ty) => (cv_size ty, 0)
  | INR (env, accounts, addr, data, element, i, n) => (cv_size element, cv$c2n n + 1))’ >>
  cv_termination_tac
);

Theorem storage_abi_value_pre[cv_pre]:
  (∀env accounts addr slot ty. storage_abi_value_pre env accounts addr slot ty) ∧
  (∀env accounts addr data element i n.
     storage_abi_elements_pre env accounts addr data element i n)
Proof
  ho_match_mp_tac storage_abi_value_ind >> rpt strip_tac >>
  simp[Once storage_abi_value_pre_def] >> rw[] >> gvs[]
QED
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
  ∀st tys vs. packed_values_pre st tys vs
Proof
  ho_match_mp_tac packed_values_ind >> rpt strip_tac >>
  simp[Once packed_values_pre_def] >> rw[] >> gvs[]
QED
val () = cv_auto_trans memory_free_pointer_def;
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
val () = cv_auto_trans copy_calldata_array_def;
val memory_value_size_pre_def = cv_auto_trans_pre_rec
  "memory_value_size_pre memory_values_size_pre" memory_value_size_def (
  WF_REL_TAC ‘measure (λx. case x of
    INL (ty, v) => cv_size v
  | INR (element, vs) => cv_size vs)’ >>
  cv_termination_tac
);

Theorem memory_value_size_pre[cv_pre]:
  (∀ty v. memory_value_size_pre ty v) ∧
  (∀element vs. memory_values_size_pre element vs)
Proof
  ho_match_mp_tac memory_value_size_ind >> rpt strip_tac >>
  simp[Once memory_value_size_pre_def] >> rw[] >> gvs[]
QED

val () = cv_auto_trans array_copy_value_def;
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
val indexed_array_data_pre_def = cv_auto_trans_pre_rec
  "indexed_array_data_pre indexed_array_elements_pre" indexed_array_data_def (
  WF_REL_TAC ‘measure (λx. case x of
    INL (ty, a, encoded) => cv_size a
  | INR (element, vs, encoded, pos) => cv_size vs)’ >>
  cv_termination_tac
);

Theorem indexed_array_data_pre[cv_pre]:
  (∀ty a encoded. indexed_array_data_pre ty a encoded) ∧
  (∀element vs encoded pos. indexed_array_elements_pre element vs encoded pos)
Proof
  ho_match_mp_tac indexed_array_data_ind >> rpt strip_tac >>
  simp[Once indexed_array_data_pre_def] >> rw[] >> gvs[]
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
