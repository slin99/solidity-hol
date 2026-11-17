(* Scalar semantics: operators and conversions over canonical values.
 *
 * Values carry no dirty bits: IntegerValue holds the mathematical integer, and
 * fixed bytes hold exactly n bytes. "Cleanup" is therefore wrapping into a
 * type's range; cleanup of raw EVM words belongs to the ABI/storage boundary.
 *
 * Behaviour follows the pinned Solidity documentation (SOLIDITY_PIN):
 * docs/types/value-types.rst, docs/types/conversion.rst and the panic codes in
 * docs/control-structures.rst. Inputs are checked against the operator
 * signature and value types; ill-typed input is ScalarInvalid, never a panic.
 *)
Theory solidityScalar
Ancestors
  solidityCoreWf vfmExecution byte arithmetic integer words
Libs
  cv_transLib wordsLib intLib

Datatype:
  scalar_outcome = ScalarOk scalar | ScalarPanic num | ScalarInvalid
End

Definition panic_arithmetic_def:
  panic_arithmetic = 0x11n
End

Definition panic_division_by_zero_def:
  panic_division_by_zero = 0x12n
End

Definition panic_enum_conversion_def:
  panic_enum_conversion = 0x21n
End

(* A call of the zero internal function value. *)
Definition panic_zero_function_def:
  panic_zero_function = 0x51n
End

(* Integers *)

(* Two's complement truncation to n bits. *)
Definition wrap_integer_def:
  wrap_integer signed n (i : int) =
    let m = i % &(2 ** n) in
    if signed ∧ 0 < n ∧ &(2 ** (n - 1)) ≤ m then m - &(2 ** n) else m
End

Theorem wrap_integer_in_range:
  integer_in_range signed n (wrap_integer signed n i)
Proof
  ‘∃M. (2 : num) ** n = M’ by simp[] >>
  ‘0 < M’ by (rw[] >> gvs[]) >>
  ‘0 ≤ i % &M ∧ i % &M < &M’
    by (mp_tac (Q.SPECL [‘i’, ‘&M’] INT_MOD_BOUNDS) >> simp[]) >>
  qabbrev_tac ‘m = i % &M’ >>
  Cases_on ‘n’ >> gvs[EXP, wrap_integer_def, integer_in_range_def] >>
  rw[] >> intLib.ARITH_TAC
QED

Theorem wrap_integer_id:
  0 < n ∧ integer_in_range signed n i ⇒ wrap_integer signed n i = i
Proof
  strip_tac >> Cases_on ‘n’ >> gvs[EXP] >>
  qabbrev_tac ‘H = (2 : num) ** n'’ >>
  gvs[integer_in_range_def, wrap_integer_def, EXP] >>
  Cases_on ‘signed’ >> gvs[]
  >- (Cases_on ‘0 ≤ i’
      >- (‘i % &(2 * H) = i’ by (irule INT_LESS_MOD >> intLib.ARITH_TAC) >>
          simp[] >> intLib.ARITH_TAC) >>
      ‘i % &(2 * H) = i + &(2 * H)’
        by (irule INT_MOD_UNIQUE >> qexists_tac ‘-1’ >> intLib.ARITH_TAC) >>
      simp[] >> intLib.ARITH_TAC) >>
  irule INT_LESS_MOD >> simp[]
QED

Definition integer_result_def:
  integer_result signed n i = ScalarOk (IntegerValue (wrap_integer signed n i))
End

(* Checked overflow panics with 0x11; unchecked arithmetic wraps. *)
Definition arithmetic_result_def:
  arithmetic_result mode signed n i =
    if integer_in_range signed n i then ScalarOk (IntegerValue i)
    else case mode of
           CheckedArithmetic => ScalarPanic panic_arithmetic
         | UncheckedArithmetic => integer_result signed n i
End

(* Exponents range over uint256, so x ** e is never built for a large e:
 * bases 0, 1 and -1 have closed forms, any other base overflows n bits once
 * e ≥ n, and unchecked results use verifereum's square-and-multiply modexp
 * modulo 2 ** n (modexp_exp gives its meaning).
 *)
Definition integer_exponent_def:
  integer_exponent mode signed n (x : int) (e : num) =
    case mode of
      UncheckedArithmetic =>
        integer_result signed n (&modexp (Num (x % &(2 ** n))) e (2 ** n) 1)
    | CheckedArithmetic =>
        if x = 0 then arithmetic_result mode signed n (if e = 0 then 1 else 0)
        else if x = 1 then arithmetic_result mode signed n 1
        else if x = -1 then
          arithmetic_result mode signed n (if EVEN e then 1 else -1)
        else if e < n then arithmetic_result mode signed n (x ** e)
        else ScalarPanic panic_arithmetic
End

(* Shifts are never checked. x << y truncates x * 2 ** y; x >> y is
 * x / 2 ** y rounded towards negative infinity. Amounts ≥ n are capped.
 *)
Definition shift_left_def:
  shift_left signed n (x : int) (y : num) =
    if n ≤ y then 0 else wrap_integer signed n (x * &(2 ** y))
End

Definition shift_right_def:
  shift_right n (x : int) (y : num) =
    if n ≤ y then (if x < 0 then -1 else 0) else x / &(2 ** y)
End

(* The binary bitwise operator of op (and, or, xor), at the two word widths
 * used here; monomorphic so that they translate to cv. The xor fall-through
 * is reached only from the BitAndOp/BitOrOp/BitXorOp branches of the callers.
 *)
Definition word256_bitwise_def:
  word256_bitwise op (a : 256 word) b =
    case op of
      BitAndOp => word_and a b
    | BitOrOp => word_or a b
    | _ => word_xor a b
End

Definition byte_bitwise_def:
  byte_bitwise op (a : byte) b =
    case op of
      BitAndOp => word_and a b
    | BitOrOp => word_or a b
    | _ => word_xor a b
End

(* Bitwise operators act on n-bit two's complement representatives. *)
Definition integer_bitwise_def:
  integer_bitwise op signed n (x : int) (y : int) =
    let rx = Num (x % &(2 ** n)) in
    let ry = Num (y % &(2 ** n)) in
    wrap_integer signed n
      (&w2n (word256_bitwise op (n2w rx) (n2w ry)))
End

(* Division rounding towards zero and the matching remainder, stated without
 * a side condition (unlike quot/rem) so that they translate to cv. They agree
 * with quot/rem for a non-zero divisor.
 *)
Definition truncating_quot_def:
  (truncating_quot (i : int) (j : int) : int) =
    if 0 < j then
      if 0 ≤ i then &(Num i DIV Num j) else -&(Num (-i) DIV Num j)
    else if 0 ≤ i then -&(Num i DIV Num (-j))
    else &(Num (-i) DIV Num (-j))
End

Definition truncating_rem_def:
  truncating_rem (i : int) (j : int) = i - truncating_quot i j * j
End

Theorem truncating_quot_eq_quot:
  j ≠ 0 ⇒ truncating_quot i j = i quot j
Proof
  rw[truncating_quot_def, int_quot]
QED

Theorem truncating_rem_eq_rem:
  j ≠ 0 ⇒ truncating_rem i j = i rem j
Proof
  rw[truncating_rem_def, int_rem, truncating_quot_eq_quot]
QED

(* Division rounds towards zero; the remainder takes the dividend's sign.
 * Division and remainder by zero panic even in unchecked mode, and
 * type(int).min / -1 is the only division that overflows. addmod and mulmod
 * take the sum or product without wrapping, and panic on a zero modulus in
 * either mode.
 *)
Definition eval_integer_operation_def:
  eval_integer_operation mode signed n op args =
    case (op, args) of
      (AddOp, [IntegerValue x; IntegerValue y]) =>
        arithmetic_result mode signed n (x + y)
    | (SubtractOp, [IntegerValue x; IntegerValue y]) =>
        arithmetic_result mode signed n (x - y)
    | (MultiplyOp, [IntegerValue x; IntegerValue y]) =>
        arithmetic_result mode signed n (x * y)
    | (DivideOp, [IntegerValue x; IntegerValue y]) =>
        if y = 0 then ScalarPanic panic_division_by_zero
        else arithmetic_result mode signed n (truncating_quot x y)
    | (RemainderOp, [IntegerValue x; IntegerValue y]) =>
        if y = 0 then ScalarPanic panic_division_by_zero
        else integer_result signed n (truncating_rem x y)
    | (AddModOp, [IntegerValue x; IntegerValue y; IntegerValue k]) =>
        if k = 0 then ScalarPanic panic_division_by_zero
        else integer_result signed n (truncating_rem (x + y) k)
    | (MulModOp, [IntegerValue x; IntegerValue y; IntegerValue k]) =>
        if k = 0 then ScalarPanic panic_division_by_zero
        else integer_result signed n (truncating_rem (x * y) k)
    | (ExponentOp, [IntegerValue x; IntegerValue e]) =>
        integer_exponent mode signed n x (Num e)
    | (ShiftLeftOp, [IntegerValue x; IntegerValue y]) =>
        ScalarOk (IntegerValue (shift_left signed n x (Num y)))
    | (ShiftRightOp, [IntegerValue x; IntegerValue y]) =>
        integer_result signed n (shift_right n x (Num y))
    | (BitAndOp, [IntegerValue x; IntegerValue y]) =>
        ScalarOk (IntegerValue (integer_bitwise op signed n x y))
    | (BitOrOp, [IntegerValue x; IntegerValue y]) =>
        ScalarOk (IntegerValue (integer_bitwise op signed n x y))
    | (BitXorOp, [IntegerValue x; IntegerValue y]) =>
        ScalarOk (IntegerValue (integer_bitwise op signed n x y))
    | (NegateOp, [IntegerValue x]) => arithmetic_result mode signed n (-x)
    | (BitNotOp, [IntegerValue x]) => integer_result signed n (-x - 1)
    | _ => ScalarInvalid
End

(* Fixed bytes *)

(* Fixed bytes are big-endian: vfmTypes' num_of_be_bytes reads them, and
 * num_to_bytes k v encodes v mod 256 ** k in exactly k bytes, a view of
 * byteTheory's little-endian bytes_of_num (cv-translated in cv_std).
 * bytesM to bytesN truncates or pads with zeros on the right, which is
 * vfmTypes' take_pad_0. *)
Definition num_to_bytes_def:
  num_to_bytes k (v : num) = REVERSE (bytes_of_num k v)
End

Definition bytes_bitwise_def:
  (bytes_bitwise op (a::as) (b::bs) =
    byte_bitwise op a b :: bytes_bitwise op as bs) ∧
  (bytes_bitwise op _ _ = [])
End

Definition bytes_not_def:
  (bytes_not [] = []) ∧
  (bytes_not ((a : byte)::as) = word_1comp a :: bytes_not as)
End

Definition eval_bytes_operation_def:
  eval_bytes_operation n op args =
    case (op, args) of
      (BitAndOp, [BytesValue a; BytesValue b]) =>
        ScalarOk (BytesValue (bytes_bitwise op a b))
    | (BitOrOp, [BytesValue a; BytesValue b]) =>
        ScalarOk (BytesValue (bytes_bitwise op a b))
    | (BitXorOp, [BytesValue a; BytesValue b]) =>
        ScalarOk (BytesValue (bytes_bitwise op a b))
    | (BitNotOp, [BytesValue a]) => ScalarOk (BytesValue (bytes_not a))
    | (ShiftLeftOp, [BytesValue a; IntegerValue y]) =>
        ScalarOk (BytesValue (num_to_bytes n
          (Num (shift_left F (8 * n) (&num_of_be_bytes a) (Num y)))))
    | (ShiftRightOp, [BytesValue a; IntegerValue y]) =>
        ScalarOk (BytesValue (num_to_bytes n
          (Num (shift_right (8 * n) (&num_of_be_bytes a) (Num y)))))
    | _ => ScalarInvalid
End

(* Comparisons *)

(* Addresses compare as uint160 and fixed bytes as big-endian integers. *)
Definition scalar_order_key_def:
  (scalar_order_key (IntegerValue i) = SOME i) ∧
  (scalar_order_key (AddressValue a) = SOME (&w2n a)) ∧
  (scalar_order_key (BytesValue bs) = SOME (&num_of_be_bytes bs)) ∧
  (scalar_order_key _ = NONE)
End

(* Operations *)

Definition scalars_have_types_def:
  (scalars_have_types env [] [] ⇔ T) ∧
  (scalars_have_types env (ty::tys) (s::ss) ⇔
    scalar_has_type env ty s ∧ scalars_have_types env tys ss) ∧
  (scalars_have_types env _ _ ⇔ F)
End

Definition eval_scalar_operation_def:
  eval_scalar_operation env ty mode op args =
    case scalar_operator_signature op ty of
      NONE => ScalarInvalid
    | SOME (operand_tys, _) =>
        if ¬scalars_have_types env operand_tys args then ScalarInvalid
        else
          case (op, args) of
            (EqualOp, [a; b]) => ScalarOk (BoolValue (a = b))
          | (LessThanOp, [a; b]) =>
              (case (scalar_order_key a, scalar_order_key b) of
                 (SOME x, SOME y) => ScalarOk (BoolValue (x < y))
               | _ => ScalarInvalid)
          | (BoolNotOp, [BoolValue b]) => ScalarOk (BoolValue (¬b))
          | _ =>
              (case ty of
                 UintT n =>
                   if valid_int_width n
                   then eval_integer_operation mode F n op args
                   else ScalarInvalid
               | IntT n =>
                   if valid_int_width n
                   then eval_integer_operation mode T n op args
                   else ScalarInvalid
               | FixedBytesT n =>
                   if valid_fixed_bytes_width n
                   then eval_bytes_operation n op args
                   else ScalarInvalid
               | _ => ScalarInvalid)
End

(* Conversions *)

(* Explicit conversions are directed by the target type and the source value;
 * core_convertible restricts the admitted pairs. Integer conversions all
 * truncate or extend in two's complement. Integer/bytes and address/bytes
 * conversions are big-endian re-encodings between equal sizes. Conversion to
 * an enum panics with 0x21 when out of range, even in unchecked mode.
 * User-defined value types share their underlying representation, and an
 * internal function value is the same under every mutability.
 *)
Definition convert_scalar_def:
  convert_scalar env dst s =
    case (dst, s) of
      (UintT n, IntegerValue i) => ScalarOk (IntegerValue (wrap_integer F n i))
    | (IntT n, IntegerValue i) => ScalarOk (IntegerValue (wrap_integer T n i))
    | (UintT n, BytesValue bs) => ScalarOk (IntegerValue (&num_of_be_bytes bs))
    | (UintT n, AddressValue a) => ScalarOk (IntegerValue (&w2n a))
    | (FixedBytesT n, BytesValue bs) => ScalarOk (BytesValue (take_pad_0 n bs))
    | (FixedBytesT n, IntegerValue i) =>
        ScalarOk (BytesValue (num_to_bytes n (Num i)))
    | (FixedBytesT n, AddressValue a) =>
        ScalarOk (BytesValue (num_to_bytes n (w2n a)))
    | (AddressT _, AddressValue a) => ScalarOk s
    | (AddressT _, IntegerValue i) => ScalarOk (AddressValue (n2w (Num i)))
    | (AddressT _, BytesValue bs) => ScalarOk (AddressValue (n2w (num_of_be_bytes bs)))
    | (EnumT id, IntegerValue i) =>
        (case lookup_enum env id of
           SOME members =>
             if 0 ≤ i ∧ i < &members then ScalarOk s
             else ScalarPanic panic_enum_conversion
         | NONE => ScalarInvalid)
    | (UserValueT _, _) => ScalarOk s
    | (BoolT, BoolValue _) => ScalarOk s
    | (FunctionT _ _ _ _, InternalFunctionValue _) => ScalarOk s
    | _ => ScalarInvalid
End

Definition eval_conversion_def:
  eval_conversion env src dst s =
    if core_convertible env src dst ∧ scalar_has_type env src s
    then convert_scalar env dst s
    else ScalarInvalid
End

(* Canonicality: a ScalarOk result has the signature's result type, and a
 * conversion's result has the target type. This is the "values carry no dirty
 * bits" invariant the evaluator's typing argument needs from this layer; no
 * valid_type_shape hypothesis is needed because wrapping lands in range at
 * every width.
 *)

Theorem arithmetic_result_in_range:
  arithmetic_result mode signed n i = ScalarOk v ⇒
  ∃j. v = IntegerValue j ∧ integer_in_range signed n j
Proof
  rw[arithmetic_result_def, integer_result_def, AllCaseEqs()] >>
  simp[wrap_integer_in_range]
QED

Theorem integer_result_in_range:
  integer_result signed n i = ScalarOk v ⇒
  ∃j. v = IntegerValue j ∧ integer_in_range signed n j
Proof
  rw[integer_result_def] >> simp[wrap_integer_in_range]
QED

Theorem shift_left_in_range:
  integer_in_range signed n (shift_left signed n x y)
Proof
  rw[shift_left_def, wrap_integer_in_range] >> rw[integer_in_range_def]
QED

Theorem integer_bitwise_in_range:
  integer_in_range signed n (integer_bitwise op signed n x y)
Proof
  rw[integer_bitwise_def, wrap_integer_in_range]
QED

Theorem eval_integer_operation_in_range:
  eval_integer_operation mode signed n op args = ScalarOk v ⇒
  ∃j. v = IntegerValue j ∧ integer_in_range signed n j
Proof
  rw[eval_integer_operation_def, AllCaseEqs()] >>
  gvs[integer_exponent_def, AllCaseEqs()] >>
  metis_tac[arithmetic_result_in_range, integer_result_in_range,
            shift_left_in_range, integer_bitwise_in_range]
QED

Theorem eval_integer_operation_not_comparison:
  eval_integer_operation mode signed n op args = ScalarOk v ⇒
  op ≠ EqualOp ∧ op ≠ LessThanOp ∧ op ≠ BoolNotOp
Proof
  rw[eval_integer_operation_def, AllCaseEqs()]
QED

Theorem bytes_bitwise_length:
  ∀op a b. LENGTH (bytes_bitwise op a b) = MIN (LENGTH a) (LENGTH b)
Proof
  ho_match_mp_tac bytes_bitwise_ind >> rw[bytes_bitwise_def, MIN_DEF]
QED

Theorem bytes_not_length:
  ∀a. LENGTH (bytes_not a) = LENGTH a
Proof
  Induct >> rw[bytes_not_def]
QED

Theorem num_to_bytes_length:
  LENGTH (num_to_bytes n v) = n
Proof
  rw[num_to_bytes_def]
QED

Theorem num_of_be_bytes_bound:
  num_of_be_bytes bs < 256 ** LENGTH bs
Proof
  rw[vfmTypesTheory.num_of_be_bytes_def] >>
  qspecl_then [‘MAP w2n (REVERSE bs)’, ‘256’] mp_tac
    numposrepTheory.l2n_lt >>
  simp[]
QED

Theorem eval_bytes_operation_canonical:
  scalars_have_types env tys args ∧
  scalar_operator_signature op (FixedBytesT n) = SOME (tys, result) ∧
  eval_bytes_operation n op args = ScalarOk v ⇒
  ∃bs. v = BytesValue bs ∧ LENGTH bs = n ∧ result = FixedBytesT n
Proof
  rw[eval_bytes_operation_def, AllCaseEqs()] >>
  gvs[scalar_operator_signature_def, scalars_have_types_def,
      scalar_has_type_def, elementary_scalar_has_type_def,
      bytes_bitwise_length, bytes_not_length, num_to_bytes_length]
QED

Theorem scalar_operator_signature_result:
  scalar_operator_signature op ty = SOME (tys, result) ⇒
  result = ty ∨ (result = BoolT ∧ (op = EqualOp ∨ op = LessThanOp))
Proof
  Cases_on ‘op’ >> rw[scalar_operator_signature_def, AllCaseEqs()]
QED

(* The branches of eval_scalar_operation that can succeed. *)
Theorem eval_scalar_operation_cases:
  eval_scalar_operation env ty mode op args = ScalarOk v ⇒
  ∃tys result.
    scalar_operator_signature op ty = SOME (tys, result) ∧
    scalars_have_types env tys args ∧
    ((∃b. v = BoolValue b ∧
          (op = EqualOp ∨ op = LessThanOp ∨ op = BoolNotOp)) ∨
     (∃n. ty = UintT n ∧ eval_integer_operation mode F n op args = ScalarOk v) ∨
     (∃n. ty = IntT n ∧ eval_integer_operation mode T n op args = ScalarOk v) ∨
     (∃n. ty = FixedBytesT n ∧ eval_bytes_operation n op args = ScalarOk v))
Proof
  rw[eval_scalar_operation_def, AllCaseEqs()] >> gvs[]
QED

Theorem eval_scalar_operation_canonical:
  scalar_operator_signature op ty = SOME (tys, result) ∧
  eval_scalar_operation env ty mode op args = ScalarOk v ⇒
  scalar_has_type env result v
Proof
  strip_tac >> drule eval_scalar_operation_cases >> strip_tac >> gvs[] >>
  TRY (gvs[scalar_operator_signature_def, scalar_has_type_def,
           elementary_scalar_has_type_def] >> NO_TAC)
  >- (drule eval_integer_operation_in_range >>
      drule eval_integer_operation_not_comparison >>
      drule scalar_operator_signature_result >>
      rw[] >> gvs[scalar_has_type_def, elementary_scalar_has_type_def])
  >- (drule eval_integer_operation_in_range >>
      drule eval_integer_operation_not_comparison >>
      drule scalar_operator_signature_result >>
      rw[] >> gvs[scalar_has_type_def, elementary_scalar_has_type_def])
  >- (drule_all eval_bytes_operation_canonical >>
      rw[] >> gvs[scalar_has_type_def, elementary_scalar_has_type_def])
QED

Theorem eval_conversion_canonical:
  wf_core_environment env ∧ eval_conversion env src dst s = ScalarOk v ⇒
  scalar_has_type env dst v
Proof
  rw[eval_conversion_def] >>
  gvs[convert_scalar_def, AllCaseEqs()] >>
  simp[scalar_has_type_def, elementary_scalar_has_type_def,
       wrap_integer_in_range, num_to_bytes_length] >>
  Cases_on ‘src’ >>
  gvs[core_convertible_def, AllCaseEqs()] >>
  gvs[elementary_convertible_def, AllCaseEqs()] >>
  gvs[scalar_has_type_def, elementary_scalar_has_type_def, AllCaseEqs()]
  >- (gvs[integer_in_range_def, AllCasePreds()] >>
      irule LESS_LESS_EQ_TRANS >> irule_at Any w2n_lt >> simp[])
  >- simp[integer_in_range_def, EXP_EXP_MULT, num_of_be_bytes_bound] >>
  TRY (drule_all wf_core_environment_user_value >> simp[] >> NO_TAC) >>
  BasicProvers.EVERY_CASE_TAC >> gvs[]
QED

(* Progress: operations the checker admits never return ScalarInvalid on
 * well-typed operands, and admitted conversions never do on a well-typed
 * source value. Together with canonicality this is what the evaluator's
 * progress argument needs from this layer.
 *)

Theorem scalars_have_types_LIST_REL:
  ∀tys args.
    scalars_have_types env tys args ⇔ LIST_REL (scalar_has_type env) tys args
Proof
  Induct >> Cases_on ‘args’ >> rw[scalars_have_types_def]
QED

Theorem scalar_has_type_cases:
  (scalar_has_type env (UintT n) v ⇔
     ∃i. v = IntegerValue i ∧ integer_in_range F n i) ∧
  (scalar_has_type env (IntT n) v ⇔
     ∃i. v = IntegerValue i ∧ integer_in_range T n i) ∧
  (scalar_has_type env BoolT v ⇔ ∃b. v = BoolValue b) ∧
  (scalar_has_type env (AddressT p) v ⇔ ∃a. v = AddressValue a) ∧
  (scalar_has_type env (FixedBytesT n) v ⇔
     ∃bs. v = BytesValue bs ∧ LENGTH bs = n) ∧
  (scalar_has_type env (EnumT id) v ⇔
     ∃i k. v = IntegerValue i ∧ lookup_enum env id = SOME k ∧
           0 ≤ i ∧ i < &k) ∧
  (scalar_has_type env (UserValueT id) v ⇔
     ∃u. lookup_user_value env id = SOME u ∧ elementary_scalar_has_type u v)
Proof
  Cases_on ‘v’ >> Cases_on ‘lookup_enum env id’ >>
  Cases_on ‘lookup_user_value env id’ >>
  rw[scalar_has_type_def, elementary_scalar_has_type_def]
QED

Theorem arithmetic_result_not_invalid:
  arithmetic_result mode signed n i ≠ ScalarInvalid
Proof
  Cases_on ‘mode’ >> rw[arithmetic_result_def, integer_result_def]
QED

Theorem integer_exponent_not_invalid:
  integer_exponent mode signed n x e ≠ ScalarInvalid
Proof
  Cases_on ‘mode’ >>
  rw[integer_exponent_def, arithmetic_result_not_invalid, integer_result_def]
QED

Theorem eval_scalar_operation_progress:
  core_scalar_type env ty ∧
  scalar_operator_signature op ty = SOME (tys, result) ∧
  scalars_have_types env tys args ⇒
  eval_scalar_operation env ty mode op args ≠ ScalarInvalid
Proof
  rw[scalars_have_types_LIST_REL] >>
  Cases_on ‘ty’ >> Cases_on ‘op’ >>
  gvs[scalar_operator_signature_def] >>
  gvs[listTheory.LIST_REL_CONS1, core_scalar_type_def,
      solidityASTTheory.valid_type_shape_def, scalar_has_type_cases] >>
  rw[eval_scalar_operation_def, scalar_operator_signature_def,
     scalars_have_types_def, scalar_has_type_cases, scalar_order_key_def,
     eval_integer_operation_def, eval_bytes_operation_def,
     arithmetic_result_not_invalid, integer_exponent_not_invalid,
     integer_result_def]
QED

Theorem eval_conversion_progress:
  core_scalar_type env dst ∧ core_convertible env src dst ∧
  scalar_has_type env src v ⇒
  eval_conversion env src dst v ≠ ScalarInvalid
Proof
  rw[eval_conversion_def, core_scalar_type_def] >>
  Cases_on ‘dst’ >>
  gvs[solidityASTTheory.is_value_type_def, declared_type_ok_def,
      optionTheory.IS_SOME_EXISTS] >>
  TRY (Cases_on ‘src’) >>
  gvs[core_convertible_def, elementary_convertible_def, AllCaseEqs()] >>
  TRY (Cases_on ‘v’) >>
  gvs[scalar_has_type_cases, convert_scalar_def, scalar_has_type_def,
      elementary_scalar_has_type_def, AllCaseEqs()] >>
  gvs[AllCasePreds()]
QED

(* The fast paths agree with the plain definitions: integer_exponent with
 * arithmetic on x ** e, and the capped shifts with x * 2 ** y truncated and
 * x / 2 ** y.
 *)

Theorem power_congruence[local]:
  ∀e. ∃q. (k * &M + &u) ** e = q * &M + &(u ** e) : int
Proof
  Induct >- (qexists_tac ‘0’ >> simp[int_exp]) >>
  pop_assum strip_assume_tac >>
  qexists_tac ‘k * q * &M + k * &(u ** e) + &u * q’ >>
  ONCE_REWRITE_TAC [int_exp, EXP] >>
  qpat_x_assum ‘_ = _’ (fn th => ONCE_REWRITE_TAC [th]) >>
  ONCE_REWRITE_TAC [GSYM INT_MUL] >>
  intLib.INT_RING_TAC
QED

Theorem wrap_integer_mod_cong:
  i % &(2 ** n) = j % &(2 ** n) ⇒
  wrap_integer signed n i = wrap_integer signed n j
Proof
  rw[wrap_integer_def]
QED

Theorem wrap_integer_modexp:
  wrap_integer signed n (&modexp (Num (x % &(2 ** n))) e (2 ** n) 1) =
  wrap_integer signed n (x ** e)
Proof
  irule wrap_integer_mod_cong >>
  qabbrev_tac ‘M = (2 : num) ** n’ >>
  ‘0 < M’ by simp[Abbr ‘M’] >>
  ‘(&M : int) ≠ 0’ by simp[] >>
  ‘0 ≤ x % &M’
    by (mp_tac (Q.SPECL [‘x’, ‘&M’] INT_MOD_BOUNDS) >> simp[]) >>
  qabbrev_tac ‘u = Num (x % &M)’ >>
  ‘x % &M = &u’ by simp[Abbr ‘u’, INT_OF_NUM] >>
  ‘x ** e = (x / &M * &M + &u) ** e’ by metis_tac[INT_DIVISION] >>
  qspec_then ‘e’ strip_assume_tac
    (Q.INST [‘k’ |-> ‘x / &M’] power_congruence) >>
  simp[modexp_exp, INT_MOD_ADD_MULTIPLES, INT_MOD]
QED

Theorem large_power_out_of_range:
  0 < n ∧ n ≤ e ∧ x ≠ 0 ∧ x ≠ 1 ∧ x ≠ -1 ⇒
  ¬integer_in_range signed n (x ** e)
Proof
  strip_tac >>
  ‘∃k. 2 ≤ k ∧ (x = &k ∨ x = -&k)’
    by (strip_assume_tac (Q.SPEC ‘x’ INT_NUM_CASES) >> gvs[] >>
        qexists_tac ‘n'’ >> simp[] >> CCONTR_TAC >> gvs[] >>
        ‘n' = 1’ by decide_tac >> gvs[]) >>
  ‘2 ** n ≤ k ** e’
    by (irule LESS_EQ_TRANS >> qexists_tac ‘2 ** e’ >>
        simp[EXP_BASE_LE_MONO, EXP_EXP_LE_MONO]) >>
  ‘x ** e = &(k ** e) ∨ x ** e = -&(k ** e)’
    by (gvs[INT_EXP] >> Cases_on ‘EVEN e’ >>
        gvs[INT_EXP_NEG, GSYM ODD_EVEN]) >>
  ‘(2 : num) ** n = 2 * 2 ** (n - 1)’ by (Cases_on ‘n’ >> gvs[EXP]) >>
  qabbrev_tac ‘H = (2 : num) ** (n - 1)’ >>
  qabbrev_tac ‘P = k ** e’ >>
  gvs[integer_in_range_def] >> rw[] >> intLib.ARITH_TAC
QED

Theorem integer_exponent_spec:
  0 < n ⇒
  integer_exponent mode signed n x e = arithmetic_result mode signed n (x ** e)
Proof
  strip_tac >> Cases_on ‘mode’ >> rw[integer_exponent_def]
  >- (Cases_on ‘e’ >> gvs[EXP])
  >- gvs[INT_EXP_NEG]
  >- gvs[INT_EXP_NEG, GSYM ODD_EVEN]
  >- (‘¬integer_in_range signed n (x ** e)’
        by (irule large_power_out_of_range >> simp[]) >>
      simp[arithmetic_result_def]) >>
  simp[arithmetic_result_def, integer_result_def, wrap_integer_modexp] >>
  rw[wrap_integer_id]
QED

Theorem shift_left_spec:
  shift_left signed n x y = wrap_integer signed n (x * &(2 ** y))
Proof
  rw[shift_left_def] >>
  ‘&(2 ** y) = &(2 ** (y - n)) * &(2 ** n) : int’
    by simp[INT_MUL, GSYM EXP_ADD] >>
  ‘(x * &(2 ** y)) % &(2 ** n) = 0’
    by (pop_assum SUBST1_TAC >> REWRITE_TAC [INT_MUL_ASSOC] >>
        irule INT_MOD_COMMON_FACTOR >> simp[]) >>
  rw[wrap_integer_def]
QED

Theorem shift_right_spec:
  0 < n ∧ integer_in_range signed n x ⇒ shift_right n x y = x / &(2 ** y)
Proof
  rw[shift_right_def] >>
  ‘(2 : num) ** n ≤ 2 ** y’ by simp[EXP_BASE_LE_MONO] >>
  ‘(2 : num) ** n = 2 * 2 ** (n - 1)’ by (Cases_on ‘n’ >> gvs[EXP]) >>
  qabbrev_tac ‘H = (2 : num) ** (n - 1)’ >>
  qabbrev_tac ‘Y = (2 : num) ** y’ >>
  ‘0 < Y’ by simp[Abbr ‘Y’] >>
  gvs[integer_in_range_def] >>
  irule INT_DIV_UNIQUE >> Cases_on ‘signed’ >> gvs[] >>
  TRY (qexists_tac ‘x + &Y’ >> intLib.ARITH_TAC >> NO_TAC) >>
  intLib.ARITH_TAC
QED

(* Implicit conversions never panic: integers keep their value and fixed
 * bytes are padded with zeros on the right.
 *)

Theorem integer_in_range_mono:
  0 < m ∧ m ≤ n ∧ integer_in_range signed m i ⇒ integer_in_range signed n i
Proof
  strip_tac >>
  ‘(2 : num) ** m ≤ 2 ** n ∧ 2 ** (m - 1) ≤ 2 ** (n - 1)’
    by simp[EXP_BASE_LE_MONO] >>
  qabbrev_tac ‘A = (2 : num) ** m’ >> qabbrev_tac ‘B = (2 : num) ** n’ >>
  qabbrev_tac ‘C = (2 : num) ** (m - 1)’ >>
  qabbrev_tac ‘D = (2 : num) ** (n - 1)’ >>
  gvs[integer_in_range_def] >> rw[] >> gvs[] >> intLib.ARITH_TAC
QED

Theorem implicit_integer_conversion_id:
  implicitly_convertible src dst ∧ is_integer_type src ∧
  valid_type_shape src ∧ scalar_has_type env src v ⇒
  eval_conversion env src dst v = ScalarOk v
Proof
  strip_tac >>
  ‘core_convertible env src dst’
    by metis_tac[implicitly_convertible_explicit] >>
  Cases_on ‘src’ >> Cases_on ‘dst’ >>
  gvs[implicitly_convertible_def, solidityASTTheory.valid_type_shape_def,
      solidityASTTheory.valid_int_width_def, scalar_has_type_cases] >>
  rw[eval_conversion_def, scalar_has_type_cases, convert_scalar_def] >>
  irule wrap_integer_id >> simp[] >>
  irule integer_in_range_mono >> first_assum (irule_at Any) >> simp[]
QED

Theorem implicit_bytes_conversion_pads:
  m ≤ n ∧ LENGTH bs = m ⇒
  eval_conversion env (FixedBytesT m) (FixedBytesT n) (BytesValue bs) =
  ScalarOk (BytesValue (bs ++ REPLICATE (n - m) 0w))
Proof
  rw[eval_conversion_def, core_convertible_def, elementary_convertible_def,
     scalar_has_type_cases, convert_scalar_def, vfmTypesTheory.take_pad_0_def,
     listTheory.TAKE_LENGTH_TOO_LONG, listTheory.PAD_RIGHT,
     rich_listTheory.REPLICATE_GENLIST]
QED

Theorem implicit_conversion_succeeds:
  implicitly_convertible src dst ∧ scalar_has_type env src v ⇒
  ∃w. eval_conversion env src dst v = ScalarOk w
Proof
  strip_tac >>
  ‘core_convertible env src dst’
    by metis_tac[implicitly_convertible_explicit] >>
  simp[eval_conversion_def] >>
  qpat_x_assum ‘implicitly_convertible _ _’ mp_tac >>
  rw[implicitly_convertible_def]
  >- (Cases_on ‘dst’ >>
      gvs[scalar_has_type_cases, scalar_has_type_def,
          elementary_scalar_has_type_def, convert_scalar_def] >>
      gvs[AllCasePreds()] >> BasicProvers.EVERY_CASE_TAC >> gvs[]) >>
  Cases_on ‘src’ >> Cases_on ‘dst’ >>
  gvs[AllCaseEqs(), scalar_has_type_cases, convert_scalar_def] >>
  gvs[scalar_has_type_def, AllCasePreds()] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[]
QED

(* cv translation, so the evaluator can run scalar steps under cv_compute. *)

val wrap_integer_pre_def = cv_auto_trans_pre "wrap_integer_pre" wrap_integer_def;

Theorem wrap_integer_pre[cv_pre]:
  ∀signed n i. wrap_integer_pre signed n i
Proof
  rw[wrap_integer_pre_def]
QED

val integer_exponent_pre_def =
  cv_auto_trans_pre "integer_exponent_pre" integer_exponent_def;

Theorem integer_exponent_pre[cv_pre]:
  ∀mode signed n x e. integer_exponent_pre mode signed n x e
Proof
  rw[integer_exponent_pre_def]
QED

val shift_right_pre_def = cv_auto_trans_pre "shift_right_pre" shift_right_def;

Theorem shift_right_pre[cv_pre]:
  ∀n x y. shift_right_pre n x y
Proof
  rw[shift_right_pre_def]
QED

val integer_bitwise_pre_def =
  cv_auto_trans_pre "integer_bitwise_pre" integer_bitwise_def;

Theorem integer_bitwise_pre[cv_pre]:
  ∀op signed n x y. integer_bitwise_pre op signed n x y
Proof
  rw[integer_bitwise_pre_def]
QED

val () = cv_auto_trans eval_scalar_operation_def;
val () = cv_auto_trans eval_conversion_def;
