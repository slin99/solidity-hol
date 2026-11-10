(* Concrete scalar cases, checked against the documented behaviour at the
 * pinned Solidity revision (value-types.rst, conversion.rst and the panic
 * codes in control-structures.rst).
 *)
Theory solidityScalarTest
Ancestors
  solidityScalar
Libs
  intLib wordsLib cv_transLib

Overload u8 = “UintT 8”
Overload u16 = “UintT 16”
Overload u256 = “UintT 256”
Overload i8 = “IntT 8”
Overload i256 = “IntT 256”
Overload checked = “CheckedArithmetic”
Overload unchecked = “UncheckedArithmetic”

Definition scalar_env_def:
  scalar_env = <|
    procedures := [];
    state_variables := []; immutables := [];
    struct_layouts := [];
    type_declarations := [(AstId 900, EnumDeclaration 3);
                          (AstId 901, UserValueDeclaration (UintT 64))]
  |>
End

Definition binop_def:
  binop ty mode op x y =
    eval_scalar_operation scalar_env ty mode op [IntegerValue x; IntegerValue y]
End

Definition unop_def:
  unop ty mode op x =
    eval_scalar_operation scalar_env ty mode op [IntegerValue x]
End

Definition convert_def:
  convert src dst s = eval_conversion scalar_env src dst s
End

(* Addition, subtraction, multiplication *)

Theorem uint8_add_overflow_checked:
  binop u8 checked AddOp 255 1 = ScalarPanic 0x11
Proof
  EVAL_TAC
QED

Theorem uint8_add_overflow_unchecked:
  binop u8 unchecked AddOp 255 1 = ScalarOk (IntegerValue 0)
Proof
  EVAL_TAC
QED

Theorem uint8_sub_underflow_checked:
  binop u8 checked SubtractOp 0 1 = ScalarPanic 0x11
Proof
  EVAL_TAC
QED

Theorem uint8_sub_underflow_unchecked:
  binop u8 unchecked SubtractOp 0 1 = ScalarOk (IntegerValue 255)
Proof
  EVAL_TAC
QED

Theorem int8_add_sub_overflow_checked:
  binop i8 checked AddOp 127 1 = ScalarPanic 0x11 ∧
  binop i8 checked SubtractOp (-128) 1 = ScalarPanic 0x11
Proof
  EVAL_TAC
QED

Theorem int8_sub_unchecked_wraps_across_sign:
  binop i8 unchecked SubtractOp (-128) 1 = ScalarOk (IntegerValue 127)
Proof
  EVAL_TAC
QED

Theorem int256_mul_overflow_checked:
  binop i256 checked MultiplyOp (&(2 ** 255) - 1) 2 = ScalarPanic 0x11
Proof
  EVAL_TAC
QED

Theorem int8_mul_unchecked_wraps_negative:
  binop i8 unchecked MultiplyOp 64 2 = ScalarOk (IntegerValue (-128))
Proof
  EVAL_TAC
QED

(* Division and remainder *)

Theorem int8_min_div_minus_one_checked:
  binop i8 checked DivideOp (-128) (-1) = ScalarPanic 0x11
Proof
  EVAL_TAC
QED

Theorem int8_min_div_minus_one_unchecked:
  binop i8 unchecked DivideOp (-128) (-1) = ScalarOk (IntegerValue (-128))
Proof
  EVAL_TAC
QED

Theorem division_rounds_towards_zero:
  binop i256 checked DivideOp (-5) 2 = ScalarOk (IntegerValue (-2))
Proof
  EVAL_TAC
QED

Theorem remainder_takes_dividend_sign:
  binop i256 checked RemainderOp 5 2 = ScalarOk (IntegerValue 1) ∧
  binop i256 checked RemainderOp 5 (-2) = ScalarOk (IntegerValue 1) ∧
  binop i256 checked RemainderOp (-5) 2 = ScalarOk (IntegerValue (-1)) ∧
  binop i256 checked RemainderOp (-5) (-2) = ScalarOk (IntegerValue (-1))
Proof
  EVAL_TAC
QED

Theorem int8_min_rem_minus_one:
  binop i8 checked RemainderOp (-128) (-1) = ScalarOk (IntegerValue 0)
Proof
  EVAL_TAC
QED

Theorem division_by_zero_panics_unchecked:
  binop u8 unchecked DivideOp 7 0 = ScalarPanic 0x12 ∧
  binop u8 unchecked RemainderOp 23 0 = ScalarPanic 0x12
Proof
  EVAL_TAC
QED

(* Unary minus: only signed, and -x at the minimum overflows. *)

Theorem negate_min_checked:
  unop i8 checked NegateOp (-128) = ScalarPanic 0x11
Proof
  EVAL_TAC
QED

Theorem negate_min_unchecked:
  unop i8 unchecked NegateOp (-128) = ScalarOk (IntegerValue (-128))
Proof
  EVAL_TAC
QED

Theorem negate_ordinary:
  unop i8 checked NegateOp 5 = ScalarOk (IntegerValue (-5))
Proof
  EVAL_TAC
QED

Theorem negate_unsigned_invalid:
  unop u8 checked NegateOp 5 = ScalarInvalid
Proof
  EVAL_TAC
QED

(* Exponentiation *)

Theorem zero_pow_zero:
  binop u8 checked ExponentOp 0 0 = ScalarOk (IntegerValue 1)
Proof
  EVAL_TAC
QED

Theorem int8_signed_base_fits:
  binop i8 checked ExponentOp (-2) 7 = ScalarOk (IntegerValue (-128))
Proof
  EVAL_TAC
QED

Theorem int8_signed_base_overflows:
  binop i8 checked ExponentOp (-2) 8 = ScalarPanic 0x11 ∧
  binop i8 unchecked ExponentOp (-2) 8 = ScalarOk (IntegerValue 0)
Proof
  EVAL_TAC
QED

Theorem int8_positive_base_boundary:
  binop i8 checked ExponentOp 2 6 = ScalarOk (IntegerValue 64) ∧
  binop i8 checked ExponentOp 2 7 = ScalarPanic 0x11
Proof
  EVAL_TAC
QED

(* (-3) ** 5 = -243 ≡ 13 (mod 256) *)
Theorem int8_signed_base_unchecked_wraps_nonzero:
  binop i8 unchecked ExponentOp (-3) 5 = ScalarOk (IntegerValue 13)
Proof
  EVAL_TAC
QED

Theorem uint8_pow_boundary:
  binop u8 checked ExponentOp 3 5 = ScalarOk (IntegerValue 243) ∧
  binop u8 checked ExponentOp 3 6 = ScalarPanic 0x11 ∧
  binop u8 unchecked ExponentOp 3 6 = ScalarOk (IntegerValue 217)
Proof
  EVAL_TAC
QED

Theorem uint256_two_pow_256:
  binop u256 checked ExponentOp 2 256 = ScalarPanic 0x11 ∧
  binop u256 unchecked ExponentOp 2 256 = ScalarOk (IntegerValue 0)
Proof
  EVAL_TAC
QED

Theorem huge_exponent_small_bases:
  binop u256 checked ExponentOp 1 (&(2 ** 256) - 1) = ScalarOk (IntegerValue 1) ∧
  binop i8 checked ExponentOp (-1) (&(2 ** 256) - 1) =
    ScalarOk (IntegerValue (-1)) ∧
  binop u256 checked ExponentOp 0 (&(2 ** 256) - 1) = ScalarOk (IntegerValue 0)
Proof
  EVAL_TAC
QED

(* Square-and-multiply over a 2 ** 255 exponent is too slow for EVAL's
 * numerals; cv_eval runs the translated definitions.
 *)
val () = cv_auto_trans binop_def;

Theorem huge_exponent_unchecked:
  binop u256 unchecked ExponentOp 3 (&(2 ** 255) + 1) = ScalarOk (IntegerValue 3)
Proof
  CONV_TAC cv_eval
QED

(* Shifts: truncated, never checked; >> rounds towards negative infinity. *)

Theorem int8_shift_left_into_sign_bit:
  binop i8 checked ShiftLeftOp 1 7 = ScalarOk (IntegerValue (-128))
Proof
  EVAL_TAC
QED

Theorem uint8_shift_left_truncates:
  binop u8 checked ShiftLeftOp 255 1 = ScalarOk (IntegerValue 254)
Proof
  EVAL_TAC
QED

Theorem shift_by_width_or_more:
  binop u256 checked ShiftLeftOp 1 256 = ScalarOk (IntegerValue 0) ∧
  binop u256 checked ShiftLeftOp 1 255 = ScalarOk (IntegerValue (&(2 ** 255))) ∧
  binop i8 checked ShiftRightOp (-1) 300 = ScalarOk (IntegerValue (-1)) ∧
  binop i8 checked ShiftRightOp 100 300 = ScalarOk (IntegerValue 0)
Proof
  EVAL_TAC
QED

Theorem signed_shift_right_floors:
  binop i8 checked ShiftRightOp (-5) 1 = ScalarOk (IntegerValue (-3))
Proof
  EVAL_TAC
QED

Theorem unsigned_shift_right_is_logical:
  binop u8 checked ShiftRightOp 255 1 = ScalarOk (IntegerValue 127)
Proof
  EVAL_TAC
QED

Theorem negative_shift_amount_invalid:
  binop u8 checked ShiftLeftOp 1 (-1) = ScalarInvalid
Proof
  EVAL_TAC
QED

Theorem bytes_shifts:
  eval_scalar_operation scalar_env (FixedBytesT 2) checked ShiftLeftOp
    [BytesValue [0x12w; 0x34w]; IntegerValue 8] =
    ScalarOk (BytesValue [0x34w; 0w]) ∧
  eval_scalar_operation scalar_env (FixedBytesT 2) checked ShiftRightOp
    [BytesValue [0x12w; 0x34w]; IntegerValue 4] =
    ScalarOk (BytesValue [0x01w; 0x23w])
Proof
  EVAL_TAC
QED

Theorem bytes_shift_by_width_clears:
  eval_scalar_operation scalar_env (FixedBytesT 2) checked ShiftLeftOp
    [BytesValue [1w; 2w]; IntegerValue 16] = ScalarOk (BytesValue [0w; 0w])
Proof
  EVAL_TAC
QED

(* Bitwise operators on two's complement and on bytes *)

Theorem bit_not_integers:
  unop i256 checked BitNotOp 0 = ScalarOk (IntegerValue (-1)) ∧
  unop u8 checked BitNotOp 0 = ScalarOk (IntegerValue 255)
Proof
  EVAL_TAC
QED

Theorem signed_bitwise:
  binop i8 checked BitAndOp (-1) 15 = ScalarOk (IntegerValue 15) ∧
  binop i8 checked BitOrOp (-16) 1 = ScalarOk (IntegerValue (-15)) ∧
  binop i8 checked BitXorOp (-1) 1 = ScalarOk (IntegerValue (-2))
Proof
  EVAL_TAC
QED

Theorem bytes_bitwise:
  eval_scalar_operation scalar_env (FixedBytesT 2) checked BitAndOp
    [BytesValue [0x12w; 0x34w]; BytesValue [0xFFw; 0w]] =
    ScalarOk (BytesValue [0x12w; 0w]) ∧
  eval_scalar_operation scalar_env (FixedBytesT 2) checked BitNotOp
    [BytesValue [0x12w; 0x34w]] = ScalarOk (BytesValue [0xEDw; 0xCBw])
Proof
  EVAL_TAC
QED

(* Comparisons *)

Theorem comparisons:
  binop i8 checked LessThanOp (-1) 1 = ScalarOk (BoolValue T) ∧
  binop u8 checked EqualOp 3 3 = ScalarOk (BoolValue T) ∧
  eval_scalar_operation scalar_env (AddressT NonpayableAddress) checked
    LessThanOp [AddressValue 1w; AddressValue 2w] = ScalarOk (BoolValue T) ∧
  eval_scalar_operation scalar_env (FixedBytesT 2) checked LessThanOp
    [BytesValue [0x12w; 0xFFw]; BytesValue [0x13w; 0w]] =
    ScalarOk (BoolValue T) ∧
  eval_scalar_operation scalar_env (EnumT (AstId 900)) checked LessThanOp
    [IntegerValue 2; IntegerValue 1] = ScalarOk (BoolValue F) ∧
  eval_scalar_operation scalar_env BoolT checked EqualOp
    [BoolValue T; BoolValue F] = ScalarOk (BoolValue F) ∧
  eval_scalar_operation scalar_env BoolT checked BoolNotOp [BoolValue F] =
    ScalarOk (BoolValue T)
Proof
  EVAL_TAC
QED

(* Ill-typed input is invalid, never a panic. *)

Theorem ill_typed_operations_invalid:
  binop u8 checked AddOp 300 1 = ScalarInvalid ∧
  eval_scalar_operation scalar_env BoolT checked AddOp
    [BoolValue T; BoolValue T] = ScalarInvalid ∧
  binop u8 checked AddOp 1 2 = ScalarOk (IntegerValue 3) ∧
  eval_scalar_operation scalar_env u8 checked AddOp [IntegerValue 1] =
    ScalarInvalid
Proof
  EVAL_TAC
QED

(* A width the type system never admits is invalid rather than computed at a
 * width the bitwise helpers do not support.
 *)
Theorem invalid_width_invalid:
  eval_scalar_operation scalar_env (UintT 512) unchecked BitAndOp
    [IntegerValue (2 ** 300); IntegerValue (2 ** 300)] = ScalarInvalid
Proof
  CONV_TAC cv_eval
QED

(* Conversions *)

Theorem integer_truncation_and_extension:
  convert (UintT 32) u16 (IntegerValue 0x12345678) =
    ScalarOk (IntegerValue 0x5678) ∧
  convert u16 (UintT 32) (IntegerValue 0x1234) = ScalarOk (IntegerValue 0x1234) ∧
  convert i256 u256 (IntegerValue (-3)) =
    ScalarOk (IntegerValue (&(2 ** 256) - 3)) ∧
  convert u8 i8 (IntegerValue 255) = ScalarOk (IntegerValue (-1)) ∧
  convert i8 i256 (IntegerValue (-1)) = ScalarOk (IntegerValue (-1))
Proof
  EVAL_TAC
QED

Theorem signed_narrowing_wraps:
  convert (IntT 16) i8 (IntegerValue 384) = ScalarOk (IntegerValue (-128)) ∧
  convert (IntT 16) i8 (IntegerValue (-129)) = ScalarOk (IntegerValue 127)
Proof
  EVAL_TAC
QED

(* The translated eval_conversion; convert itself is not translated. *)
Theorem signed_to_unsigned_translated:
  eval_conversion scalar_env i8 u8 (IntegerValue (-1)) =
    ScalarOk (IntegerValue 255)
Proof
  CONV_TAC cv_eval
QED

Theorem fixed_bytes_resize:
  convert (FixedBytesT 2) (FixedBytesT 1) (BytesValue [0x12w; 0x34w]) =
    ScalarOk (BytesValue [0x12w]) ∧
  convert (FixedBytesT 2) (FixedBytesT 4) (BytesValue [0x12w; 0x34w]) =
    ScalarOk (BytesValue [0x12w; 0x34w; 0w; 0w])
Proof
  EVAL_TAC
QED

Theorem integer_bytes_reencoding:
  convert (FixedBytesT 2) u16 (BytesValue [0x12w; 0x34w]) =
    ScalarOk (IntegerValue 0x1234) ∧
  convert u16 (FixedBytesT 2) (IntegerValue 0x1234) =
    ScalarOk (BytesValue [0x12w; 0x34w])
Proof
  EVAL_TAC
QED

Theorem address_conversions:
  convert (AddressT NonpayableAddress) (UintT 160) (AddressValue 0xABw) =
    ScalarOk (IntegerValue 0xAB) ∧
  convert (UintT 160) (AddressT NonpayableAddress) (IntegerValue 0xAB) =
    ScalarOk (AddressValue 0xABw) ∧
  convert (AddressT NonpayableAddress) (FixedBytesT 20) (AddressValue 0xABw) =
    ScalarOk (BytesValue (REPLICATE 19 0w ++ [0xABw])) ∧
  convert (FixedBytesT 20) (AddressT NonpayableAddress)
    (BytesValue (REPLICATE 19 0w ++ [0xABw])) = ScalarOk (AddressValue 0xABw) ∧
  convert (AddressT PayableAddress) (AddressT NonpayableAddress)
    (AddressValue 0xABw) = ScalarOk (AddressValue 0xABw)
Proof
  EVAL_TAC
QED

Theorem enum_conversions:
  convert u8 (EnumT (AstId 900)) (IntegerValue 2) = ScalarOk (IntegerValue 2) ∧
  convert u8 (EnumT (AstId 900)) (IntegerValue 3) = ScalarPanic 0x21 ∧
  convert i8 (EnumT (AstId 900)) (IntegerValue (-1)) = ScalarPanic 0x21 ∧
  convert (EnumT (AstId 900)) u8 (IntegerValue 2) = ScalarOk (IntegerValue 2)
Proof
  EVAL_TAC
QED

Theorem user_value_wrap_unwrap:
  convert (UintT 64) (UserValueT (AstId 901)) (IntegerValue 5) =
    ScalarOk (IntegerValue 5) ∧
  convert (UserValueT (AstId 901)) (UintT 64) (IntegerValue 5) =
    ScalarOk (IntegerValue 5)
Proof
  EVAL_TAC
QED

Theorem unsupported_conversions_invalid:
  convert BoolT u8 (BoolValue T) = ScalarInvalid ∧
  convert (IntT 16) u8 (IntegerValue 1) = ScalarInvalid ∧
  convert u8 (FixedBytesT 2) (IntegerValue 1) = ScalarInvalid ∧
  convert u8 u16 (IntegerValue 256) = ScalarInvalid
Proof
  EVAL_TAC
QED

(* Implicit conversions (Types.cpp isImplicitlyConvertibleTo at the pin) *)

Theorem implicit_conversions_admitted:
  implicitly_convertible u8 u16 ∧
  implicitly_convertible i8 i256 ∧
  implicitly_convertible (FixedBytesT 1) (FixedBytesT 2) ∧
  implicitly_convertible (AddressT PayableAddress)
    (AddressT NonpayableAddress) ∧
  implicitly_convertible (EnumT (AstId 900)) (EnumT (AstId 900)) ∧
  implicitly_convertible BoolT BoolT
Proof
  EVAL_TAC
QED

Theorem implicit_conversions_rejected:
  ¬implicitly_convertible u8 (IntT 16) ∧
  ¬implicitly_convertible u16 u8 ∧
  ¬implicitly_convertible i8 u256 ∧
  ¬implicitly_convertible (FixedBytesT 2) (FixedBytesT 1) ∧
  ¬implicitly_convertible (AddressT NonpayableAddress)
    (AddressT PayableAddress) ∧
  ¬implicitly_convertible (EnumT (AstId 900)) u8 ∧
  ¬implicitly_convertible (UintT 64) (UserValueT (AstId 901)) ∧
  ¬implicitly_convertible (UintT 160) (AddressT NonpayableAddress)
Proof
  EVAL_TAC
QED

Theorem implicit_conversions_lossless:
  convert u8 u16 (IntegerValue 200) = ScalarOk (IntegerValue 200) ∧
  convert i8 i256 (IntegerValue (-128)) = ScalarOk (IntegerValue (-128)) ∧
  convert (FixedBytesT 1) (FixedBytesT 2) (BytesValue [0xABw]) =
    ScalarOk (BytesValue [0xABw; 0w])
Proof
  EVAL_TAC
QED
