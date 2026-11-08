(* The Yul evaluator: a fuel-indexed, executable interpreter for creation and
 * runtime objects, written so that it cv_evals.
 *
 * Fuel: n bounds every recursive step that is not structural. Sibling
 * statements and the arguments of one call reuse the bound; entering a
 * function takes two off, the call expression's own test and the invoked
 * body's, and a loop's back edge takes one off, so straight-line code and a
 * loop's first iteration need none. A run that nests deeper or iterates
 * longer than its fuel reaches ends in YulOutOfFuel rather than in a wrong
 * answer.
 *
 * Scopes: a block, an if branch, a switch case, a loop body, a loop's post
 * statement and a call each run in a pushed scope; leaving pops exactly that
 * scope, so writes to enclosing bindings survive and a branch's locals do not.
 * A for loop's prelude runs in the loop's own scope, which is why its variable
 * is visible in the condition, body and post statement.
 *
 * Order: a call's arguments are evaluated right to left, as Yul specifies, and
 * case values are tried in order.
 *
 * Values: expressions produce a list of 256-bit words, since a call to a
 * user-defined function can return several. Binding or returning the wrong
 * number of them is an error rather than a silent truncation, as is an
 * argument that is not exactly one value, a literal too long for the dialect,
 * an unknown function, an unbound name, a builtin called with the wrong number
 * of arguments, an immutable the frame does not carry, or an unknown object
 * name. Object builtins read the frame's code, extents and immutable offsets;
 * linker symbols remain unsupported.
 * So is a break or continue that leaves a loop's post statement: Yul allows
 * them only in a loop's body, and one from the post would otherwise reach an
 * enclosing loop.
 *
 * Memory, storage, calls and logs: the builtins that read or write them are in
 * eval_yul_builtin below, on the machine in yulState. Memory is byte-addressed
 * and every access raises its active size.
 *
 * A message call is Verifereum's, not a second call mechanics: call and
 * staticcall both hand the call to run_external_call, the same one-frame
 * construction the source evaluator's high-level calls use, which runs
 * Verifereum's run_call. The callee is always bytecode -- a Yul frame never
 * nests inside another Yul frame -- so a call back into the frame's own
 * address runs that account's deployed code. The callee's return data lands in
 * the frame's return_data buffer, whatever the caller asked for as an output
 * region, and the output region gets the first min(outsize, returndatasize)
 * bytes of it, the same bytes Verifereum's own sub-frame return writes. A call
 * that leaves the model ends in YulInvalid rather than in a guess.
 *
 * Gas is not charged, so gas() reports the whole budget the frame was given
 * and never falls, and a call hands its own gas argument on to the callee,
 * capped at that budget: solc writes gas() there unless the source names a
 * limit. delegatecall is not
 * implemented and the dialect does not name it, so importing Yul that uses it
 * fails closed. docs/yul-call-design.md says why, and what the model does not
 * do.
 *)
Theory yulEvaluator
Ancestors
  yulAST yulState yulDialect externalCall vfmState vfmConstants vfmExecution
  vfmCompute keccak cv_string_fmap
Libs
  cv_transLib wordsLib

(* Scopes *)

Definition yul_push_scope_def:
  yul_push_scope m =
    m with scopes := (FEMPTY : string |-> bytes32) :: m.scopes
End

Definition yul_pop_scope_def:
  yul_pop_scope m = m with scopes := TL m.scopes
End

(* Results *)

Definition yul_normal_def:
  yul_normal m = <| completion := YulNormal; machine := m |>
End

Definition yul_abrupt_def:
  yul_abrupt c m = <| completion := c; machine := m |>
End

Definition yul_invalid_def:
  yul_invalid reason m = yul_abrupt (YulInvalid reason) m
End

Definition yul_pop_result_def:
  yul_pop_result (r : yul_result) =
    r with machine := yul_pop_scope r.machine
End

(* The scope and binding types are pinned rather than left to inference: a
 * polymorphic finite-map argument is not something the cv translation can
 * encode, and these are the only scopes this machine has.
 *)
Definition yul_lookup_def:
  (yul_lookup (x : string) [] = NONE) ∧
  (yul_lookup (x : string) ((scope : string |-> bytes32) :: rest) =
    case FLOOKUP scope x of SOME v => SOME v | NONE => yul_lookup x rest)
End

Definition yul_lookup_names_def:
  (yul_lookup_names [] scopes = SOME []) ∧
  (yul_lookup_names (x :: xs) scopes =
    case yul_lookup x scopes of
      NONE => NONE
    | SOME v =>
        (case yul_lookup_names xs scopes of
           NONE => NONE
         | SOME vs => SOME (v :: vs)))
End

(* Writing bindings into a scope, a pair at a time: the later pair of a name
 * wins, as FUPDATE_LIST would.  Spelled out rather than left to FUPDATE_LIST
 * because that operation's cv equation is conditional, which the cv
 * translation of a non-recursive definition cannot discharge.
 *)
Definition yul_bind_scope_def:
  (yul_bind_scope (scope : string |-> bytes32) [] = scope) ∧
  (yul_bind_scope (scope : string |-> bytes32) ((x, v) :: ps) =
     yul_bind_scope (scope |+ (x, v)) ps)
End

(* A call's own scope: its parameters bound to the arguments, and its result
 * variables bound to zero.  The compiler declares the results with the
 * function, so a body assigns one without a `let` -- the pinned solc emits
 * `sum := add(x, y)` -- and that assignment is legal only because the name is
 * already bound here.  Zero is what the compiler's own codegen gives a
 * declared result: `function g() -> x { }` is accepted, and the assembly for
 * it starts `x`'s byte by pushing 0.  A named function rather than an update
 * written out at the call, because a mutual recursion translated through a
 * pre-relation is compared on its arguments as terms: a constant application
 * is the same term on both sides, an inlined record update is not.
 *
 * The frame is the callee's *whole* scope stack, not the caller's with one more
 * scope on top: Yul functions cannot access variables defined outside the
 * function, so the caller's scopes are not the callee's to read, and a body that
 * looks one up is rejected rather than answered.  `invoke_yul` gives the caller
 * its own scopes back, which is what keeps the frame the callee's alone.
 *)
Definition yul_push_frame_def:
  yul_push_frame params args results m =
    m with scopes :=
      [yul_bind_scope (FEMPTY : string |-> bytes32)
         (ZIP (params, args) ++
          ZIP (results, REPLICATE (LENGTH results) 0w))]
End

(* Binds names in the innermost scope.  Written as a case on the scope stack
 * rather than with HD and TL, whose cv equations carry a non-emptiness
 * condition a translated definition cannot discharge.
 *)
Definition yul_bind_def:
  yul_bind names values m =
    if LENGTH names ≠ LENGTH values then yul_invalid "bad binding" m
    else
      case m.scopes of
        [] => yul_invalid "bad binding" m
      | scope :: rest =>
          yul_normal (m with scopes :=
            yul_bind_scope scope (ZIP (names, values)) :: rest)
End

(* Updates the innermost scope that binds x. *)
Definition yul_update_def:
  (yul_update (x : string) (v : bytes32) [] = NONE) ∧
  (yul_update (x : string) (v : bytes32)
     ((scope : string |-> bytes32) :: rest) =
    if FLOOKUP scope x = NONE then
      case yul_update x v rest of
        NONE => NONE
      | SOME rest' => SOME (scope :: rest')
    else SOME ((scope |+ (x, v)) :: rest))
End

Definition yul_assign_list_def:
  (yul_assign_list [] (rest : (string |-> bytes32) list) = SOME rest) ∧
  (yul_assign_list ((x, v) :: ps) (rest : (string |-> bytes32) list) =
    case yul_update x v rest of
      NONE => NONE
    | SOME rest' => yul_assign_list ps rest')
End

Definition yul_assign_def:
  yul_assign names values m =
    if LENGTH names ≠ LENGTH values then yul_invalid "bad assignment" m
    else
      case yul_assign_list (ZIP (names, values)) m.scopes of
        NONE => yul_invalid "unbound assignment" m
      | SOME scopes => yul_normal (m with scopes := scopes)
End

(* Memory: a byte per address, absent bytes being zero, with the active size
 * beside it.  Every access raises the size to the end of the last word it
 * touches, and an access of no bytes touches nothing, as in the EVM.
 *)

Definition yul_memory_byte_def:
  yul_memory_byte m (a : num) =
    case FLOOKUP m.memory a of NONE => 0w | SOME b => b
End

Definition yul_memory_read_def:
  (yul_memory_read m offset 0 = []) ∧
  (yul_memory_read m offset (SUC k) =
     yul_memory_byte m offset :: yul_memory_read m (offset + 1) k)
End

Definition yul_memory_write_def:
  yul_memory_write m offset [] = m ∧
  yul_memory_write m offset (b :: bs) =
    yul_memory_write (m with memory := m.memory |+ (offset, b)) (offset + 1) bs
End


Definition yul_memory_touch_def:
  yul_memory_touch m offset sz =
    m with memory_size :=
      MAX m.memory_size
          (if sz = 0 then 0 else word_size (offset + sz) * 32)
End

(* The touched machine and the bytes read from it. *)
Definition yul_memory_region_def:
  yul_memory_region m offset sz =
    let m' = yul_memory_touch m offset sz in
      (m', yul_memory_read m' offset sz)
End

Definition yul_mload_def:
  yul_mload m offset =
    yul_memory_region m offset 32
End

Definition yul_mstore_def:
  yul_mstore m offset value =
    yul_memory_write (yul_memory_touch m offset 32) offset (word_to_bytes_be value)
End

(* Storage, straight to the executing account's. *)

Definition yul_sload_def:
  yul_sload m slot =
    lookup_storage slot (lookup_account m.self_address m.accounts).storage
End

Definition yul_sstore_def:
  yul_sstore m slot value =
    let account = lookup_account m.self_address m.accounts in
      m with accounts :=
        update_account m.self_address
          (account with storage := update_storage slot value account.storage)
          m.accounts
End

(* Transient storage, the executing account's part of the frame's.  The frame
 * has no static mode, so tstore always takes effect, as sstore does. *)

Definition yul_tload_def:
  yul_tload m slot =
    lookup_storage slot (lookup_transient_storage m.self_address m.transient)
End

Definition yul_tstore_def:
  yul_tstore m slot value =
    m with transient :=
      update_transient_storage m.self_address
        (update_storage slot value
           (lookup_transient_storage m.self_address m.transient))
        m.transient
End

(* SIGNEXTEND(i, x): the low 8*(i+1) bits of x as a signed number, extended
 * through the word; i ≥ 31 leaves x alone, since the whole word is already in
 * view.  This is what the EVM's SIGNEXTEND does, spelled with HOL's
 * word_sign_extend rather than vfmExecution's byte-level sign_extend: that one
 * needs a cv pre-relation for its NULL/HD side condition and its word_to_bytes
 * rewriting to word_to_bytes_be, which is how vfmCompute translates it.
 *)
Definition yul_sign_extend_def:
  yul_sign_extend (i : bytes32) (w : bytes32) =
    if i > 31w then w else word_sign_extend (8 * (w2n i + 1)) w
End

(* Literals *)

Definition yul_literal_value_def:
  yul_literal_value (LitNumber w) = SOME w ∧
  yul_literal_value (LitBytes bs) =
    (if LENGTH bs ≤ 32 then
       SOME (word_of_bytes_be (take_pad_0 32 bs))
     else NONE) ∧
  yul_literal_value (LitBool b) = SOME (b2w b)
End

(* The name a string literal spells, one character per byte.  A Yul name is the
 * text the compiler wrote, and loadimmutable's argument is a name rather than a
 * value, so the frame's immutable table is keyed by this and the evaluator
 * reads its argument as text rather than as a word.
 *)
Definition yul_name_of_bytes_def:
  (yul_name_of_bytes ([] : byte list) = "") ∧
  (yul_name_of_bytes (b :: bs) = CHR (w2n b) :: yul_name_of_bytes bs)
End

(* Expression results: values, or an abrupt completion with the machine it
 * left behind. *)
Datatype:
  yul_expr_result
  = EvalValues (bytes32 list) yul_machine
  | EvalAbrupt yul_completion yul_machine
End

(* A message call, as the EVM's CALL and STATICCALL make it.
 *
 * The input region is read out of the caller's memory and touched, then the
 * call goes to run_external_call, which is Verifereum's run_call on the fresh
 * one-frame state a message call needs (semantics/externalCallScript.sml).
 * The caller is this frame, the callee the builtin's address argument
 * truncated to 160 bits, the value moved before the callee runs, and the
 * callee's own budget the builtin's gas argument capped at this frame's: gas
 * is not charged here, so the frame's budget is the most it can hand on.
 * The callee's code is the account's -- a delegated
 * account runs its delegate's, as the EVM's CALL does. The callee starts
 * from the frame's transient storage, as it does from the frame's accounts.
 *
 * What comes back is CALL's own answer: 1 if the callee stopped or returned
 * and 0 if it reverted or halted exceptionally, with the frame's accounts,
 * transient storage and logs taken from the callee only in the first case. The return data is the
 * callee's output either way -- the revert data for a revert, nothing for an
 * exceptional halt -- and is kept whole in return_data, while the output
 * region gets only the first min(outsize, returndatasize) bytes of it, left
 * as they were beyond that.
 *
 * run_external_call answers NONE where the call leaves the model: a recipient
 * balance overflow, a run outside the domain (one that ends in no frame, in
 * more than one, or in a vfm_abort), or a callee that ends with accounts
 * pending deletion. That is an invalid outcome, not a failed call, since the
 * model cannot say whether it would have succeeded.
 *)
(* The words are pinned rather than left to inference: every one of the sizes
 * reaches the machine only through w2n, which says nothing about its width, so
 * a call with a literal argument and no other use of that argument would leave
 * the width free -- and a free type variable in one clause of the builtin
 * dispatch is a definition the kernel will not accept.
 *)
Definition yul_call_def:
  yul_call (m : yul_machine) (static : bool) (gas : bytes32)
           (callee : bytes32) (value : bytes32) (input : bytes32)
           (input_size : bytes32) (output : bytes32) (output_size : bytes32) =
    let (m1, args) = yul_memory_region m (w2n input) (w2n input_size) in
      case run_external_call m1.self_address (w2w callee) args (w2n value)
             static (MIN (w2n gas) m1.gas_limit) m1.accounts m1.transient
             m1.transaction_parameters of
        NONE => EvalAbrupt (YulInvalid "call outside the model") m1
      | SOME outcome =>
          let m2 = m1 with <| accounts := outcome.call_accounts;
                               transient := outcome.call_transient;
                               logs := m1.logs ++ outcome.call_logs;
                               return_data := outcome.call_return |> in
            EvalValues [b2w outcome.call_success]
              (yul_memory_write
                 (yul_memory_touch m2 (w2n output) (w2n output_size))
                 (w2n output) (TAKE (w2n output_size) outcome.call_return))
End

(* returndatacopy: the bytes it reads come from return_data, not from memory,
 * so it is not yul_memory_region.  Reading past the end of the buffer is the
 * EVM's OutOfBoundsRead, an exceptional halt rather than a short copy.
 *)
Definition yul_return_data_copy_def:
  yul_return_data_copy (m : yul_machine) (dest : bytes32) (source : bytes32)
                       (size : bytes32) =
    if w2n source + w2n size > LENGTH m.return_data then
      EvalAbrupt (YulInvalid "return data out of bounds") m
    else
      EvalValues []
        (yul_memory_write
           (yul_memory_touch m (w2n dest) (w2n size))
           (w2n dest) (TAKE (w2n size) (DROP (w2n source) m.return_data)))
End

(* addmod and mulmod as the EVM computes them (verifereum's step_modop): the
 * sum or product of the full values, without wrapping, modulo n, and 0 for a
 * zero modulus.  The words are pinned, since a and b reach the result only
 * through w2n.
 *)
Definition modular_word_def:
  modular_word f (a : bytes32) (b : bytes32) (n : bytes32) : bytes32 =
    if n = 0w then 0w else n2w (f (w2n a) (w2n b) MOD w2n n)
End

(* One builtin on evaluated values. Literal-name operands are dispatched by
 * eval_yul_builtin_call; unsupported builtins and wrong arities fail closed.
 *)
Definition eval_yul_builtin_def:
  eval_yul_builtin op args m =
    case (op, args) of
      (YAdd, [a; b]) => EvalValues [a + b] m
    | (YSub, [a; b]) => EvalValues [a - b] m
    | (YMul, [a; b]) => EvalValues [a * b] m
    | (YDiv, [a; b]) => EvalValues [with_zero word_div a b] m
    | (YSDiv, [a; b]) => EvalValues [with_zero word_quot a b] m
    | (YMod, [a; b]) => EvalValues [with_zero word_mod a b] m
    | (YSMod, [a; b]) => EvalValues [with_zero word_rem a b] m
    | (YAddMod, [a; b; n]) => EvalValues [modular_word $+ a b n] m
    | (YMulMod, [a; b; n]) => EvalValues [modular_word $* a b n] m
    | (YExp, [a; b]) => EvalValues [word_exp a b] m
    | (YSignExtend, [a; b]) => EvalValues [yul_sign_extend a b] m
    | (YLt, [a; b]) => EvalValues [b2w (w2n a < w2n b)] m
    | (YGt, [a; b]) => EvalValues [b2w (w2n a > w2n b)] m
    | (YSLt, [a; b]) => EvalValues [b2w (word_lt a b)] m
    | (YSGt, [a; b]) => EvalValues [b2w (word_gt a b)] m
    | (YEq, [a; b]) => EvalValues [b2w (a = b)] m
    | (YIsZero, [a]) => EvalValues [b2w (a = 0w)] m
    | (YAnd, [a; b]) => EvalValues [word_and a b] m
    | (YOr, [a; b]) => EvalValues [word_or a b] m
    | (YXor, [a; b]) => EvalValues [word_xor a b] m
    | (YNot, [a]) => EvalValues [word_1comp a] m
    | (YShl, [n; w]) => EvalValues [word_lsl w (w2n n)] m
    | (YShr, [n; w]) => EvalValues [word_lsr w (w2n n)] m
    | (YSar, [n; w]) => EvalValues [word_asr w (w2n n)] m
    | (YByte, [i; w]) =>
        EvalValues [if w2n i < 32 then n2w ((w2n w DIV 2 ** (8 * (31 - w2n i))) MOD 256)
                    else 0w] m
    | (YKeccak256, [p; s]) =>
        let (m', bs) = yul_memory_region m (w2n p) (w2n s) in
          EvalValues [word_of_bytes_be (Keccak_256_w64 bs)] m'
    | (YMLoad, [p]) =>
        let (m', bs) = yul_mload m (w2n p) in
          EvalValues [word_of_bytes_be bs] m'
    | (YMStore, [p; v]) => EvalValues [] (yul_mstore m (w2n p) v)
    | (YMStore8, [p; v]) =>
        EvalValues [] (yul_memory_write (yul_memory_touch m (w2n p) 1)
          (w2n p) [(n2w (w2n v) : byte)])
    | (YMCopy, [d; s; l]) =>
        (* both ranges are touched, whichever of them reaches further, and the
         * bytes are read before any is written, so overlapping regions copy as
         * the EVM's MCOPY does *)
        let (m', bs) = yul_memory_region m (w2n s) (w2n l) in
          EvalValues []
            (yul_memory_write (yul_memory_touch m' (w2n d) (w2n l))
               (w2n d) bs)
    | (YSLoad, [s]) => EvalValues [yul_sload m s] m
    | (YSStore, [s; v]) => EvalValues [] (yul_sstore m s v)
    | (YTLoad, [s]) => EvalValues [yul_tload m s] m
    | (YTStore, [s; v]) => EvalValues [] (yul_tstore m s v)
    | (YCallDataLoad, [i]) =>
        EvalValues
          [word_of_bytes_be (take_pad_0 32 (DROP (w2n i) m.call_data))]
          m
    | (YCallDataSize, []) => EvalValues [n2w (LENGTH m.call_data)] m
    | (YCallDataCopy, [dst; src; sz]) =>
        EvalValues []
          (yul_memory_write (yul_memory_touch m (w2n dst) (w2n sz))
            (w2n dst) (take_pad_0 (w2n sz) (DROP (w2n src) m.call_data)))
    | (YCallValue, []) => EvalValues [m.call_value] m
    | (YMemoryGuard, [x]) => EvalValues [x] m
    | (YCaller, []) => EvalValues [n2w (w2n m.caller_address)] m
    | (YAddress, []) => EvalValues [n2w (w2n m.self_address)] m
    | (YOrigin, []) =>
        EvalValues [n2w (w2n m.transaction_parameters.origin)] m
    | (YGasPrice, []) =>
        EvalValues [n2w m.transaction_parameters.gasPrice] m
    | (YChainId, []) => EvalValues [n2w m.transaction_parameters.chainId] m
    | (YBaseFee, []) =>
        EvalValues [n2w m.transaction_parameters.baseFeePerGas] m
    | (YGasLimit, []) =>
        EvalValues [n2w m.transaction_parameters.blockGasLimit] m
    | (YNumber, []) =>
        EvalValues [n2w m.transaction_parameters.blockNumber] m
    | (YTimestamp, []) =>
        EvalValues [n2w m.transaction_parameters.blockTimeStamp] m
    | (YCoinbase, []) =>
        EvalValues [n2w (w2n m.transaction_parameters.blockCoinBase)] m
    | (YLog0, [p; s]) =>
        let (m', bs) = yul_memory_region m (w2n p) (w2n s) in
          EvalValues []
            (m' with logs := m'.logs ++
              [<| logger := m'.self_address; topics := []; data := bs |>])
    | (YLog1, [p; s; topic]) =>
        let (m', bs) = yul_memory_region m (w2n p) (w2n s) in
          EvalValues []
            (m' with logs := m'.logs ++
              [<| logger := m'.self_address; topics := [topic];
                  data := bs |>])
    | (YLog2, [p; s; t1; t2]) =>
        let (m', bs) = yul_memory_region m (w2n p) (w2n s) in
          EvalValues []
            (m' with logs := m'.logs ++
              [<| logger := m'.self_address; topics := [t1; t2];
                  data := bs |>])
    | (YLog3, [p; s; t1; t2; t3]) =>
        let (m', bs) = yul_memory_region m (w2n p) (w2n s) in
          EvalValues []
            (m' with logs := m'.logs ++
              [<| logger := m'.self_address; topics := [t1; t2; t3];
                  data := bs |>])
    | (YLog4, [p; s; t1; t2; t3; t4]) =>
        let (m', bs) = yul_memory_region m (w2n p) (w2n s) in
          EvalValues []
            (m' with logs := m'.logs ++
              [<| logger := m'.self_address; topics := [t1; t2; t3; t4];
                  data := bs |>])
    | (YPop, [_]) => EvalValues [] m
    | (YGas, []) => EvalValues [n2w m.gas_limit] m
    | (YExtCodeSize, [a]) =>
        EvalValues [n2w (LENGTH (lookup_account (w2w a) m.accounts).code)] m
    | (YReturnDataSize, []) =>
        EvalValues [n2w (LENGTH m.return_data)] m
    | (YReturnDataCopy, [dst; src; sz]) => yul_return_data_copy m dst src sz
    (* call(gas, address, value, args, argsSize, ret, retSize) *)
    | (YCall, [gl; ad; v; inp; insz; outp; outsz]) =>
        yul_call m F gl ad v inp insz outp outsz
    (* staticcall(gas, address, args, argsSize, ret, retSize) *)
    | (YStaticCall, [gl; ad; inp; insz; outp; outsz]) =>
        yul_call m T gl ad 0w inp insz outp outsz
    | (YStop, []) => EvalAbrupt (YulReturn []) m
    | (YReturn, [p; s]) =>
        let (m', bs) = yul_memory_region m (w2n p) (w2n s) in
          EvalAbrupt (YulReturn bs) m'
    | (YRevert, [p; s]) =>
        let (m', bs) = yul_memory_region m (w2n p) (w2n s) in
          EvalAbrupt (YulRevert bs) m'
    | (YCodeSize, []) => EvalValues [n2w (LENGTH m.code)] m
    | (YCodeCopy, [dst; src; sz]) =>
        EvalValues []
          (yul_memory_write (yul_memory_touch m (w2n dst) (w2n sz))
             (w2n dst) (take_pad_0 (w2n sz) (DROP (w2n src) m.code)))
    | (YDataSize, _) => EvalAbrupt (YulInvalid "object-level builtin") m
    | (YDataOffset, _) => EvalAbrupt (YulInvalid "object-level builtin") m
    | (YSetImmutable, _) => EvalAbrupt (YulInvalid "object-level builtin") m
    | (YLinkerSymbol, _) => EvalAbrupt (YulInvalid "object-level builtin") m
    | _ => EvalAbrupt (YulInvalid "bad builtin call") m
End

(* Object and immutable names are identifiers, not 256-bit values. *)
Definition yul_builtin_value_args_def:
  yul_builtin_value_args op args =
    case (op, args) of
      (YLoadImmutable, [YulLit (LitBytes _)]) => []
    | (YDataSize, [YulLit (LitBytes _)]) => []
    | (YDataOffset, [YulLit (LitBytes _)]) => []
    | (YSetImmutable, [position; YulLit (LitBytes _); value]) => [position; value]
    | _ => args
End

Theorem yul_builtin_value_args_size:
  list_size yul_expr_size (yul_builtin_value_args op args) ≤
  list_size yul_expr_size args
Proof
  rw[yul_builtin_value_args_def] >>
  BasicProvers.every_case_tac >> simp[listTheory.list_size_def]
QED

(* setimmutable patches every occurrence in the copied runtime object.
 * An immutable unused by that object has no patch offsets. *)
Definition yul_set_immutable_def:
  yul_set_immutable name (position : bytes32) (value : bytes32) m =
    let offsets = case FLOOKUP m.immutable_offsets name of
                    NONE => [] | SOME offsets => offsets in
    (FOLDL (λm off. yul_mstore m (w2n position + off) value) m offsets)
      with immutables := m.immutables |+ (name, value)
End

Definition eval_yul_builtin_call_def:
  eval_yul_builtin_call op args vs m =
    case (op, args, vs) of
      (YLoadImmutable, [YulLit (LitBytes nm)], []) =>
        (case FLOOKUP m.immutables (yul_name_of_bytes nm) of
           SOME v => EvalValues [v] m
         | NONE => EvalAbrupt (YulInvalid "unknown immutable") m)
    | (YDataSize, [YulLit (LitBytes nm)], []) =>
        (case FLOOKUP m.objects (yul_name_of_bytes nm) of
           SOME extent => EvalValues [n2w (SND extent)] m
         | NONE => EvalAbrupt (YulInvalid "unknown object") m)
    | (YDataOffset, [YulLit (LitBytes nm)], []) =>
        (case FLOOKUP m.objects (yul_name_of_bytes nm) of
           SOME extent => EvalValues [n2w (FST extent)] m
         | NONE => EvalAbrupt (YulInvalid "unknown object") m)
    | (YSetImmutable, [_; YulLit (LitBytes nm); _], [position; value]) =>
        EvalValues [] (yul_set_immutable (yul_name_of_bytes nm) position value m)
    | _ => eval_yul_builtin op vs m
End

(* Termination measures, one per group of the mutual recursion: the relation
 * handed to WF_REL_TAC is then small, and the obligations it leaves are
 * applications of these, which the step after it reduces to arithmetic.
 *
 * Fuel comes first, since a loop's back edge and a call each spend one; the
 * second component is the size of the syntax that group has still to walk.  A
 * group's row must exceed the rows of the groups it calls, which is what the
 * constants are for: a statement's row exceeds the block rows beneath it, and
 * a block's row exceeds the rows of the statements in it.
 *)
Definition yul_measure_block_def:
  yul_measure_block (n : num, fns, ss, m) =
    (n, list_size yul_stmt_size ss + 2)
End

Definition yul_measure_stmt_def:
  yul_measure_stmt (n : num, fns, q, m) = (n, yul_stmt_size q + 2)
End

Definition yul_measure_expr_def:
  yul_measure_expr (n : num, fns, e, m) = (n, yul_expr_size e)
End

Definition yul_measure_args_def:
  yul_measure_args (n : num, fns, es, m) = (n, list_size yul_expr_size es)
End

Definition yul_measure_loop_def:
  yul_measure_loop (n : num, fns, cond, post, body, m) =
    (n, yul_expr_size cond + list_size yul_stmt_size body +
        list_size yul_stmt_size post + 2)
End

Definition yul_measure_cases_def:
  yul_measure_cases (n : num, fns, v, cases, default, m) =
    (n, list_size (pair_size yul_literal_size (list_size yul_stmt_size)) cases +
        list_size yul_stmt_size default + 3)
End

(* A call is reached through the expression that makes it, so its row only has
 * to be smaller than that one's; the fuel is what decreases. *)
Definition yul_measure_invoke_def:
  yul_measure_invoke (n : num, fns, name, args, m) = (n, 0n)
End

(* Two obligations a loop's own row leaves behind: it has to be bigger than the
 * rows of the body and the post it walks, both of which are block rows.  Its
 * room for them is its condition's size -- the condition is an expression, and
 * an expression always has a size -- so these are just arithmetic. *)
Theorem yul_measure_loop_body_lt:
  ∀b p c : num. 0 < c ⇒ b + 2 < c + (b + (p + 2))
Proof
  decide_tac
QED

Theorem yul_measure_loop_post_lt:
  ∀b p c : num. 0 < c ⇒ p + 2 < c + (b + (p + 2))
Proof
  decide_tac
QED

(* The evaluator.  n is fuel, fns the functions a call may reach. *)
Definition eval_yul_block_def:
  (* statement lists: siblings reuse the bound, a non-normal completion stops *)
  (eval_yul_block (n : num) (fns : string |-> yul_function) [] m =
     yul_normal m) ∧
  (eval_yul_block n fns (s :: ss) m =
     let r = eval_yul_stmt n fns s m in
       if r.completion = YulNormal then
         eval_yul_block n fns ss r.machine
       else r) ∧

  (eval_yul_stmt n fns (YulBlock ss) m =
     yul_pop_result (eval_yul_block n fns ss (yul_push_scope m))) ∧
  (* a definition has no runtime effect: yul_env collected it beforehand *)
  (eval_yul_stmt n fns (YulFunction name params results body) m =
     yul_normal m) ∧
  (eval_yul_stmt n fns (YulLet names value) m =
     case value of
       NONE => yul_bind names (REPLICATE (LENGTH names) 0w) m
     | SOME e =>
         (case eval_yul_expr n fns e m of
            EvalAbrupt c m' => yul_abrupt c m'
          | EvalValues vs m' => yul_bind names vs m')) ∧
  (eval_yul_stmt n fns (YulAssign names e) m =
     case eval_yul_expr n fns e m of
       EvalAbrupt c m' => yul_abrupt c m'
     | EvalValues vs m' => yul_assign names vs m') ∧
  (eval_yul_stmt n fns (YulIf c body) m =
     case eval_yul_expr n fns c m of
       EvalAbrupt co m' => yul_abrupt co m'
     | EvalValues [v] m' =>
         if v = 0w then yul_normal m'
         else yul_pop_result (eval_yul_block n fns body (yul_push_scope m'))
     | EvalValues _ m' => yul_invalid "condition is not one value" m') ∧
  (eval_yul_stmt n fns (YulSwitch e cases default) m =
     case eval_yul_expr n fns e m of
       EvalAbrupt co m' => yul_abrupt co m'
     | EvalValues [v] m' => eval_yul_cases n fns v cases default m'
     | EvalValues _ m' => yul_invalid "case value is not one value" m') ∧
  (* the prelude runs once, in the loop's own scope *)
  (eval_yul_stmt n fns (YulFor init cond post body) m =
     let m1 = yul_push_scope m in
     let r = eval_yul_block n fns init m1 in
       if r.completion = YulNormal then
         eval_yul_loop n fns cond post body r.machine
       else yul_pop_result r) ∧
  (eval_yul_stmt n fns YulBreak m = yul_abrupt YulBreak m) ∧
  (eval_yul_stmt n fns YulContinue m = yul_abrupt YulContinue m) ∧
  (eval_yul_stmt n fns YulLeave m = yul_abrupt YulLeave m) ∧
  (eval_yul_stmt n fns (YulExprStmt e) m =
     case eval_yul_expr n fns e m of
       EvalAbrupt c m' => yul_abrupt c m'
     | EvalValues _ m' => yul_normal m') ∧

  (eval_yul_expr n fns (YulLit l) m =
     case yul_literal_value l of
       SOME v => EvalValues [v] m
     | NONE => EvalAbrupt (YulInvalid "literal out of range") m) ∧
  (eval_yul_expr n fns (YulName x) m =
     case yul_lookup x m.scopes of
       SOME v => EvalValues [v] m
     | NONE => EvalAbrupt (YulInvalid "unbound name") m) ∧
  (eval_yul_expr n fns (YulBuiltin op args) m =
     case eval_yul_args n fns (yul_builtin_value_args op args) m of
       EvalAbrupt c m' => EvalAbrupt c m'
     | EvalValues vs m' => eval_yul_builtin_call op args vs m') ∧
  (eval_yul_expr n fns (YulApply f args) m =
     if n = 0 then EvalAbrupt YulOutOfFuel m
     else
       case eval_yul_args n fns args m of
         EvalAbrupt c m' => EvalAbrupt c m'
       | EvalValues vs m' => invoke_yul (n - 1) fns f vs m') ∧

  (* arguments right to left: the tail first, then the head *)
  (eval_yul_args n fns [] m = EvalValues [] m) ∧
  (eval_yul_args n fns (a :: args) m =
     case eval_yul_args n fns args m of
       EvalAbrupt c m' => EvalAbrupt c m'
     | EvalValues vs m' =>
         (case eval_yul_expr n fns a m' of
            EvalAbrupt c m'' => EvalAbrupt c m''
          | EvalValues [w] m'' => EvalValues (w :: vs) m''
          | EvalValues _ m'' =>
              EvalAbrupt (YulInvalid "argument is not one value") m'')) ∧

  (* one iteration of a for loop, in the scope the prelude made; fuel is spent
   * on the back edge, so the first iteration is free *)
  (eval_yul_loop n fns cond post body m =
     case eval_yul_expr n fns cond m of
       EvalAbrupt c m' => yul_pop_result (yul_abrupt c m')
     | EvalValues [v] m' =>
         if v = 0w then yul_normal (yul_pop_scope m')
         else
           let rb = yul_pop_result (eval_yul_block n fns body (yul_push_scope m')) in
             if rb.completion = YulBreak then
               yul_normal (yul_pop_scope rb.machine)
             else if rb.completion ≠ YulNormal ∧ rb.completion ≠ YulContinue then
               yul_pop_result rb
             else
               let rp = yul_pop_result
                          (eval_yul_block n fns post (yul_push_scope rb.machine)) in
                 if rp.completion = YulBreak ∨ rp.completion = YulContinue then
                   yul_invalid "break or continue in loop post"
                     (yul_pop_scope rp.machine)
                 else if rp.completion ≠ YulNormal then yul_pop_result rp
                 else if n = 0 then
                   yul_abrupt YulOutOfFuel (yul_pop_scope rp.machine)
                 else eval_yul_loop (n - 1) fns cond post body rp.machine
     | EvalValues _ m' => yul_invalid "condition is not one value" (yul_pop_scope m')) ∧

  (* the case a switch runs: the first whose value matches, else the default;
   * a case value too long for the dialect is an error, not a skip *)
  (eval_yul_cases n fns v [] default m =
     yul_pop_result (eval_yul_block n fns default (yul_push_scope m))) ∧
  (eval_yul_cases n fns v ((lit, body) :: rest) default m =
     case yul_literal_value lit of
       NONE => yul_invalid "case value out of range" m
     | SOME w =>
         if w = v then
           yul_pop_result (eval_yul_block n fns body (yul_push_scope m))
         else eval_yul_cases n fns v rest default m) ∧

  (* a call: parameters in a scope of their own, results read out of it, then
   * leave, or falling off the end, returns them.  The frame is the callee's
   * alone (`yul_push_frame`), so what the caller gets back is the caller's own
   * scope stack -- not the callee's popped, which would be the same list only
   * while the callee left the caller's scopes alone, which is exactly what a
   * frame of its own makes sure of. *)
  (invoke_yul n fns name args m =
     if n = 0 then EvalAbrupt YulOutOfFuel m
     else
       case FLOOKUP fns name of
         NONE => EvalAbrupt (YulInvalid "unknown function") m
       | SOME fd =>
           if LENGTH fd.function_params ≠ LENGTH args then
             EvalAbrupt (YulInvalid "bad call arity") m
           else
             let m1 = yul_push_frame fd.function_params args
                        fd.function_results m in
             let r = eval_yul_block (n - 1) fns fd.function_body m1 in
             let m2 = r.machine with scopes := m.scopes in
               if r.completion = YulNormal ∨ r.completion = YulLeave then
                 (* the frame scope yul_push_frame made is still on top, so
                  * every result is bound and this lookup cannot fail; the
                  * branch is only what keeps it total *)
                 (case yul_lookup_names fd.function_results r.machine.scopes of
                    NONE => EvalAbrupt (YulInvalid "missing return binding") m2
                  | SOME vs => EvalValues vs m2)
               else EvalAbrupt r.completion m2)
Termination
  WF_REL_TAC `inv_image ($< LEX $<)
    (\x. case x of
           INL t => yul_measure_block t
         | INR (INL t) => yul_measure_stmt t
         | INR (INR (INL t)) => yul_measure_expr t
         | INR (INR (INR (INL t))) => yul_measure_args t
         | INR (INR (INR (INR (INL t)))) => yul_measure_loop t
         | INR (INR (INR (INR (INR (INL t))))) => yul_measure_cases t
         | INR (INR (INR (INR (INR (INR t))))) => yul_measure_invoke t)` >>
  rw[yul_measure_block_def, yul_measure_stmt_def, yul_measure_expr_def,
     yul_measure_args_def, yul_measure_loop_def, yul_measure_cases_def,
     yul_measure_invoke_def, listTheory.list_size_def,
     basicSizeTheory.pair_size_def, yul_expr_size_pos,
     yul_measure_loop_body_lt, yul_measure_loop_post_lt] >>
  mp_tac yul_builtin_value_args_size >> simp[]
End


(* A program: the object's code, with its own functions collected, started in
 * a scope of its own.
 *)
Definition run_yul_def:
  run_yul n code m =
    eval_yul_block n (yul_env code) code
      (m with scopes := (FEMPTY : string |-> bytes32) :: m.scopes)
End

(* cv translation, so compiled Yul runs under cv_compute.  The recursive
 * functions come as one mutually recursive group, which cv translates through
 * a pre-relation: the group's termination order and the totality of that
 * relation are supplied here rather than left to the translator to guess.
 *)

(* A cv pair is at least as large as its two halves together.  A recursion's
 * cv obligations compare sums of projections of the encoded argument tuples,
 * so each such sum needs a bound of this shape.  The toolchain proves the
 * same fact locally, in cv_string_fmap, where it does not cross theories.
 *)
Theorem cv_size_cv_fst_cv_snd[local]:
  ∀x. cv_size (cv_fst x) + cv_size (cv_snd x) ≤ cv_size x
Proof
  Cases \\ gvs [cvTheory.cv_size_def, cvTheory.cv_fst_def, cvTheory.cv_snd_def]
QED

val () = cv_auto_trans yul_lookup_def;
val () = cv_auto_trans yul_lookup_names_def;
val () = cv_auto_trans yul_bind_scope_def;
val () = cv_auto_trans yul_bind_def;
val () = cv_auto_trans yul_assign_def;
val () = cv_auto_trans yul_literal_value_def;

(* CHR is defined only up to 255, so the translation of a byte -> char function
 * carries that bound as a precondition, which cv_auto_trans cannot discharge on
 * its own: a byte satisfies it by construction, but the fact needs saying.
 * The translations below may call the converted function because of the
 * yul_name_of_bytes_pre theorem.
 *)
Theorem w2n_byte_lt[local]:
  ∀(b : word8). w2n b < 256
Proof
  gen_tac >> qspec_then ‘b’ mp_tac wordsTheory.w2n_lt >>
  simp[EVAL “dimword (:8)”]
QED

val yul_name_of_bytes_pre_def =
  cv_trans_pre "yul_name_of_bytes_pre" yul_name_of_bytes_def;

Theorem yul_name_of_bytes_pre[cv_pre]:
  ∀bs. yul_name_of_bytes_pre bs
Proof
  Induct >> rpt strip_tac >>
  once_rewrite_tac [yul_name_of_bytes_pre_def] >> fs [w2n_byte_lt]
QED

val () = cv_auto_trans yul_call_def;
val () = cv_auto_trans yul_return_data_copy_def;
(* Bound left shifts before computing powers, as in the EVM translation. *)
val () = cv_auto_trans
  (REWRITE_RULE [word_lsl_modexp, modular_word_def] eval_yul_builtin_def);
val () = cv_auto_trans yul_builtin_value_args_def;
Theorem cv_yul_builtin_value_args_size[local]:
  ∀op args. cv_size (cv_yul_builtin_value_args op args) ≤ cv_size args
Proof
  rw[DB.fetch "yulEvaluator" "cv_yul_builtin_value_args_def", cvTheory.cv_if_def] >>
  cv_termination_tac >>
  qspec_then ‘args’ assume_tac cv_size_cv_fst_cv_snd >>
  qspec_then ‘cv_snd args’ assume_tac cv_size_cv_fst_cv_snd >>
  qspec_then ‘cv_snd (cv_snd args)’ assume_tac cv_size_cv_fst_cv_snd >>
  gvs[]
QED

val () = cv_auto_trans yul_set_immutable_def;
val () = cv_auto_trans eval_yul_builtin_call_def;
val () = cv_auto_trans yul_env_def;

(* Termination of the translated evaluator: a scaled (fuel, size) order on the
 * cv encodings, strictly decreasing on every recursive call.  Fuel is tested
 * for zero before a back edge or a call, and sizes fall going into a
 * statement, an expression, a body or a case.
 *)
val yul_pre_def = cv_auto_trans_pre_rec "" eval_yul_block_def
  (WF_REL_TAC `inv_image ($< LEX $<)
     (\x. case x of
            INL (n0, e0, s0, m0) => (cv$c2n n0, 2 * cv_size s0)
          | INR (INL (n0, e0, q0, m0)) => (cv$c2n n0, 2 * cv_size q0 + 1)
          | INR (INR (INL (n0, e0, x0, m0))) => (cv$c2n n0, 2 * cv_size x0)
          | INR (INR (INR (INL (n0, e0, x1, m0)))) => (cv$c2n n0, 2 * cv_size x1)
          | INR (INR (INR (INR (INL (n0, e0, c0, p0, b0, m0))))) =>
              (cv$c2n n0, 2 * (cv_size c0 + cv_size b0 + cv_size p0) + 1)
          | INR (INR (INR (INR (INR (INL (n0, e0, v0, cs0, d0, m0)))))) =>
              (cv$c2n n0, 2 * (cv_size cs0 + cv_size d0) + 1)
          | INR (INR (INR (INR (INR (INR (n0, e0, nm0, a0, m0)))))) =>
              (cv$c2n n0, 0))` >>
   cv_termination_tac >>
   (* The obligations compare sums of projections of the encoded argument
    * tuples.  Each such sum is bounded by the size of the pair it projects
    * from, so supply that bound at every pair this recursion reaches into,
    * and the rest is arithmetic. *)
   qspec_then ‘x2’ assume_tac cv_size_cv_fst_cv_snd >>
   qspec_then ‘cv_snd x2’ assume_tac cv_size_cv_fst_cv_snd >>
   qspec_then ‘cv_snd (cv_snd x2)’ assume_tac cv_size_cv_fst_cv_snd >>
   gvs [] >>
   qspecl_then [‘cv_fst z’, ‘cv_snd z’] assume_tac
     cv_yul_builtin_value_args_size >>
   qspec_then ‘z’ assume_tac cv_size_cv_fst_cv_snd >> gvs []
   );

(* The pre-relation is total: every input of every function has a translated
 * step, so the equations cv derives from it fire unconditionally.
 *)
Theorem yul_pre[cv_pre]:
  (∀n fns v m. eval_yul_block_pre n fns v m) ∧
  (∀n fns v m. eval_yul_stmt_pre n fns v m) ∧
  (∀n fns v m. eval_yul_expr_pre n fns v m) ∧
  (∀n fns v m. eval_yul_args_pre n fns v m) ∧
  (∀n fns cond post body m. eval_yul_loop_pre n fns cond post body m) ∧
  (∀n fns v cases default m. eval_yul_cases_pre n fns v cases default m) ∧
  (∀n fns name args m. invoke_yul_pre n fns name args m)
Proof
  ho_match_mp_tac eval_yul_block_ind \\ rw []
  \\ simp [Once yul_pre_def]
  (* a call's precondition is the precondition of each of its sub-calls, at
   * the machine the sub-call is actually made on; the case split puts that
   * machine in the form the induction hypothesis wants *)
  \\ rw []
  \\ Cases_on ‘m’ \\ gvs []
  \\ metis_tac []
QED

val () = cv_auto_trans run_yul_def;
