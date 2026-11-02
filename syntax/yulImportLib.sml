(* Import of the pinned compiler's Yul into yulASTTheory's tree.
 *
 * The compiler emits its Yul as a JSON AST alongside the text form: irAst is
 * the code generator's output and irOptimizedAst is what the Yul
 * transformations leave, but only under settings.experimental. The JSON is
 * the tree the compiler's own converter walks, so importing it needs neither
 * a parser for the surface syntax nor a re-derivation of what the text means.
 *
 * What is imported is the runtime object: the creation object's single
 * subobject, whose code is the frame the EVM runs. The creation object is
 * checked only for its shape; its own code (codecopy, dataoffset, subobject
 * references) is a later step, as yulAST's object-level builtins say.
 *
 * The import fails closed. ImportError names a node kind the AST has no
 * constructor for, a call to a name that is neither a builtin nor a function
 * the object's code block defines, a function definition nested in a body
 * (the evaluator collects the object's top level only), an object with more
 * than one subobject or a nested one, and a literal that is neither a number
 * nor a string. Missing or ill-typed fields raise MalformedInput.
 *)
structure yulImportLib :> yulImportLib =
struct

open HolKernel boolLib bossLib yulASTTheory yulDialectTheory

datatype stage = Ir | IrOptimized

exception ImportError of string
exception MalformedInput of string

fun fail msg = raise ImportError msg

(* JSON access, with JSONUtil errors reported against the enclosing node. *)

val field = JSONUtil.lookupField
fun string_field v k = JSONUtil.asString (field v k)
fun array_field v k = JSONUtil.arrayMap I (field v k)

fun node_type v = string_field v "nodeType"

fun describe v = node_type v handle _ => "node"

fun within v f =
  f v
  handle ImportError msg => raise ImportError msg
       | e as JSONUtil.JSONError _ => raise MalformedInput (describe v ^ ": " ^ JSONUtil.exnMessage e)
       | e as JSONUtil.FieldNotFound _ => raise MalformedInput (describe v ^ ": " ^ JSONUtil.exnMessage e)
       | e as JSONUtil.NotObject => raise MalformedInput (describe v ^ ": " ^ JSONUtil.exnMessage e)
       | e as JSONUtil.NotArray => raise MalformedInput (describe v ^ ": " ^ JSONUtil.exnMessage e)

fun require v cond msg = if cond then () else fail (describe v ^ ": " ^ msg)

fun expect v ty = require v (node_type v = ty) ("expected " ^ ty)

fun optional_field v k =
  case JSONUtil.findField v k of
    NONE => NONE
  | SOME JSON.NULL => NONE
  | SOME x => SOME x

(* Terms *)

fun yul name args =
  list_mk_comb (prim_mk_const {Thy = "yulAST", Name = name}, args)

val builtin_ty = mk_thy_type {Thy = "yulAST", Tyop = "yul_builtin", Args = []}
val literal_ty = mk_thy_type {Thy = "yulAST", Tyop = "yul_literal", Args = []}
val expr_ty = mk_thy_type {Thy = "yulAST", Tyop = "yul_expr", Args = []}
val stmt_ty = mk_thy_type {Thy = "yulAST", Tyop = "yul_stmt", Args = []}
val byte_ty = wordsSyntax.mk_int_word_type 8

val mk_str = stringSyntax.fromMLstring

fun stmt_list ss = listSyntax.mk_list (ss, stmt_ty)
fun expr_list es = listSyntax.mk_list (es, expr_ty)
fun name_list ns = listSyntax.mk_list (map mk_str ns, stringSyntax.string_ty)

fun bytes_term bs =
  listSyntax.mk_list (map (fn b => wordsSyntax.mk_wordii (b, 8)) bs, byte_ty)

(* Numbers are the compiler's decimal or 0x-prefixed hex, and must fit the
 * word the AST stores them in. IntInf throughout: a 256-bit number does not
 * fit an SML int.
 *)
fun hex_digit c =
  if Char.isDigit c then ord c - ord #"0"
  else if #"a" <= c andalso c <= #"f" then ord c - ord #"a" + 10
  else if #"A" <= c andalso c <= #"F" then ord c - ord #"A" + 10
  else fail ("not a hex digit: " ^ String.str c)

(* The digits of a hex string, with the 0x the compiler's numbers carry and
 * without it where it leaves it off: a string literal's `hexValue` is the same
 * hex, unprefixed.
 *)
fun hex_digits s =
  if String.isPrefix "0x" s then String.extract (s, 2, NONE) else s

fun hex_number s =
  let val digits = hex_digits s in
    if size digits = 0 then fail ("empty hex literal " ^ s)
    else List.foldl (fn (c, acc) => acc * 16 + IntInf.fromInt (hex_digit c)) 0
           (explode digits)
  end

fun decimal_number s =
  case IntInf.fromString s of
    SOME n => n
  | NONE => fail ("not an integer: " ^ s)

fun word_term value =
  let
    val n = if String.isPrefix "0x" value then hex_number value
            else decimal_number value
    val () = if 0 <= n andalso n < IntInf.pow (2, 256) then ()
             else fail ("literal does not fit 256 bits: " ^ value)
  in
    wordsSyntax.mk_word (Arbnum.fromString (IntInf.toString n), Arbnum.fromInt 256)
  end

fun hex_bytes s =
  let
    fun go [] = []
      | go (h :: l :: rest) = (16 * hex_digit h + hex_digit l) :: go rest
      | go [_] = fail ("odd number of hex digits: " ^ s)
  in
    go (explode (hex_digits s))
  end

(* The dialect's own name-to-builtin table, so it cannot drift from
 * builtin_of_name: every constructor of yul_builtin is named by builtin_name
 * and looked back up, and a name that does not come back is a build failure
 * here rather than a wrong import later.
 *)
val builtin_table : (string * term) list =
  let
    val name_of = prim_mk_const {Thy = "yulDialect", Name = "builtin_name"}
    val of_name = prim_mk_const {Thy = "yulDialect", Name = "builtin_of_name"}
    fun lookup name =
      let
        val result =
          rhs (concl (EVAL (mk_comb (of_name, stringSyntax.fromMLstring name))))
      in
        if can dest_comb result andalso
           same_const (fst (dest_comb result)) optionSyntax.some_tm
        then snd (dest_comb result)
        else fail ("the dialect does not know the builtin " ^ name)
      end
  in
    map (fn c =>
           let val name = stringSyntax.fromHOLstring
                            (rhs (concl (EVAL (mk_comb (name_of, c)))))
           in (name, lookup name) end)
        (TypeBase.constructors_of builtin_ty)
  end

fun builtin_of name =
  case List.find (fn (n, _) => n = name) builtin_table of
    SOME (_, b) => SOME b
  | NONE => NONE

(* Nodes *)

fun import_literal v = within v (fn v =>
  case string_field v "kind" of
    "number" => yul "LitNumber" [word_term (string_field v "value")]
  | "string" =>
      (* Both the decoded text (`value`) and the bytes (`hexValue`) are there;
       * the bytes are what the literal holds, and a literal written in hex has
       * no text to read.
       *)
      yul "LitBytes" [bytes_term (hex_bytes (string_field v "hexValue"))]
  | kind => fail (describe v ^ ": unsupported literal kind " ^ kind))

fun import_name v = within v (fn v =>
  (expect v "YulIdentifier"; string_field v "name"))

(* A list of YulTypedName nodes, as a string list. *)
fun import_names vs = JSONUtil.arrayMap (fn v => within v (fn v =>
  (expect v "YulTypedName"; string_field v "name"))) vs

(* The compiler omits a function's parameter and result lists when they are
 * empty, so both are optional fields. *)
fun optional_names v key =
  case optional_field v key of
    NONE => []
  | SOME vs => import_names vs

fun import_call defined v =
  let
    val name = import_name (field v "functionName")
    val args = expr_list (map (import_expr defined) (array_field v "arguments"))
  in
    if List.exists (fn n => n = name) defined then yul "YulApply" [mk_str name, args]
    else case builtin_of name of
           SOME b => yul "YulBuiltin" [b, args]
         | NONE =>
             fail (describe v ^ ": call to " ^ name ^ ", which is neither a \
                   \builtin nor a function the object defines")
  end

and import_expr defined v = within v (fn v =>
  case node_type v of
    "YulFunctionCall" => import_call defined v
  | "YulIdentifier" => yul "YulName" [mk_str (import_name v)]
  | "YulLiteral" => yul "YulLit" [import_literal v]
  | other => fail (describe v ^ ": unsupported expression " ^ other))

(* Statements of a body. A function definition is not one of them: the
 * evaluator collects the object's own top-level definitions, so a nested one
 * would be unreachable, and the compiler never emits one.
 *)
fun import_statements defined v = within v (fn v =>
  (expect v "YulBlock";
   map (import_statement defined) (array_field v "statements")))

and import_statement defined v = within v (fn v =>
  case node_type v of
    "YulBlock" => yul "YulBlock" [stmt_list (import_statements defined v)]
  | "YulExpressionStatement" =>
      yul "YulExprStmt" [import_expr defined (field v "expression")]
  | "YulVariableDeclaration" =>
      let
        val names = import_names (field v "variables")
        val value = case optional_field v "value" of
                      NONE => optionSyntax.mk_none expr_ty
                    | SOME e => optionSyntax.mk_some (import_expr defined e)
      in
        yul "YulLet" [name_list names, value]
      end
  | "YulAssignment" =>
      yul "YulAssign" [name_list (map import_name (array_field v "variableNames")),
                       import_expr defined (field v "value")]
  | "YulIf" =>
      yul "YulIf" [import_expr defined (field v "condition"),
                   stmt_list (import_statements defined (field v "body"))]
  | "YulSwitch" => import_switch defined v
  | "YulForLoop" =>
      yul "YulFor" [stmt_list (import_statements defined (field v "pre")),
                    import_expr defined (field v "condition"),
                    stmt_list (import_statements defined (field v "post")),
                    stmt_list (import_statements defined (field v "body"))]
  | "YulBreak" => yul "YulBreak" []
  | "YulContinue" => yul "YulContinue" []
  | "YulLeave" => yul "YulLeave" []
  | other => fail (describe v ^ ": unsupported statement " ^ other))

and import_switch defined v =
  let
    val cases = array_field v "cases"
    (* The compiler writes its default case as the JSON string "default" where
     * every other case has a literal. *)
    fun is_default c =
      (case JSONUtil.findField c "value" of
         SOME (JSON.STRING s) => s = "default"
       | _ => false)
    fun import_case c = within c (fn c =>
      (expect c "YulCase";
       pairSyntax.mk_pair
         (import_literal (field c "value"),
          stmt_list (import_statements defined (field c "body")))))
    val defaults = List.filter is_default cases
    val () = require v (length defaults <= 1) "more than one default case"
    val cases_ty =
      pairSyntax.mk_prod (literal_ty, listSyntax.mk_list_type stmt_ty)
  in
    yul "YulSwitch"
      [import_expr defined (field v "expression"),
       listSyntax.mk_list
         (map import_case (List.filter (fn c => not (is_default c)) cases), cases_ty),
       case defaults of
         [] => stmt_list []
       | [d] => stmt_list (import_statements defined (field d "body"))
       | _ => fail (describe v ^ ": more than one default case")]
  end

(* A function definition: only the object's own, and its body resolves names
 * the same way the object's does.
 *)
and import_function defined v = within v (fn v =>
  yul "YulFunction"
    [mk_str (string_field v "name"),
     name_list (optional_names v "parameters"),
     name_list (optional_names v "returnVariables"),
     stmt_list (import_statements defined (field v "body"))])

(* The object *)

fun runtime_ast output source contract stage =
  let
    val key = case stage of Ir => "irAst" | IrOptimized => "irOptimizedAst"
  in
    JSONUtil.get (output, [JSONUtil.SEL "contracts", JSONUtil.SEL source,
                           JSONUtil.SEL contract, JSONUtil.SEL key])
      handle e => fail ("no " ^ key ^ " for " ^ contract ^ ": " ^
                        JSONUtil.exnMessage e)
  end

fun is_function v =
  (case JSONUtil.findField v "nodeType" of
     SOME (JSON.STRING s) => s = "YulFunctionDefinition"
   | _ => false)

fun import_runtime output source contract stage =
  within (runtime_ast output source contract stage) (fn ast =>
    (expect ast "YulObject";
     let
       val subs = array_field ast "subObjects"
       val () = require ast (length subs = 1)
                  "expected exactly one subobject, the runtime object"
       val runtime = hd subs
       val () = within runtime (fn runtime => expect runtime "YulObject")
       (* A runtime object's own subobjects are its data sections, which the
        * AST has no node for: the code block the frame runs names them only
        * through the object-level builtins, which the evaluator rejects, so
        * dropping them cannot change what a run computes. Anything else
        * nested in the runtime object is an object form this importer does
        * not read.
        *)
       val () = List.app (fn d => within d (fn d => expect d "YulData"))
                  (array_field runtime "subObjects")
       val code = field runtime "code"
       val () = within code (fn code => expect code "YulCode")
       val block = field code "block"
       val statements = within block (fn block =>
         (expect block "YulBlock"; array_field block "statements"))
       val () = require block (not (null statements))
                  "the runtime object's code block is empty"
       val defined = map (fn v => string_field v "name")
                       (List.filter is_function statements)
     in
       stmt_list (map (fn v => if is_function v then import_function defined v
                               else import_statement defined v) statements)
     end))

fun import_runtime_artifact path source contract stage =
  let
    val artifact = JSONParser.parseFile path
      handle e => fail (path ^ ": " ^ General.exnMessage e)
    val format = string_field artifact "format"
      handle e => fail (path ^ ": " ^ JSONUtil.exnMessage e)
  in
    if format <> "solidity-hol-solc-artifact-v1" then
      fail (path ^ ": unsupported artifact format " ^ format)
    else import_runtime (field artifact "output") source contract stage
  end

end
