(* The importer's read of the pinned compiler's own Yul, and what it refuses.
 * See syntax/yulImportLib.sml.
 *
 * The fixture is a real artifact of the pinned compiler, of the corpus's
 * smallest suite, so the admitted shape is one solc really emits rather than
 * one written to suit the importer. Its two stages cover both keys the
 * importer reads (irAst and irOptimizedAst).
 *
 * The refusal cases below are built here as JSON values, each differing from
 * an admitted minimal object in exactly one place; the build fails if the
 * importer admits one of them, or refuses it for the wrong reason.
 *)
Theory yulImportTest
Ancestors
  yulAST yulDialect yulState yulEvaluator cv_string_fmap vfmCompute
Libs
  yulImportLib cv_transLib wordsLib

(* Read by holbuild's dependency scanner, which stages the fixture. *)
fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps [
  "../testdata/yul/expected/shadowed_builtins.json",
  "../testdata/yul/expected/shadowed_builtins-optimized.json",
  "../testdata/differential/shadowed_builtins.sol"
]

val fixture = "../testdata/yul/expected/shadowed_builtins.json"
val optimized_fixture = "../testdata/yul/expected/shadowed_builtins-optimized.json"
val source = "testdata/differential/shadowed_builtins.sol"
val contract = "ShadowedBuiltins"

Definition shadowed_builtins_ir_def:
  shadowed_builtins_ir =
    ^(yulImportLib.import_runtime_artifact fixture source contract
        yulImportLib.Ir)
End

Definition shadowed_builtins_ir_optimized_def:
  shadowed_builtins_ir_optimized =
    ^(yulImportLib.import_runtime_artifact fixture source contract
        yulImportLib.IrOptimized)
End

(* The optimizer's own output, which is the third stage the harness runs. *)
Definition shadowed_builtins_optimized_def:
  shadowed_builtins_optimized =
    ^(yulImportLib.import_runtime_artifact optimized_fixture source contract
        yulImportLib.IrOptimized)
End

(* The imported tree is a concrete term, and cv can translate it: what the
 * harness runs is the object, not a re-reading of the file.
 *)
val () = cv_auto_trans shadowed_builtins_ir_def;

(* What the importer refuses *)

fun obj fields = JSON.OBJECT fields
fun str s = JSON.STRING s
fun arr vs = JSON.ARRAY vs

fun identifier name = obj [("nodeType", str "YulIdentifier"), ("name", str name)]
fun number value =
  obj [("nodeType", str "YulLiteral"), ("kind", str "number"),
       ("value", str value), ("type", str "")]
fun call name args =
  obj [("nodeType", str "YulFunctionCall"), ("functionName", identifier name),
       ("arguments", arr args)]
fun expression_statement e = obj [("nodeType", str "YulExpressionStatement"),
                                  ("expression", e)]

fun object_node statements subobjects =
  obj [("nodeType", str "YulObject"),
       ("code", obj [("nodeType", str "YulCode"),
                     ("block", obj [("nodeType", str "YulBlock"),
                                    ("statements", arr statements)])]),
       ("subObjects", arr subobjects)]

(* An admitted runtime object: one statement, pop(0), and one data section.
 * The creation object's own code is not read, as yulImportLib says.
 *)
val data_section = obj [("nodeType", str "YulData"), ("name", str "d")]
val creation_code = [expression_statement (call "pop" [number "0"])]

fun output_with subobjects code =
  obj [("contracts",
        obj [("s.sol",
              obj [("C",
                    obj [("irAst",
                          obj [("nodeType", str "YulObject"),
                               ("code", obj [("nodeType", str "YulCode"),
                                             ("block", obj [("nodeType", str "YulBlock"),
                                                            ("statements", arr code)])]),
                               ("subObjects", arr subobjects)])])])])]

fun runtime_object statements = object_node statements [data_section]

fun minimal_output () = output_with [runtime_object creation_code] creation_code

fun import v = yulImportLib.import_runtime v "s.sol" "C" yulImportLib.Ir

fun expect_unknown what v =
  (ignore (import v);
   raise ERR "yulImportTest"
     (what ^ ": the importer admitted an object it must refuse"))
  handle yulImportLib.ImportError _ => ()
       | yulImportLib.MalformedInput msg =>
           raise ERR "yulImportTest"
             (what ^ ": refused, but as malformed rather than as unknown: " ^ msg)

fun expect_malformed what v =
  (ignore (import v);
   raise ERR "yulImportTest"
     (what ^ ": the importer admitted an object it must refuse"))
  handle yulImportLib.MalformedInput _ => ()
       | yulImportLib.ImportError msg =>
           raise ERR "yulImportTest"
             (what ^ ": refused, but as unknown rather than as malformed: " ^ msg)

(* The base is admitted, so a refusal below is the change, not a typo here. *)
val () = ignore (import (minimal_output ()));

(* A string literal, as the compiler emits one: the bytes in `hexValue`, which
 * is hex without the 0x the numbers carry, and the decoded text in `value`,
 * which is null when the literal is written in hex and has no text at all. What
 * the importer must read is the bytes, so this fixture is a hex literal whose
 * text is not there and whose bytes are not text.
 *)
val () =
  let
    val literal = obj [("nodeType", str "YulLiteral"), ("kind", str "string"),
                       ("value", JSON.NULL), ("hexValue", str "00ff"),
                       ("type", str "")]
    val imported =
      import (output_with
                [runtime_object [expression_statement
                                   (call "mstore" [number "0", literal])]]
                creation_code)
    val expected = listSyntax.mk_list
      (map (fn i => wordsSyntax.mk_wordii (i, 8)) [0x00, 0xff],
       wordsSyntax.mk_int_word_type 8)
  in
    if List.exists (fn t => aconv t expected) (find_terms (fn _ => true) imported)
    then ()
    else raise ERR "yulImportTest"
           "a string literal did not import as its bytes"
  end

val () = expect_unknown "unknown node kind"
  (output_with [runtime_object [obj [("nodeType", str "YulNonsense")]]]
     creation_code)

val () = expect_unknown "unknown builtin"
  (output_with
     [runtime_object [expression_statement (call "not_a_builtin" [])]] creation_code)

val () = expect_unknown "call to an undefined function"
  (output_with
     [runtime_object [expression_statement (call "helper" [])]] creation_code)

(* A runtime object's subobjects are its data sections and nothing else. *)
val () = expect_unknown "object nested in the runtime object"
  (output_with
     [object_node creation_code [data_section, object_node creation_code []]]
     creation_code)

val () = expect_unknown "two subobjects at the top level"
  (output_with [runtime_object creation_code, runtime_object creation_code]
     creation_code)

val () = expect_unknown "no runtime subobject" (output_with [] creation_code)

val () = expect_unknown "empty runtime code"
  (output_with [runtime_object []] creation_code)

val () = expect_malformed "expression statement without an expression"
  (output_with
     [runtime_object [obj [("nodeType", str "YulExpressionStatement")]]]
     creation_code)

val () = expect_unknown "unsupported literal kind"
  (output_with
     [runtime_object
        [expression_statement
           (call "pop" [obj [("nodeType", str "YulLiteral"),
                             ("kind", str "address"), ("value", str "0")]])]]
     creation_code)
