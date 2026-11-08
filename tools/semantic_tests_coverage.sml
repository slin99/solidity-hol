(* Run by tools/semantic_tests_coverage.py under `holbuild run-action`, or
 * `holbuild run` without a fleet. The manifest has one "name<TAB>path" line
 * per compiler artifact. Results go to the declared output on the fleet,
 * or stdout locally.
 *)
load "wordsLib";
load "solidityPrepareLib";
(* cv_eval proves lemmas as it goes (to unfold record updates), and HOL
 * refuses to prove anything without a current theory. *)
val () = Theory.new_theory "semanticTestsCoverage";

local
  open HolKernel boolLib

  val output_dir = OS.Process.getEnv "HOLBUILD_RUN_OUTPUT_DIR"
  val output =
    case output_dir of
      SOME dir => TextIO.openOut (OS.Path.concat (dir, "results.jsonl"))
    | NONE => TextIO.stdOut

  fun json_string s =
    let
      fun escape #"\"" = "\\\""
        | escape #"\\" = "\\\\"
        | escape c =
            if Char.isPrint c then String.str c
            else "\\u" ^ StringCvt.padLeft #"0" 4 (Int.fmt StringCvt.HEX (ord c))
    in
      "\"" ^ String.translate escape s ^ "\""
    end

  (* An admitted unit reports how many functions calls reach and why the
   * unsupported ones among them are. *)
  fun emit test status message functions =
    (TextIO.output (output, "coverage-result: {\"test\":" ^ json_string test ^
            ",\"status\":" ^ json_string status ^
            (case message of
               NONE => ""
             | SOME m => ",\"message\":" ^ json_string m) ^
            (case functions of
               NONE => ""
             | SOME (n, reasons) =>
                 ",\"functions\":" ^ Int.toString n ^
                 ",\"unsupported\":[" ^
                 String.concatWith "," (map json_string reasons) ^ "]") ^ "}\n");
     TextIO.flushOut output)

  fun run_test test path =
    let
      val artifact = solidityPrepareLib.read_artifact {root = ".", path = path}
      val sources = case JSONUtil.lookupField
        (JSONUtil.lookupField artifact "output") "sources" of
          JSON.OBJECT sources => map fst sources
        | _ => raise Fail (path ^ ": expected output sources object")
      (* Report import blockers before lowering any source of a multi-source test. *)
      val units = map (fn source =>
        (source, solidityPrepareLib.import_unit artifact source)) sources
      val prepared = map (fn (source, unit) => solidityPrepareLib.prepare_unit unit
        handle solidityPrepareLib.PreparationError (kind, message) =>
          raise solidityPrepareLib.PreparationError (kind, source ^ ": " ^ message)) units
      val functions = List.concat (map #functions prepared)
      val reasons = List.mapPartial #reason functions
    in
      emit test (if null reasons then "admitted" else "partially-admitted") NONE
        (SOME (length functions, reasons))
    end
    handle solidityPrepareLib.PreparationError (kind, message) =>
      let val status = case kind of
        solidityPrepareLib.UnsupportedImport => "import-rejected"
      | solidityPrepareLib.UnsupportedLowering => "elaboration-rejected"
      | _ => solidityPrepareLib.failure_name kind
      in emit test status (SOME message) NONE end

  val manifest =
    case OS.Process.getEnv "SEMANTIC_TESTS_MANIFEST" of
      SOME m => m
    | NONE => "manifest.txt"

  fun lines stream =
    case TextIO.inputLine stream of
      NONE => []
    | SOME l => String.substring (l, 0, size l - 1) :: lines stream
in
  val () =
    List.app
      (fn line =>
         case String.fields (fn c => c = #"\t") line of
           [test, path] => run_test test path
         | _ => raise Fail ("malformed manifest line " ^ line))
      (lines (TextIO.openIn manifest))
  val () = case output_dir of NONE => () | SOME _ => TextIO.closeOut output
end;
