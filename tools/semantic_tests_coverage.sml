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

  fun json_list xs = "[" ^ String.concatWith "," (map json_string xs) ^ "]"

  (* A rejected test reports every blocker line; an admitted one how many
   * functions calls reach and why the unsupported ones among them are. *)
  fun emit test status fields =
    (TextIO.output (output, "coverage-result: {\"test\":" ^ json_string test ^
            ",\"status\":" ^ json_string status ^
            String.concat (map (fn (k, v) => ",\"" ^ k ^ "\":" ^ v) fields) ^ "}\n");
     TextIO.flushOut output)

  (* Of several rejected sources, the test is reported as its most severe
   * rejection, with the blockers of all of them. *)
  val severity = let open solidityPrepareLib in
    [MalformedInput, InvalidCore, UnsupportedImport, SourceRejected, UnsupportedLowering] end

  fun status_name solidityPrepareLib.UnsupportedImport = "import-rejected"
    | status_name solidityPrepareLib.UnsupportedLowering = "elaboration-rejected"
    | status_name kind = solidityPrepareLib.failure_name kind

  datatype outcome = Prepared of solidityPrepareLib.prepared
                   | Rejected of solidityPrepareLib.failure * string list

  fun run_test test path =
    let
      val artifact = solidityPrepareLib.read_artifact {root = ".", path = path}
      val sources = case JSONUtil.lookupField
        (JSONUtil.lookupField artifact "output") "sources" of
          JSON.OBJECT sources => map fst sources
        | _ => raise Fail (path ^ ": expected output sources object")
      val outcomes = map (fn source =>
        Prepared (solidityPrepareLib.prepare_source artifact source)
        handle solidityPrepareLib.PreparationError (kind, message) =>
          Rejected (kind, String.fields (fn c => c = #"\n") message)) sources
      val failures = List.mapPartial (fn Rejected f => SOME f | Prepared _ => NONE) outcomes
    in
      case List.find (fn kind => List.exists (fn (k, _) => k = kind) failures) severity of
        SOME kind =>
          let
            (* The reasons of the unsupported functions of the sources that
             * did prepare block the test too. *)
            val reasons = List.concat (map (fn Prepared p =>
                List.concat (map (String.fields (fn c => c = #"\n"))
                  (List.mapPartial #reason (#functions p)))
              | Rejected _ => []) outcomes)
          in
            emit test (status_name kind)
              [("blockers", json_list (List.concat (map #2 failures) @ reasons))]
          end
      | NONE =>
          let
            val functions = List.concat
              (map (fn Prepared p => #functions p | Rejected _ => []) outcomes)
            val reasons = List.mapPartial #reason functions
          in
            emit test (if null reasons then "admitted" else "partially-admitted")
              [("functions", Int.toString (length functions)),
               ("unsupported", json_list reasons)]
          end
    end
    handle solidityPrepareLib.PreparationError (kind, message) =>
      emit test (status_name kind)
        [("blockers", json_list (String.fields (fn c => c = #"\n") message))]

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
