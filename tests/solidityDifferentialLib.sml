structure solidityDifferentialLib :> solidityDifferentialLib =
struct

open HolKernel boolLib bossLib solidityDifferentialTheory solidityBytecodeTheory
     solidityBytecodeLib cv_transLib intLib wordsLib

val ERR = mk_HOL_ERR "solidityDifferentialLib"

val result_output = ref (NONE : TextIO.outstream option)

fun with_results path run =
  let
    val stream = TextIO.openOut path
    val previous = !result_output
    fun close () = (result_output := previous; TextIO.closeOut stream)
  in
    result_output := SOME stream;
    (run () handle e => (close (); raise e));
    close ()
  end

fun emit_result prefix fields =
  let val line = prefix ^ json_object fields ^ "\n" in
    print line;
    case !result_output of
      NONE => ()
    | SOME stream => (TextIO.output (stream, line); TextIO.flushOut stream)
  end

fun emit fields = emit_result "differential-result: " fields

fun prepared_constants prefix (prepared : solidityPrepareLib.prepared) =
  let
    val unit_def = define (prefix ^ "_unit") (#unit prepared)
    val () = cv_auto_trans unit_def
    val program_def = define (prefix ^ "_program") (#program prepared)
    val () = cv_auto_trans program_def
    fun named name th = save_thm (prefix ^ name,
      REWRITE_RULE [SYM unit_def, SYM program_def] th)
    val _ = named "_source_valid" (#source_valid prepared)
    val _ = named "_elaborates" (#elaborates prepared)
    val _ = named "_program_wf" (#core_wf prepared)
  in
    (lhs (concl unit_def), lhs (concl program_def))
  end

(* The contract's immutables, by name, and, from the artifact, the offsets in
 * its deployed code of each immutable the code reads. An artifact exported
 * without the offsets serves only a contract without immutables. *)

fun unit_immutables unit artifact source contract =
  let
    val names =
      case fst (listSyntax.dest_list (record_field "unit_contracts" unit)) of
        c :: _ =>
          map (fn v =>
                 (stringSyntax.fromHOLstring (record_field "var_name" v),
                  IntInf.fromInt (numSyntax.int_of_term
                    (record_field "node_id" (record_field "var_info" v)))))
            (fst (listSyntax.dest_list (record_field "contract_immutables" c)))
      | [] => []
    val path = map JSONUtil.SEL ["output", "contracts", source, contract, "evm",
                                 "deployedBytecode", "immutableReferences"]
    val kvs =
      case (SOME (JSONUtil.get (artifact, path)) handle _ => NONE) of
        SOME (JSON.OBJECT kvs) => kvs
      | SOME _ => fail "immutableReferences is not an object"
      | NONE =>
          if null names then []
          else fail "the artifact lists no immutableReferences"
    fun entry (k, JSON.ARRAY rs) =
          pairSyntax.mk_pair (num_term (decimal k),
            listSyntax.mk_list
              (map (fn r => num_term (integer (field r "start"))) rs,
               numSyntax.num))
      | entry _ = fail "an immutable's references are a list"
  in
    {names = names,
     refs = listSyntax.mk_list (map entry kvs, “:num # num list”)}
  end

(* The fuel the core run of a case is given: the case's own, or the corpus's
 * for one that declares none. The Yul run has its own (yul_fuel below) and
 * does not read this.
 *)
fun case_fuel c fuel =
  case JSONUtil.findField c "fuel" of SOME v => integer v | NONE => fuel

fun run_case {suite, code, initcode, peer, immutables, unit, program, fuel, bytecode} c =
  let
    val case_name = name_field c "name"
    val theorem = suite ^ "_" ^ case_name
    val fuel = case_fuel c fuel
    val input = call_input initcode c

    val expect = expectation (field c "expect")
    val case_tm = case_term peer immutables input c
    val verdict_tm =
      list_mk_comb (prim_mk_const {Thy = "solidityDifferential",
                                   Name = "differential_verdict"},
                    [code, unit, program, num_term fuel, case_tm])
    val verdict =
      case bytecode of
        NONE => cv_eval verdict_tm
      | SOME theory =>
          let
            val cached = DB.fetch theory ("bytecode_" ^ theorem)
            val cached_input = rand (lhs (concl cached))
            val prepared = “prepared_evm_input ^code ^unit ^case_tm”
            val bridge_result = cv_eval “^prepared = INR ^cached_input”
          in
            if not (rhs (concl bridge_result) ~~ T) andalso
               sumSyntax.is_inl (rhs (concl (cv_eval prepared))) then
              cv_eval verdict_tm
            else let
            val () = if rhs (concl bridge_result) ~~ T then () else
              let
                val checks =
                  [("accounts", “case ^prepared of INL d => F | INR (a,t,r) => a = FST ^cached_input”),
                   ("transaction", “case ^prepared of INL d => F | INR (a,t,r) => t = FST (SND ^cached_input)”),
                   ("immutable references", “case ^prepared of INL d => F | INR (a,t,r) => r = SND (SND ^cached_input)”)]
                val different = List.filter
                  (fn (_, tm) => not (rhs (concl (cv_eval tm)) ~~ T)) checks
              in
                fail ("prepared EVM input differs from cached bytecode input: " ^
                      String.concatWith ", " (map #1 different))
              end
            val bridge = EQT_ELIM bridge_result
            val evm = (REWRITE_CONV [evm_execution_def, bridge, sumTheory.sum_case_def]
                       THENC DEPTH_CONV BETA_CONV THENC REWRITE_CONV [cached])
              “evm_execution ^code ^unit ^case_tm”
            val () = if rhs (concl evm) ~~ rhs (concl cached) then () else
              fail "cached bytecode result was not substituted completely"
          in
            (PURE_REWRITE_CONV [differential_verdict_def, evm] THENC cv_eval) verdict_tm
            end
          end
    val result = rhs (concl verdict)
    val base = [("kind", json_string "case"), ("suite", json_string suite),
                ("case", json_string case_name)]
  in
    if is_con "Agree" result then
      let
        val agrees_tm = list_mk_comb (prim_mk_const {Thy = "solidityDifferential",
                                                     Name = "differential_agrees"},
                                      snd (strip_comb verdict_tm))
        val th = EQT_ELIM ((PURE_REWRITE_CONV [differential_agrees_def, verdict]
                            THENC REWRITE_CONV [is_agreement_def]) agrees_tm)
        val _ = save_thm (theorem, th)
      in
        emit (base @ [("status", json_string "agree"),
                      ("theorem", json_string theorem),
                      ("outcome", outcome_json (rand result))]);
        true
      end
    else if is_con "LogMismatch" result orelse is_con "LogUnexpected" result then
      let
        val mismatch = is_con "LogMismatch" result
        val (bytecode, other) =
          case snd (strip_comb result) of
            [b, x] => (b, x)
          | _ => raise ERR "run_case" "unexpected verdict"
      in
        emit (base @ [("status", json_string (if mismatch then "log-mismatch"
                                              else "log-unexpected")),
                      ("bytecode_logs", logs_json bytecode),
                      (if mismatch then "source_logs" else "expected_logs",
                       logs_json other)]);
        false
      end
    else if is_con "StorageMismatch" result orelse is_con "StorageUnexpected" result
    then
      let
        (* a mismatch carries the source's storage, an unexpected result the
         * expected one; in the latter both runs ended with the first *)
        val mismatch = is_con "StorageMismatch" result
        val (bytecode, other) =
          case snd (strip_comb result) of
            [b, x] => (b, x)
          | _ => raise ERR "run_case" "unexpected verdict"
      in
        emit (base @ [("message", json_string
                        "Complete storage is compared; displayed values cover the listed slots."),
                      ("status", json_string (if mismatch then "storage-mismatch"
                                              else "storage-unexpected")),
                      ("bytecode_storage", storage_json bytecode),
                      (if mismatch then "source_storage" else "expected_storage",
                       storage_json other)]);
        false
      end
    else
      let
        val expected = rhs (concl (cv_eval
                         (list_mk_comb (prim_mk_const {Thy = "solidityDifferential",
                                                       Name = "expected_outcome"},
                                        [unit, input, expect]))))
        val (kind, args) = strip_comb result
        val (bytecode, source) =
          case (fst (dest_const kind), args) of
            ("Unexpected", [agreed, _]) => (agreed, agreed)
          | (_, [b, s]) => (b, s)
          | _ => raise ERR "run_case" "unexpected verdict"
      in
        emit (base @ [("status", json_string (String.map Char.toLower
                                                (fst (dest_const kind)))),
                      ("bytecode", outcome_json bytecode),
                      ("source", outcome_json source),
                      ("expected", outcome_json expected)]);
        false
      end
  end
  handle e =>
    (emit [("kind", json_string "case"), ("suite", json_string suite),
           ("case", json_string (string_field c "name" handle _ => "?")),
           ("status", json_string "error"),
           ("message", json_string (General.exnMessage e))];
     false)

(* Suites *)

fun suite_failure suite status message =
  (emit [("kind", json_string "suite"), ("suite", json_string suite),
         ("status", json_string status), ("message", json_string message)];
   false)

(* The importer keeps the one contract no other inherits; the bytecode
 * compared must be that contract's, on both sides of the comparison.
 *)

fun check_unit_contracts prepared contract =
  let
    val names =
      map (stringSyntax.fromHOLstring o record_field "contract_name")
        (fst (listSyntax.dest_list
                (record_field "unit_contracts" (#unit prepared))))
  in
    if names = [contract] then ()
    else fail ("the unit's contracts are [" ^ String.concatWith ", " names ^
               "], not " ^ contract)
  end

fun run_suite_with_bytecode bytecode root fuel s =
  let
    val suite = name_field s "name"
    val prefix = "corpus_" ^ suite
    val artifact = root ^ "/" ^ string_field s "artifact"
    val source = string_field s "source"
    val contract = string_field s "contract"
    val cases = array_field s "cases"
  in
    let
      val checked = solidityPrepareLib.prepare_artifact
        {root = root, path = artifact, source = source}
      val () = check_unit_contracts (#prepared checked) contract
      val (unit, program) = prepared_constants prefix (#prepared checked)
      val code = code_constant (prefix ^ "_code") "deployedBytecode"
                   (#artifact checked) source contract
      (* Defined once, by the suite's first creation case. *)
      val initcode_constant = ref NONE
      fun initcode () =
        case !initcode_constant of
          SOME tm => tm
        | NONE =>
            let val tm = code_constant (prefix ^ "_initcode") "bytecode"
                           (#artifact checked) source contract
            in initcode_constant := SOME tm; tm end
      val peer = peer_code root prefix s
      val () = emit [("kind", json_string "suite"),
                     ("suite", json_string suite),
                     ("status", json_string "ok"),
                     ("theorems", json_array (map json_string
                       [prefix ^ "_elaborates", prefix ^ "_program_wf"]))]
      val immutables = unit_immutables (#unit (#prepared checked))
                         (#artifact checked) source contract
      val env = {suite = suite, code = code, initcode = initcode, peer = peer,
                 immutables = immutables, unit = unit, program = program,
                 fuel = fuel, bytecode = bytecode}
    in
      List.foldl (fn (c, ok) => run_case env c andalso ok) true cases
    end
  end
  handle solidityPrepareLib.PreparationError (kind, message) =>
           suite_failure (string_field s "name" handle _ => "?")
             (solidityPrepareLib.failure_name kind) message
       | CorpusError msg => suite_failure (string_field s "name" handle _ => "?")
                              "error" msg
       | e as HOL_ERR _ => suite_failure (string_field s "name" handle _ => "?")
                             "error" (General.exnMessage e)

fun run_suite root fuel s = run_suite_with_bytecode NONE root fuel s

(* The source side reuses its suite's independently checked bytecode results. *)
fun run_suite_file {root, suite_file, fuel, bytecode_theory} =
  if run_suite_with_bytecode (SOME bytecode_theory) root fuel
       (JSONParser.parseFile (root ^ "/" ^ suite_file)) then ()
  else raise ERR "run_suite_file" "differential suite failed"

(* Suite paths are relative to the corpus config; artifact/source paths remain
 * relative to the repository root. Inline suites support standalone corpora. *)
fun corpus_suites path v =
  case JSONUtil.findField v "suite_directory" of
      NONE => array_field v "suites"
    | SOME value =>
        let
          val () = if JSONUtil.hasField "suites" v then
                     fail "suite_directory excludes suites" else ()
          val dir = OS.Path.concat (OS.Path.dir path, JSONUtil.asString value)
          val names = Listsort.sort String.compare
                        (List.filter (String.isSuffix ".json") (Portable.listDir dir))
          val () = if null names then fail (dir ^ ": no suite JSON files") else ()
        in map (fn name => JSONParser.parseFile (OS.Path.concat (dir, name))) names end

fun run_corpus {root, corpus} =
  let
    val path = root ^ "/" ^ corpus
    val v = JSONParser.parseFile path
    val () = if string_field v "format" = "solidity-hol-differential-corpus-v1"
             then () else raise ERR "run_corpus" (path ^ ": unsupported format")
    val fuel = integer (field v "fuel")
    val ok = List.foldl (fn (s, ok) => run_suite root fuel s andalso ok) true
               (corpus_suites path v)
  in
    if ok then ()
    else raise ERR "run_corpus" "differential corpus failed; see the \
                                \differential-result lines"
  end
  handle CorpusError msg => raise ERR "run_corpus" msg

(* The three-way run: the compiler's own Yul, at the three stages the design
 * separates, held to the same expectation the corpus theory holds the
 * elaborated core and the deployed bytecode to (yulDifferentialTheory says
 * what the comparison is). This reads the corpus, imports each suite's Yul,
 * runs every case at every stage, and reports each result as a line
 * "yul-differential-result: " followed by JSON.
 *)

fun emit_yul fields =
  emit_result "yul-differential-result: " fields

(* A stage as the name its theorem carries, the name the report uses, the
 * artifact it is imported from, and which of the two ASTs in that artifact to
 * read. The optimizer-off artifact holds both stages the compiler defines:
 * irAst, the code generator's own output, and irOptimizedAst, what its
 * transformations leave. The optimizer-on artifact is the production build's
 * irOptimizedAst.
 *)
fun yul_stages yul_root suite =
  [("ir", "ir", yul_root ^ "/" ^ suite ^ ".ir.json", yulImportLib.Ir),
   ("ir_optimized", "ir-optimized", yul_root ^ "/" ^ suite ^ ".ir.json",
    yulImportLib.IrOptimized),
   ("optimized", "optimized", yul_root ^ "/" ^ suite ^ ".optimized.json",
    yulImportLib.IrOptimized)]

(* One fuel for every case, and a generous one: a frame that runs out is a
 * diagnostic rather than an agreement, and fuel costs nothing unless it runs
 * out.
 *)
val yul_fuel = 1000000;

fun yul_code_constant name path source contract stage =
  let
    val def = define name
                (yulImportLib.import_runtime_artifact path source contract stage)
    val () = cv_auto_trans def
  in
    lhs (concl def)
  end

(* Importing is where a stage is admitted, so admission is reported on its own
 * line: an unknown node kind, builtin or object form leaves the stage not
 * admitted, and its cases are not run at that stage. The report counts these
 * separately from agreements.
 *)
fun yul_stage_code prefix suite source contract (tag, json_tag, path, stage) =
  SOME (tag, json_tag,
        yul_code_constant (prefix ^ "_" ^ tag ^ "_code") path source contract
          stage)
  handle yulImportLib.ImportError msg =>
           (emit_yul [("kind", json_string "stage"), ("suite", json_string suite),
                      ("stage", json_string json_tag),
                      ("status", json_string "import-rejected"),
                      ("message", json_string msg)];
            NONE)
       | yulImportLib.MalformedInput msg =>
           (emit_yul [("kind", json_string "stage"), ("suite", json_string suite),
                      ("stage", json_string json_tag),
                      ("status", json_string "import-malformed"),
                      ("message", json_string msg)];
            NONE)
       | e =>
           (emit_yul [("kind", json_string "stage"), ("suite", json_string suite),
                      ("stage", json_string json_tag),
                      ("status", json_string "error"),
                      ("message", json_string (General.exnMessage e))];
            NONE)

(* The Yul run has its own fuel (yul_fuel below): the corpus's fuel is the
 * core evaluator's, which this verdict does not call.
 *)
fun yul_verdict_term {code, unit, program, case_tm, ycode} =
  list_mk_comb
    (prim_mk_const {Thy = "yulDifferential", Name = "yul_case_verdict"},
     [code, unit, program, case_tm,
      num_term (IntInf.fromInt yul_fuel), ycode])

fun yul_expected_outcome unit input expect =
  rhs (concl (cv_eval
    (list_mk_comb (prim_mk_const {Thy = "solidityDifferential",
                                  Name = "expected_outcome"},
                   [unit, input, expect]))))

(* One case at one stage: a single cv_eval of the verdict, which runs the
 * bytecode and the Yul. An agreement saves the case's yul_agrees theorem.
 *)
fun run_yul_stage env (stage_tag, json_tag, ycode) =
  let
    val suite = #suite env
    val case_name = #case_name env
    val theorem = "yul_" ^ suite ^ "_" ^ case_name ^ "_" ^ stage_tag
    val base = [("kind", json_string "case"), ("suite", json_string suite),
                ("case", json_string case_name),
                ("stage", json_string json_tag)]
    fun emit_status status extra =
      emit_yul (base @ [("status", json_string status)] @ extra)
    val tm = yul_verdict_term
      {code = #code env, unit = #unit env, program = #program env,
       case_tm = #case_tm env, ycode = ycode}
    val th = cv_eval tm
    val verdict = rhs (concl th)
    fun both_sides () =
      (* On Unexpected the second operand is the expectation, not the Yul run
       * (see run_case's own case for it), and printing it as the Yul run would
       * name the wrong thing.
       *)
      case (fst (dest_const (fst (strip_comb verdict))), snd (strip_comb verdict)) of
        ("Unexpected", [agreed, _]) =>
          [("bytecode", outcome_json agreed), ("yul", outcome_json agreed)]
      | (_, [a, b]) => [("bytecode", outcome_json a), ("yul", outcome_json b)]
      | _ => []
  in
    if is_con "Agree" verdict then
      let
        val agrees_tm =
          list_mk_comb
            (prim_mk_const {Thy = "yulDifferential", Name = "yul_agrees"},
             snd (strip_comb tm))
        val proved = EQT_ELIM
          ((PURE_REWRITE_CONV [yulDifferentialTheory.yul_agrees_def, th]
              THENC REWRITE_CONV [is_agreement_def])
             agrees_tm)
        val _ = save_thm (theorem, proved)
      in
        emit_status "agree"
          [("theorem", json_string theorem),
           ("outcome", outcome_json (rand verdict))];
        true
      end
    else if is_con "StorageMismatch" verdict orelse
            is_con "StorageUnexpected" verdict then
      let
        val mismatch = is_con "StorageMismatch" verdict
        val (bytecode_st, other_st) =
          case snd (strip_comb verdict) of
            [b, x] => (b, x)
          | _ => raise ERR "run_yul_stage" "unexpected verdict"
      in
        emit_status
          (if mismatch then "storage-mismatch" else "storage-unexpected")
          [("message", json_string
             "Complete storage is compared; displayed values cover the listed slots."),
           ("bytecode_storage", storage_json bytecode_st),
           (if mismatch then "yul_storage" else "expected_storage",
            storage_json other_st)];
        false
      end
    else if is_con "LogMismatch" verdict orelse is_con "LogUnexpected" verdict then
      let
        val mismatch = is_con "LogMismatch" verdict
        val (bytecode_logs, other_logs) =
          case snd (strip_comb verdict) of
            [b, x] => (b, x)
          | _ => raise ERR "run_yul_stage" "unexpected verdict"
      in
        emit_status
          (if mismatch then "log-mismatch" else "log-unexpected")
          [("bytecode_logs", logs_json bytecode_logs),
           (if mismatch then "yul_logs" else "expected_logs",
            logs_json other_logs)];
        false
      end
    else
      (emit_status
         (String.map Char.toLower (fst (dest_const (fst (strip_comb verdict)))))
         ([("expected",
            outcome_json (yul_expected_outcome (#unit env) (#input env)
                            (#expect env)))]
          @ both_sides ());
       false)
  end
  handle e =>
    (emit_yul [("kind", json_string "case"), ("suite", json_string (#suite env)),
               ("case", json_string (#case_name env)),
               ("stage", json_string json_tag),
               ("status", json_string "error"),
               ("message", json_string (General.exnMessage e))];
     false)

fun run_case_three_way suite_name env c =
  let
    val input = call_input (fn () => fail "Yul deployment is unsupported") c
    val case_env =
      {suite = suite_name, case_name = name_field c "name",
       case_tm = case_term (#peer env) (#immutables env) input c, input = input,
       expect = expectation (field c "expect"),
       unit = #unit env, code = #code env, program = #program env}
  in
    List.foldl (fn (stage, ok) => run_yul_stage case_env stage andalso ok)
      true (#stages env)
  end
  handle e =>
    (emit_yul [("kind", json_string "case"), ("suite", json_string suite_name),
               ("case", json_string (string_field c "name" handle _ => "?")),
               ("status", json_string "error"),
               ("message", json_string (General.exnMessage e))];
     false)

fun run_suite_three_way root yul_root s =
  let
    val suite = name_field s "name"
    val prefix = "corpus_" ^ suite
    val artifact = root ^ "/" ^ string_field s "artifact"
    val source = string_field s "source"
    val contract = string_field s "contract"
    val cases = array_field s "cases"
    val checked = solidityPrepareLib.prepare_artifact
      {root = root, path = artifact, source = source}
    val () = check_unit_contracts (#prepared checked) contract
    val (unit, program) = prepared_constants prefix (#prepared checked)
    val code = code_constant (prefix ^ "_code") "deployedBytecode"
                 (#artifact checked) source contract
    val peer = peer_code root prefix s
    val stages = List.mapPartial (yul_stage_code prefix suite source contract)
                   (yul_stages yul_root suite)
    val immutables = unit_immutables (#unit (#prepared checked))
                       (#artifact checked) source contract
    val env = {unit = unit, code = code, peer = peer, immutables = immutables,
               program = program, stages = stages}
  in
    emit_yul [("kind", json_string "suite"), ("suite", json_string suite),
              ("status", json_string "ok"),
              ("stages",
               json_array (map (fn (_, json_tag, _) => json_string json_tag)
                             stages))];
    List.foldl (fn (c, ok) => run_case_three_way suite env c andalso ok)
      true cases
  end
  handle solidityPrepareLib.PreparationError (kind, message) =>
           (emit_yul [("kind", json_string "suite"),
                      ("suite", json_string (string_field s "name" handle _ => "?")),
                      ("status", json_string
                         (solidityPrepareLib.failure_name kind)),
                      ("message", json_string message)];
            false)
       | CorpusError msg =>
           (emit_yul [("kind", json_string "suite"),
                      ("suite", json_string (string_field s "name" handle _ => "?")),
                      ("status", json_string "error"),
                      ("message", json_string msg)];
            false)
       | e as HOL_ERR _ =>
           (emit_yul [("kind", json_string "suite"),
                      ("suite", json_string (string_field s "name" handle _ => "?")),
                      ("status", json_string "error"),
                      ("message", json_string (General.exnMessage e))];
            false)

fun run_yul_suite_file {root, suite_file, yul_root} =
  if run_suite_three_way root yul_root
       (JSONParser.parseFile (root ^ "/" ^ suite_file)) then ()
  else raise ERR "run_yul_suite_file" "Yul differential suite failed"

fun run_three_way {root, corpus, yul_root} =
  let
    val path = root ^ "/" ^ corpus
    val v = JSONParser.parseFile path
    val () = if string_field v "format" = "solidity-hol-differential-corpus-v1"
             then () else raise ERR "run_three_way" (path ^ ": unsupported format")
    val ok = List.foldl (fn (s, ok) =>
                           run_suite_three_way root yul_root s andalso ok)
               true (corpus_suites path v)
  in
    if ok then ()
    else raise ERR "run_three_way" "the Yul corpus failed; see the \
                                   \yul-differential-result lines"
  end
  handle CorpusError msg => raise ERR "run_three_way" msg


(* The sweep uses the same preparation, bytecode reader, frames and cv evaluator
 * as the maintained corpus. Only transaction sequencing differs. *)
fun run_expectations {root, manifest} =
  let
    fun discharge th =
      if is_imp (concl th) then
        let val premise = fst (dest_imp (concl th))
            val proved = EQT_ELIM (discharge (cv_eval premise))
        in discharge (MP th proved) end
      else th
    fun eval tm = rhs (concl (discharge (cv_eval tm)))
    fun event_logs_json tm =
      logs_json (listSyntax.mk_list
        (map (fn e => TypeBase.mk_record (“:event”,
          [("logger", eval “^e.logger”), ("topics", eval “^e.topics”),
           ("data", eval “^e.data”)]))
          (fst (listSyntax.dest_list tm)), “:event”))
    val serial = ref 0
    fun keep tm =
      let val () = serial := !serial + 1 in
        rhs (concl (discharge (cv_eval_pat
          (cvName ("expectation_state_" ^ Int.toString (!serial))) tm)))
      end
    fun output fields =
      (print ("expectation-result: " ^ json_object fields ^ "\n");
       TextIO.flushOut TextIO.stdOut)
    fun run_test (index, test) =
      let
        val name = string_field test "test"
        val base = [("test", json_string name)]
        val artifact = string_field test "artifact"
        val source = string_field test "source"
        val contract = string_field test "contract"
        val prefix = "expectation_" ^ Int.toString index
        val checked = solidityPrepareLib.prepare_artifact
          {root = root, path = artifact, source = source}
        val () = check_unit_contracts (#prepared checked) contract
        val (unit, program) = prepared_constants prefix (#prepared checked)
        val code = code_constant (prefix ^ "_code") "deployedBytecode"
                     (#artifact checked) source contract
        val refs = #refs (unit_immutables (#unit (#prepared checked))
                           (#artifact checked) source contract)
        val initial_sender = “0x1212121212121212121212121212120000000012w : address”
        val address = eval “address_for_create ^initial_sender 1”
        val precompile_accounts = List.foldl (fn (i, accounts) =>
          let val addr = word_term 160 (IntInf.fromInt i) in
            “update_account ^addr (empty_account_state with balance := 1) ^accounts”
          end) “empty_accounts” (List.tabulate (8, fn i => i + 1))
        val accounts = List.foldl (fn (i, accounts) =>
          let val n = num_term (IntInf.fromInt i) in
            “update_account (n2w (w2n ^initial_sender + ^n * 4096))
              (empty_account_state with balance := 2 ** 100) ^accounts”
          end) precompile_accounts (List.tabulate (10, fn i => i))
        val world = ref (keep “differential_world ^accounts”)
        val evm_accounts = ref (keep “update_account ^initial_sender
          ((lookup_account ^initial_sender ^accounts) with nonce := 1) ^accounts”)
        val verify = case JSONUtil.findField test "verify_bytecode" of
          SOME (JSON.BOOL v) => v | _ => false
        val initcode = if verify then
          code_constant (prefix ^ "_initcode") "bytecode"
            (#artifact checked) source contract else bytes_term []
        val block = ref 0
        val imm = ref “FEMPTY : num |-> scalar”
        val stopped = ref (NONE : string option)
                fun run_call c =
          let
            val id = integer (field c "index")
            val fields = base @ [("index", String.translate (fn #"~" => "-" | c => String.str c) (IntInf.toString id))]
            fun unavailable message = output (fields @
              [("status", json_string "not-runnable"),
               ("reason", json_string message)])
          in
            case !stopped of
              SOME reason => unavailable ("earlier transaction not runnable: " ^ reason)
            | NONE =>
              (case JSONUtil.findField c "builtin" of
                 SOME (JSON.STRING builtin) =>
                   let
                     val arg = case JSONUtil.findField c "builtin_arg" of
                       NONE => address
                     | SOME v => word_term 160 (integer v)
                     val n = case builtin of
                       "account" => eval “w2n ^arg”
                     | "balance" => eval “(lookup_account ^arg ^(!world).accounts).balance”
                     | "storageEmpty" => eval “if
                         (lookup_account ^address ^(!world).accounts).storage = empty_storage
                         then 1n else 0”
                     | _ => fail ("unknown builtin " ^ builtin)
                     val bs = eval “word_to_bytes (n2w ^n : bytes32) T”
                   in output (fields @ [("status", json_string "executed"),
                        ("actual", outcome_json (con "Returned" [bs]))]) end
               | SOME _ => fail "builtin must be a string"
               | NONE => (case JSONUtil.findField c "calldata" of
                 NONE =>
                   let val reason = string_field c "reason" in
                     stopped := SOME reason; unavailable reason
                   end
               | SOME (JSON.STRING hex) =>
                 let
                   val creating = JSONUtil.asBool (field c "deploy")
                   val raw_data = bytes_term (hex_bytes hex)
                   val data = case JSONUtil.findField c "signature" of
                     NONE => raw_data
                   | SOME v =>
                       let val sig_bytes = bytes_term (map ord
                         (explode (JSONUtil.asString v))) in
                         eval “TAKE 4 (Keccak_256_w64 ^sig_bytes) ++ ^raw_data”
                       end
                   val value = num_term (integer (field c "value"))
                   val sender = word_term 160 (integer (field c "sender"))
                   val prior_world = !world
                   val () = block := !block + 1
                   val bn = num_term (IntInf.fromInt (!block))
                   val fr = eval “(differential_frame ^sender ^value ^data) with
                     <| self_address := ^address; code_address := ^address;
                        tx_params := (differential_frame ^sender ^value ^data).tx_params with
                          <| origin := 0x9292929292929292929292929292929292929292w;
                             gasPrice := 3000000000; blockNumber := ^bn;
                             blockTimeStamp := 15 * ^bn; chainId := 1;
                             blockCoinBase := 0x7878787878787878787878787878787878787878w;
                             blockGasLimit := 20000000;
                             prevRandao := 0xa86c2e601b6c44eb4848f7d23d9df3113fbcac42041c49cbed5000cb4f118777w |> |>”
                   fun bytecode () =
                     if not verify then [] else
                     let
                       fun observed outcome logs =
                         [("bytecode", outcome_json outcome),
                          ("bytecode_logs", event_logs_json logs)]
                     in
                       if creating then
                         let
                           val blk = eval “differential_block with
                             <| number := ^bn; timeStamp := 15 * ^bn;
                                coinBase := 0x7878787878787878787878787878787878787878w;
                                baseFeePerGas := 0; gasLimit := 100000000;
                                prevRandao := ^fr.tx_params.prevRandao |>”
                           val tx = eval “(differential_tx ^sender ^value
                             (^initcode ++ ^data)) with
                             <| to := NONE; nonce := 1; gasLimit := 10000000;
                                gasPrice := 0 |>”
                           val start = keep “run_create (Collect empty_domain) F 1 []
                             ^blk ^(!evm_accounts) ^tx”
                           val runnable = eval “case ^start of
                             SOME (INR _) => 1n | _ => 0”
                         in
                           if aconv runnable “0n” then
                             [("bytecode_reason", json_string "creation transaction not runnable")]
                           else
                             let
                               val acc = keep “FST (THE (case ^start of
                                 SOME (INR p) => SOME p | _ => NONE))”
                               val initial = keep “FST (SND (THE (case ^start of
                                 SOME (INR p) => SOME p | _ => NONE))) with txParams := ^fr.tx_params”
                               val state = keep “^initial with contexts :=
                                 (case ^initial.contexts of
                                    [] => []
                                  | (ctxt, rb)::rest =>
                                      (ctxt with msgParams updated_by
                                        (λmsg. msg with gasLimit := 100000000), rb)::rest)”
                               val ran = keep “run ^state”
                               val finished = eval “case ^ran of
                                 SOME (INR _, _) => 1n | _ => 0”
                             in
                               if aconv finished “0n” then
                                 [("bytecode_reason", json_string "creation EVM left the model")]
                               else
                                 let
                                   val resultvalue = eval “OUTR (FST (THE ^ran))”
                                   val post = keep “post_transaction_accounting ^blk
                                     (^tx with gasLimit := 100000000)
                                     ^resultvalue ^acc (SND (THE ^ran))”
                                   val success = aconv “1n” (eval “if IS_NONE (FST ^post).result then 1n else 0”)
                                   val () = evm_accounts := keep “SND ^post”
                                   val outcome = con (if success then "Returned" else "Reverted")
                                     [bytes_term []]
                                 in
                                   if aconv resultvalue “SOME OutOfGas” then
                                     [("bytecode_reason", json_string "creation EVM ran out of gas")]
                                   else observed outcome (eval “(FST ^post).logs”)
                                 end
                             end
                         end
                       else
                         let
                           val result = keep “run_external_call ^sender ^address ^data
                             ^value F (100000000 - (if ^value = 0 then 0 else call_stipend))
                             ^(!evm_accounts) empty_transient_storage ^fr.tx_params”
                           val unavailable = aconv “1n” (eval “if IS_NONE ^result then 1n else 0”)
                         in
                           if unavailable then
                             [("bytecode_reason", json_string "EVM call left the model")]
                           else
                             let
                               val success = aconv “1n” (eval “if (THE ^result).call_success then 1n else 0”)
                               val () = evm_accounts := keep “(THE ^result).call_accounts”
                             in
                               observed (con (if success then "Returned" else "Reverted")
                                 [eval “(THE ^result).call_return”])
                                 (eval “(THE ^result).call_logs”)
                             end
                         end
                     end
                   val bytecode_fields = bytecode ()
                   val entered = “^prior_world with accounts :=
                     transfer_value ^sender ^address ^value ^prior_world.accounts”
                   val invocation = if creating then
                     “deploy_contract 10000 ^program ^fr ^entered”
                     else “call_contract 10000 ^program ^(!imm) ^fr ^entered”
                   val result = keep “if
                     (lookup_account ^sender ^prior_world.accounts).balance < ^value then
                       ContractReverted [] ^prior_world else ^invocation”
                   val r = eval “case ^result of
                     ContractCreated im _ => ContractCreated im (differential_world empty_accounts)
                   | ContractReturned bs _ => ContractReturned bs (differential_world empty_accounts)
                   | ContractReverted bs _ => ContractReverted bs (differential_world empty_accounts)
                   | other => other”
                   val result_world = “case ^result of
                     ContractCreated _ w => w | ContractReturned _ w => w
                     | ContractReverted _ w => w | _ => ^entered”
                   val (constructor, args) = strip_comb r
                   val kind = fst (dest_const constructor)
                   val (outcome, logs) =
                     case (kind, args) of
                       ("ContractCreated", [_, _]) =>
                         let
                           val im = “case ^result of ContractCreated im _ => im | _ => FEMPTY”
                           fun patch (entry, code) =
                             let
                               val (_, offsets) = pairSyntax.dest_pair entry
                               val one = listSyntax.mk_list ([entry], “:num # num list”)
                               val word = eval “created_immutable_words ^unit ^one ^im”
                             in List.foldl (fn (offset, code) =>
                                  eval “patch_word ^word ^code ^offset”) code
                                  (fst (listSyntax.dest_list offsets)) end
                           val patched = List.foldl patch code
                             (fst (listSyntax.dest_list refs))
                           val w = “^result_world with accounts :=
                             update_account ^address
                               ((lookup_account ^address ^result_world.accounts)
                                  with code := ^patched) ^result_world.accounts”
                         in
                           imm := im; world := w;
                           (con "Returned" [bytes_term []], eval “^w.logs”)
                         end
                     | ("ContractReturned", [bs, w]) =>
                         (world := result_world;
                          (con "Returned" [bs], eval “^result_world.logs”))
                     | ("ContractReverted", [bs, _]) =>
                         (world := prior_world;
                          if creating then stopped := SOME "deployment reverted" else ();
                          (con "Reverted" [if creating then bytes_term [] else bs], bytes_term []))
                     | ("ContractInvalid", [reason]) =>
                         (stopped := SOME (stringSyntax.fromHOLstring reason);
                          (con "Diagnostic" [“InvalidCompletion”], bytes_term []))
                     | ("ContractOutOfFuel", []) =>
                         (stopped := SOME "core evaluator exhausted fuel";
                          (con "Diagnostic" [“OutOfFuel”], bytes_term []))
                     | _ => raise ERR "run_expectations" "unexpected contract_result"
                   val () = world := keep “^(!world) with
                     <| logs := []; transient := empty_transient_storage |>”
                   fun expected_event e =
                     let
                       val event_sig = string_field e "signature"
                       val sigbytes = bytes_term (map ord (explode event_sig))
                       val sigtopic = eval “n2w (num_of_be_bytes
                         (Keccak_256_w64 ^sigbytes)) : bytes32”
                       val topics = (if event_sig = "<anonymous>" then [] else [sigtopic]) @
                         map (word_term 256 o integer) (array_field e "topics")
                       val logger = case JSONUtil.findField e "logger" of
                         SOME JSON.NULL => address
                       | NONE => address
                       | SOME v => word_term 160 (integer v)
                     in
                       TypeBase.mk_record (“:event”,
                         [("logger", logger),
                          ("topics", listSyntax.mk_list (topics, “:bytes32”)),
                          ("data", bytes_term (hex_bytes (string_field e "data")))])
                     end
                   val expected_logs = listSyntax.mk_list
                     (map expected_event (array_field c "events"), “:event”)
                   val diagnostic = is_con "Diagnostic" outcome
                   val () = output (fields @
                     bytecode_fields @ [("status", json_string (if diagnostic then "not-runnable" else "executed")),
                      ("actual", outcome_json outcome)] @
                     (if not diagnostic then [("logs", if is_con "Reverted" outcome then "[]" else event_logs_json logs),
                       ("expected_logs", event_logs_json expected_logs)] else []) @
                     (case !stopped of SOME why => [("reason", json_string why)] | NONE => []))
                 in () end
               | _ => fail "calldata must be a hex string"))
          end
        val () = List.app run_call (array_field test "calls")
      in
        output (base @ [("kind", json_string "complete")])
      end
      handle solidityPrepareLib.PreparationError (kind, message) =>
        output [("test", json_string (string_field test "test")),
                ("kind", json_string "preparation"),
                ("status", json_string (solidityPrepareLib.failure_name kind)),
                ("reason", json_string message)]
    val tests = array_field (JSONParser.parseFile manifest) "tests"
  in
    List.app run_test (ListPair.zip (List.tabulate (length tests, fn i => i), tests))
  end

end
