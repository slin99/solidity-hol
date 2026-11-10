(* A real contract's runtime object, imported from the pinned compiler's own
 * Yul and run.
 *
 * The corpus is hand-written Solidity; this is OpenZeppelin Contracts v5.1.0's
 * ERC20 with one contract of its own on top, compiled at the pin with the same
 * profile the corpus uses, and the artifact committed under
 * testdata/yul/expected so that CI, which has no compiler, can import it. The
 * fixture is what tests/yulImportTest's is for the importer alone, one step
 * further on: the object is not just read, it runs.
 *
 * Two things have to hold of a run on a real contract. The runtime object's
 * own dispatch must reach a function and the frame's inputs must reach it.
 * And the answer must be the one the bytecode would give: name(),
 * totalSupply() and owner() return what the frame's storage holds in the
 * slots the constructor would have written, ABI-encoded; cap() the immutable
 * the constructor would have patched into the code.
 *)
Theory yulContractTest
Ancestors
  yulAST yulDialect yulState yulEvaluator cv_string_fmap vfmState vfmCompute
Libs
  yulImportLib cv_transLib wordsLib

(* Read by holbuild's dependency scanner, which stages the fixture. *)
fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps [
  "../testdata/yul/expected/openzeppelin-erc20.json"
]

val fixture = "../testdata/yul/expected/openzeppelin-erc20.json"
val source = "testdata/yul/openzeppelin/contracts/MyToken.sol"
val contract = "MyToken"

(* The code generator's own output, which is the stage a contract's `--ir`
 * text is printed from. *)
Definition openzeppelin_erc20_ir_def:
  openzeppelin_erc20_ir =
    ^(yulImportLib.import_runtime_artifact fixture source contract
        yulImportLib.Ir)
End

val () = cv_auto_trans openzeppelin_erc20_ir_def;

(* The transaction and block the frame runs in. Neither function this runs
 * reads them, so they are only here to fill the record.
 *)
Definition yul_contract_tx_params_def:
  yul_contract_tx_params =
    <| origin := 0w; gasPrice := 0; baseFeePerGas := 0;
       baseFeePerBlobGas := 0; blockNumber := 0; blockTimeStamp := 0;
       blockCoinBase := 0w; blockGasLimit := 0; prevRandao := 0w;
       prevHashes := []; blobHashes := []; chainId := 0; authRefund := 0 |>
End

(* What the constructor would have left in storage: ERC20's _totalSupply at
 * slot 2, its _name at 3 as the compiler writes a string that fits in a word
 * -- the bytes, then the length doubled in the last one -- and Ownable's
 * _owner at 5. The constructor itself is in the creation object, which a
 * runtime object does not contain, so the frame carries the slots instead.
 *)
Definition yul_contract_storage_def:
  yul_contract_storage =
    update_storage 2w (n2w 1234)
      (update_storage 3w (n2w (0x4d79546f6b656e * 256 ** 25 + 14))
         (update_storage 5w 0xabcw empty_storage))
End

(* The frame: the deployed contract at 0x1000 holding those slots, called by
 * 0x2000 with the calldata the test names, and the one immutable MyToken
 * declares patched in -- the runtime object cannot supply that for itself,
 * since the constructor patched it into the code this object was cut from --
 * under the name the getter's loadimmutable spells.
 *)
Definition yul_contract_machine_def:
  yul_contract_machine data =
    <| accounts :=
         update_account 0x1000w
           (empty_account_state with <| storage := yul_contract_storage |>)
           empty_accounts;
       transient := empty_transient_storage;
       logs := []; self_address := 0x1000w;
       caller_address := 0x2000w; call_value := 0w; call_data := data;
       return_data := [];
       code := []; objects := FEMPTY; immutable_offsets := FEMPTY;
       immutables := (FEMPTY : string |-> bytes32) |+ ("11", 1000000w);
       memory := FEMPTY; memory_size := 0; gas_limit := 10000000; scopes := [];
       transaction_parameters := yul_contract_tx_params |>
End

Definition run_contract_def:
  run_contract data =
    run_yul 1000000 openzeppelin_erc20_ir (yul_contract_machine data)
End

val () = cv_auto_trans run_contract_def;

(* name() is a public string getter: the runtime object's own dispatch reaches
 * it through the selector, it reads slot 3 and the ABI encoder writes what it
 * found -- a word of 32 for the offset, a word of 7 for the length, then
 * "MyToken" padded to a word.
 *)
Theorem openzeppelin_erc20_returns_its_name:
  (run_contract [0x06w; 0xfdw; 0xdew; 0x03w]).completion =
  YulReturn (word_to_bytes_be (32w : bytes32) ++
             word_to_bytes_be (7w : bytes32) ++
             [0x4dw; 0x79w; 0x54w; 0x6fw; 0x6bw; 0x65w; 0x6ew] ++
             REPLICATE 25 0x00w)
Proof
  CONV_TAC cv_eval
QED

(* totalSupply() and owner() likewise read slots 2 and 5. *)
Theorem openzeppelin_erc20_returns_its_total_supply:
  (run_contract [0x18w; 0x16w; 0x0dw; 0xddw]).completion =
  YulReturn (word_to_bytes_be (1234w : bytes32))
Proof
  CONV_TAC cv_eval
QED

Theorem openzeppelin_erc20_returns_its_owner:
  (run_contract [0x8dw; 0xa5w; 0xcbw; 0x5bw]).completion =
  YulReturn (word_to_bytes_be (0xabcw : bytes32))
Proof
  CONV_TAC cv_eval
QED

(* cap() is the immutable accessor: the runtime object has no value of its own
 * for it -- the constructor patched it into the code this object was cut from
 * -- so what it returns is the one the frame carried, under the name the
 * getter's loadimmutable spells.
 *)
Theorem openzeppelin_erc20_reads_its_immutable_from_the_frame:
  (run_contract [0x35w; 0x52w; 0x74w; 0xeaw]).completion =
  YulReturn (word_to_bytes_be (1000000w : bytes32))
Proof
  CONV_TAC cv_eval
QED
