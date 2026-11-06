"""Regression examples from upstream isoltest's expectation language."""

from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import run_semantic_expectations as runner


class ExpectationTests(unittest.TestCase):
    def test_dynamic_arguments_are_raw_bytes(self) -> None:
        calls = runner.parse_calls('// ----\n// f(bytes): 0x20, 3, "abc" -> 3', {"f(bytes)": "12345678"})
        self.assertEqual(calls[1].calldata, "0x12345678" + (32).to_bytes(32, "big").hex()
                         + (3).to_bytes(32, "big").hex() + b"abc".ljust(32, b"\0").hex())

    def test_panic_and_empty_revert_are_distinct(self) -> None:
        calls = runner.parse_calls('// ----\n// f() -> FAILURE, hex"4e487b71", 0x32\n// f() -> FAILURE', {"f()": "12345678"})
        self.assertEqual(calls[1].expected, {"reverted": "0x4e487b71" + (50).to_bytes(32, "big").hex()})
        self.assertEqual(calls[2].expected, {"reverted": "0x"})

    def test_constructor_and_following_calls_share_value_and_sender(self) -> None:
        calls = runner.parse_calls('// ----\n// constructor(), 1 ether: 7 ->\n// account: 2 -> 0\n// f(), 3 wei ->', {"f()": "12345678"})
        self.assertEqual(len(calls), 3)
        self.assertTrue(calls[0].deploy)
        self.assertEqual(calls[0].value, 10**18)
        self.assertEqual(calls[2].sender, str(runner.ACCOUNT + 8192))
        self.assertEqual(calls[2].value, 3)

    def test_multiline_expectations_and_quoted_commas(self) -> None:
        calls = runner.parse_calls('// ----\n// f(): "a,b",\n// 3 ->\n// "a,b" #comment#\n// gas irOptimized: 25', {"f()": "12345678"})
        self.assertEqual(calls[1].expected, {"returned": "0x" + b"a,b".ljust(32, b"\0").hex()})
        self.assertEqual(calls[1].observations[0]["reason"], "gas is not modeled")

    def test_events_keep_indexed_markers(self) -> None:
        calls = runner.parse_calls('// ----\n// f() ->\n// ~ emit E(uint256,uint256): #1, 2', {"f()": "12345678"})
        self.assertEqual(calls[1].events[0]["topics"], ["0x" + (1).to_bytes(32, "big").hex()])
        self.assertEqual(calls[1].events[0]["data"], "0x" + (2).to_bytes(32, "big").hex())

    def test_alignment_and_negative_words(self) -> None:
        self.assertEqual(runner.encode_bytes("left(0x1234)"), "0x1234" + "00" * 30)
        self.assertEqual(runner.encode_bytes("-1"), "0x" + "ff" * 32)
        self.assertEqual(runner.encode_bytes('hex"1234"'), "0x1234")

    def test_hex_alignment_preserves_leading_zero_bytes(self) -> None:
        self.assertEqual(runner.encode_bytes("left(0x0001)"), "0x0001" + "00" * 30)

    def test_strings_use_isoltest_escapes_and_keep_hashes(self) -> None:
        calls = runner.parse_calls('// ----\n// f(): "#a#" #comment# -> "#b#"', {"f()": "12345678"})
        self.assertEqual(calls[1].expected, {"returned": "0x" + b"#b#".ljust(32, b"\0").hex()})
        self.assertEqual(runner.decode_string(r"a\x00\0"), b"a\0\0")

    def test_consecutive_builtins_are_separate_calls(self) -> None:
        calls = runner.parse_calls('// ----\n// f() -> 1\n// balance -> 2\n// storageEmpty -> false', {"f()": "12345678"})
        self.assertEqual([c.builtin for c in calls[1:]], [None, "balance", "storageEmpty"])

    def test_out_of_gas_expectation_is_not_executed(self) -> None:
        calls = runner.parse_calls('// ----\n// f() -> FAILURE # Out-of-gas #', {"f()": "12345678"})
        self.assertIsNone(calls[1].calldata)
        self.assertEqual(calls[1].reason, "out-of-gas expectation: gas is not modeled")

    def test_revert_and_builtin_event_mismatches_are_not_agreement(self) -> None:
        call = runner.Call(0, "f() -> FAILURE", calldata="0x", expected={"reverted": "0x"})
        actual = {0: {"status": "executed", "actual": {"reverted": "0x"},
                      "logs": [], "expected_logs": [{"data": "0x"}]}}
        self.assertEqual(runner.classify([call], actual)[0]["status"], "disagree")
        builtin = runner.Call(0, "balance -> 0", builtin="balance", expected={"returned": "0x"},
                              events=[{"signature": "E()"}])
        self.assertEqual(runner.classify([builtin], {0: {"status": "executed", "actual": {"returned": "0x"}}})[0]["status"], "disagree")

    def test_unknown_input_is_not_encoded(self) -> None:
        calls = runner.parse_calls('// ----\n// f(): something -> 1', {"f()": "12345678"})
        self.assertIsNone(calls[1].calldata)
        self.assertIn("unsupported byte token", calls[1].reason or "")


if __name__ == "__main__":
    unittest.main()
