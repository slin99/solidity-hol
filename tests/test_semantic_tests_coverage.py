#!/usr/bin/env python3

from pathlib import Path
import json
import sys
import tempfile
import textwrap
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))

import semantic_tests_coverage as coverage  # noqa: E402

PROFILE = {"settings": {"evmVersion": "osaka", "debug": {"revertStrings": "default"}}}


def variable(node_id: int, *, state: bool = False, type_identifier: str = "t_uint256",
             visibility: str = "private") -> dict:
    return {
        "nodeType": "VariableDeclaration", "id": node_id, "stateVariable": state,
        "constant": False, "mutability": "mutable", "storageLocation": "default",
        "visibility": visibility,
        "typeDescriptions": {"typeIdentifier": type_identifier},
        "typeName": {"nodeType": "ElementaryTypeName", "id": node_id + 100, "name": "uint256"},
    }


def function(node_id, statements):
    return {
        "nodeType": "FunctionDefinition", "id": node_id, "kind": "function",
        "implemented": True, "virtual": False, "stateMutability": "pure", "modifiers": [],
        "parameters": {"nodeType": "ParameterList", "id": node_id + 100, "parameters": []},
        "body": {"nodeType": "Block", "id": node_id + 200, "statements": statements},
    }


def unit(members):
    return {"nodeType": "SourceUnit", "id": 1, "nodes": [{
        "nodeType": "ContractDefinition", "id": 2, "contractKind": "contract",
        "abstract": False, "baseContracts": [], "linearizedBaseContracts": [2],
        "nodes": members,
    }]}


def error_definition(node_id: int, type_identifier: str) -> dict:
    return {"nodeType": "ErrorDefinition", "id": node_id, "name": "E",
            "parameters": {"nodeType": "ParameterList", "id": node_id + 1,
                           "parameters": [variable(node_id + 2, type_identifier=type_identifier)]}}


def revert(node_id: int, error: int, arguments: list) -> dict:
    return {"nodeType": "RevertStatement", "id": node_id, "errorCall": {
        "nodeType": "FunctionCall", "id": node_id + 1, "kind": "functionCall", "names": [],
        "tryCall": False, "typeDescriptions": {"typeIdentifier": "t_tuple$__$"}, "arguments": arguments,
        "expression": {"nodeType": "Identifier", "id": node_id + 2, "name": "E",
                       "referencedDeclaration": error,
                       "typeDescriptions": {"typeIdentifier": "t_function_error_pure$__$returns$__$"}}}}


def yul_call(name: str, *arguments) -> dict:
    return {"nodeType": "YulFunctionCall", "arguments": list(arguments),
            "functionName": {"nodeType": "YulIdentifier", "name": name}}


def assembly(statements: list, references: list = ()) -> dict:
    return {"nodeType": "InlineAssembly", "id": 20, "externalReferences": list(references),
            "AST": {"nodeType": "YulBlock", "statements": statements}}


# A block the importer rejects: balance is not a builtin of the dialect.
ASSEMBLY = assembly([{"nodeType": "YulExpressionStatement",
                      "expression": yul_call("pop", yul_call("balance", yul_call("caller")))}])


class BuiltinCoverageTests(unittest.TestCase):
    def test_messages_must_be_literals(self) -> None:
        def call(message: dict) -> dict:
            return {"nodeType": "FunctionCall", "id": 5, "kind": "functionCall", "names": [],
                    "tryCall": False, "typeDescriptions": {"typeIdentifier": "t_tuple$__$"},
                    "expression": {"nodeType": "Identifier", "id": 6, "name": "revert",
                                   "referencedDeclaration": coverage.REVERT,
                                   "typeDescriptions": {"typeIdentifier": "t_function_revert_pure$__$"}},
                    "arguments": [message]}

        literal = {"nodeType": "Literal", "id": 7, "kind": "string", "value": "no",
                   "typeDescriptions": {"typeIdentifier": "t_stringliteral_abc"}}
        statement = {"nodeType": "ExpressionStatement", "id": 8, "expression": call(literal)}
        self.assertEqual(coverage.scan({"t.sol": unit([function(4, [statement])])}), {})
        variable_message = {"nodeType": "Identifier", "id": 7, "name": "s", "referencedDeclaration": 3,
                            "typeDescriptions": {"typeIdentifier": "t_string_memory_ptr"}}
        statement["expression"] = call(variable_message)
        self.assertEqual(coverage.scan({"t.sol": unit([function(4, [statement])])})[5], [
            coverage.Blocker("FunctionCall", "messages that are not literals", "elaboration")])

    def test_shadowed_names_are_ordinary_calls(self) -> None:
        artifact = json.loads((ROOT / "testdata/differential/expected/shadowed_builtins.json").read_text())
        ast = artifact["output"]["sources"]["testdata/differential/shadowed_builtins.sol"]["ast"]
        self.assertEqual(coverage.scan({"shadowed_builtins.sol": ast}), {})
        for node in coverage.nodes(ast):
            if node["nodeType"] == "FunctionCall":
                self.assertGreaterEqual(node["expression"]["referencedDeclaration"], 0)


class ReadTestTests(unittest.TestCase):
    def read(self, text: str) -> coverage.SemanticTest:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            path = root / "dir" / "t.sol"
            path.parent.mkdir()
            path.write_text(textwrap.dedent(text), encoding="utf-8")
            return coverage.read_test(root, path)

    def test_splits_sources_and_reads_settings(self) -> None:
        test = self.read("""\
            ==== Source: a.sol ====
            contract A {}
            ==== Source: b.sol ====
            import "a.sol";
            // ====
            // EVMVersion: >=cancun
            // compileViaYul: true
            // ----
            // f() -> 1
            """)
        self.assertEqual(test.name, "dir/t.sol")
        self.assertEqual(list(test.sources), ["a.sol", "b.sol"])
        self.assertEqual(test.sources["a.sol"], "contract A {}\n")
        self.assertEqual(test.sources["b.sol"], 'import "a.sol";\n')
        self.assertEqual(test.settings, {"EVMVersion": ">=cancun", "compileViaYul": "true"})
        self.assertIsNone(coverage.skip_reason(test, PROFILE))

    def test_skips_by_own_settings(self) -> None:
        def reason(settings: str) -> str | None:
            return coverage.skip_reason(
                self.read(f"contract C {{}}\n// ====\n{settings}// ----\n"), PROFILE)

        self.assertIn("legacy", reason("// compileViaYul: false\n"))
        self.assertIn("EVMVersion: <osaka", reason("// EVMVersion: <osaka\n"))
        self.assertIsNone(reason("// EVMVersion: >=osaka\n"))
        self.assertIn("revertStrings: debug", reason("// revertStrings: debug\n"))


class ClassifyTests(unittest.TestCase):
    def test_preparation_failures_are_not_unsupported_features(self) -> None:
        for status in (coverage.MALFORMED_INPUT, coverage.INVALID_CORE):
            with self.subTest(status=status):
                result = coverage.classify("t.sol", {}, {"status": status, "message": "bad input/core"})
                self.assertEqual(result.category, status)
                self.assertFalse(result.scan_agrees)
                self.assertIsNone(result.first)

    def test_import_rejection_records_first_and_all_blockers(self) -> None:
        ast = unit([variable(3, state=True, visibility="public"), function(4, [ASSEMBLY])])
        result = coverage.classify(
            "t.sol", coverage.scan({"t.sol": ast}),
            {"status": "import-rejected",
             "message": "VariableDeclaration 3: public state variables are not supported"})
        self.assertEqual(result.category, coverage.IMPORT_REJECTED)
        self.assertEqual(result.first, coverage.Blocker(
            "VariableDeclaration", "public state variables", "import"))
        self.assertEqual({b.feature for b in result.blockers},
                         {"public state variables", "inline assembly"})
        self.assertTrue(result.scan_agrees)

    def test_scan_must_explain_the_importer(self) -> None:
        ast = unit([function(4, [])])
        result = coverage.classify(
            "t.sol", coverage.scan({"t.sol": ast}),
            {"status": "import-rejected", "message": "Block 204: unsupported statement X"})
        self.assertEqual(result.first.feature, "unclassified")
        self.assertFalse(result.scan_agrees)

    def test_source_rejection_is_distinct(self) -> None:
        rejected = coverage.classify("t.sol", {}, {
            "status": "source-rejected", "message": "valid_src_unit failed"})
        self.assertEqual(rejected.category, coverage.SOURCE_REJECTED)
        self.assertFalse(rejected.scan_agrees)

    def test_import_rejection_names_its_source(self) -> None:
        ast = unit([variable(3, state=True, visibility="public")])
        named = coverage.classify("t.sol", coverage.scan({"t.sol": ast}), {
            "status": "import-rejected",
            "message": "a.sol: VariableDeclaration 3: public state variables are not supported"})
        self.assertEqual(named.first.feature, "public state variables")
        self.assertTrue(named.scan_agrees)

    def test_elaboration_rejection_and_admission(self) -> None:
        arrays = unit([function(4, [{
            "nodeType": "VariableDeclarationStatement", "id": 5,
            "declarations": [variable(6, type_identifier="t_array$_t_uint256_$dyn_memory_ptr")],
        }])])
        rejected = coverage.classify(
            "s.sol", coverage.scan({"s.sol": arrays}),
            {"status": "elaboration-rejected", "message": "elaborate_unit returned NONE"})
        self.assertEqual([b.feature for b in rejected.blockers], ["arrays"])
        self.assertTrue(rejected.scan_agrees)
        admitted = coverage.classify(
            "a.sol", coverage.scan({"a.sol": unit([function(4, [])])}), {"status": "admitted"})
        self.assertEqual(admitted.blockers, [])
        self.assertTrue(admitted.scan_agrees)

    def test_scan_records_every_property_of_a_variable(self) -> None:
        constant = dict(variable(3, state=True), constant=True, mutability="constant",
                        value={"nodeType": "Literal", "id": 4, "kind": "number",
                               "typeDescriptions": {"typeIdentifier": "t_rational_1_by_1"}})
        self.assertEqual({b.feature for b in coverage.scan({"t.sol": unit([constant])})[3]},
                         {"constants"})

    def test_scan_finds_literals_of_non_integer_types(self) -> None:
        def literal(node_id, type_identifier):
            return {"nodeType": "Literal", "id": node_id, "kind": "number", "value": "1",
                    "typeDescriptions": {"typeIdentifier": type_identifier}}

        address = literal(5, "t_address")
        declaration = {
            "nodeType": "VariableDeclarationStatement", "id": 6,
            "declarations": [variable(7, type_identifier="t_bytes4")],
            "initialValue": literal(8, "t_rational_305419896_by_1"),
        }
        boolean = {"nodeType": "Literal", "id": 9, "kind": "bool", "value": "false",
                   "typeDescriptions": {"typeIdentifier": "t_bool"}}
        found = coverage.scan({"t.sol": unit([function(4, [address, declaration, boolean])])})
        self.assertEqual(found[5], [coverage.Blocker(
            "Literal", "literals of non-integer types", "elaboration")])
        self.assertEqual(found[6], [coverage.Blocker(
            "VariableDeclarationStatement", "literals of non-integer types", "elaboration")])
        self.assertNotIn(8, found)
        self.assertNotIn(9, found)

    def test_state_initializers_and_revert_arguments_are_coerced(self) -> None:
        def string(node_id):
            return {"nodeType": "Literal", "id": node_id, "kind": "string", "value": "abcd",
                    "typeDescriptions": {"typeIdentifier": "t_stringliteral_abcd"}}

        state = dict(variable(3, state=True, type_identifier="t_bytes4"), value=string(8))
        error = error_definition(30, "t_bytes4")
        found = coverage.scan({"t.sol": unit([state, error, function(4, [revert(40, 30, [string(9)])])])})
        feature = "string literals as fixed-size bytes"
        self.assertEqual(found[3], [coverage.Blocker("VariableDeclaration", feature, "elaboration")])
        self.assertEqual(found[40], [coverage.Blocker("RevertStatement", feature, "elaboration")])

    def test_only_reverted_errors_have_their_parameters_read(self) -> None:
        error = error_definition(30, "t_bytes_memory_ptr")
        self.assertEqual(coverage.scan({"t.sol": unit([error, function(4, [])])}), {})
        found = coverage.scan({"t.sol": unit([error, function(4, [revert(40, 30, [])])])})
        self.assertEqual(found[32], [coverage.Blocker(
            "VariableDeclaration", "custom errors with reference parameters", "elaboration")])

    def test_inline_assembly_by_slice(self) -> None:
        def statement(expression):
            return {"nodeType": "YulExpressionStatement", "expression": expression}

        local = variable(5, type_identifier="t_uint256")
        memory = dict(variable(6, type_identifier="t_bytes_memory_ptr"), storageLocation="memory")
        state = variable(7, state=True)
        by_id = {5: local, 6: memory, 7: state}
        value = assembly([statement(yul_call("sstore", yul_call("calldataload", {"nodeType": "YulLiteral", "kind": "number", "value": "0"}),
                                                yul_call("add", {"nodeType": "YulIdentifier", "name": "x"})))],
                         [{"declaration": 5}, {"declaration": 7, "suffix": "slot"}])
        self.assertEqual(coverage.assembly_blockers(value, by_id), [])
        self.assertEqual(coverage.assembly_blockers(ASSEMBLY, by_id),
                         [coverage.Blocker("InlineAssembly", "inline assembly", "import")])
        calls = assembly([statement(yul_call("pop", yul_call("gas")))], [{"declaration": 6}])
        self.assertEqual(coverage.assembly_blockers(calls, by_id), [
            coverage.Blocker("InlineAssembly", "inline assembly calls, gas and return data", "elaboration"),
            coverage.Blocker("InlineAssembly", "inline assembly memory references", "elaboration")])
        own = assembly([{"nodeType": "YulFunctionDefinition", "name": "gas", "body": {
                            "nodeType": "YulBlock", "statements": [{
                                "nodeType": "YulFunctionDefinition", "name": "inner",
                                "body": {"nodeType": "YulBlock", "statements": []}}]}},
                        statement(yul_call("gas"))],
                       [{"declaration": 5, "suffix": "length"}])
        self.assertEqual(coverage.assembly_blockers(own, by_id),
                         [coverage.Blocker("InlineAssembly", "inline assembly", "import")])

    def test_overridden_functions_are_only_imported(self) -> None:
        coerced = {"nodeType": "VariableDeclarationStatement", "id": 6,
                   "declarations": [variable(7, type_identifier="t_bytes4")],
                   "initialValue": {"nodeType": "Literal", "id": 8, "kind": "string", "value": "abcd",
                                    "typeDescriptions": {"typeIdentifier": "t_stringliteral_abcd"}}}
        base = {"nodeType": "ContractDefinition", "id": 50, "contractKind": "contract",
                "abstract": False, "baseContracts": [], "linearizedBaseContracts": [50],
                "nodes": [dict(function(60, [coerced, ASSEMBLY]), virtual=True)]}
        derived = dict(function(70, []), baseFunctions=[60])
        ast = unit([derived])
        ast["nodes"][0]["linearizedBaseContracts"] = [2, 50]
        ast["nodes"].insert(0, base)
        found = coverage.scan({"t.sol": ast})
        self.assertEqual(found, {20: [coverage.Blocker("InlineAssembly", "inline assembly", "import")]})
        del derived["baseFunctions"]
        self.assertIn(6, coverage.scan({"t.sol": ast}))

    def test_base_arguments_tuple_returns_and_calls_with_options_are_coerced(self) -> None:
        def string(node_id):
            return {"nodeType": "Literal", "id": node_id, "kind": "string", "value": "abcd",
                    "typeDescriptions": {"typeIdentifier": "t_stringliteral_abcd"}}

        def parameters(node_id, *types):
            return {"nodeType": "ParameterList", "id": node_id,
                    "parameters": [variable(node_id + 1 + i, type_identifier=t) for i, t in enumerate(types)]}

        feature = "string literals as fixed-size bytes"
        constructor = dict(function(51, []), kind="constructor", parameters=parameters(52, "t_bytes4"))
        base = {"nodeType": "ContractDefinition", "id": 50, "nodes": [constructor]}
        specifier = {"nodeType": "InheritanceSpecifier", "id": 55, "arguments": [string(57)],
                     "baseName": {"nodeType": "IdentifierPath", "id": 56, "referencedDeclaration": 50}}
        self.assertEqual(coverage.coerced_literals(specifier, {50: base}),
                         [coverage.Blocker("InheritanceSpecifier", feature, "elaboration")])
        invocation = {"nodeType": "ModifierInvocation", "id": 58, "kind": "baseConstructorSpecifier",
                      "arguments": [string(59)], "modifierName": specifier["baseName"]}
        self.assertEqual(coverage.coerced_literals(invocation, {50: base}),
                         [coverage.Blocker("ModifierInvocation", feature, "elaboration")])

        returns = parameters(300, "t_bool", "t_bytes4")
        flag = {"nodeType": "Literal", "id": 312, "kind": "bool", "value": "true",
                "typeDescriptions": {"typeIdentifier": "t_bool"}}
        statement = {"nodeType": "Return", "id": 310, "functionReturnParameters": 300,
                     "expression": {"nodeType": "TupleExpression", "id": 311,
                                    "components": [flag, string(313)]}}
        self.assertEqual(coverage.coerced_literals(statement, {300: returns}),
                         [coverage.Blocker("Return", feature, "elaboration")])

        callee = dict(function(400, []), parameters=parameters(401, "t_bytes4"))
        call = {"nodeType": "FunctionCall", "id": 320, "kind": "functionCall", "arguments": [string(323)],
                "expression": {"nodeType": "FunctionCallOptions", "id": 321, "names": ["value"],
                               "expression": {"nodeType": "MemberAccess", "id": 322, "memberName": "f",
                                              "referencedDeclaration": 400}}}
        self.assertEqual(coverage.coerced_literals(call, {400: callee}),
                         [coverage.Blocker("FunctionCall", feature, "elaboration")])

    def test_functions_live_in_their_own_source_keep_their_blockers(self) -> None:
        coerced = {"nodeType": "VariableDeclarationStatement", "id": 6,
                   "declarations": [variable(7, type_identifier="t_bytes4")],
                   "initialValue": {"nodeType": "Literal", "id": 8, "kind": "string", "value": "abcd",
                                    "typeDescriptions": {"typeIdentifier": "t_stringliteral_abcd"}}}
        b = unit([dict(function(60, [coerced]), virtual=True)])
        d = {"nodeType": "SourceUnit", "id": 80, "nodes": [{
            "nodeType": "ContractDefinition", "id": 81, "contractKind": "contract", "abstract": False,
            "baseContracts": [], "linearizedBaseContracts": [81, 2],
            "nodes": [dict(function(90, []), baseFunctions=[60])]}]}
        self.assertEqual(coverage.scan({"b.sol": b, "d.sol": d})[6], [coverage.Blocker(
            "VariableDeclarationStatement", "string literals as fixed-size bytes", "elaboration")])

    def test_reverts_in_overridden_functions_leave_errors_unchecked(self) -> None:
        for parameter in ("t_bytes_memory_ptr", "t_array$_t_uint256_$dyn_memory_ptr"):
            base = {"nodeType": "ContractDefinition", "id": 50, "contractKind": "contract",
                    "abstract": False, "baseContracts": [], "linearizedBaseContracts": [50],
                    "nodes": [dict(function(60, [revert(40, 30, [])]), virtual=True)]}
            derived = dict(function(70, []), baseFunctions=[60])
            ast = unit([error_definition(30, parameter), derived])
            ast["nodes"][0]["linearizedBaseContracts"] = [2, 50]
            ast["nodes"].insert(0, base)
            self.assertNotIn(32, coverage.scan({"t.sol": ast}))
            del derived["baseFunctions"]
            self.assertIn(32, coverage.scan({"t.sol": ast}))

    def test_external_calls_in_overridden_functions_leave_signatures_unchecked(self) -> None:
        parameter = dict(variable(83, type_identifier="t_array$_t_uint256_$dyn_calldata_ptr"),
                         storageLocation="calldata")
        target = dict(function(81, []), implemented=False, visibility="external",
                      parameters={"nodeType": "ParameterList", "id": 82, "parameters": [parameter]},
                      returnParameters={"nodeType": "ParameterList", "id": 84, "parameters": []})
        target.pop("body")
        interface = {"nodeType": "ContractDefinition", "id": 80, "contractKind": "interface",
                     "abstract": False, "baseContracts": [], "linearizedBaseContracts": [80],
                     "nodes": [target]}
        member = {"nodeType": "MemberAccess", "id": 42, "memberName": "g", "referencedDeclaration": 81,
                  "expression": {"nodeType": "Identifier", "id": 43, "name": "i",
                                 "typeDescriptions": {"typeIdentifier": "t_contract$_I_$80"}},
                  "typeDescriptions": {"typeIdentifier": "t_function_external_nonpayable$__$returns$__$"}}
        call = {"nodeType": "ExpressionStatement", "id": 40, "expression": {
            "nodeType": "FunctionCall", "id": 41, "kind": "functionCall", "names": [], "arguments": [],
            "tryCall": False, "expression": member, "typeDescriptions": {"typeIdentifier": "t_tuple$__$"}}}
        self.assertEqual(coverage.signatures(member, {81: target}), [])
        base = {"nodeType": "ContractDefinition", "id": 50, "contractKind": "contract",
                "abstract": False, "baseContracts": [], "linearizedBaseContracts": [50],
                "nodes": [dict(function(60, [call]), virtual=True)]}
        derived = dict(function(70, []), baseFunctions=[60])
        ast = unit([derived])
        ast["nodes"][0]["linearizedBaseContracts"] = [2, 50]
        ast["nodes"][:0] = [interface, base]
        self.assertNotIn(83, coverage.scan({"t.sol": ast}))
        del derived["baseFunctions"]
        self.assertIn(83, coverage.scan({"t.sol": ast}))

    def test_named_arguments_are_paired_by_name(self) -> None:
        def string(node_id):
            return {"nodeType": "Literal", "id": node_id, "kind": "string", "value": "abcd",
                    "typeDescriptions": {"typeIdentifier": "t_stringliteral_abcd"}}

        def named(node_id, name, type_identifier):
            return dict(variable(node_id, type_identifier=type_identifier), name=name)

        error = {"nodeType": "ErrorDefinition", "id": 30, "name": "E",
                 "parameters": {"nodeType": "ParameterList", "id": 31,
                                "parameters": [named(32, "a", "t_bytes4"), named(33, "b", "t_string_memory_ptr")]}}
        statement = revert(40, 30, [string(45)])
        statement["errorCall"]["names"] = ["b"]
        self.assertEqual(coverage.coerced_literals(statement, {30: error}), [])
        statement["errorCall"]["names"] = ["a"]
        self.assertEqual(coverage.coerced_literals(statement, {30: error}), [coverage.Blocker(
            "RevertStatement", "string literals as fixed-size bytes", "elaboration")])

    def test_mapping_keys_parentheses_and_tuples_are_coerced(self) -> None:
        def string(node_id):
            return {"nodeType": "Literal", "id": node_id, "kind": "string", "value": "abcd",
                    "typeDescriptions": {"typeIdentifier": "t_stringliteral_abcd"}}

        def tuple_of(node_id, *components):
            return {"nodeType": "TupleExpression", "id": node_id, "isInlineArray": False,
                    "components": list(components)}

        def feature(kind):
            return coverage.Blocker(kind, "string literals as fixed-size bytes", "elaboration")

        index = {"nodeType": "IndexAccess", "id": 10, "indexExpression": string(11),
                 "baseExpression": {"nodeType": "Identifier", "id": 12, "typeDescriptions": {
                     "typeIdentifier": "t_mapping$_t_bytes4_$_t_uint256_$"}}}
        self.assertEqual(coverage.coerced_literals(index, {}), [feature("IndexAccess")])

        returns = {"nodeType": "ParameterList", "id": 20,
                   "parameters": [variable(21, type_identifier="t_bytes4")]}
        statement = {"nodeType": "Return", "id": 22, "functionReturnParameters": 20,
                     "expression": tuple_of(23, string(24))}
        self.assertEqual(coverage.coerced_literals(statement, {20: returns}),
                         [feature("Return")])

        flag = {"nodeType": "Literal", "id": 34, "kind": "number", "value": "1",
                "typeDescriptions": {"typeIdentifier": "t_rational_1_by_1"}}
        declaration = {"nodeType": "VariableDeclarationStatement", "id": 30,
                       "declarations": [variable(31, type_identifier="t_bytes4"),
                                        variable(32, type_identifier="t_bool")],
                       "initialValue": tuple_of(33, string(35), flag)}
        self.assertEqual(coverage.coerced_literals(declaration, {}), [
            coverage.Blocker("VariableDeclarationStatement", "string literals as fixed-size bytes",
                             "elaboration"),
            coverage.Blocker("VariableDeclarationStatement", "literals of non-integer types",
                             "elaboration")])

        assignment = {"nodeType": "Assignment", "id": 40, "operator": "=",
                      "typeDescriptions": {"typeIdentifier": "t_tuple$__$"},
                      "leftHandSide": tuple_of(41, variable(42, type_identifier="t_bytes4"),
                                               variable(45, type_identifier="t_uint256")),
                      "rightHandSide": tuple_of(43, string(44), dict(flag, id=46))}
        self.assertEqual(coverage.coerced_literals(assignment, {}), [feature("Assignment")])

    def test_structs_only_unused_errors_refer_to_are_imported(self) -> None:
        struct = {"nodeType": "StructDefinition", "id": 10, "scope": 1, "members": []}
        error = error_definition(30, "t_struct$_S_$10_memory_ptr")
        error["parameters"]["parameters"][0]["typeName"] = {
            "nodeType": "UserDefinedTypeName", "id": 33, "referencedDeclaration": 10}
        ast = unit([error, function(4, [])])
        ast["nodes"].insert(0, struct)
        by_id = {n["id"]: n for n in coverage.nodes(ast)}
        self.assertIn(struct, coverage.imported({"t.sol": ast}, by_id))

    def test_tuples_are_classified_by_a_component(self) -> None:
        self.assertTrue(coverage.decodes("t_tuple$_t_bool_$_t_bytes4_$"))
        self.assertTrue(coverage.decodes("t_tuple$_t_bool_$_t_bytes_memory_ptr_$"))
        self.assertFalse(coverage.decodes("t_tuple$_t_bool_$_t_array$_t_uint8_$dyn_memory_ptr_$"))
        self.assertEqual(coverage.type_feature("t_tuple$_t_bool_$_t_array$_t_uint8_$dyn_memory_ptr_$"),
                         "arrays")
        self.assertEqual(coverage.type_feature("t_bytes32"),
                         "fixed-size bytes members and indexing")

    def test_storage_and_every_mutability_are_admitted(self) -> None:
        f = function(4, [])
        ast = unit([variable(3, state=True), f])
        for mutability in ("pure", "view", "nonpayable", "payable"):
            with self.subTest(mutability=mutability):
                f["stateMutability"] = mutability
                self.assertEqual(coverage.scan({"t.sol": ast}), {})

    def test_nested_mappings_are_storage_types(self) -> None:
        tid = "t_mapping$_t_int8_$_t_mapping$_t_address_$_t_bytes4_$_$"
        self.assertTrue(coverage.storage_type_supported(tid))
        self.assertTrue(coverage.storage_type_supported("t_mapping$_t_uint160_$_t_bytes32_$"))
        self.assertTrue(coverage.storage_type_supported("t_mapping$_t_int80_$_t_bytes16_$"))
        self.assertTrue(coverage.storage_type_supported("t_mapping$_t_address_payable_$_t_bool_$"))
        self.assertFalse(coverage.storage_type_supported("t_mapping$_t_bytes_memory_ptr_$_t_uint8_$"))
        self.assertFalse(coverage.storage_type_supported("t_mapping$_t_uint8_$_t_uint8_$junk"))
        self.assertFalse(coverage.storage_type_supported("t_mapping$_t_mapping$_t_uint8_$_t_uint8_$_$_t_uint8_$"))
        v = variable(3, state=True, type_identifier=tid)
        self.assertEqual(coverage.elaboration_blockers(v), [])
        v["stateVariable"] = False
        v["storageLocation"] = "storage"
        self.assertIn("local reference bindings", {b.feature for b in coverage.elaboration_blockers(v)})

    def test_mapping_and_storage_array_indexing_are_admitted(self) -> None:
        base = {"nodeType": "Identifier", "id": 5, "name": "m", "referencedDeclaration": 3,
                "typeDescriptions": {"typeIdentifier": "t_mapping$_t_uint256_$_t_uint8_$"}}
        index = {"nodeType": "IndexAccess", "id": 6, "baseExpression": base,
                 "indexExpression": {"nodeType": "Literal", "id": 7, "kind": "number", "value": "1",
                                     "typeDescriptions": {"typeIdentifier": "t_rational_1_by_1"}},
                 "typeDescriptions": {"typeIdentifier": "t_uint8"}}
        self.assertEqual(coverage.scan({"t.sol": unit([function(4, [index])])}), {})
        base["typeDescriptions"]["typeIdentifier"] = "t_array$_t_uint8_$2_storage"
        self.assertEqual(coverage.node_blockers(index), [])
        self.assertEqual(coverage.scan({"t.sol": unit([function(4, [index])])}), {})
        base["typeDescriptions"]["typeIdentifier"] = "t_array$_t_uint8_$dyn_storage"
        self.assertEqual(coverage.scan({"t.sol": unit([function(4, [index])])}), {})
        self.assertTrue(coverage.storage_type_supported("t_array$_t_array$_t_uint8_$dyn_storage_$dyn_storage"))
        self.assertTrue(coverage.storage_type_supported("t_array$_t_array$_t_uint8_$dyn_storage_$2_storage"))

    def test_nested_array_types_and_fixed_length_prefix(self) -> None:
        tid = "t_array$_t_array$_t_uint24_$11_storage_$2_storage"
        self.assertTrue(coverage.storage_type_supported(tid))
        self.assertFalse(coverage.storage_type_supported(tid + "_ptr"))
        self.assertFalse(coverage.storage_type_supported("t_array$_t_uint8_$2_memory_ptr"))
        self.assertTrue(coverage.storage_type_supported("t_array$_t_mapping$_t_uint8_$_t_uint8_$_$2_storage"))
        root = {"nodeType": "Identifier", "id": 5, "name": "rows", "referencedDeclaration": 3,
                "typeDescriptions": {"typeIdentifier": tid}}
        length = {"nodeType": "MemberAccess", "id": 6, "memberName": "length", "expression": root,
                  "typeDescriptions": {"typeIdentifier": "t_uint256"}}
        self.assertEqual(coverage.scan({"t.sol": unit([function(4, [length])])}), {})

    def test_array_type_expression_without_index_is_import_rejection(self) -> None:
        node = {"nodeType": "IndexAccess", "id": 13}
        self.assertEqual(coverage.node_blockers(node),
                         [coverage.Blocker("IndexAccess", "array type expressions", "import")])

    def test_corpus_suites_have_no_coverage_blockers(self) -> None:
        """The scan admits what the differential corpus prepares: each suite's
        own source. Its other sources only hold bases, interfaces and errors,
        so they are units without exactly one contract."""
        corpus = json.loads((ROOT / "testdata/differential/corpus.json").read_text())
        for suite in corpus["suites"]:
            with self.subTest(suite=suite["name"]):
                artifact = json.loads((ROOT / suite["artifact"]).read_text())
                asts = {s: d["ast"] for s, d in artifact["output"]["sources"].items()}
                others = {ast["id"] for s, ast in asts.items() if s != suite["source"]}
                found = {i: bs for i, bs in coverage.scan(asts).items() if i not in others}
                self.assertEqual(found, {})

    def test_compilation_retains_artifact_contract_for_preparation(self) -> None:
        metadata = {"storageLayout": {"storage": [{"astId": 3, "slot": "0"}]},
                    "evm": {"deployedBytecode": {"object": "00"}}}
        output = {"sources": {"t.sol": {"ast": unit([])}},
                  "contracts": {"t.sol": {"C": metadata}}}
        artifact = {"format": "solidity-hol-solc-artifact-v1", "compiler": {"pin": "pinned"},
                    "profile": PROFILE, "input": {"settings": PROFILE["settings"]},
                    "output": output}
        with patch.object(coverage.exporter, "build_artifact_from_sources",
                          return_value=artifact):
            result = coverage.compile_test(Path("solc"), coverage.SemanticTest("t.sol", {}, {}),
                                           Path("profile"))
        self.assertEqual(result, artifact)

    def test_ranking_counts_only_blockers(self) -> None:
        def rejected(name: str, members: list) -> coverage.Classification:
            return coverage.classify(
                name, coverage.scan({name: unit(members)}),
                {"status": "import-rejected",
                 "message": "VariableDeclaration 3: public state variables are not supported"})

        report = coverage.Report("pin", "profile", [
            rejected("a.sol", [variable(3, state=True, visibility="public"), function(4, [])]),
            rejected("b.sol", [variable(3, state=True, visibility="public"), function(4, [ASSEMBLY])]),
        ])
        ranking = {f["feature"]: f for f in report.feature_ranking()}
        self.assertEqual(ranking["public state variables"]["tests"], 2)
        self.assertEqual(ranking["public state variables"]["only_blocker"], 1)
        self.assertEqual(ranking["public state variables"]["first_rejection"], 2)
        self.assertEqual(ranking["inline assembly"]["only_blocker"], 0)
        self.assertEqual(report.greedy_order(5), [("public state variables", 1), ("inline assembly", 2)])


if __name__ == "__main__":
    unittest.main()
