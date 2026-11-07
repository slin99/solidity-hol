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


class GetterTests(unittest.TestCase):
    def test_public_state_variables_need_a_getter_shape(self) -> None:
        def elementary(node_id, type_identifier):
            return {"nodeType": "ElementaryTypeName", "id": node_id,
                    "typeDescriptions": {"typeIdentifier": type_identifier}}

        def mapping(node_id, key, value):
            return {"nodeType": "Mapping", "id": node_id, "keyType": key, "valueType": value,
                    "typeDescriptions": {"typeIdentifier": "t_mapping"}}

        nested = mapping(10, elementary(11, "t_address"),
                         {"nodeType": "ArrayTypeName", "id": 12, "baseType": elementary(13, "t_string_storage_ptr"),
                          "typeDescriptions": {"typeIdentifier": "t_array"}})
        self.assertTrue(coverage.has_getter(nested, {}, set()))
        self.assertFalse(coverage.has_getter(mapping(20, elementary(21, "t_string_memory_ptr"),
                                                     elementary(22, "t_uint256")), {}, set()))

        def struct(members):
            definition = {"nodeType": "StructDefinition", "id": 1,
                          "members": [{"nodeType": "VariableDeclaration", "id": 40 + i, "typeName": t}
                                      for i, t in enumerate(members)]}
            return ({"nodeType": "UserDefinedTypeName", "id": 30, "referencedDeclaration": 1,
                     "typeDescriptions": {"typeIdentifier": "t_struct$_S_$1_storage_ptr"}},
                    {1: dict(definition, scope=9), 9: {"nodeType": "SourceUnit", "id": 9}}, set())

        def array(node_id, base):
            return {"nodeType": "ArrayTypeName", "id": node_id, "baseType": base,
                    "typeDescriptions": {"typeIdentifier": "t_array"}}

        # A struct's getter returns its values and byte sequences, skipping
        # mappings and other arrays.
        returned = struct([elementary(50, "t_uint8"), elementary(51, "t_bytes_storage_ptr"),
                           elementary(59, "t_enum_7"), elementary(65, "t_address"),
                           mapping(52, elementary(53, "t_uint256"), elementary(54, "t_uint256")),
                           array(55, elementary(56, "t_uint256"))])
        self.assertTrue(coverage.has_getter(*returned))
        self.assertTrue(coverage.has_getter(mapping(57, elementary(58, "t_uint256"), returned[0]), *returned[1:]))
        # A struct of a contract that is not a base of the deployed one is not
        # the contract's; one of a base is.
        type_name, by_id, _ = returned
        elsewhere = {**by_id, 1: dict(by_id[1], scope=8), 8: {"nodeType": "ContractDefinition", "id": 8}}
        self.assertFalse(coverage.has_getter(type_name, elsewhere, set()))
        self.assertTrue(coverage.has_getter(type_name, elsewhere, {8}))
        self.assertFalse(coverage.has_getter(*struct([mapping(60, elementary(61, "t_uint256"),
                                                              elementary(62, "t_uint256"))])))
        nested = struct([elementary(63, "t_uint256"),
                         {"nodeType": "UserDefinedTypeName", "id": 64, "referencedDeclaration": 2,
                          "typeDescriptions": {"typeIdentifier": "t_struct$_T_$2_storage_ptr"}}])
        self.assertFalse(coverage.has_getter(*nested))
        # A contract type is read as address.
        contract_typed = {"nodeType": "UserDefinedTypeName", "id": 31,
                          "typeDescriptions": {"typeIdentifier": "t_contract$_C_$2"}}
        public_contract = dict(variable(5, state=True, visibility="public",
                                        type_identifier="t_contract$_C_$2"), typeName=contract_typed)
        self.assertEqual(coverage.scan({"t.sol": unit([public_contract, function(4, [])])}), {})
        state = dict(variable(3, state=True, visibility="public"), typeName=elementary(103, "t_uint256"))
        self.assertEqual(coverage.scan({"t.sol": unit([state, function(4, [])])}), {})
        overriding = dict(state, overrides={"nodeType": "OverrideSpecifier", "id": 104, "overrides": []})
        self.assertEqual({b.feature for b in coverage.scan({"t.sol": unit([overriding, function(4, [])])})[3]},
                         {"overriding state variables"})

    def test_struct_getters_need_the_contracts_structs(self) -> None:
        """A getter of a struct the deployed contract doesn't inherit, such as
        one of a contract deployed beside it, is rejected as the importer
        rejects it."""
        artifact = json.loads((ROOT / "testdata/differential/expected/struct_getters.json").read_text())
        asts = {s: d["ast"] for s, d in artifact["output"]["sources"].items()}
        self.assertEqual(coverage.scan(asts), {})
        (unit_ast,) = asts.values()
        contracts = {n["name"]: n for n in unit_ast["nodes"] if n["nodeType"] == "ContractDefinition"}
        getters = contracts["StructGetters"]
        getters["linearizedBaseContracts"] = [getters["id"]]
        based = next(n for n in getters["nodes"] if n.get("name") == "based")
        self.assertIn(coverage.Blocker("VariableDeclaration", "public state variables", "elaboration"),
                      coverage.scan(asts).get(based["id"], []))

    def test_struct_getters_need_the_structs_in_every_deployment(self) -> None:
        """A base's getter of a struct one deploying contract inherits and
        another doesn't is rejected, as the importer rejects it in the other."""
        def contract(node_id, bases, members):
            return {"nodeType": "ContractDefinition", "id": node_id, "contractKind": "contract",
                    "abstract": False, "baseContracts": [], "linearizedBaseContracts": bases,
                    "nodes": members}

        struct = {"nodeType": "StructDefinition", "id": 11, "name": "S", "scope": 10,
                  "members": [dict(variable(12), typeName={
                      "nodeType": "ElementaryTypeName", "id": 112, "name": "uint256",
                      "typeDescriptions": {"typeIdentifier": "t_uint256"}})]}
        getter = dict(variable(21, state=True, visibility="public", type_identifier="t_struct$_S_$11_storage"),
                      scope=20, typeName={"nodeType": "UserDefinedTypeName", "id": 121, "referencedDeclaration": 11,
                                          "typeDescriptions": {"typeIdentifier": "t_struct$_S_$11_storage_ptr"}})
        # contract C is B, A, where A declares S and B has the getter
        a = {"nodeType": "SourceUnit", "id": 1, "nodes": [
            contract(10, [10], [struct]), contract(20, [20], [getter]), contract(30, [30, 10, 20], [])]}
        rejected = coverage.Blocker("VariableDeclaration", "public state variables", "elaboration")
        self.assertNotIn(rejected, coverage.scan({"a.sol": a}).get(21, []))
        # contract D is B, in another unit
        b = {"nodeType": "SourceUnit", "id": 2, "nodes": [contract(40, [40, 20], [])]}
        self.assertIn(rejected, coverage.scan({"a.sol": a, "b.sol": b}).get(21, []))

    def test_external_calls_to_getters_are_blocked(self) -> None:
        # C(a).x() for the public state variable x of C
        state = dict(variable(3, state=True, visibility="public"),
                     typeName={"nodeType": "ElementaryTypeName", "id": 103, "name": "uint256",
                               "typeDescriptions": {"typeIdentifier": "t_uint256"}})
        address = {"nodeType": "Identifier", "id": 20, "name": "a", "referencedDeclaration": 30,
                   "typeDescriptions": {"typeIdentifier": "t_address"}}
        target = {"nodeType": "FunctionCall", "id": 21, "kind": "typeConversion", "names": [], "tryCall": False,
                  "arguments": [address],
                  "expression": {"nodeType": "Identifier", "id": 22, "name": "C", "referencedDeclaration": 2,
                                 "typeDescriptions": {"typeIdentifier": "t_type$_t_contract$_C_$2_$"}},
                  "typeDescriptions": {"typeIdentifier": "t_contract$_C_$2"}}
        member = {"nodeType": "MemberAccess", "id": 23, "memberName": "x", "referencedDeclaration": 3,
                  "expression": target,
                  "typeDescriptions": {"typeIdentifier": "t_function_external_view$__$returns$_t_uint256_$"}}
        call = {"nodeType": "FunctionCall", "id": 24, "kind": "functionCall", "names": [], "arguments": [], "tryCall": False,
                "expression": member, "typeDescriptions": {"typeIdentifier": "t_uint256"}}
        statement = {"nodeType": "ExpressionStatement", "id": 25, "expression": call}
        found = coverage.scan({"t.sol": unit([state, function(4, [statement])])})
        self.assertIn(coverage.Blocker("MemberAccess", "external calls to getters", "import"), found[23])
        # The same call to the getter of an abstract contract A that is neither
        # deployed nor a base, so the importer reads none of A.
        ast = unit([function(4, [statement])])
        ast["nodes"].insert(0, {
            "nodeType": "ContractDefinition", "id": 50, "contractKind": "contract",
            "abstract": True, "baseContracts": [], "linearizedBaseContracts": [50],
            "nodes": [state]})
        found = coverage.scan({"t.sol": ast})
        self.assertIn(coverage.Blocker("MemberAccess", "external calls to getters", "import"), found[23])


class ClassifyTests(unittest.TestCase):
    def test_preparation_failures_are_not_unsupported_features(self) -> None:
        for status in (coverage.MALFORMED_INPUT, coverage.INVALID_CORE):
            with self.subTest(status=status):
                result = coverage.classify("t.sol", {}, {"status": status, "message": "bad input/core"})
                self.assertEqual(result.category, status)
                self.assertFalse(result.scan_agrees)
                self.assertIsNone(result.first)

    def test_import_rejection_records_first_and_all_blockers(self) -> None:
        ast = unit([dict(variable(3, state=True), constant=True), function(4, [ASSEMBLY])])
        result = coverage.classify(
            "t.sol", coverage.scan({"t.sol": ast}),
            {"status": "import-rejected",
             "message": "VariableDeclaration 3: constants are not supported"})
        self.assertEqual(result.category, coverage.IMPORT_REJECTED)
        self.assertEqual(result.first, coverage.Blocker(
            "VariableDeclaration", "constants", "import"))
        self.assertEqual({b.feature for b in result.blockers},
                         {"constants", "inline assembly"})
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
        ast = unit([dict(variable(3, state=True), constant=True)])
        named = coverage.classify("t.sol", coverage.scan({"t.sol": ast}), {
            "status": "import-rejected",
            "message": "a.sol: VariableDeclaration 3: constants are not supported"})
        self.assertEqual(named.first.feature, "constants")
        self.assertTrue(named.scan_agrees)

    def test_elaboration_rejection_and_admission(self) -> None:
        arrays = unit([function(4, [{
            "nodeType": "VariableDeclarationStatement", "id": 5,
            "declarations": [variable(6, type_identifier="t_array$_t_struct$_S_$3_memory_ptr_$dyn_memory_ptr")],
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
        self.assertEqual(coverage.scan({"t.sol": unit([constant])}), {})
        mapping = dict(constant, typeDescriptions={
            "typeIdentifier": "t_mapping$_t_uint256_$_t_uint256_$"})
        self.assertEqual({b.feature for b in coverage.scan({"t.sol": unit([mapping])})[3]},
                         {"constants"})

    def test_immutables_of_value_type_are_admitted(self) -> None:
        immutable = dict(variable(3, state=True), mutability="immutable")
        self.assertEqual(coverage.scan({"t.sol": unit([immutable])}), {})
        # A contract type is an address.
        contract_typed = dict(immutable, typeDescriptions={
            "typeIdentifier": "t_contract$_C_$2"})
        self.assertEqual(coverage.scan({"t.sol": unit([contract_typed])}), {})
        string_typed = dict(immutable, typeDescriptions={
            "typeIdentifier": "t_string_storage"})
        self.assertIn("immutables", {b.feature for b in
                                     coverage.scan({"t.sol": unit([string_typed])})[3]})

    def test_operations_over_literals_fold_to_integers(self) -> None:
        def literal(node_id, value):
            return {"nodeType": "Literal", "id": node_id, "kind": "number", "value": value,
                    "typeDescriptions": {"typeIdentifier": f"t_rational_{value}_by_1"}}

        def power(node_id, type_identifier):
            return {"nodeType": "BinaryOperation", "id": node_id, "operator": "**",
                    "leftExpression": literal(node_id + 1, "10"),
                    "rightExpression": literal(node_id + 2, "27"),
                    "commonType": {"typeIdentifier": type_identifier},
                    "typeDescriptions": {"typeIdentifier": type_identifier}}

        folded = {"nodeType": "VariableDeclarationStatement", "id": 6,
                  "declarations": [variable(7)],
                  "initialValue": power(10, "t_rational_1000000000000000000000000000_by_1")}
        half = {"nodeType": "VariableDeclarationStatement", "id": 20,
                "declarations": [variable(21)],
                "initialValue": power(30, "t_rational_1_by_2")}
        found = coverage.scan({"t.sol": unit([function(4, [folded, half])])})
        self.assertNotIn(10, found)
        self.assertEqual(found[30], [coverage.Blocker(
            "BinaryOperation", "constant expressions over literals", "elaboration")])
        bytes4 = dict(folded, declarations=[variable(7, type_identifier="t_bytes4")])
        found = coverage.scan({"t.sol": unit([function(4, [bytes4])])})
        self.assertEqual(found[6], [coverage.Blocker(
            "VariableDeclarationStatement", "literals of non-integer types", "elaboration")])

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

    def test_abi_encodings_take_scalars_byte_sequences_and_literals(self) -> None:
        def name(node_id, type_identifier):
            return {"nodeType": "Identifier", "id": node_id, "name": "x", "referencedDeclaration": 3,
                    "typeDescriptions": {"typeIdentifier": type_identifier}}

        def literal(node_id, kind, type_identifier):
            return {"nodeType": "Literal", "id": node_id, "kind": kind, "value": "1", "hexValue": "31",
                    "typeDescriptions": {"typeIdentifier": type_identifier}}

        def call(node_id, member, arguments):
            abi = {"nodeType": "Identifier", "id": node_id + 1, "name": "abi", "referencedDeclaration": -1,
                   "typeDescriptions": {"typeIdentifier": "t_magic_abi"}}
            callee = {"nodeType": "MemberAccess", "id": node_id + 2, "memberName": member, "expression": abi,
                      "typeDescriptions": {"typeIdentifier": "t_function_abiencode_pure$__$returns$__$"}}
            return {"nodeType": "FunctionCall", "id": node_id, "kind": "functionCall", "names": [],
                    "tryCall": False, "expression": callee, "arguments": arguments,
                    "typeDescriptions": {"typeIdentifier": "t_bytes_memory_ptr"}}

        def abi_blockers(statements):
            found = coverage.scan({"t.sol": unit([variable(3, state=True), function(4, statements)])})
            return {node_id for node_id, blockers in found.items()
                    if any(b.feature == "abi.* functions" for b in blockers)}

        admitted = [
            call(10, "encode", [name(20, "t_uint8"), name(21, "t_enum_7"), name(22, "t_bytes_storage_ptr"),
                                literal(23, "number", "t_rational_minus_3_by_1"),
                                literal(24, "string", "t_stringliteral_abcd")]),
            call(30, "encodePacked", [name(40, "t_bytes3"), name(41, "t_string_calldata_ptr"),
                                      literal(42, "string", "t_stringliteral_abcd")]),
            call(50, "encodeWithSelector", [name(60, "t_bytes4"), name(61, "t_address")]),
            call(70, "encodeWithSignature", [literal(80, "string", "t_stringliteral_abcd"), name(81, "t_bool")]),
        ]
        self.assertEqual(abi_blockers(admitted), set())
        rejected = [
            call(100, "encodePacked", [literal(110, "number", "t_rational_1_by_1")]),
            call(120, "encode", [name(130, "t_array$_t_uint256_$dyn_memory_ptr")]),
            call(140, "encodeWithSignature", [name(150, "t_string_memory_ptr")]),
            call(160, "encodeWithSelector", [name(170, "t_bytes32")]),
            call(180, "encodeCall", []),
            call(190, "decode", []),
        ]
        self.assertEqual(abi_blockers(rejected), {110, 130, 140, 160, 180, 190})

    def test_interface_ids_are_admitted_and_other_contract_type_members_blocked(self) -> None:
        def type_member(node_id, member, target=50):
            interface = {"nodeType": "Identifier", "id": node_id + 1, "name": "I",
                         "referencedDeclaration": target,
                         "typeDescriptions": {"typeIdentifier": "t_type$_t_contract$_I_$2"}}
            callee = {"nodeType": "Identifier", "id": node_id + 2, "name": "type",
                      "referencedDeclaration": -27,
                      "typeDescriptions": {"typeIdentifier": "t_function_metatype_pure$__$returns$__$"}}
            call = {"nodeType": "FunctionCall", "id": node_id + 3, "kind": "functionCall", "names": [],
                    "expression": callee, "arguments": [interface],
                    "typeDescriptions": {"typeIdentifier": "t_magic_meta_type_t_contract$_I_$2"}}
            return {"nodeType": "MemberAccess", "id": node_id, "memberName": member, "expression": call,
                    "typeDescriptions": {"typeIdentifier": "t_bytes4"}}

        # An abstract contract has an interfaceId too, which the importer rejects.
        ast = unit([function(4, [type_member(10, "interfaceId"), type_member(20, "name"),
                                 type_member(30, "interfaceId", target=2)])])
        ast["nodes"].append({"nodeType": "ContractDefinition", "id": 50, "contractKind": "interface",
                             "abstract": False, "baseContracts": [],
                             "linearizedBaseContracts": [50], "nodes": []})
        found = coverage.scan({"t.sol": ast})
        self.assertFalse({10, 11, 12, 13} & set(found))
        self.assertEqual(found[21], [coverage.Blocker("Identifier", "type(…)", "import")])
        self.assertEqual(found[31], [coverage.Blocker("Identifier", "type(…)", "import")])

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

    def test_inline_assembly_memory(self) -> None:
        def lit(n):
            return {"nodeType": "YulLiteral", "kind": "number", "value": hex(n)}

        def call(name, *args):
            return {"nodeType": "YulExpressionStatement", "expression": yul_call(name, *args)}

        x = {"nodeType": "YulIdentifier", "name": "x"}
        ok = coverage.assembly_memory_ok
        # scratch written then read in the same block
        self.assertTrue(ok([call("mstore", lit(0), x), call("mstore", lit(0x20), x),
                            call("pop", yul_call("keccak256", lit(0), lit(0x40)))]))
        # scratch read the block did not write, or only partly wrote; the free
        # memory pointer, which the compiler may raise
        self.assertFalse(ok([call("pop", yul_call("mload", lit(0)))]))
        self.assertFalse(ok([call("pop", yul_call("mload", lit(0x40)))]))
        self.assertFalse(ok([call("mstore", lit(1), x), call("log0", lit(0), lit(0x40))]))
        # a write in a nested list covers nothing after it
        self.assertFalse(ok([{"nodeType": "YulIf", "condition": x, "body": {
                                 "nodeType": "YulBlock", "statements": [call("mstore", lit(0), x)]}},
                             call("pop", yul_call("mload", lit(0)))]))
        # writes outside the scratch space only in a block that halts
        self.assertFalse(ok([call("mstore", lit(0x40), x)]))
        self.assertFalse(ok([call("mstore", yul_call("mload", lit(0x40)), x)]))
        self.assertTrue(ok([call("mstore", lit(0x80), x), call("return", lit(0x80), lit(0x20))]))
        found = coverage.assembly_blockers(assembly([call("mstore", lit(0x40), x)]), {})
        self.assertEqual(found, [coverage.Blocker(
            "InlineAssembly", "inline assembly memory outside the scratch space", "elaboration")])

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
            coverage.Blocker("InlineAssembly", "inline assembly calls, gas, return data and code", "elaboration"),
            coverage.Blocker("InlineAssembly", "inline assembly memory references", "elaboration")])
        code = assembly([statement(yul_call("pop", yul_call("codesize")))], [])
        self.assertEqual(coverage.assembly_blockers(code, by_id), [
            coverage.Blocker("InlineAssembly", "inline assembly calls, gas, return data and code", "elaboration")])
        own = assembly([{"nodeType": "YulFunctionDefinition", "name": "gas", "body": {
                            "nodeType": "YulBlock", "statements": [{
                                "nodeType": "YulFunctionDefinition", "name": "inner",
                                "body": {"nodeType": "YulBlock", "statements": []}}]}},
                        statement(yul_call("gas"))],
                       [{"declaration": 5, "suffix": "length"}])
        self.assertEqual(coverage.assembly_blockers(own, by_id),
                         [coverage.Blocker("InlineAssembly", "inline assembly", "import")])
        constant = dict(variable(8, type_identifier="t_uint256"), constant=True)
        self.assertEqual(coverage.assembly_blockers(assembly([], [{"declaration": 8}]), {8: constant}),
                         [coverage.Blocker("InlineAssembly", "inline assembly memory references", "elaboration")])

    def test_inline_assembly_halts_in_constructors(self) -> None:
        stop = assembly([{"nodeType": "YulExpressionStatement", "expression": yul_call("stop")}])
        halts = [coverage.Blocker("InlineAssembly", "inline assembly halts in a constructor", "elaboration")]
        self.assertEqual(coverage.scan({"t.sol": unit([function(4, [stop])])}), {})
        constructor = dict(function(4, [stop]), kind="constructor", stateMutability="nonpayable")
        self.assertEqual(coverage.scan({"t.sol": unit([constructor])}), {20: halts})
        # in a modifier only where a constructor runs it
        modifier = {"nodeType": "ModifierDefinition", "id": 60, "name": "m", "virtual": False,
                    "parameters": {"nodeType": "ParameterList", "id": 61, "parameters": []},
                    "body": {"nodeType": "Block", "id": 63, "statements": [
                        stop, {"nodeType": "PlaceholderStatement", "id": 64}]}}
        invocation = {"nodeType": "ModifierInvocation", "id": 70, "kind": "modifierInvocation",
                      "arguments": [], "modifierName": {"nodeType": "IdentifierPath", "id": 72,
                                                        "name": "m", "referencedDeclaration": 60}}
        self.assertEqual(coverage.scan({"t.sol": unit([modifier, dict(function(4, []), modifiers=[invocation])])}), {})
        constructor = dict(function(4, []), kind="constructor", stateMutability="nonpayable",
                           modifiers=[invocation])
        self.assertEqual(coverage.scan({"t.sol": unit([modifier, constructor])}), {20: halts})

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

    def test_super_calls_reach_overridden_functions(self) -> None:
        def super_call(node_id, declaration):
            base = {"nodeType": "Identifier", "id": node_id + 2, "name": "super",
                    "referencedDeclaration": -24,
                    "typeDescriptions": {"typeIdentifier": "t_type$_t_super$_C$2_$"}}
            callee = {"nodeType": "MemberAccess", "id": node_id + 1, "memberName": "f",
                      "referencedDeclaration": declaration, "expression": base,
                      "typeDescriptions": {"typeIdentifier": "t_function_internal_pure$__$returns$__$"}}
            return {"nodeType": "ExpressionStatement", "id": node_id + 3, "expression": {
                "nodeType": "FunctionCall", "id": node_id, "kind": "functionCall", "names": [], "tryCall": False,
                "arguments": [], "expression": callee,
                "typeDescriptions": {"typeIdentifier": "t_tuple$__$"}}}

        coerced = {"nodeType": "VariableDeclarationStatement", "id": 6,
                   "declarations": [variable(7, type_identifier="t_bytes4")],
                   "initialValue": {"nodeType": "Literal", "id": 8, "kind": "string", "value": "abcd",
                                    "typeDescriptions": {"typeIdentifier": "t_stringliteral_abcd"}}}
        base = {"nodeType": "ContractDefinition", "id": 50, "contractKind": "contract",
                "abstract": False, "baseContracts": [], "linearizedBaseContracts": [50],
                "nodes": [dict(function(60, [coerced]), virtual=True, name="f", scope=50)]}
        derived = dict(function(70, [super_call(90, 60)]), baseFunctions=[60], name="f", scope=2)
        ast = unit([derived])
        ast["nodes"][0]["linearizedBaseContracts"] = [2, 50]
        ast["nodes"].insert(0, base)
        found = coverage.scan({"t.sol": ast})
        self.assertEqual(found, {6: [coverage.Blocker("VariableDeclarationStatement",
                                                      "string literals as fixed-size bytes",
                                                      "elaboration")]})
        derived["body"]["statements"] = []
        self.assertEqual(coverage.scan({"t.sol": ast}), {})
        modifier = {"nodeType": "ModifierDefinition", "id": 80, "name": "m", "virtual": False,
                    "parameters": {"nodeType": "ParameterList", "id": 81, "parameters": []},
                    "body": {"nodeType": "Block", "id": 82, "statements": [
                        super_call(95, 60), {"nodeType": "PlaceholderStatement", "id": 84}]}}
        invocation = {"nodeType": "ModifierInvocation", "id": 85, "kind": "modifierInvocation",
                      "arguments": [],
                      "modifierName": {"nodeType": "IdentifierPath", "id": 86, "name": "m",
                                       "referencedDeclaration": 80}}
        ast["nodes"][1]["nodes"] = [modifier, dict(derived, modifiers=[invocation])]
        self.assertIn(coverage.Blocker("Identifier", "super calls", "import"),
                      coverage.scan({"t.sol": ast})[97])
        specifier = {"nodeType": "ModifierInvocation", "id": 87, "kind": "baseConstructorSpecifier",
                     "arguments": [super_call(100, 60)["expression"]],
                     "modifierName": {"nodeType": "IdentifierPath", "id": 88, "name": "B",
                                      "referencedDeclaration": 50}}
        ast["nodes"][1]["nodes"] = [derived, dict(function(75, []), kind="constructor", scope=2,
                                                  modifiers=[specifier])]
        self.assertIn(coverage.Blocker("Identifier", "super calls", "import"),
                      coverage.scan({"t.sol": ast})[102])

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
        parameter = dict(variable(83, type_identifier="t_struct$_S_$3_calldata_ptr"),
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

    def test_modifiers_are_checked_where_live_functions_invoke_them(self) -> None:
        def string(node_id):
            return {"nodeType": "Literal", "id": node_id, "kind": "string", "value": "abcd",
                    "typeDescriptions": {"typeIdentifier": "t_stringliteral_abcd"}}

        coerced = {"nodeType": "VariableDeclarationStatement", "id": 66,
                   "declarations": [variable(67, type_identifier="t_bytes4")],
                   "initialValue": string(68)}
        modifier = {"nodeType": "ModifierDefinition", "id": 60, "name": "m", "virtual": False,
                    "parameters": {"nodeType": "ParameterList", "id": 61,
                                   "parameters": [variable(62, type_identifier="t_bytes4")]},
                    "body": {"nodeType": "Block", "id": 63, "statements": [
                        coerced, {"nodeType": "PlaceholderStatement", "id": 64}]}}
        invocation = {"nodeType": "ModifierInvocation", "id": 70, "kind": "modifierInvocation",
                      "arguments": [string(71)],
                      "modifierName": {"nodeType": "IdentifierPath", "id": 72, "name": "m",
                                       "referencedDeclaration": 60}}
        feature = "string literals as fixed-size bytes"
        self.assertEqual(coverage.coerced_literals(invocation, {60: modifier}),
                         [coverage.Blocker("ModifierInvocation", feature, "elaboration")])
        self.assertEqual(coverage.scan({"t.sol": unit([modifier, function(4, [])])}), {})
        found = coverage.scan({"t.sol": unit([modifier, dict(function(4, []), modifiers=[invocation])])})
        self.assertEqual(found[66], [coverage.Blocker("VariableDeclarationStatement", feature, "elaboration")])
        self.assertEqual(found[70], [coverage.Blocker("ModifierInvocation", feature, "elaboration")])
        found = coverage.scan({"t.sol": unit([dict(modifier, virtual=True), function(4, [])])})
        self.assertEqual(found[60], [coverage.Blocker("ModifierDefinition", "virtual modifiers", "import")])
        returns = {"nodeType": "ParameterList", "id": 80, "parameters": [variable(81)]}
        assignment = {"nodeType": "Assignment", "id": 82, "operator": "=",
                      "leftHandSide": {"nodeType": "Identifier", "id": 83, "name": "r",
                                       "referencedDeclaration": 81,
                                       "typeDescriptions": {"typeIdentifier": "t_uint256"}},
                      "rightHandSide": {"nodeType": "Literal", "id": 84, "kind": "number", "value": "7",
                                        "typeDescriptions": {"typeIdentifier": "t_rational_7_by_1"}},
                      "typeDescriptions": {"typeIdentifier": "t_uint256"}}
        uses_return = dict(invocation, arguments=[assignment])
        found = coverage.scan({"t.sol": unit([modifier, dict(function(4, []), returnParameters=returns,
                                                              modifiers=[uses_return])])})
        self.assertIn(coverage.Blocker("Identifier", "return variables in modifier arguments", "elaboration"),
                      found[83])
        found = coverage.scan({"t.sol": unit([modifier, dict(function(4, []),
                                                              modifiers=[dict(invocation, kind="other")])])})
        self.assertIn(coverage.Blocker("ModifierInvocation", "modifiers", "import"), found[70])
        static = dict(variable(85, type_identifier="t_array$_t_uint256_$2_memory_ptr"),
                      storageLocation="memory")
        dynamic = dict(variable(86, type_identifier="t_array$_t_uint256_$dyn_memory_ptr"),
                       storageLocation="memory")
        returns = {"nodeType": "ParameterList", "id": 80, "parameters": [static, dynamic]}
        found = coverage.scan({"t.sol": unit([modifier, dict(function(4, []), returnParameters=returns,
                                                              modifiers=[invocation])])})
        self.assertIn(coverage.Blocker("VariableDeclaration", "static memory array returns under modifiers",
                                       "elaboration"), found[85])
        self.assertNotIn(86, found)

    def test_event_array_parameters_are_rejected(self) -> None:
        parameter = variable(6, type_identifier="t_array$_t_uint256_$dyn_memory_ptr")
        self.assertIn("event array parameters",
                      {b.feature for b in coverage.elaboration_blockers(parameter)})

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

    def test_memory_and_calldata_arrays_of_elementary_leaves_decode(self) -> None:
        self.assertTrue(coverage.decodes("t_array$_t_uint8_$dyn_memory_ptr"))
        self.assertTrue(coverage.decodes("t_array$_t_array$_t_bytes_memory_ptr_$2_memory_ptr_$dyn_memory_ptr"))
        self.assertFalse(coverage.decodes("t_array$_t_uint8_$0_memory_ptr"))
        self.assertTrue(coverage.decodes("t_array$_t_uint8_$dyn_calldata_ptr"))
        self.assertTrue(coverage.decodes("t_array$_t_array$_t_uint8_$2_calldata_ptr_$dyn_calldata_ptr"))
        self.assertFalse(coverage.decodes("t_array$_t_array$_t_uint8_$dyn_calldata_ptr_$2_calldata_ptr"))
        self.assertFalse(coverage.decodes("t_array$_t_bytes_calldata_ptr_$2_calldata_ptr"))
        self.assertFalse(coverage.decodes("t_array$_t_struct$_S_$3_memory_ptr_$dyn_memory_ptr"))

    def test_tuples_are_classified_by_a_component(self) -> None:
        self.assertTrue(coverage.decodes("t_tuple$_t_bool_$_t_bytes4_$"))
        self.assertTrue(coverage.decodes("t_tuple$_t_bool_$_t_bytes_memory_ptr_$"))
        self.assertTrue(coverage.decodes("t_tuple$_t_bool_$_t_array$_t_uint8_$dyn_memory_ptr_$"))
        self.assertTrue(coverage.decodes(
            "t_tuple$_t_array$_t_array$_t_uint8_$2_memory_ptr_$dyn_memory_ptr_$_t_uint256_$"))
        self.assertFalse(coverage.decodes("t_tuple$_t_bool_$_t_array$_t_uint8_$dyn_storage_ptr_$"))
        self.assertEqual(coverage.type_feature("t_tuple$_t_bool_$_t_array$_t_uint8_$dyn_storage_ptr_$"),
                         "arrays")
        self.assertEqual(coverage.type_feature("t_bytes32"),
                         "fixed-size bytes members and indexing")

    def test_uninitialized_calldata_locals_are_blocked(self) -> None:
        local = variable(3, type_identifier="t_array$_t_uint256_$dyn_calldata_ptr")
        local["storageLocation"] = "calldata"
        declaration = {"nodeType": "VariableDeclarationStatement", "declarations": [local]}
        self.assertEqual({b.feature for b in coverage.elaboration_blockers(declaration)},
                         {"calldata locals without an initializer"})
        declaration["initialValue"] = {"nodeType": "Identifier", "id": 4}
        self.assertEqual(coverage.elaboration_blockers(declaration), [])

    def test_tuple_assignments_to_elements_are_blocked(self) -> None:
        ident = {"nodeType": "Identifier", "id": 5, "name": "x"}
        element = {"nodeType": "IndexAccess", "id": 6}
        assign = {"nodeType": "Assignment", "operator": "=",
                  "leftHandSide": {"nodeType": "TupleExpression", "isInlineArray": False,
                                   "components": [ident, None]}}
        self.assertEqual(coverage.elaboration_blockers(assign), [])
        assign["leftHandSide"]["components"] = [ident, element]
        self.assertEqual({b.feature for b in coverage.elaboration_blockers(assign)},
                         {"tuple assignments to element or member targets"})

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

    def test_named_arguments_need_a_declared_callee(self) -> None:
        def call(callee, kind="functionCall"):
            return {"nodeType": "FunctionCall", "id": 9, "kind": kind, "names": ["b", "a"],
                    "tryCall": False, "expression": callee, "arguments": []}

        declared = {"nodeType": "Identifier", "id": 5, "name": "f", "referencedDeclaration": 3}
        named = coverage.Blocker("FunctionCall", "named arguments", "import")
        self.assertNotIn(named, coverage.node_blockers(call(declared)))
        parenthesized = {"nodeType": "TupleExpression", "id": 6, "components": [declared],
                         "isInlineArray": False}
        self.assertIn(named, coverage.node_blockers(call(parenthesized)))
        builtin = dict(declared, referencedDeclaration=-8)
        self.assertIn(named, coverage.node_blockers(call(builtin)))
        self.assertIn(named, coverage.node_blockers(call(declared, kind="structConstructorCall")))
        # c.f{value: v}({...}): the callee is the call options' expression.
        member = {"nodeType": "MemberAccess", "id": 7, "memberName": "f", "referencedDeclaration": 3}
        options = {"nodeType": "FunctionCallOptions", "id": 8, "expression": member,
                   "names": ["value"], "options": []}
        self.assertNotIn(named, coverage.node_blockers(call(options)))
        self.assertIn(named, coverage.node_blockers(call(dict(options, expression={
            "nodeType": "NewExpression", "id": 10, "typeName": {"nodeType": "ElementaryTypeName"}}))))
        self.assertIn(named, coverage.node_blockers(call({"nodeType": "NewExpression", "id": 10, "typeName": {"nodeType": "ElementaryTypeName"}})))

    def test_named_arguments_of_events_and_errors_are_taken(self) -> None:
        statement = revert(40, 30, [])
        statement["errorCall"]["names"] = ["a"]
        event = {"nodeType": "EmitStatement", "id": 50, "eventCall": dict(
            statement["errorCall"], id=51, names=["a"],
            expression=dict(statement["errorCall"]["expression"], id=52, name="Ev"))}
        reached = {n["id"]: n for n in (statement, event)}
        _, found = coverage.special_forms(reached, reached)
        self.assertNotIn("named arguments", {b.feature for bs in found.values() for b in bs})

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

    def test_library_functions_are_read_only_where_used(self) -> None:
        """A contract's library calls read the functions they reach, so only
        those must be internal; libraries are not read whole."""
        artifact = json.loads((ROOT / "testdata/differential/expected/using_for.json").read_text())
        asts = {s: d["ast"] for s, d in artifact["output"]["sources"].items()}
        self.assertEqual(coverage.scan(asts), {})
        functions = {n["name"]: n for ast in asts.values() for n in coverage.nodes(ast)
                     if n.get("nodeType") == "FunctionDefinition"}
        functions["twice"]["visibility"] = "public"
        self.assertEqual(coverage.scan(asts), {functions["twice"]["id"]: [coverage.Blocker(
            "FunctionDefinition", "external library functions", "import")]})

    def test_library_modifiers_are_checked_where_library_functions_invoke_them(self) -> None:
        artifact = json.loads((ROOT / "testdata/differential/expected/using_for.json").read_text())
        asts = {s: d["ast"] for s, d in artifact["output"]["sources"].items()}
        modifier = next(n for ast in asts.values() for n in coverage.nodes(ast)
                        if n.get("nodeType") == "ModifierDefinition" and n["name"] == "nonZero")
        code = dict(assembly([{"nodeType": "YulExpressionStatement",
                               "expression": yul_call("pop", yul_call("codesize"))}]), id=999999)
        modifier["body"]["statements"].insert(0, code)
        self.assertIn(999999, coverage.scan(asts))

    def test_using_directives_of_reached_libraries_are_read(self) -> None:
        artifact = json.loads((ROOT / "testdata/differential/expected/using_for.json").read_text())
        asts = {s: d["ast"] for s, d in artifact["output"]["sources"].items()}
        arith = next(n for ast in asts.values() for n in coverage.nodes(ast)
                     if n.get("nodeType") == "ContractDefinition" and n["name"] == "Arith")
        directive = {"nodeType": "UsingForDirective", "id": 999998, "global": False,
                     "functionList": [], "typeName": None}
        arith["nodes"].append(directive)
        self.assertEqual(coverage.scan(asts), {999998: [coverage.Blocker(
            "UsingForDirective", "using for with functions", "import")]})

    def test_using_directives_of_other_files_are_read(self) -> None:
        artifact = json.loads((ROOT / "testdata/differential/expected/using_for.json").read_text())
        asts = {s: d["ast"] for s, d in artifact["output"]["sources"].items()}
        (unit,) = asts.values()
        arith = next(n for n in unit["nodes"] if n.get("name") == "Arith")
        unit["nodes"].remove(arith)
        other = {"nodeType": "SourceUnit", "id": 999990, "absolutePath": "arith.sol",
                 "nodes": [arith]}
        asts["arith.sol"] = other
        # A file deploying no contract is a blocker of its own; the directive adds one.
        alone = coverage.scan(asts)
        self.assertEqual(set(alone), {999990})
        other["nodes"].append({"nodeType": "UsingForDirective", "id": 999998, "global": False,
                               "functionList": [], "typeName": None})
        self.assertEqual(coverage.scan(asts), alone | {999998: [coverage.Blocker(
            "UsingForDirective", "using for with functions", "import")]})

    def test_bound_calls_copying_their_receiver_are_blocked(self) -> None:
        artifact = json.loads((ROOT / "testdata/differential/expected/using_for.json").read_text())
        asts = {s: d["ast"] for s, d in artifact["output"]["sources"].items()}
        fill = next(n for ast in asts.values() for n in coverage.nodes(ast)
                    if n.get("nodeType") == "MemberAccess" and n.get("memberName") == "fill")
        fill["expression"]["typeDescriptions"]["typeIdentifier"] = \
            "t_array$_t_uint256_$dyn_storage_ptr"
        # The importer rejects the call, where the copy happens.
        call = next(n for ast in asts.values() for n in coverage.nodes(ast)
                    if n.get("nodeType") == "FunctionCall" and n["expression"] is fill)
        self.assertEqual(coverage.scan(asts), {call["id"]: [coverage.Blocker(
            "FunctionCall", "bound calls copying their receiver", "import")]})

    def test_overloads_differing_only_in_contract_types_are_blocked(self) -> None:
        def overload(node_id, type_identifier):
            parameter = variable(node_id + 1, type_identifier=type_identifier)
            return dict(function(node_id, []), name="f", parameters={
                "nodeType": "ParameterList", "id": node_id + 100, "parameters": [parameter]})

        blocker = coverage.Blocker("FunctionDefinition", "overloads differing only in contract types", "import")
        found = coverage.scan({"t.sol": unit([overload(4, "t_contract$_C_$2"), overload(10, "t_address")])})
        self.assertEqual((found[4], found[10]), ([blocker], [blocker]))
        self.assertEqual(coverage.scan({"t.sol": unit([overload(4, "t_contract$_C_$2"),
                                                       overload(10, "t_uint256")])}), {})
        # Constructors and declarations are never matched by parameter types.
        constructors = [dict(overload(i, t), name="", kind="constructor")
                        for i, t in ((4, "t_contract$_C_$2"), (10, "t_address"))]
        self.assertNotIn(4, coverage.scan({"t.sol": unit(constructors)}))
        declared = dict(overload(4, "t_contract$_C_$2"), implemented=False, body=None)
        self.assertEqual(coverage.scan({"t.sol": unit([declared, overload(10, "t_address")])}), {})

    def test_contract_creation_is_blocked_at_the_call(self) -> None:
        new = {"nodeType": "NewExpression", "id": 21,
               "typeName": {"nodeType": "UserDefinedTypeName", "id": 22,
                            "typeDescriptions": {"typeIdentifier": "t_contract$_C_$2"}},
               "typeDescriptions": {"typeIdentifier": "t_function_creation_nonpayable$__$returns$_t_contract$_C_$2_$"}}
        call = {"nodeType": "FunctionCall", "id": 20, "kind": "functionCall", "names": [],
                "tryCall": False, "expression": new, "arguments": [],
                "typeDescriptions": {"typeIdentifier": "t_contract$_C_$2"}}
        statement = {"nodeType": "ExpressionStatement", "id": 6, "expression": call}
        found = coverage.scan({"t.sol": unit([function(4, [statement])])})
        self.assertIn("contract creation (new C)", {b.feature for b in found[20]})
        self.assertNotIn(21, found)

    def test_bound_call_receivers_are_coerced_to_the_first_parameter(self) -> None:
        artifact = json.loads((ROOT / "testdata/differential/expected/using_for.json").read_text())
        asts = {s: d["ast"] for s, d in artifact["output"]["sources"].items()}
        by_id = {n["id"]: n for ast in asts.values() for n in coverage.nodes(ast)}
        # uint256(3).addBonus(4), made ("abc").addBonus(4) with addBonus taking bytes32 first
        member, call = next((n["expression"], n) for n in by_id.values()
                            if n.get("nodeType") == "FunctionCall"
                            and n["expression"].get("memberName") == "addBonus"
                            and n["expression"]["expression"].get("nodeType") == "FunctionCall")
        member["expression"] = {"nodeType": "Literal", "id": 999997, "kind": "string",
                                "value": "abc", "subdenomination": None,
                                "typeDescriptions": {"typeIdentifier": "t_stringliteral_abc"}}
        target = by_id[member["referencedDeclaration"]]
        target["parameters"]["parameters"][0]["typeDescriptions"]["typeIdentifier"] = "t_bytes32"
        self.assertIn(coverage.Blocker("FunctionCall", "string literals as fixed-size bytes",
                                       "elaboration"), coverage.scan(asts).get(call["id"], []))

    def test_enums_are_admitted(self) -> None:
        artifact = json.loads((ROOT / "testdata/differential/expected/enums.json").read_text())
        asts = {s: d["ast"] for s, d in artifact["output"]["sources"].items()}
        self.assertEqual(coverage.scan(asts), {})

    def test_enum_mapping_keys_are_blocked(self) -> None:
        artifact = json.loads((ROOT / "testdata/differential/expected/enums.json").read_text())
        asts = {s: d["ast"] for s, d in artifact["output"]["sources"].items()}
        statuses = next(n for ast in asts.values() for n in coverage.nodes(ast)
                        if n.get("nodeType") == "VariableDeclaration" and n.get("name") == "statuses")
        enum = statuses["typeName"]["valueType"]["typeDescriptions"]["typeIdentifier"]
        statuses["typeDescriptions"]["typeIdentifier"] = f"t_mapping$_{enum}_$_t_uint256_$"
        self.assertIn(coverage.Blocker("VariableDeclaration", "enum mapping keys", "elaboration"),
                      coverage.scan(asts)[statuses["id"]])

    def test_enums_returned_by_external_calls_are_blocked(self) -> None:
        artifact = json.loads((ROOT / "testdata/differential/expected/contract_types.json").read_text())
        asts = {s: d["ast"] for s, d in artifact["output"]["sources"].items()}
        by_id = {n["id"]: n for ast in asts.values() for n in coverage.nodes(ast)}
        balance_of = next(n for n in by_id.values() if n.get("nodeType") == "FunctionDefinition"
                          and n.get("name") == "balanceOf")
        balance_of["returnParameters"]["parameters"][0]["typeDescriptions"]["typeIdentifier"] = \
            "t_enum$_E_$1"
        calls = {n["id"] for n in by_id.values() if n.get("nodeType") == "FunctionCall"
                 and n["expression"].get("referencedDeclaration") == balance_of["id"]}
        found = coverage.scan(asts)
        self.assertTrue(calls)
        for call in calls:
            self.assertIn(coverage.Blocker("FunctionCall", "enums returned by external calls",
                                           "elaboration"), found[call])

    def test_enum_types_as_expressions_are_blocked(self) -> None:
        artifact = json.loads((ROOT / "testdata/differential/expected/enums.json").read_text())
        asts = {s: d["ast"] for s, d in artifact["output"]["sources"].items()}
        by_id = {n["id"]: n for ast in asts.values() for n in coverage.nodes(ast)}
        # Rounding.divide(a, b, Rounding.Mode.Ceil), made Rounding.divide(a, b, Rounding.Mode)
        call = next(n for n in by_id.values() if n.get("nodeType") == "FunctionCall"
                    and n["expression"].get("memberName") == "divide")
        mode = call["arguments"][2]["expression"]
        call["arguments"][2] = mode
        self.assertIn(coverage.Blocker("MemberAccess", "enum types as expressions", "elaboration"),
                      coverage.scan(asts).get(mode["id"], []))

    def test_selectors_of_computed_values_are_blocked(self) -> None:
        artifact = json.loads((ROOT / "testdata/differential/expected/hashes.json").read_text())
        asts = {s: d["ast"] for s, d in artifact["output"]["sources"].items()}
        by_id = {n["id"]: n for ast in asts.values() for n in coverage.nodes(ast)}
        # this.ofBytes.selector, made (this).ofBytes.selector: a base the importer
        # does not read as a name
        selector = next(n for n in by_id.values() if n.get("nodeType") == "MemberAccess"
                        and n["memberName"] == "selector"
                        and n["expression"].get("memberName") == "ofBytes")
        this = selector["expression"]["expression"]
        selector["expression"]["expression"] = {
            "nodeType": "TupleExpression", "id": 10 ** 6, "components": [this],
            "isInlineArray": False, "typeDescriptions": this["typeDescriptions"]}
        self.assertIsNone(coverage.selector_declaration(selector, by_id))
        self.assertIn(selector["id"], coverage.scan(asts))

    def test_selectors_through_variables_are_blocked(self) -> None:
        artifact = json.loads((ROOT / "testdata/differential/expected/hashes.json").read_text())
        asts = {s: d["ast"] for s, d in artifact["output"]["sources"].items()}
        by_id = {n["id"]: n for ast in asts.values() for n in coverage.nodes(ast)}
        # IReceiver.onReceived.selector, made r.onReceived.selector for a
        # contract-typed variable r, which the compiler evaluates
        selector = next(n for n in by_id.values() if n.get("nodeType") == "MemberAccess"
                        and n["memberName"] == "selector"
                        and n["expression"].get("memberName") == "onReceived")
        receiver = selector["expression"]["expression"]
        self.assertIsNotNone(coverage.selector_declaration(selector, by_id))
        receiver["typeDescriptions"]["typeIdentifier"] = "t_contract$_IReceiver_$1"
        self.assertIsNone(coverage.selector_declaration(selector, by_id))

    def test_conditionals_of_values_and_memory_only(self) -> None:
        def blockers(tid: str) -> list[tuple[str, str]]:
            node = {"nodeType": "Conditional", "typeDescriptions": {"typeIdentifier": tid}}
            return [(b.feature, b.stage) for b in
                    coverage.node_blockers(node) + coverage.elaboration_blockers(node)]
        for tid in ("t_uint16", "t_bool", "t_string_memory_ptr", "t_array$_t_uint256_$dyn_memory_ptr"):
            self.assertEqual(blockers(tid), [], tid)
        for tid in ("t_tuple$__$", "t_tuple$_t_uint256_$_t_uint256_$", "t_function_internal_pure$__$returns$__$",
                    "t_bytes_storage", "t_bytes_storage_ptr", "t_array$_t_uint256_$dyn_calldata_ptr",
                    "t_mapping$_t_uint256_$_t_uint256_$", "t_struct$_S_$5_memory_ptr"):
            self.assertEqual(blockers(tid), [("conditional expressions", "elaboration")], tid)

    def test_state_variable_selectors_only_through_this(self) -> None:
        artifact = json.loads((ROOT / "testdata/differential/expected/hashes.json").read_text())
        asts = {s: d["ast"] for s, d in artifact["output"]["sources"].items()}
        by_id = {n["id"]: n for ast in asts.values() for n in coverage.nodes(ast)}
        def selector_of(member: str) -> dict:
            return next(n for n in by_id.values() if n.get("nodeType") == "MemberAccess"
                        and n["memberName"] == "selector"
                        and n["expression"].get("memberName", n["expression"].get("name")) == member)
        total = next(n["id"] for n in by_id.values()
                     if n.get("nodeType") == "VariableDeclaration" and n["name"] == "total")
        getter = selector_of("total")
        self.assertIsNotNone(coverage.selector_declaration(getter, by_id))
        # C.total.selector is the selector of the value total holds
        getter["expression"]["expression"].update(
            referencedDeclaration=1, typeDescriptions={"typeIdentifier": "t_type$_t_contract$_Hashes_$1"})
        self.assertIsNone(coverage.selector_declaration(getter, by_id))
        # so is total.selector
        named = selector_of("Denied")
        self.assertIsNotNone(coverage.selector_declaration(named, by_id))
        named["expression"]["referencedDeclaration"] = total
        self.assertIsNone(coverage.selector_declaration(named, by_id))

    def test_enum_storage_arrays_are_not_values(self) -> None:
        self.assertFalse(coverage.storage_array("t_array$_t_enum_5_$dyn_storage"))
        self.assertFalse(coverage.storage_array_value("t_array$_t_enum_5_$dyn_storage"))

    def test_enum_type_identifiers_are_read_by_id(self) -> None:
        self.assertEqual(coverage.normalize_type_ids(
            {"typeIdentifier": "t_mapping$_t_address_$_t_enum$_S_$5_$"}),
            {"typeIdentifier": "t_mapping$_t_address_$_t_enum_5_$"})
        # A type expression keeps its enum's name, as the importer reads its callee.
        self.assertEqual(coverage.normalize_type_ids({"typeIdentifier": "t_type$_t_enum$_S_$5_$"}),
                         {"typeIdentifier": "t_type$_t_enum$_S_$5_$"})
        self.assertTrue(coverage.storage_type_supported("t_array$_t_enum_5_$dyn_storage"))
        self.assertFalse(coverage.located_array("t_array$_t_enum_5_$dyn_memory_ptr"))

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
                 "message": "VariableDeclaration 3: constants are not supported"})

        report = coverage.Report("pin", "profile", [
            rejected("a.sol", [dict(variable(3, state=True), constant=True), function(4, [])]),
            rejected("b.sol", [dict(variable(3, state=True), constant=True), function(4, [ASSEMBLY])]),
        ])
        ranking = {f["feature"]: f for f in report.feature_ranking()}
        self.assertEqual(ranking["constants"]["tests"], 2)
        self.assertEqual(ranking["constants"]["only_blocker"], 1)
        self.assertEqual(ranking["constants"]["first_rejection"], 2)
        self.assertEqual(ranking["inline assembly"]["only_blocker"], 0)
        self.assertEqual(report.greedy_order(5), [("constants", 1), ("inline assembly", 2)])


if __name__ == "__main__":
    unittest.main()
