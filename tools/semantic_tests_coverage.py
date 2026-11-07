#!/usr/bin/env python3
"""Report how much of solc's semantic test corpus the semantics admits.

Every test under test/libsolidity/semanticTests of a solidity checkout at
SOLIDITY_PIN is compiled with the pinned compiler and profile, then imported
(syntax/solidityImportLib.sml) and elaborated (elaborate_unit) in HOL by
tools/semantic_tests_coverage.sml. Each test is classified as skipped by its
own settings, a compile failure, an importer rejection, an elaborator
rejection, partially admitted (the unit is admitted with some of its functions
unsupported) or admitted (every function supported). Admitted and partially
admitted tests also count their functions and the reasons of the unsupported
ones. The tests' call expectations are not run.

The importer stops at its first rejection. To rank features by how many tests
they block, and by how many they alone block, this tool also scans each AST
for every construct outside the importer's vocabulary. The scan restates the
importer's checks; the report counts every test where the scan disagrees with
the importer, so drift between the two shows up rather than skewing the
ranking.
"""

from __future__ import annotations

import argparse
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass, field
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
from typing import Any, Callable, Iterator

import export_solc_artifacts as exporter

ROOT = Path(__file__).resolve().parents[1]
TESTS_DIR = Path("test/libsolidity/semanticTests")
HOL_SCRIPT = ROOT / "tools" / "semantic_tests_coverage.sml"
REPORT_FORMAT = "solidity-hol-semantic-tests-coverage-v1"
RESULT_PREFIX = "coverage-result: "

SOURCE_MARKER = re.compile(r"^==== (Source|ExternalSource): (.*) ====\s*$")
SETTING = re.compile(r"^//\s*([A-Za-z][A-Za-z0-9]*)\s*:\s*(.*?)\s*$")
EVM_VERSIONS = [
    "homestead", "tangerineWhistle", "spuriousDragon", "byzantium", "constantinople",
    "petersburg", "istanbul", "berlin", "london", "paris", "shanghai", "cancun",
    "prague", "osaka", "amsterdam", "@future",
]
IMPORT_ERROR_NODE = re.compile(r"^(?:.*?: )?([A-Za-z]+) ([0-9]+): (.*)$", re.S)

SKIPPED = "skipped"
COMPILE_FAILURE = "compile-failure"
IMPORT_REJECTED = "import-rejected"
ELABORATION_REJECTED = "elaboration-rejected"
ADMITTED = "admitted"
PARTIALLY_ADMITTED = "partially-admitted"
MALFORMED_INPUT = "malformed-input"
INVALID_CORE = "invalid-core"
SOURCE_REJECTED = "source-rejected"
GREEDY_STEPS = 20
CATEGORIES = [ADMITTED, PARTIALLY_ADMITTED, ELABORATION_REJECTED, IMPORT_REJECTED, COMPILE_FAILURE,
              MALFORMED_INPUT, SOURCE_REJECTED, INVALID_CORE, SKIPPED]


class TestFormatError(Exception):
    pass


# Test files


@dataclass
class SemanticTest:
    """A test file: its sources, by Standard JSON name, and its settings."""

    name: str
    sources: dict[str, str]
    settings: dict[str, str]


def read_test(tests_root: Path, path: Path) -> SemanticTest:
    """Parse a test as solc's TestCaseReader does: `==== Source: name ====` and
    `==== ExternalSource: [name=]path ====` markers split the sources, and the
    `// key: value` lines between `// ====` and `// ----` are its settings."""
    name = path.relative_to(tests_root).as_posix()
    sources: dict[str, list[str]] = {}
    current = name
    settings: dict[str, str] = {}
    in_settings = False
    for line in path.read_text(encoding="utf-8").splitlines(keepends=True):
        stripped = line.rstrip("\r\n")
        marker = SOURCE_MARKER.match(stripped)
        if marker is not None:
            kind, spec = marker.groups()
            if kind == "Source":
                current = spec
                sources[current] = []
            else:
                source_name, _, external = (part.strip() for part in spec.partition("="))
                external = external or source_name
                external_path = Path(os.path.normpath(path.parent / external))
                sources[source_name] = [external_path.read_text(encoding="utf-8")]
            continue
        if stripped.startswith("// ----"):
            break
        if stripped.startswith("// ===="):
            in_settings = True
        elif in_settings:
            setting = SETTING.match(stripped)
            if setting is None:
                raise TestFormatError(f"{name}: malformed setting {stripped!r}")
            settings[setting.group(1)] = setting.group(2)
        else:
            sources.setdefault(current, []).append(line)
    return SemanticTest(name, {k: "".join(v) for k, v in sources.items()}, settings)


def find_tests(tests_root: Path) -> list[Path]:
    """Test files, without the directories starting with `_` that hold
    external sources, which isoltest does not run either."""
    return sorted(
        path for path in tests_root.rglob("*.sol")
        if not any(part.startswith("_") for part in path.relative_to(tests_root).parts)
    )


def evm_version_admits(requirement: str, version: str) -> bool:
    """Whether `version` meets an `EVMVersion` setting such as `>=cancun`."""
    if requirement == "any":
        return True
    match = re.fullmatch(r"([<>=!]*)(.*)", requirement)
    assert match is not None
    comparator, required = match.groups()
    if required not in EVM_VERSIONS:
        raise TestFormatError(f"unknown EVM version {required!r}")
    a, b = EVM_VERSIONS.index(version), EVM_VERSIONS.index(required)
    comparisons = {">": a > b, ">=": a >= b, "<": a < b, "<=": a <= b, "=": a == b, "!": a != b}
    if comparator not in comparisons:
        raise TestFormatError(f"unknown EVM version comparator {comparator!r}")
    return comparisons[comparator]


def skip_reason(test: SemanticTest, profile: dict[str, Any]) -> str | None:
    """Why the test's own settings exclude it from the via-IR profile, if
    they do."""
    settings = test.settings
    if settings.get("compileViaYul", "also") == "false":
        return "legacy pipeline only (compileViaYul: false)"
    evm = settings.get("EVMVersion", "any")
    if not evm_version_admits(evm, profile["settings"]["evmVersion"]):
        return f"EVM version (EVMVersion: {evm})"
    revert_strings = settings.get("revertStrings", "default")
    if revert_strings != profile["settings"]["debug"]["revertStrings"]:
        return f"revert strings (revertStrings: {revert_strings})"
    return None


# Compilation


def compile_test(solc: Path, test: SemanticTest, profile_path: Path) -> dict[str, Any]:
    """Full compiler artifact; shared HOL preparation checks its provenance."""
    return exporter.build_artifact_from_sources(solc, test.sources, profile_path)


# The scan


@dataclass(frozen=True)
class Blocker:
    """A construct the semantics does not support: the AST node's type, the
    feature it belongs to, and the stage that rejects it, the importer
    ("import") or the elaborator ("elaboration")."""

    node_type: str
    feature: str
    stage: str


EXPRESSIONS = {
    "Identifier", "Literal", "UnaryOperation", "BinaryOperation", "Assignment",
    "TupleExpression", "FunctionCall", "IndexAccess", "Conditional",
}
STATEMENTS = {
    "Block", "UncheckedBlock", "ExpressionStatement", "VariableDeclarationStatement",
    "IfStatement", "WhileStatement", "DoWhileStatement", "ForStatement", "Break",
    "Continue", "Return", "EmitStatement", "RevertStatement", "InlineAssembly",
    "PlaceholderStatement",
}
# Nodes the importer reads only in a fixed position, checked there, and nodes
# it never reaches because it rejects their parents (IdentifierPath) or never
# reads the field holding them (StructuredDocumentation, base and override
# names, which it takes from the linearization and baseFunctions).
STRUCTURAL = {
    "SourceUnit", "PragmaDirective", "ImportDirective", "ContractDefinition",
    "FunctionDefinition", "ParameterList", "VariableDeclaration", "ElementaryTypeName",
    "ElementaryTypeNameExpression", "IdentifierPath", "StructuredDocumentation", "Mapping",
    "StructDefinition", "EventDefinition", "ErrorDefinition", "InheritanceSpecifier",
    "OverrideSpecifier", "ModifierDefinition", "ModifierInvocation", "EnumDefinition",
    "EnumValue",
}
FEATURES = {
    "FunctionTypeName": "function types",
    "IndexRangeAccess": "array slices",
    "TryCatchClause": "try/catch",
    "TryStatement": "try/catch",
    "UserDefinedValueTypeDefinition": "user-defined value types",
}
FUNCTION_KINDS = {"function", "constructor", "receive", "fallback"}
# By the leading part of a type identifier.
TYPE_FEATURES = [
    ("t_magic_message", "msg/block/tx globals"),
    ("t_magic_block", "msg/block/tx globals"),
    ("t_magic_transaction", "msg/block/tx globals"),
    ("t_magic_abi", "abi.* functions"),
    ("t_magic_meta_type", "type(…)"),
    ("t_type$_t_enum", "enums"),
    ("t_type$_t_struct", "structs"),
    ("t_type$_t_userDefinedValueType", "user-defined value types"),
    ("t_type$_t_contract", "library calls and contract-name members"),
    ("t_type$_t_super", "super calls"),
    ("t_type$_t_bytes_", "bytes.concat and string.concat"),
    ("t_type$_t_string", "bytes.concat and string.concat"),
    ("t_type$_t_array", "arrays"),
    ("t_type", "members of elementary type names"),
    ("t_struct", "structs"),
    ("t_enum", "enums"),
    ("t_userDefinedValueType", "user-defined value types"),
    ("t_mapping", "mappings"),
    ("t_array", "arrays"),
    ("t_bytes_", "bytes and string"),
    ("t_bytes", "fixed-size bytes members and indexing"),
    ("t_string", "bytes and string"),
    ("t_contract", "external calls and contract members"),
    ("t_super", "super calls"),
    ("t_address", "address members (balance, call, transfer, …)"),
    ("t_function_event", "events"),
    ("t_function_error", "custom errors"),
    ("t_error", "custom errors"),
    ("t_function", "function members (selector, address, …)"),
    ("t_module", "imports"),
    ("t_uint", "using for"),
    ("t_int", "using for"),
    ("t_bool", "using for"),
    ("t_rational", "using for"),
]
BUILTINS = {
    "msg": "msg/block/tx globals", "block": "msg/block/tx globals",
    "tx": "msg/block/tx globals", "abi": "abi.* functions", "type": "type(…)",
    "require": "require/assert/revert", "assert": "require/assert/revert",
    "revert": "require/assert/revert", "this": "this", "super": "super calls",
    "keccak256": "hash and signature built-ins", "sha256": "hash and signature built-ins",
    "ripemd160": "hash and signature built-ins", "ecrecover": "hash and signature built-ins",
}
# The members of msg, tx and block, by the built-in declaration ids of the
# pinned compiler (environment_field in solidityImportLib).
ENVIRONMENT = {
    -15: {"sender", "value", "data"},
    -26: {"origin", "gasprice"},
    -4: {"number", "timestamp", "chainid", "coinbase", "basefee", "gaslimit"},
}
# require, assert and revert.
REQUIRE, ASSERT, REVERT = -18, -3, -19
KECCAK256 = -8
ABI = -1
# The field holding the selector the compiler records on each kind of
# declaration that has one.
SELECTOR_FIELDS = {"FunctionDefinition": "functionSelector", "EventDefinition": "eventSelector",
                   "ErrorDefinition": "errorSelector", "VariableDeclaration": "functionSelector"}
THIS = -28
STRING_LITERALS = {"string", "unicodeString", "hexString"}


def type_feature(type_identifier: str | None) -> str:
    """The feature a type needs, classifying a tuple by its first component
    outside the elementary types."""
    if (type_identifier or "").startswith("t_tuple$_"):
        if "$__$" in type_identifier:
            return "tuples with empty components"
        for component in type_identifier[len("t_tuple$_"):].split("_$_"):
            component = component.removesuffix("_$")
            if component.startswith("t_tuple"):
                return "nested tuples"
            if not decodes_component(component):
                return type_feature(component)
    if (type_identifier or "").startswith("t_mapping$_t_enum_"):
        return "enum mapping keys"
    for prefix, feature in TYPE_FEATURES:
        if (type_identifier or "").startswith(prefix):
            return feature
    return f"values of type {type_identifier}"


def nodes(value: Any, *, skip: Callable[[dict[str, Any]], bool] = lambda _: False
          ) -> Iterator[dict[str, Any]]:
    """Every Solidity AST node under `value`, in document order, leaving out
    the subtrees of the nodes `skip` holds. The Yul nodes of inline assembly,
    which have no id, are left out, and so are storage layout specifiers,
    which the importer does not read."""
    if isinstance(value, dict):
        if value.get("nodeType") == "StorageLayoutSpecifier":
            return
        if "nodeType" in value and "id" in value:
            if skip(value):
                return
            yield value
        for key, child in value.items():
            if value.get("nodeType") == "ArrayTypeName" and key == "length":
                continue
            yield from nodes(child, skip=skip)
    elif isinstance(value, list):
        for child in value:
            yield from nodes(child, skip=skip)


def deployable(unit: dict[str, Any]) -> list[dict[str, Any]]:
    """The contracts a source unit is imported as: those that are neither
    interfaces, libraries, abstract nor a base of another contract of the
    unit."""
    contracts = [m for m in unit["nodes"] if m["nodeType"] == "ContractDefinition"]
    inherited = {b for c in contracts for b in c["linearizedBaseContracts"][1:]}
    return [c for c in contracts if c["contractKind"] == "contract" and not c["abstract"]
            and c["id"] not in inherited]


def library_members(by_id: dict[int, dict[str, Any]]) -> dict[int, dict[str, Any]]:
    """The members of the compilation's libraries, by id."""
    return {m["id"]: m for n in by_id.values()
            if n["nodeType"] == "ContractDefinition" and n["contractKind"] == "library"
            for m in n["nodes"]}


def imported(asts: dict[str, Any], by_id: dict[int, dict[str, Any]]) -> list[dict[str, Any]]:
    """The parts of the compilation the importer reads, as subtrees: each
    unit's members other than pragmas, imports, file-level structs and errors,
    interfaces, libraries and contracts imported only as bases; the bases of
    the contracts imported; the file-level structs, library members other
    than errors and external function parameters those refer to, library
    members only from the functions calls can reach; and the parameters of
    the errors their revert statements name."""
    roots: list[dict[str, Any]] = []
    for ast in asts.values():
        contracts = {c["id"] for c in deployable(ast)}
        for member in ast["nodes"]:
            kind = member["nodeType"]
            if kind in {"PragmaDirective", "ImportDirective", "StructDefinition",
                        "ErrorDefinition"}:
                continue
            if kind == "ContractDefinition":
                if member["id"] in contracts:
                    roots.extend(by_id[b] for b in member["linearizedBaseContracts"] if b in by_id)
                continue
            roots.append(member)
    # Structs are found from every reference, read or not, as the importer
    # finds them from the whole of each base.
    members = library_members(by_id)
    based, live = live_functions(asts, by_id)
    unreachable = {n["id"] for f in based - live for n in nodes(by_id[f])}
    # Nor the modifiers of the bases that no live function invokes.
    invoked = {m["modifierName"].get("referencedDeclaration")
               for f in live for m in by_id[f].get("modifiers", [])}
    unreachable.update(n["id"] for m in by_id.values()
                       if m["nodeType"] == "ModifierDefinition" and m["id"] not in members
                       and m["id"] not in invoked for n in nodes(m))
    seen: set[int] = set()
    rooted = {root["id"] for root in roots}

    def add(root: dict[str, Any]) -> None:
        if root["id"] not in rooted:
            rooted.add(root["id"])
            roots.append(root)
            pending.append(root)

    pending = list(roots)
    while pending:
        # A selector's base is not imported.
        for node in nodes(pending.pop(), skip=is_selector):
            if node["id"] in seen:
                continue
            seen.add(node["id"])
            for _, signature in signatures(node, by_id):
                add(signature)
            target = by_id.get(node.get("referencedDeclaration"))
            if (target is not None and target["nodeType"] == "StructDefinition"
                    and by_id.get(target.get("scope"), {}).get("nodeType") == "SourceUnit"):
                add(target)
            elif (target is not None and target["id"] in members
                  and target["nodeType"] != "ErrorDefinition" and node["id"] not in unreachable):
                add(target)
                # The using directives of a library whose functions run.
                if target["nodeType"] == "FunctionDefinition":
                    for directive in by_id[target["scope"]]["nodes"]:
                        if directive["nodeType"] == "UsingForDirective":
                            add(directive)
    return roots


def signatures(node: dict[str, Any], by_id: dict[int, dict[str, Any]]
               ) -> list[tuple[dict[str, Any], dict[str, Any]]]:
    """The parameter lists the importer reads at a node, with their
    declarations: those of the error a revert names, and those of an
    external function a call calls through a member access."""
    if node["nodeType"] == "RevertStatement":
        error = by_id.get(node["errorCall"]["expression"].get("referencedDeclaration"))
        return [] if error is None else [(error, error["parameters"])]
    if node["nodeType"] != "FunctionCall":
        return []
    callee = node["expression"]
    if callee["nodeType"] == "FunctionCallOptions":
        callee = callee["expression"]
    target = by_id.get(callee.get("referencedDeclaration"))
    if (target is not None and target["nodeType"] == "FunctionDefinition"
            and callee["nodeType"] == "MemberAccess" and is_external(callee)):
        return [(target, target["parameters"]), (target, target["returnParameters"])]
    return []


def read(node: dict[str, Any]) -> bool:
    """Whether the importer reads a node within an imported contract: not the
    declarations without a body, which only calls refer to, nor errors, whose
    parameters it reads only where a revert statement names them."""
    return not ((node["nodeType"] == "FunctionDefinition" and not node["implemented"])
                or node["nodeType"] == "ErrorDefinition")


def overridden(functions: list[dict[str, Any]], by_id: dict[int, dict[str, Any]]) -> set[int]:
    """The functions some other function overrides, directly or through the
    functions it overrides: those valid_src_unit and elaborate_unit leave
    out, as no call or dispatch reaches them."""
    found: set[int] = set()
    pending = [b for f in functions for b in f.get("baseFunctions", [])]
    while pending:
        base = pending.pop()
        if base not in found:
            found.add(base)
            pending.extend(by_id.get(base, {}).get("baseFunctions", []))
    return found


def super_callee(node: dict[str, Any]) -> bool:
    """Whether a node is super.f called as a function."""
    callee = node.get("expression") or {}
    return (node["nodeType"] == "FunctionCall" and node["kind"] == "functionCall"
            and callee["nodeType"] == "MemberAccess"
            and callee["expression"]["nodeType"] == "Identifier"
            and (callee["expression"]["typeDescriptions"].get("typeIdentifier") or ""
                 ).startswith("t_type$_t_super"))


def super_calls(function: dict[str, Any]) -> list[dict[str, Any]]:
    """The super calls the importer admits in a function: those in its body and
    in its modifier invocations' arguments."""
    roots = [function.get("body")] + [m.get("arguments") for m in function.get("modifiers", [])
                                      if m.get("kind") == "modifierInvocation"]
    return [n for root in roots for n in nodes(root) if super_callee(n)]


def parameter_types(function: dict[str, Any]) -> list[str | None]:
    return [p["typeDescriptions"].get("typeIdentifier") for p in function["parameters"]["parameters"]]


def super_target(declaration: dict[str, Any], later: list[int],
                 functions: list[dict[str, Any]]) -> dict[str, Any] | None:
    """The function a super call naming a declaration runs: the first, along
    the bases after the caller's, with its name and parameter types
    (super_target in solidityImport)."""
    for base in later:
        for f in functions:
            if (f["scope"] == base and f["kind"] == "function" and f["name"] == declaration["name"]
                    and parameter_types(f) == parameter_types(declaration)):
                return f
    return None


def live_functions(asts: dict[str, Any], by_id: dict[int, dict[str, Any]]) -> tuple[set[int], set[int]]:
    """The implemented functions of the deployable contracts' bases, and those
    of them valid_src_unit and elaborate_unit see: the ones no other function
    of the same contract overrides, and the ones super calls reach from
    those."""
    based: set[int] = set()
    live: set[int] = set()
    for ast in asts.values():
        for contract in deployable(ast):
            bases = contract["linearizedBaseContracts"]
            functions = [m for b in bases if b in by_id
                         for m in by_id[b]["nodes"]
                         if m["nodeType"] == "FunctionDefinition" and m["implemented"]]
            dead = overridden(functions, by_id)
            based.update(f["id"] for f in functions)
            pending = [f for f in functions if f["id"] not in dead]
            seen = {f["id"] for f in pending}
            while pending:
                f = pending.pop()
                live.add(f["id"])
                for call in super_calls(f):
                    declaration = by_id.get(call["expression"].get("referencedDeclaration"))
                    later = bases[bases.index(f["scope"]) + 1:] if f.get("scope") in bases else []
                    target = declaration and super_target(declaration, later, functions)
                    if target is not None and target["id"] not in seen:
                        seen.add(target["id"])
                        pending.append(target)
    return based, live


def constructor_parameters(contract: dict[str, Any]) -> list[dict[str, Any]]:
    return next((m["parameters"]["parameters"] for m in contract.get("nodes", [])
                 if m["nodeType"] == "FunctionDefinition" and m["kind"] == "constructor"), [])


def is_external(node: dict[str, Any]) -> bool:
    return (node["nodeType"] == "MemberAccess"
            and node["typeDescriptions"].get("typeIdentifier", "").startswith("t_function_external_"))


def is_type_call(node: dict[str, Any]) -> bool:
    """Whether a node is type(T), which the importer reads with its member."""
    return (node["nodeType"] == "FunctionCall" and node["expression"]["nodeType"] == "Identifier"
            and node["expression"]["name"] == "type"
            and node["expression"].get("referencedDeclaration", 0) < 0)


def node_blockers(node: dict[str, Any], *, builtin_callee: bool = False) -> list[Blocker]:
    """What the importer rejects at this node itself; children are checked as
    nodes of their own. Member and index accesses are classified by the type
    of the value accessed."""
    kind = node["nodeType"]
    found: list[str] = []
    if kind in FEATURES:
        found.append(FEATURES[kind])
    elif kind == "IndexAccess" and node.get("indexExpression") is None:
        found.append("array type expressions")
    elif kind == "ArrayTypeName":
        length = node.get("length")
        tid = (length or {}).get("typeDescriptions", {}).get("typeIdentifier", "")
        match = re.fullmatch(r"t_rational_([0-9]+)_by_1", tid)
        if length is not None and (match is None or int(match[1]) == 0):
            found.append("arrays")
    elif kind == "MemberAccess":
        base = node["expression"]
        if node.get("referencedDeclaration") is not None:
            pass
        elif base["nodeType"] == "Identifier" and base.get("referencedDeclaration", 0) < 0:
            if node["memberName"] not in ENVIRONMENT.get(base["referencedDeclaration"], set()):
                found.append(type_feature(base["typeDescriptions"].get("typeIdentifier")))
        elif node["memberName"] not in {"length", "push", "pop"} and not is_type_call(base):
            found.append(type_feature(base["typeDescriptions"].get("typeIdentifier")))
    elif kind == "NewExpression":
        created = node["typeName"]
        result = (node["typeDescriptions"].get("typeIdentifier") or "").partition("$returns$_")[2]
        if created["nodeType"] == "ArrayTypeName" and not located_array(result.removesuffix("_$")):
            found.append("memory arrays (new T[](n))")
    elif kind == "UserDefinedTypeName":
        if not node["typeDescriptions"].get("typeIdentifier", "").startswith(("t_struct$_", "t_address", "t_enum_")):
            found.append(type_feature(node["typeDescriptions"].get("typeIdentifier")))
    elif kind == "Literal":
        if node.get("subdenomination") is not None:
            found.append("literal subdenominations (ether, days, …)")
    elif kind == "Identifier":
        if node.get("referencedDeclaration", 0) < 0 and node["referencedDeclaration"] != THIS and not builtin_callee:
            found.append(BUILTINS.get(node["name"], f"built-in {node['name']}"))
    elif kind == "TupleExpression":
        if node["isInlineArray"]:
            found.append("inline arrays")
    elif kind == "FunctionCall":
        # Named arguments are taken on calls of declared functions only,
        # with or without call options; `new` names no declaration.
        callee = node["expression"]
        if callee["nodeType"] == "FunctionCallOptions":
            callee = callee["expression"]
        if node["names"] and (node["kind"] != "functionCall"
                              or callee.get("referencedDeclaration", -1) < 0):
            found.append("named arguments")
        if node["tryCall"]:
            found.append("try/catch")
        if node["kind"] == "structConstructorCall":
            found.append("structs")
        # The importer rejects new C at the call.
        callee = node["expression"]
        if callee["nodeType"] == "FunctionCallOptions":
            callee = callee["expression"]
        if callee["nodeType"] == "NewExpression" and callee["typeName"]["nodeType"] == "UserDefinedTypeName":
            found.append("contract creation (new C)")
    elif kind == "ModifierDefinition":
        if node["virtual"] or node.get("overrides"):
            found.append("virtual modifiers")
    elif kind == "ModifierInvocation":
        if node.get("kind") not in ("modifierInvocation", "baseConstructorSpecifier"):
            found.append("modifiers")
    elif kind == "VariableDeclaration":
        if node.get("overrides"):
            found.append("overriding state variables")
        if node["constant"] and not (
                node.get("stateVariable") and node.get("value") is not None
                and CONSTANT_TYPE.fullmatch(node["typeDescriptions"].get("typeIdentifier") or "")):
            found.append("constants")
        if node["mutability"] == "immutable" and not VALUE_TYPE.fullmatch(
                node["typeDescriptions"].get("typeIdentifier") or ""):
            found.append("immutables")
    elif kind == "FunctionDefinition":
        if node["kind"] not in FUNCTION_KINDS:
            found.append("free functions" if node["kind"] == "freeFunction"
                         else f"{node['kind']} functions")
    elif kind == "UsingForDirective":
        if node.get("libraryName") is None:
            found.append("using for with functions")
    elif kind not in EXPRESSIONS | STATEMENTS | STRUCTURAL:
        found.append(f"{kind} nodes")
    return [Blocker(kind, feature, "import") for feature in found]


VALUE_TYPE = re.compile(
    r"t_(bool|address_payable|address|u?int(8|16|24|32|40|48|56|64|72|80|88|96|104|112|120"
    r"|128|136|144|152|160|168|176|184|192|200|208|216|224|232|240|248|256)"
    r"|bytes([1-9]|[12][0-9]|3[0-2]))(?=_\$_|_\$|$)"
)
# An enum type, as normalize_type_ids reads it.
ENUM = re.compile(r"t_enum_[0-9]+")
ENUM_PREFIX = re.compile(r"t_enum_[0-9]+(?=_\$_|_\$|$)")
# The types of constants: value types, and byte sequences, which references
# see in memory.
CONSTANT_TYPE = re.compile(rf"(?:{VALUE_TYPE.pattern})|t_(string|bytes)_memory_ptr")
RATIONAL = re.compile(r"t_rational_(minus_)?[0-9]+_by_[0-9]+")
# The type of an operation over literals that elaborates to its value.
INTEGER_RATIONAL = re.compile(r"t_rational_(minus_)?[0-9]+_by_1")
# bytes and string in storage, and references to them in each location
# (decode_elementary_identifier).
BYTE_SEQUENCE = re.compile(r"t_(bytes|string)_(storage|(memory|calldata|storage)_ptr)")


def located_array(type_identifier: str) -> bool:
    """Whether decode_located_array admits a type identifier: a memory or
    calldata array, possibly nested, of elementary value types or byte
    sequences, each dimension dynamic or of a positive length; in calldata, a
    fixed-size dimension holds only static elements."""
    fields = type_identifier.split("$")
    if fields[0] != "t_array":
        return False
    k = 0
    while 1 + k < len(fields) and fields[1 + k] == "_t_array":
        k += 1
    base, *dimensions = fields[1 + k:] or [""]
    if len(dimensions) != k + 1 or len(base) < 2 or base[0] != "_" or base[-1] != "_":
        return False
    location = "calldata" if dimensions[-1].endswith("_calldata_ptr") else "memory"
    element = base[1:-1]
    sequence = element in (f"t_bytes_{location}_ptr", f"t_string_{location}_ptr")
    if not (sequence or VALUE_TYPE.fullmatch(element)):
        return False
    static = not sequence
    for i, dimension in enumerate(dimensions):
        suffix = f"_{location}_ptr" if i == k else f"_{location}_ptr_"
        if not dimension.endswith(suffix):
            return False
        digits = dimension[:-len(suffix)]
        if digits == "dyn":
            static = False
        elif not (digits.isdigit() and int(digits) > 0):
            return False
        elif location == "calldata" and not static:
            return False
    return True


def decodes_component(type_identifier: str) -> bool:
    """Whether tuple_component admits a component's type identifier."""
    return (VALUE_TYPE.fullmatch(type_identifier) is not None
            or ENUM.fullmatch(type_identifier) is not None
            or BYTE_SEQUENCE.fullmatch(type_identifier) is not None
            or located_array(type_identifier) or storage_array_value(type_identifier)
            or type_identifier.startswith("t_stringliteral_"))


def decodes(type_identifier: str) -> bool:
    """Whether decode_type_identifier admits a type identifier: an elementary
    value type, enum or byte sequence, a literal type, or a tuple of those."""
    if (VALUE_TYPE.fullmatch(type_identifier) or ENUM.fullmatch(type_identifier)
            or RATIONAL.fullmatch(type_identifier)
            or BYTE_SEQUENCE.fullmatch(type_identifier) or located_array(type_identifier)
            or storage_array_value(type_identifier)
            or type_identifier.startswith("t_stringliteral_")):
        return True
    if type_identifier == "t_tuple$__$":
        return True
    if not type_identifier.startswith("t_tuple$"):
        return False
    *fields, last = type_identifier[len("t_tuple$"):].split("$")
    components = tuple_identifier_components(fields)
    return last == "" and components is not None and all(
        len(c) >= 2 and c[0] == c[-1] == "_" and decodes_component(c[1:-1])
        for c in components
    )


def tuple_identifier_components(fields: list[str]) -> list[str] | None:
    """tuple_identifier_components: rejoin an array's `$`-separated fields, where
    "_t_array" opens an array and a field without a leading "_" closes one."""
    components, depth, current = [], 0, None
    for field in fields:
        current = field if current is None else f"{current}${field}"
        depth = depth + 1 if field == "_t_array" else depth if field.startswith("_") else max(depth - 1, 0)
        if depth == 0:
            components.append(current)
            current = None
    return components if current is None else None


def storage_type_supported(type_identifier: str) -> bool:
    """Storage scalars, enums, bytes and strings, structs and combinations of
    arrays and mappings, with elementary keys."""
    def parse_at(start: int) -> int | None:
        array = "t_array$_"
        if type_identifier.startswith(array, start):
            end = parse_at(start + len(array))
            if end is None:
                return None
            if type_identifier.startswith("_$dyn_storage", end):
                return end + len("_$dyn_storage")
            dimension = re.match(r"_\$([0-9]+)_storage", type_identifier[end:])
            if dimension is None or not 0 < int(dimension[1]) < 2**256:
                return None
            return end + dimension.end()
        prefix = "t_mapping$_"
        if type_identifier.startswith(prefix, start):
            key = VALUE_TYPE.match(type_identifier, start + len(prefix))
            if key is None or not type_identifier.startswith("_$_", key.end()):
                return None
            value_end = parse_at(key.end() + 3)
            if value_end is None or not type_identifier.startswith("_$", value_end):
                return None
            return value_end + 2
        struct = re.match(r"t_struct\$_.*?_\$[0-9]+_storage(?=_\$_|_\$|$)",
                          type_identifier[start:])
        if struct is not None:
            return start + struct.end()
        sequence = re.match(r"t_(bytes|string)_storage(?=_\$_|_\$|$)", type_identifier[start:])
        if sequence is not None:
            return start + sequence.end()
        scalar = VALUE_TYPE.match(type_identifier, start) or ENUM_PREFIX.match(type_identifier, start)
        return scalar.end() if scalar is not None else None

    return parse_at(0) == len(type_identifier)


def storage_array_value(type_identifier: str) -> bool:
    """Whether decode_located_array admits a storage array value's type
    identifier, as an assignment or tuple component has (no `_ptr`)."""
    return type_identifier.endswith("_storage") and storage_array(type_identifier)


def storage_array(type_identifier: str) -> bool:
    """Whether a storage array is read as a value (memory_object_type): an
    array, possibly nested, of elementary value types or byte sequences."""
    base = type_identifier.removesuffix("_ptr")
    return (base.startswith("t_array$_") and base.endswith("_storage")
            and "t_mapping$_" not in base and "t_struct$_" not in base
            and "t_enum" not in base and storage_type_supported(base))


UNARY_OPERATORS = {"++", "--", "-", "!", "~"}
# The bases bytes may be indexed and measured through: in storage, and
# references to it in each location.
BYTES = re.compile(r"t_bytes_(storage|(memory|calldata|storage)_ptr)")


def has_getter(type_name: dict[str, Any], by_id: dict[int, dict[str, Any]], bases: set[int]) -> bool:
    """Whether getter_shape admits a public state variable's type: mappings
    with elementary keys and arrays, down to an elementary type, an enum, a
    byte sequence or a struct with a member getter_member returns and none it
    rejects. The importer gives the contract the structs of its bases and of
    the file level only."""
    kind = type_name["nodeType"]
    if kind == "Mapping":
        key = type_name["keyType"]["typeDescriptions"].get("typeIdentifier") or ""
        return VALUE_TYPE.fullmatch(key) is not None and has_getter(type_name["valueType"], by_id, bases)
    if kind == "ArrayTypeName":
        return has_getter(type_name["baseType"], by_id, bases)
    declaration = by_id.get(type_name.get("referencedDeclaration"), {})
    if kind == "UserDefinedTypeName" and declaration.get("nodeType") == "StructDefinition":
        scope = by_id.get(declaration.get("scope"), {})
        if scope.get("nodeType") != "SourceUnit" and scope.get("id") not in bases:
            return False
        # mappings and arrays other than byte sequences are skipped
        returned = [m["typeName"] for m in declaration["members"]
                    if m["typeName"]["nodeType"] not in ("Mapping", "ArrayTypeName")]
        return bool(returned) and all(getter_value(t) for t in returned)
    return getter_value(type_name)


def getter_value(type_name: dict[str, Any]) -> bool:
    """Whether a getter returns a value of this type: an elementary type, an
    enum or a byte sequence."""
    type_identifier = type_name["typeDescriptions"].get("typeIdentifier") or ""
    # A contract type name is read as address.
    return (type_name["nodeType"] in ("ElementaryTypeName", "UserDefinedTypeName")
            and (VALUE_TYPE.fullmatch(type_identifier) is not None
                 or ENUM.fullmatch(type_identifier) is not None
                 or type_identifier in ("t_bytes_storage_ptr", "t_string_storage_ptr")))


def elaboration_blockers(node: dict[str, Any], *, storage_field: bool = False,
                         error_parameter: bool = False) -> list[Blocker]:
    """What valid_src_unit or elaborate_unit rejects at a node the importer
    admits: unsupported storage/reference types and indexing, conversions
    outside the elementary types and byte sequences, `delete`, and units that
    are not one contract. Other expressions get their types from these, or
    are rejected by the importer."""
    kind = node["nodeType"]
    found: list[str] = []
    if (kind == "VariableDeclaration"
            or (kind == "FunctionCall" and node["kind"] == "typeConversion")
            or (kind == "Literal" and node["kind"] not in ("number", "bool"))):
        type_identifier = node["typeDescriptions"].get("typeIdentifier") or ""
        admitted_storage = (kind == "VariableDeclaration" and (node["stateVariable"] or storage_field)
                            and storage_type_supported(type_identifier.removesuffix("_ptr")
                                                       if storage_field else type_identifier))
        if not decodes(type_identifier) and not admitted_storage:
            found.append(type_feature(type_identifier))
        if kind == "VariableDeclaration":
            location = node["storageLocation"]
            if location == "transient":
                found.append("transient storage")
            elif (location not in ("default", "memory") and not BYTE_SEQUENCE.fullmatch(type_identifier)
                  and not (location == "calldata" and located_array(type_identifier))):
                found.append("local reference bindings")
            elif location == "default" and located_array(type_identifier):
                found.append("event array parameters")
            if error_parameter and not VALUE_TYPE.fullmatch(type_identifier):
                found.append("custom errors with reference parameters")
    elif (kind == "TupleExpression" and not node["isInlineArray"]
          and not decodes(node["typeDescriptions"]["typeIdentifier"])):
        type_identifier = node["typeDescriptions"]["typeIdentifier"]
        found.append("tuples of literals" if "t_rational" in type_identifier
                     else type_feature(type_identifier))
    elif (kind == "Assignment" and unwrap(node["leftHandSide"])["nodeType"] == "TupleExpression"
          and any(c is not None and unwrap(c)["nodeType"] != "Identifier"
                  for c in unwrap(node["leftHandSide"])["components"])):
        found.append("tuple assignments to element or member targets")
    elif (kind == "VariableDeclarationStatement" and node.get("initialValue") is None
          and any(d is not None and d["storageLocation"] == "calldata"
                  for d in node["declarations"])):
        found.append("calldata locals without an initializer")
    elif kind == "UnaryOperation" and node["operator"] not in UNARY_OPERATORS:
        found.append(f"operator {node['operator']}")
    elif (kind in ("UnaryOperation", "BinaryOperation")
          and not INTEGER_RATIONAL.fullmatch(node["typeDescriptions"]["typeIdentifier"])
          and (RATIONAL.fullmatch(node["typeDescriptions"]["typeIdentifier"])
               or (kind == "BinaryOperation"
                   and RATIONAL.fullmatch(node["commonType"]["typeIdentifier"])))):
        found.append("constant expressions over literals")
    elif kind == "Literal" and node["kind"] == "number" and not RATIONAL.fullmatch(
            node["typeDescriptions"].get("typeIdentifier") or ""):
        found.append("literals of non-integer types")
    elif kind == "IndexAccess":
        base_type = node["baseExpression"]["typeDescriptions"].get("typeIdentifier") or ""
        if not (BYTES.fullmatch(base_type) or located_array(base_type)
                or (base_type.startswith(("t_mapping$_", "t_array$_"))
                    and storage_type_supported(base_type))):
            found.append(type_feature(base_type))
    elif kind == "MemberAccess":
        base_type = node["expression"]["typeDescriptions"].get("typeIdentifier") or ""
        if base_type.startswith("t_type$_t_super"):
            pass  # super.f: whether it is called where admitted is the import's check
        elif base_type.startswith("t_type$_t_enum$_"):
            pass  # E.A, an enum's member
        elif node.get("referencedDeclaration") is not None:
            if not base_type.startswith("t_struct$_") or not storage_type_supported(base_type):
                found.append(type_feature(base_type))
        elif node["memberName"] == "length":
            if not BYTES.fullmatch(base_type) and not located_array(base_type) and not (
                    base_type.startswith("t_array$_") and storage_type_supported(base_type)):
                found.append(type_feature(base_type))
        elif node["memberName"] in {"push", "pop"}:
            if BYTES.fullmatch(base_type):
                found.append("bytes push and pop")
            elif not base_type.startswith("t_array$_") or not storage_type_supported(base_type):
                found.append(type_feature(base_type))
            elif not base_type.endswith("_$dyn_storage"):
                found.append("fixed array mutation")
            elif not (VALUE_TYPE.fullmatch(element := base_type[len("t_array$_"):-len("_$dyn_storage")])
                      or ENUM.fullmatch(element)):
                found.append("aggregate array mutation")
    elif kind == "Conditional":
        # the checker and elaborator take a value or a memory reference
        type_identifier = node["typeDescriptions"].get("typeIdentifier") or ""
        if not (VALUE_TYPE.fullmatch(type_identifier) or ENUM.fullmatch(type_identifier)
                or type_identifier in ("t_bytes_memory_ptr", "t_string_memory_ptr")
                or (located_array(type_identifier) and type_identifier.endswith("_memory_ptr"))):
            found.append("conditional expressions")
    elif kind == "SourceUnit":
        if len(deployable(node)) != 1:
            found.append("source units without exactly one contract")
    return [Blocker(kind, feature, "elaboration") for feature in found]


def callee_blockers(node: dict[str, Any], callees: set[int],
                    conversions: set[int]) -> list[Blocker]:
    """Type names and function names, which the semantics admits only as the
    callee of a conversion or a call; and the callees of conversions to
    non-elementary types, where the importer rejects those."""
    if node["id"] in conversions and node["nodeType"] != "ElementaryTypeNameExpression":
        return [Blocker(node["nodeType"], "conversions to non-elementary types", "import")]
    if node["id"] in callees:
        return []
    if (node["nodeType"] == "MemberAccess" and node.get("referencedDeclaration") is None
            and node["memberName"] in {"push", "pop"}):
        return [Blocker("MemberAccess", "array members as values", "elaboration")]
    if node["nodeType"] == "ElementaryTypeNameExpression":
        return [Blocker(node["nodeType"], "type names as values", "import")]
    if (node["nodeType"] == "Identifier"
            and node["typeDescriptions"].get("typeIdentifier", "").startswith("t_function_internal")):
        return [Blocker(node["nodeType"], "functions as values", "elaboration")]
    return []


INTEGER_TYPE = re.compile(r"t_u?int[0-9]+")


# The builtins of the Yul dialect (yulDialect's builtin_name), and those an
# inline assembly block may not use (assembly_unsupported).
YUL_BUILTINS = {
    "add", "sub", "mul", "div", "sdiv", "mod", "smod", "exp", "signextend", "lt", "gt",
    "slt", "sgt", "eq", "iszero", "and", "or", "xor", "not", "shl", "shr", "sar", "byte",
    "keccak256", "mload", "mstore", "mstore8", "mcopy", "sload", "sstore", "tload", "tstore",
    "calldataload", "calldatasize", "calldatacopy", "callvalue", "memoryguard", "caller",
    "loadimmutable", "log0", "log1", "log2", "log3", "log4", "address", "origin", "chainid",
    "number", "timestamp", "coinbase", "gasprice", "basefee", "gaslimit", "stop", "call",
    "staticcall", "extcodesize", "returndatasize", "returndatacopy", "gas", "pop", "return",
    "revert", "codesize", "codecopy", "datasize", "dataoffset",
}
YUL_UNSUPPORTED = {
    "gas", "call", "staticcall", "returndatasize", "returndatacopy",
    "codesize", "codecopy", "datasize", "dataoffset",
}


def yul_literal(value: dict[str, Any]) -> int | None:
    """A number literal's value (yul_lit)."""
    if value.get("nodeType") != "YulLiteral" or value.get("kind") != "number":
        return None
    text = value["value"]
    return int(text, 16) if text.startswith("0x") else int(text)


def assembly_memory_ok(statements: list[dict[str, Any]]) -> bool:
    """assembly_memory_ok: memory reads at literal ranges covered by earlier
    literal mstores on the same path, and, unless the block's
    last statement halts, memory writes only at literal ranges inside the
    scratch space [0, 0x40)."""
    last = statements[-1] if statements else {}
    halts = (last.get("nodeType") == "YulExpressionStatement"
             and last["expression"].get("nodeType") == "YulFunctionCall"
             and last["expression"]["functionName"]["name"] in ("return", "revert", "stop"))

    def covered(ws: list[int], a: int, n: int) -> bool:
        return n <= 32 * len(ws) and all(any(w <= a + i < w + 32 for w in ws) for i in range(n))

    def read_ok(ws: list[int], p: dict[str, Any], length: dict[str, Any]) -> bool:
        a, n = yul_literal(p), yul_literal(length)
        return a is not None and n is not None and covered(ws, a, n)

    def write_ok(p: dict[str, Any], n: int | None) -> bool:
        a = yul_literal(p)
        return halts or (a is not None and n is not None and a + n <= 64)

    def builtin_ok(ws: list[int], name: str, args: list[dict[str, Any]]) -> bool:
        if name == "mload":
            return len(args) == 1 and read_ok(
                ws, args[0], {"nodeType": "YulLiteral", "kind": "number", "value": "32"})
        if name == "mstore":
            return len(args) == 2 and write_ok(args[0], 32)
        if name == "mstore8":
            return len(args) == 2 and write_ok(args[0], 1)
        if name == "mcopy":
            return len(args) == 3 and write_ok(args[0], yul_literal(args[2])) and read_ok(ws, args[1], args[2])
        if name == "calldatacopy":
            return len(args) == 3 and write_ok(args[0], yul_literal(args[2]))
        if name in ("keccak256", "return", "revert", "log0"):
            return len(args) == 2 and read_ok(ws, args[0], args[1])
        if name in ("log1", "log2", "log3", "log4"):
            return len(args) >= 2 and read_ok(ws, args[0], args[1])
        return True

    def expr_ok(ws: list[int], e: dict[str, Any] | None) -> bool:
        if e is None or e.get("nodeType") != "YulFunctionCall":
            return True
        args = e.get("arguments", [])
        return builtin_ok(ws, e["functionName"]["name"], args) and all(expr_ok(ws, a) for a in args)

    def stmts_ok(ws: list[int], ss: list[dict[str, Any]]) -> bool:
        for st in ss:
            if not stmt_ok(ws, st):
                return False
            if (st["nodeType"] == "YulExpressionStatement"
                    and st["expression"].get("nodeType") == "YulFunctionCall"
                    and st["expression"]["functionName"]["name"] == "mstore"
                    and len(st["expression"].get("arguments", [])) == 2):
                a = yul_literal(st["expression"]["arguments"][0])
                if a is not None:
                    ws = [a] + ws
        return True

    def stmt_ok(ws: list[int], st: dict[str, Any]) -> bool:
        kind = st["nodeType"]
        if kind == "YulBlock":
            return stmts_ok(ws, st["statements"])
        if kind == "YulFunctionDefinition":
            return stmts_ok([], st["body"]["statements"])
        if kind in ("YulVariableDeclaration", "YulAssignment"):
            return expr_ok(ws, st.get("value"))
        if kind == "YulIf":
            return expr_ok(ws, st["condition"]) and stmts_ok(ws, st["body"]["statements"])
        if kind == "YulSwitch":
            return expr_ok(ws, st["expression"]) and all(
                stmts_ok(ws, c["body"]["statements"]) for c in st["cases"])
        if kind == "YulForLoop":
            return (stmts_ok(ws, st["pre"]["statements"]) and expr_ok(ws, st["condition"])
                    and stmts_ok(ws, st["post"]["statements"]) and stmts_ok(ws, st["body"]["statements"]))
        if kind == "YulExpressionStatement":
            return expr_ok(ws, st["expression"])
        return True

    return stmts_ok([], statements)


def assembly_blockers(node: dict[str, Any], by_id: dict[int, dict[str, Any]],
                      creation: bool = False) -> list[Blocker]:
    """What the importer and the elaborator reject in an inline assembly
    block: Yul the importer does not read (functions other than the block's
    own, builtins outside the dialect, boolean literals, references other
    than slot and offset), then builtins the source state cannot run (gas,
    calls, return data, code), `return` and `stop` in a block a constructor
    runs (creation), memory use outside assembly_memory_ok, and
    references to anything but value-type locals and state variable
    locations."""
    if node["nodeType"] != "InlineAssembly":
        return []
    found: list[Blocker] = []

    def blocker(feature: str, stage: str) -> None:
        if Blocker("InlineAssembly", feature, stage) not in found:
            found.append(Blocker("InlineAssembly", feature, stage))

    statements = node["AST"].get("statements", [])
    defined = {s["name"] for s in statements if s["nodeType"] == "YulFunctionDefinition"}

    def walk(value: Any, top: bool) -> None:
        if isinstance(value, list):
            for v in value:
                walk(v, top)
        elif isinstance(value, dict):
            kind = value.get("nodeType")
            if kind == "YulFunctionDefinition" and not top:
                blocker("inline assembly", "import")
            elif kind == "YulLiteral" and value.get("kind") not in ("number", "string"):
                blocker("inline assembly", "import")
            elif kind == "YulFunctionCall":
                name = value["functionName"]["name"]
                if name not in defined and name not in YUL_BUILTINS:
                    blocker("inline assembly", "import")
                elif name not in defined and name in YUL_UNSUPPORTED:
                    blocker("inline assembly calls, gas, return data and code", "elaboration")
                elif name not in defined and creation and name in ("return", "stop"):
                    blocker("inline assembly halts in a constructor", "elaboration")
            for k, v in value.items():
                if k != "functionName":
                    walk(v, top and kind == "YulBlock" and value is node["AST"])

    walk(statements, True)
    if not assembly_memory_ok(statements):
        blocker("inline assembly memory outside the scratch space", "elaboration")
    for reference in node.get("externalReferences", []):
        suffix = reference.get("suffix")
        declaration = by_id.get(reference["declaration"], {})
        if suffix not in (None, "slot", "offset"):
            blocker("inline assembly", "import")
        elif suffix is None and (declaration.get("stateVariable", True) or declaration.get("constant", False)
                                 or not VALUE_TYPE.fullmatch(
                declaration.get("typeDescriptions", {}).get("typeIdentifier") or "")):
            blocker("inline assembly memory references", "elaboration")
        elif suffix is not None and not declaration.get("stateVariable", False):
            blocker("inline assembly memory references", "elaboration")
    return sorted(found, key=lambda b: b.stage != "import")


def coerced_literals(node: dict[str, Any], by_id: dict[int, dict[str, Any]]) -> list[Blocker]:
    """Integer literals used where a value of another type is expected, which
    elaborate_unit converts only to integer types, and string literals used
    as fixed-size bytes, which it does not convert: initial values of locals
    and state variables, returned and assigned values, tuple components
    included, operands, mapping keys, arguments of calls, emits and reverts,
    and conversions."""
    kind = node["nodeType"]
    expected: list[tuple[dict[str, Any] | None, dict[str, Any] | None]] = []

    def components(value: dict[str, Any] | None, targets: list[Any]) -> None:
        """Each value of a tuple with the target of its position."""
        value = unwrap(value)
        if len(targets) == 1:
            expected.append((value, targets[0]))
        elif value is not None and value["nodeType"] == "TupleExpression":
            expected.extend(zip(value["components"], targets))

    if kind == "VariableDeclarationStatement":
        components(node.get("initialValue"), node["declarations"])
    elif kind == "VariableDeclaration" and node.get("stateVariable"):
        expected.append((node.get("value"), node))
    elif kind == "Return" and node.get("expression") is not None:
        components(node["expression"],
                   by_id.get(node.get("functionReturnParameters"), {}).get("parameters", []))
    elif kind == "ModifierInvocation" and node.get("kind") == "modifierInvocation":
        modifier = by_id.get(node["modifierName"].get("referencedDeclaration"), {})
        expected.extend(zip(node.get("arguments") or [],
                            modifier.get("parameters", {}).get("parameters", [])))
    elif kind == "InheritanceSpecifier" or (kind == "ModifierInvocation"
                                            and node.get("kind") == "baseConstructorSpecifier"):
        base = node["baseName" if kind == "InheritanceSpecifier" else "modifierName"]
        expected.extend(zip(node.get("arguments") or [],
                            constructor_parameters(by_id.get(base.get("referencedDeclaration"), {}))))
    elif kind == "Assignment" and node["operator"] not in ("<<=", ">>="):
        target = unwrap(node["leftHandSide"])
        components(node["rightHandSide"],
                   target["components"] if target["nodeType"] == "TupleExpression" else [node])
    elif kind == "IndexAccess" and node.get("indexExpression") is not None:
        match = re.match(r"t_mapping\$_(t_[^$]+)_\$_",
                         node["baseExpression"]["typeDescriptions"].get("typeIdentifier") or "")
        if match is not None:
            expected.append((node["indexExpression"], {"typeDescriptions": {"typeIdentifier": match[1]}}))
    elif kind == "BinaryOperation":
        common = {"typeDescriptions": node["commonType"]}
        expected.append((node["leftExpression"], common))
        if node["operator"] not in ("<<", ">>", "**"):
            expected.append((node["rightExpression"], common))
    elif kind == "FunctionCall" and node["kind"] == "functionCall":
        name = node["expression"]
        if name["nodeType"] == "FunctionCallOptions":
            name = name["expression"]
        callee = by_id.get(name.get("referencedDeclaration"), {})
        if callee.get("nodeType") == "FunctionDefinition":
            parameters = callee["parameters"]["parameters"]
            # x.f(args): x is f's first argument
            if "$attached_to$" in (name.get("typeDescriptions", {}).get("typeIdentifier") or "") and parameters:
                expected.append((name["expression"], parameters[0]))
                parameters = parameters[1:]
            expected.extend(arguments(node, parameters))
        member = node["expression"]
        if (member.get("nodeType") == "MemberAccess" and member["memberName"] == "push"
                and len(node["arguments"]) == 1):
            array_type = member["expression"]["typeDescriptions"].get("typeIdentifier", "")
            match = re.fullmatch(r"t_array\$_(t_[^$]+)_\$dyn_storage", array_type)
            if match is not None:
                expected.append((node["arguments"][0],
                                 {"typeDescriptions": {"typeIdentifier": match[1]}}))
    elif kind == "FunctionCall" and node["kind"] == "typeConversion" and len(node["arguments"]) == 1:
        expected.append((node["arguments"][0], node))
    elif kind == "EmitStatement":
        event = by_id.get(node["eventCall"]["expression"].get("referencedDeclaration"), {})
        if event.get("nodeType") == "EventDefinition":
            expected.extend(arguments(node["eventCall"], event["parameters"]["parameters"]))
    elif kind == "RevertStatement":
        error = by_id.get(node["errorCall"]["expression"].get("referencedDeclaration"), {})
        if error.get("nodeType") == "ErrorDefinition":
            expected.extend(arguments(node["errorCall"], error["parameters"]["parameters"]))
    found: list[str] = []
    for value, target in expected:
        value = unwrap(value)
        target_type = (target or {}).get("typeDescriptions", {}).get("typeIdentifier") or ""
        if value is None or not VALUE_TYPE.fullmatch(target_type):
            continue
        value_type = value["typeDescriptions"].get("typeIdentifier") or ""
        if not (value["nodeType"] == "Literal" or (
                value["nodeType"] in ("UnaryOperation", "BinaryOperation")
                and INTEGER_RATIONAL.fullmatch(value_type))):
            continue
        conversion = kind == "FunctionCall" and node["kind"] == "typeConversion"
        if RATIONAL.fullmatch(value_type) and not INTEGER_TYPE.fullmatch(target_type) and not conversion:
            found.append("literals of non-integer types")
        if value_type.startswith("t_stringliteral_"):
            found.append("string literals as fixed-size bytes")
    return [Blocker(kind, feature, "elaboration") for feature in dict.fromkeys(found)]


def arguments(call: dict[str, Any], parameters: list[dict[str, Any]]
              ) -> list[tuple[dict[str, Any], dict[str, Any] | None]]:
    """A call's arguments with the parameters they are given to, by name for
    named arguments."""
    if not call.get("names"):
        return list(zip(call["arguments"], parameters))
    named = {p["name"]: p for p in parameters}
    return [(a, named.get(n)) for a, n in zip(call["arguments"], call["names"])]


def copies_receiver(member: dict[str, Any], function: dict[str, Any]) -> bool:
    """Whether x.f converts x from storage or calldata to memory, which the
    importer rejects (copies_receiver in solidityImportLib)."""
    receiver = member["expression"]["typeDescriptions"].get("typeIdentifier") or ""
    parameters = function["parameters"]["parameters"]
    return (receiver.endswith(("_storage", "_storage_ptr", "_calldata", "_calldata_ptr"))
            and bool(parameters)
            and (parameters[0]["typeDescriptions"].get("typeIdentifier") or "").endswith("_memory_ptr"))


def unwrap(value: dict[str, Any] | None) -> dict[str, Any] | None:
    """A value without the parentheses around it."""
    while (value is not None and value["nodeType"] == "TupleExpression"
           and not value.get("isInlineArray") and len(value["components"]) == 1):
        value = value["components"][0]
    return value


def is_selector(node: dict[str, Any]) -> bool:
    """Whether a node is f.selector, a member the compiler declares."""
    return (node["nodeType"] == "MemberAccess" and node["memberName"] == "selector"
            and node.get("referencedDeclaration") is None)


def unevaluated_receiver(node: dict[str, Any]) -> bool:
    """Whether a receiver is this or a name the compiler does not evaluate: a
    contract, interface or library name, or an imported module's, possibly
    qualified by a module (unevaluated_receiver in the importer)."""
    named = (node.get("typeDescriptions", {}).get("typeIdentifier") or "").startswith(
        ("t_type$_t_contract$_", "t_module_"))
    if node["nodeType"] == "Identifier":
        return node.get("referencedDeclaration") == THIS or named
    if node["nodeType"] == "MemberAccess":
        return named and unevaluated_receiver(node["expression"])
    return False


def selector_declaration(node: dict[str, Any], by_id: dict[int, dict[str, Any]]
                         ) -> dict[str, Any] | None:
    """The declaration whose recorded selector f.selector, E.selector,
    this.f.selector, I.f.selector or this.x.selector (a public state variable)
    names, as selector_bytes in the importer finds it: the base is an
    identifier, or a member of a receiver the compiler does not evaluate."""
    if not is_selector(node):
        return None
    base = node["expression"]
    if base["nodeType"] == "MemberAccess" and not unevaluated_receiver(base["expression"]):
        return None
    if base["nodeType"] not in {"Identifier", "MemberAccess"}:
        return None
    declaration = by_id.get(base.get("referencedDeclaration"))
    if declaration is None or SELECTOR_FIELDS.get(declaration["nodeType"]) not in declaration:
        return None
    # x.selector and C.x.selector for a variable x are the selector of the
    # function value it holds; only this.x names x's getter.
    if declaration["nodeType"] == "VariableDeclaration" and not (
            base["nodeType"] == "MemberAccess" and base["expression"]["nodeType"] == "Identifier"
            and base["expression"].get("referencedDeclaration") == THIS):
        return None
    return declaration


def abi_argument(node: dict[str, Any], packed: bool) -> bool:
    """Whether the checker takes this argument of abi.encode*: a scalar, a
    byte sequence in any location, a string literal, or, unpacked, an
    integer literal."""
    tid = node["typeDescriptions"].get("typeIdentifier") or ""
    if VALUE_TYPE.match(tid) or tid.startswith(("t_enum_", "t_enum$_", "t_contract$_")):
        return True
    if tid.startswith(("t_bytes_", "t_string_", "t_stringliteral_")):
        return True
    return not packed and re.fullmatch(r"t_rational_(minus_)?[0-9]+_by_1", tid) is not None


def special_forms(reached: dict[int, dict[str, Any]],
                  by_id: dict[int, dict[str, Any]]) -> tuple[set[int], dict[int, list[Blocker]]]:
    """The nodes the importer reads as part of a larger form rather than as
    expressions of their own, and what it and the checker reject in those
    forms: event and error names, the members and contract conversions of
    external calls, contract and enum conversions, enum values, type(T), the members of msg, block and tx,
    the messages of require and revert, and library members named through
    their library or attached to a type, which the importer reads as names. Only the reached nodes are
    scanned; by_id indexes the whole compilation, where a call's target may
    be declared."""
    unread: set[int] = set()
    found: dict[int, list[Blocker]] = {}

    def block(node: dict[str, Any], feature: str, stage: str) -> None:
        found.setdefault(node["id"], []).append(Blocker(node["nodeType"], feature, stage))

    called = {n["expression"]["id"]: n for n in reached.values() if n["nodeType"] == "FunctionCall"}
    members = library_members(by_id)
    # The enum types the importer reads as type names: E in E.A and in E(x).
    enum_names = {n["expression"]["id"] for n in reached.values()
                  if (n["nodeType"] == "MemberAccess"
                      and by_id.get(n.get("referencedDeclaration"), {}).get("nodeType") == "EnumValue")
                  or (n["nodeType"] == "FunctionCall" and n["kind"] == "typeConversion"
                      and n["expression"]["typeDescriptions"].get("typeIdentifier", "")
                      .startswith("t_type$_t_enum$_"))}
    # f.selector: the importer reads it as the declaration's selector, and
    # none of its parts.
    selector_parts = {n["id"] for s in reached.values()
                      if selector_declaration(s, by_id) is not None for n in nodes(s)}
    unread.update(selector_parts)
    for node in reached.values():
        if node["id"] in selector_parts:
            continue
        kind = node["nodeType"]
        # Any other name of an enum type is imported as an identifier that
        # source validation rejects.
        if (kind in ("Identifier", "MemberAccess") and node["id"] not in enum_names
                and by_id.get(node.get("referencedDeclaration"), {}).get("nodeType") == "EnumDefinition"):
            block(node, "enum types as expressions", "elaboration")
        if node["id"] in members:
            if kind == "FunctionDefinition" and node["visibility"] not in ("internal", "private"):
                block(node, "external library functions", "import")
            elif kind not in ("FunctionDefinition", "VariableDeclaration", "ModifierDefinition",
                              "UsingForDirective", "EnumDefinition"):
                block(node, "library structs and events", "import")
        if kind == "MemberAccess" and node.get("referencedDeclaration") in members:
            unread.add(node["id"])
            target = members[node["referencedDeclaration"]]
            if "$attached_to$" in (node["typeDescriptions"].get("typeIdentifier") or ""):
                if node["id"] not in called:
                    block(node, "using for", "import")
                elif copies_receiver(node, target):
                    block(called[node["id"]], "bound calls copying their receiver", "import")
            else:
                unread.update(n["id"] for n in nodes(node["expression"]))
                if target["nodeType"] == "FunctionDefinition" and node["id"] not in called:
                    block(node, "functions as values", "elaboration")
        elif kind == "EmitStatement":
            callee = node["eventCall"]["expression"]
            unread.update({node["eventCall"]["id"], callee["id"]})
            unread.update(n["id"] for n in nodes(callee))
            if callee["nodeType"] != "Identifier":
                block(callee, "events named through a contract or library", "import")
        elif kind == "RevertStatement":
            callee = node["errorCall"]["expression"]
            unread.add(node["errorCall"]["id"])
            unread.update(n["id"] for n in nodes(callee))
        elif (kind == "FunctionCall" and node["kind"] == "functionCall"
              and node["expression"]["nodeType"] == "MemberAccess"
              and node["expression"]["expression"]["nodeType"] == "Identifier"
              and node["expression"]["expression"].get("referencedDeclaration") == ABI):
            # abi.encode*: the importer reads the member as the form, and a
            # literal signature as its bytes.
            callee = node["expression"]
            unread.update({callee["id"], callee["expression"]["id"]})
            member = callee["memberName"]
            arguments = node["arguments"]
            if member == "encodeWithSignature":
                if not arguments or arguments[0]["nodeType"] != "Literal" or arguments[0]["kind"] != "string":
                    block(node, "abi.* functions", "import")
                arguments = arguments[1:]
            elif member == "encodeWithSelector":
                if not arguments or arguments[0]["typeDescriptions"].get("typeIdentifier") != "t_bytes4":
                    block(node, "abi.* functions", "elaboration")
                arguments = arguments[1:]
            elif member not in ("encode", "encodePacked"):
                block(node, "abi.* functions", "import")
                arguments = []
            for argument in arguments:
                if not abi_argument(argument, member == "encodePacked"):
                    block(argument, "abi.* functions", "elaboration")
        elif kind == "MemberAccess" and node.get("referencedDeclaration") is None:
            base = node["expression"]
            if base["nodeType"] == "Identifier" and base.get("referencedDeclaration", 0) < 0:
                unread.add(base["id"])
            elif is_type_call(base):
                argument = base["arguments"][0] if base["arguments"] else base
                unread.update({base["id"], base["expression"]["id"], argument["id"]})
                if (argument["nodeType"] == "Identifier" and node["memberName"] == "interfaceId"
                        and by_id.get(argument.get("referencedDeclaration"), {}).get("contractKind")
                        == "interface"):
                    pass
                elif argument["nodeType"] != "ElementaryTypeNameExpression":
                    block(argument, "type(…)", "import")
                elif (node["memberName"] not in {"max", "min"}
                      or not re.fullmatch(r"u?int[0-9]*", argument["typeName"]["name"])):
                    block(node, "type(…)", "elaboration")
                unread.update(n["id"] for n in nodes(argument))
        elif kind == "FunctionCall" and node["kind"] == "functionCall":
            callee = node["expression"]
            member = callee["expression"] if callee["nodeType"] == "FunctionCallOptions" else callee
            if callee["nodeType"] == "FunctionCallOptions":
                unread.add(callee["id"])
                if callee["names"] != ["value"]:
                    block(callee, "call options ({value: …, gas: …})", "import")
                elif not is_external(member):
                    block(member, "call options ({value: …, gas: …})", "import")
            if is_external(member):
                unread.add(member["id"])
                if by_id.get(member.get("referencedDeclaration"), {}).get("nodeType") == "VariableDeclaration":
                    block(member, "external calls to getters", "import")
            elif (callee["nodeType"] == "Identifier"
                  and callee.get("referencedDeclaration") in {REQUIRE, REVERT}):
                message = node["arguments"][-1] if node["arguments"] else None
                if (message is not None and len(node["arguments"]) == (2 if callee["referencedDeclaration"] == REQUIRE else 1)
                        and not (message["nodeType"] == "Literal" and message["kind"] in STRING_LITERALS
                                 and message["typeDescriptions"]["typeIdentifier"].startswith("t_stringliteral_"))):
                    error = message["nodeType"] == "FunctionCall" and message["expression"][
                        "typeDescriptions"].get("typeIdentifier", "").startswith("t_function_error")
                    block(node, "require with a custom error" if error else "messages that are not literals",
                          "elaboration")
        elif (kind == "FunctionCall" and node["kind"] == "typeConversion"
              and node["expression"]["typeDescriptions"].get("typeIdentifier", "").startswith(
                  ("t_type$_t_contract$_", "t_type$_t_enum$_"))):
            # I(a), a conversion to address, and E(x): the importer reads the
            # callee as a type name
            unread.update(n["id"] for n in nodes(node["expression"]))
        if (kind == "MemberAccess"
                and by_id.get(node.get("referencedDeclaration"), {}).get("nodeType") == "EnumValue"):
            # E.A: the importer reads E as a type name
            unread.update(n["id"] for n in nodes(node["expression"]))
    return unread, found


# A contract or enum type's identifier, other than within a type expression's:
# the importer reads a contract type as t_address and an enum type by its id
# alone (normalize_type_id in solidityImportLib).
CONTRACT_TYPE = re.compile(r'(?<!t_type\$_)t_contract\$_.*?_\$[0-9]+')
ENUM_TYPE = re.compile(r'(?<!t_type\$_)t_enum\$_.*?_\$([0-9]+)')


def normalize_type_ids(value: Any) -> Any:
    """A copy of an AST with its type identifiers read as the importer reads
    them."""
    if isinstance(value, dict):
        return {k: (ENUM_TYPE.sub(r"t_enum_\1", CONTRACT_TYPE.sub("t_address", v))
                    if k == "typeIdentifier" and isinstance(v, str)
                    else normalize_type_ids(v)) for k, v in value.items()}
    if isinstance(value, list):
        return [normalize_type_ids(v) for v in value]
    return value


def contract_overloads(asts: dict[str, Any]) -> set[int]:
    """The implemented functions of an imported contract's bases with another
    of the same name whose parameter types differ only in contract types,
    which the importer rejects."""
    by_id = {n["id"]: n for ast in asts.values() for n in nodes(ast)}
    def types(f: dict[str, Any]) -> list[str]:
        return [p.get("typeDescriptions", {}).get("typeIdentifier") or "" for p in f["parameters"]["parameters"]]
    found: set[int] = set()
    for ast in asts.values():
        for contract in deployable(ast):
            functions = [m for b in contract["linearizedBaseContracts"] if b in by_id
                         for m in by_id[b]["nodes"] if m["nodeType"] == "FunctionDefinition"
                         and m.get("kind") == "function" and m.get("implemented")]
            found.update(g["id"] for f in functions for g in functions
                         if f.get("name") == g.get("name") and types(f) != types(g)
                         and [CONTRACT_TYPE.sub("t_address", t) for t in types(f)]
                         == [CONTRACT_TYPE.sub("t_address", t) for t in types(g)])
    return found


def scan(asts: dict[str, Any]) -> dict[int, list[Blocker]]:
    """Every node the importer reads that the semantics rejects, by node id,
    the importer's reasons first."""
    overloads = contract_overloads(asts)
    asts = normalize_type_ids(asts)
    by_id = {n["id"]: n for ast in asts.values() for n in nodes(ast)}
    reached = {n["id"]: n for root in imported(asts, by_id) for n in nodes(root, skip=lambda n: not read(n))}
    reached.update((ast["id"], ast) for ast in asts.values())
    calls = [n for n in reached.values() if n["nodeType"] == "FunctionCall"]
    callees = {n["expression"]["id"] for n in calls}
    conversions = {n["expression"]["id"] for n in calls if n["kind"] == "typeConversion"}
    fields = {v["id"] for n in reached.values() if n["nodeType"] == "StructDefinition"
              for v in n["members"]}
    based, live = live_functions(asts, by_id)
    # The bases of each contract deploying each contract: its getters see
    # their structs, in every deployment.
    deployed_bases: dict[int, list[set[int]]] = {}
    for ast in asts.values():
        for c in deployable(ast):
            for b in c["linearizedBaseContracts"]:
                deployed_bases.setdefault(b, []).append(set(c["linearizedBaseContracts"]))
    dead = {n["id"] for f in based - live if f in reached for n in nodes(by_id[f])}
    # The checker and the elaborator see the live functions and the library
    # functions the contracts reach.
    members = library_members(by_id)
    checked = live | {i for i, n in reached.items()
                      if n["nodeType"] == "FunctionDefinition" and i in members}
    # A modifier is checked and elaborated where such a function invokes it.
    invoked = {m["modifierName"].get("referencedDeclaration")
               for f in checked for m in by_id[f].get("modifiers", [])}
    dead.update(n["id"] for m in reached.values()
                if m["nodeType"] == "ModifierDefinition" and m["id"] not in invoked
                for n in nodes(m))
    # The assembly a constructor runs, in its body or its modifiers'.
    creation: set[int] = set()
    for f in live:
        if by_id[f]["kind"] == "constructor":
            used = [by_id.get(m["modifierName"].get("referencedDeclaration"), {})
                    for m in by_id[f].get("modifiers", [])]
            for root in [by_id[f]] + [m for m in used if m.get("nodeType") == "ModifierDefinition"]:
                creation.update(n["id"] for n in nodes(root) if n["nodeType"] == "InlineAssembly")
    # The signatures read only at nodes of overridden functions, unless they
    # belong to a function of an imported contract, which is read as such.
    read_at: dict[int, bool] = {}
    for n in reached.values():
        for declaration, signature in signatures(n, by_id):
            if declaration["id"] not in reached:
                read_at[signature["id"]] = read_at.get(signature["id"], False) or n["id"] not in dead
    dead.update(n["id"] for i, alive in read_at.items() if not alive for n in nodes(by_id[i]))
    errors = {n["errorCall"]["expression"].get("referencedDeclaration")
              for n in reached.values() if n["nodeType"] == "RevertStatement" and n["id"] not in dead}
    error_parameters = {v["id"] for e in errors if e in by_id for v in by_id[e]["parameters"]["parameters"]}
    builtin_callees = {n["expression"]["id"] for n in calls if n["kind"] == "functionCall"
                       and n["expression"]["nodeType"] == "Identifier"
                       and n["expression"].get("referencedDeclaration") in {REQUIRE, ASSERT, REVERT}}
    # super.f(...) in a function's body or its modifier invocations' arguments,
    # the only places the importer admits it.
    super_bases = {n["expression"]["expression"]["id"]
                   for f in reached.values() if f["nodeType"] == "FunctionDefinition"
                   for n in super_calls(f)}
    hash_callees = {n["expression"]["id"] for n in calls if n["kind"] == "functionCall"
                    and n["expression"]["nodeType"] == "Identifier"
                    and n["expression"].get("referencedDeclaration") == KECCAK256}
    plain_callees = builtin_callees | super_bases | hash_callees
    unread, found = special_forms(reached, by_id)
    file_level = {m["id"] for ast in asts.values() for m in ast["nodes"]}
    storage_bases = {n["baseExpression"]["id"] for n in reached.values()
                     if n["nodeType"] == "IndexAccess"}
    storage_bases.update(n["expression"]["id"] for n in reached.values()
                         if n["nodeType"] == "MemberAccess")
    for node in reached.values():
        if node["id"] in unread:
            continue
        blockers = (node_blockers(node, builtin_callee=node["id"] in plain_callees)
                    + callee_blockers(node, callees, conversions)
                    + elaboration_blockers(node, storage_field=node["id"] in fields,
                                           error_parameter=node["id"] in error_parameters)
                    + coerced_literals(node, by_id)
                    + assembly_blockers(node, by_id, creation=node["id"] in creation))
        if (node["nodeType"] == "VariableDeclaration" and node["stateVariable"]
                and node.get("visibility") == "public"
                and not all(has_getter(node["typeName"], by_id, bases)
                            for bases in deployed_bases.get(node.get("scope"), [set()]))):
            blockers.append(Blocker("VariableDeclaration", "public state variables", "elaboration"))
        if node["nodeType"] == "EventDefinition" and node["id"] in file_level:
            blockers.append(Blocker("EventDefinition", "file-level events", "import"))
        if any(declaration["nodeType"] == "FunctionDefinition"
               and signature is declaration["returnParameters"]
               and any(ENUM.fullmatch(p["typeDescriptions"].get("typeIdentifier") or "")
                       for p in signature["parameters"])
               for declaration, signature in signatures(node, by_id)):
            # The checker admits no enum in what an external call returns.
            blockers.append(Blocker("FunctionCall", "enums returned by external calls", "elaboration"))
        if node["id"] in builtin_callees:
            call = next(c for c in calls if c["expression"]["id"] == node["id"])
            if len(call["arguments"]) not in ({1, 2} if node["referencedDeclaration"] == REQUIRE else
                                              {1} if node["referencedDeclaration"] == ASSERT else {0, 1}):
                blockers.append(Blocker("FunctionCall", "custom errors", "import"))
        if (node["nodeType"] in {"Identifier", "IndexAccess", "MemberAccess"}
                and node.get("typeDescriptions", {}).get("typeIdentifier", "").startswith(("t_mapping$_", "t_array$_", "t_struct$_"))
                and node["id"] not in storage_bases
                and not located_array(node["typeDescriptions"]["typeIdentifier"])
                and not storage_array(node["typeDescriptions"]["typeIdentifier"])):
            tid = node["typeDescriptions"]["typeIdentifier"]
            feature = ("array values" if tid.startswith("t_array$_")
                       else "mapping values" if tid.startswith("t_mapping$_")
                       else "struct values and copying")
            blockers.append(Blocker(node["nodeType"], feature, "elaboration"))
        if blockers:
            found.setdefault(node["id"], []).extend(blockers)
    # Modifier arguments see the function's parameters, not its returns.
    for f in checked:
        returns = {v["id"] for v in by_id[f].get("returnParameters", {}).get("parameters", [])}
        for n in (n for m in by_id[f].get("modifiers", []) for a in m.get("arguments") or []
                  for n in nodes(a)):
            if n["nodeType"] == "Identifier" and n.get("referencedDeclaration") in returns:
                found.setdefault(n["id"], []).append(
                    Blocker("Identifier", "return variables in modifier arguments", "elaboration"))
    # A static memory return array is shared across a modifier's placeholders.
    for f in checked:
        if any(m.get("kind") == "modifierInvocation" for m in by_id[f].get("modifiers", [])):
            for v in by_id[f].get("returnParameters", {}).get("parameters", []):
                tid = v["typeDescriptions"].get("typeIdentifier") or ""
                if located_array(tid) and tid.endswith("_memory_ptr") and not tid.endswith("$dyn_memory_ptr"):
                    found.setdefault(v["id"], []).append(Blocker(
                        "VariableDeclaration", "static memory array returns under modifiers",
                        "elaboration"))
    for f in overloads:
        found.setdefault(f, []).append(Blocker(
            "FunctionDefinition", "overloads differing only in contract types", "import"))
    # The checker and the elaborator see only the functions nothing overrides.
    found = {i: [b for b in bs if not (i in dead and b.stage == "elaboration")]
             for i, bs in found.items() if i in reached}
    return {i: bs for i, bs in found.items() if bs}


# The HOL run


def run_hol(holbuild: str, work: Path, units: list[tuple[str, Path]]) -> dict[str, dict[str, Any]]:
    """Import and elaborate every unit, in one HOL session; the result of each
    test by name."""
    manifest = work / "manifest.txt"
    manifest.write_text("".join(f"{name}\t{path}\n" for name, path in units), encoding="utf-8")
    log = work / "hol.log"
    # `holbuild run` loads built theories but does not build them.
    build = [holbuild, "-j8", "build", "--skip-checkpoints", "--skip-proof-steps", "solidityPrepareLib",
             "solidityElaborateTheory"]
    print("+", " ".join(build), file=sys.stderr, flush=True)
    subprocess.run(build, cwd=ROOT, check=True)
    command = [holbuild, "-j1", "run", str(HOL_SCRIPT)]
    print("+", " ".join(command), file=sys.stderr, flush=True)
    with log.open("w", encoding="utf-8") as stream:
        status = subprocess.run(
            command, cwd=ROOT, stdin=subprocess.DEVNULL, stdout=stream,
            stderr=subprocess.STDOUT,
            env={**os.environ, "SEMANTIC_TESTS_MANIFEST": str(manifest)},
        ).returncode
    results = {}
    for line in log.read_text(encoding="utf-8", errors="replace").splitlines():
        if line.startswith(RESULT_PREFIX):
            try:
                result = json.loads(line[len(RESULT_PREFIX):])
            except json.JSONDecodeError as error:
                raise SystemExit(f"malformed HOL result: {line!r}: {error}") from error
            results[result["test"]] = result
    missing = [name for name, _ in units if name not in results]
    if status != 0 or missing:
        tail = "".join(log.read_text(encoding="utf-8", errors="replace").splitlines(True)[-30:])
        raise SystemExit(f"the HOL run failed (status {status}, {len(missing)} tests "
                         f"without a result):\n{tail}")
    return results


# Classification


@dataclass
class Classification:
    """A test's category, the first construct the importer rejected, and every
    construct the scan found that the semantics does not support."""

    test: str
    category: str
    reason: str | None = None
    first: Blocker | None = None
    blockers: list[Blocker] = field(default_factory=list)
    scan_agrees: bool = True
    # of an admitted unit: the functions calls reach, and the reasons of the
    # unsupported ones
    functions: int = 0
    unsupported: list[str] = field(default_factory=list)


def classify(test: str, scanned: dict[int, list[Blocker]], hol: dict[str, Any]) -> Classification:
    """Combine the importer's and elaborator's verdict with the scan. The scan
    agrees if it finds nothing in an admitted test, only elaboration-stage
    blockers in a test the elaborator rejects, and an import-stage blocker at
    the node the importer rejected."""
    blockers = sorted({b for bs in scanned.values() for b in bs},
                      key=lambda b: (b.feature, b.node_type, b.stage))
    stages = {b.stage for b in blockers}
    status = hol["status"]
    message = hol.get("message")
    if status == ADMITTED:
        return Classification(test, ADMITTED, blockers=blockers, scan_agrees=not blockers,
                              functions=hol.get("functions", 0))
    if status == PARTIALLY_ADMITTED:
        # The scan doesn't tell functions apart, so it isn't compared here.
        return Classification(test, PARTIALLY_ADMITTED, blockers=blockers,
                              functions=hol["functions"], unsupported=hol["unsupported"])
    if status in (ELABORATION_REJECTED, SOURCE_REJECTED):
        return Classification(test, status, message, blockers=blockers,
                              scan_agrees=stages == {"elaboration"})
    if status in (MALFORMED_INPUT, INVALID_CORE):
        return Classification(test, status, message, blockers=blockers, scan_agrees=False)
    if status != IMPORT_REJECTED:
        raise ValueError(f"{test}: unknown HOL status {status!r}")
    match = IMPORT_ERROR_NODE.match(message or "")
    at_node = [b for b in scanned.get(int(match.group(2)), []) if b.stage == "import"] if match else []
    first = at_node[0] if at_node else Blocker(match.group(1) if match else "?", "unclassified", "import")
    return Classification(test, IMPORT_REJECTED, message, first, blockers,
                          scan_agrees=bool(at_node))


# The report


@dataclass
class Report:
    pin: str
    profile: str
    results: list[Classification]

    def counts(self) -> Counter[str]:
        return Counter(r.category for r in self.results)

    def function_reasons(self) -> Counter[str]:
        """The reasons functions of admitted units are unsupported, without the
        node ids of import errors."""
        reasons: Counter[str] = Counter()
        for r in self.results:
            for reason in r.unsupported:
                match = IMPORT_ERROR_NODE.match(reason)
                reasons[f"{match.group(1)}: {match.group(3)}" if match else reason] += 1
        return reasons

    def rejected(self) -> list[Classification]:
        return [r for r in self.results if r.category in (IMPORT_REJECTED, ELABORATION_REJECTED, SOURCE_REJECTED)]

    def feature_ranking(self) -> list[dict[str, Any]]:
        """Features by how many rejected tests they occur in, with how many
        they are the only blocker of and how many the importer stopped at."""
        rejected = self.rejected()
        blocking: Counter[str] = Counter()
        only: Counter[str] = Counter()
        first: Counter[str] = Counter()
        node_types: dict[str, set[str]] = {}
        for r in rejected:
            features = {b.feature for b in r.blockers}
            for b in r.blockers:
                node_types.setdefault(b.feature, set()).add(b.node_type)
            blocking.update(features)
            if len(features) == 1:
                only.update(features)
            if r.first is not None:
                first[r.first.feature] += 1
        return [
            {"feature": f, "node_types": sorted(node_types.get(f, ())), "tests": n,
             "only_blocker": only[f], "first_rejection": first[f]}
            for f, n in sorted(blocking.items(), key=lambda kv: (-kv[1], -only[kv[0]], kv[0]))
        ]

    def greedy_order(self, limit: int) -> list[tuple[str, int]]:
        """Features in the order that admits the most rejected tests at each
        step, by the scan, with the number admitted once all up to it are
        supported. Ties go to the feature occurring in more tests."""
        tests = [{b.feature for b in r.blockers} for r in self.rejected()]
        occurrences = Counter(f for features in tests for f in features)
        chosen: set[str] = set()
        order = []
        for _ in range(min(limit, len(occurrences))):
            def admitted(f: str) -> int:
                return sum(1 for features in tests if features <= chosen | {f})
            best = max(sorted(set(occurrences) - chosen),
                       key=lambda f: (admitted(f), occurrences[f]))
            order.append((best, admitted(best)))
            chosen.add(best)
        return order

    def json(self) -> dict[str, Any]:
        return {
            "format": REPORT_FORMAT,
            "solidity_pin": self.pin,
            "profile": self.profile,
            "counts": {c: self.counts()[c] for c in CATEGORIES},
            "functions": {"total": sum(r.functions for r in self.results),
                          "unsupported": sum(len(r.unsupported) for r in self.results)},
            "features": self.feature_ranking(),
            "greedy_order": [{"feature": f, "admitted": n} for f, n in self.greedy_order(GREEDY_STEPS)],
            "tests": [
                {"test": r.test, "category": r.category, "reason": r.reason,
                 "first": r.first.feature if r.first else None,
                 "features": sorted({b.feature for b in r.blockers}),
                 "scan_agrees": r.scan_agrees,
                 "functions": r.functions, "unsupported": r.unsupported}
                for r in self.results
            ],
        }

    def markdown(self) -> str:
        counts = self.counts()
        total = len(self.results)
        disagreements = [r for r in self.results if not r.scan_agrees]
        lines = [
            "# Coverage of solc's semantic tests",
            "",
            "Generated by `tools/semantic_tests_coverage.py`; do not edit by hand.",
            "",
            f"Every test under `{TESTS_DIR.as_posix()}` of argotorg/solidity at "
            f"`{self.pin}` was compiled with profile `{self.profile}`, imported by "
            "`solidityPrepareLib`, including source validation, elaboration and full core checking. Call expectations "
            "(the `// ----` sections) are not run, so an admitted test is one the "
            "semantics accepts, not one it is known to agree on. A test is admitted "
            "when every function calls reach is supported, and partially admitted "
            "when the unit is admitted with some of them unsupported: those have no "
            "procedure and a call of them is refused.",
            "",
            "`source-rejected` records a failed `valid_src_unit` check. That check",
            "mixes subset restrictions and consistency checks; this category does",
            "not establish that a feature is unsupported. The scan only identifies",
            "known blockers present in the same test.",
            "",
            "To regenerate it from the repository root, with the pinned solc and the "
            "tests checked out outside the repository:",
            "",
            "```sh",
            "git init ../solidity-tests && cd ../solidity-tests",
            "git remote add origin https://github.com/argotorg/solidity.git",
            f"git sparse-checkout set --no-cone {TESTS_DIR.as_posix()}",
            f"git fetch --depth 1 --filter=blob:none origin {self.pin}",
            "git checkout FETCH_HEAD && cd -",
            "tools/semantic_tests_coverage.py ../solidity-tests --solc /path/to/solc",
            "```",
            "",
            "| outcome | tests |",
            "| --- | ---: |",
        ]
        lines += [f"| {c} | {counts[c]} |" for c in CATEGORIES]
        lines += [f"| total | {total} |", ""]
        functions = sum(r.functions for r in self.results)
        unsupported = sum(len(r.unsupported) for r in self.results)
        lines += [
            "## Functions of admitted units",
            "",
            f"The {counts[ADMITTED] + counts[PARTIALLY_ADMITTED]} admitted and partially "
            f"admitted tests have {functions} functions that calls reach, library "
            f"functions included; {functions - unsupported} are supported and "
            f"{unsupported} unsupported, for these reasons (an import error by the "
            "node type it stopped at):",
            "",
            "| reason | functions |",
            "| --- | ---: |",
        ]
        lines += [f"| {reason} | {n} |" for reason, n in self.function_reasons().most_common()]
        lines += [""]
        lines += [
            "## Features blocking rejected tests",
            "",
            "Each rejected test is scanned for every construct the importer or the "
            "elaborator rejects. *tests* counts the rejected tests a feature occurs in; "
            "*only blocker* the tests in which it is the only feature found, which "
            "supporting it would admit as far as the scan can tell; *first* the tests "
            "the importer stopped at it.",
            "",
            f"The scan disagrees with the HOL run on {len(disagreements)} tests"
            + (", listed at the end." if disagreements else "."),
            "",
            "| feature | AST nodes | tests | only blocker | first |",
            "| --- | --- | ---: | ---: | ---: |",
        ]
        for f in self.feature_ranking():
            node_types = ", ".join(f"`{t}`" for t in f["node_types"])
            lines.append(f"| {f['feature']} | {node_types} | {f['tests']} | "
                         f"{f['only_blocker']} | {f['first_rejection']} |")
        lines += [
            "",
            "## Features in order of tests admitted",
            "",
            "Supporting the features in this order admits the most rejected tests at "
            "each step, by the scan; *admitted* counts the tests admitted once every "
            "feature up to that row is supported. It ignores how hard a feature is.",
            "",
            "| step | feature | admitted |",
            "| ---: | --- | ---: |",
        ]
        lines += [f"| {i} | {f} | {n} |" for i, (f, n) in enumerate(self.greedy_order(GREEDY_STEPS), 1)]
        lines += ["", "## Skipped and compile failures", "", "| reason | tests |", "| --- | ---: |"]
        reasons = Counter(r.reason if r.category == SKIPPED else "compile failure"
                          for r in self.results if r.category in (SKIPPED, COMPILE_FAILURE))
        lines += [f"| {reason} | {n} |" for reason, n in sorted(reasons.items(), key=lambda kv: -kv[1])]
        for title, category in (("Admitted", ADMITTED),
                                ("Partially admitted", PARTIALLY_ADMITTED),
                                ("Source validation rejections", SOURCE_REJECTED),
                                ("Elaborator rejections", ELABORATION_REJECTED)):
            lines += ["", f"## {title}", ""]
            tests = [r for r in self.results if r.category == category]
            lines += [f"- `{r.test}`" + (f": {r.reason}" if r.reason else "") for r in tests] or ["None."]
        if disagreements:
            lines += ["", "## Scan disagreements", ""]
            lines += [f"- `{r.test}` ({r.category}): {r.reason}" for r in disagreements]
        return "\n".join(lines) + "\n"


def parse_args(argv: list[str] | None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("solidity", type=Path,
                        help="a checkout of argotorg/solidity at SOLIDITY_PIN")
    parser.add_argument("--solc", required=True, type=Path)
    parser.add_argument("--holbuild", default="holbuild")
    parser.add_argument("-j", "--jobs", type=int, default=os.cpu_count())
    parser.add_argument("--output", type=Path, default=ROOT / "docs" / "semantic-tests-coverage",
                        help="report path without extension; .md and .json are written")
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv)
    pin = exporter.PIN_FILE.read_text(encoding="ascii").strip()
    profile = exporter.read_json(exporter.DEFAULT_PROFILE)
    # Checked once here, so that every failure below is the test's own.
    exporter.compiler_identity(args.solc, profile["compilerVersion"], pin)
    tests_root = args.solidity / TESTS_DIR
    tests = [read_test(tests_root, path) for path in find_tests(tests_root)]

    results: dict[str, Classification] = {}
    to_compile = []
    for test in tests:
        reason = skip_reason(test, profile)
        if reason is not None:
            results[test.name] = Classification(test.name, SKIPPED, reason)
        else:
            to_compile.append(test)

    def compile_one(test: SemanticTest) -> tuple[SemanticTest, dict[str, Any] | str]:
        try:
            return test, compile_test(args.solc, test, exporter.DEFAULT_PROFILE)
        except SystemExit as error:
            return test, str(error)

    with tempfile.TemporaryDirectory(prefix="semantic-tests-") as temporary:
        work = Path(temporary)
        compiled: dict[str, dict[str, Any]] = {}
        units = []
        with ThreadPoolExecutor(max_workers=args.jobs) as pool:
            for index, (test, outcome) in enumerate(pool.map(compile_one, to_compile)):
                if isinstance(outcome, str):
                    results[test.name] = Classification(test.name, COMPILE_FAILURE, outcome)
                    continue
                compiled[test.name] = outcome
                path = work / f"{index}.json"
                path.write_text(json.dumps(outcome), encoding="utf-8")
                units.append((test.name, path))
        print(f"{len(tests)} tests, {len(units)} compiled", file=sys.stderr, flush=True)
        hol = run_hol(args.holbuild, work, units)
    for name, sources in compiled.items():
        results[name] = classify(name, scan({source: data["ast"] for source, data in sources["output"]["sources"].items()}),
                                 hol[name])

    report = Report(pin, exporter.DEFAULT_PROFILE.stem, [results[t.name] for t in tests])
    exporter.write_json_atomic(args.output.with_suffix(".json"), report.json())
    args.output.with_suffix(".md").write_text(report.markdown(), encoding="utf-8")
    counts = report.counts()
    print(", ".join(f"{counts[c]} {c}" for c in CATEGORIES), file=sys.stderr)
    return 1 if counts[MALFORMED_INPUT] or counts[INVALID_CORE] else 0


if __name__ == "__main__":
    sys.exit(main())
