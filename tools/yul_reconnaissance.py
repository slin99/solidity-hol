#!/usr/bin/env python3
"""Reconnaissance: the Yul subset the pinned solc emits, unoptimized and
optimized.

Compiles every fixture under `testdata/` with the pinned compiler and the
`solc-0.8.37-via-ir-osaka` profile, asks for the `ir` and `irOptimized`
artifacts, parses each with the small Yul parser below, and enumerates

  * the Yul node kinds that occur,
  * the builtins that occur -- a call to a name that no `function` definition
    in the same object binds, which is how the dialect supplies its builtin set,
  * the object-level forms (subobjects, `code` and `data` sections, and the
    object-level builtins `datasize`, `dataoffset`, `datacopy`, `verbatim_*`,
    `memoryguard`, `linkersymbol`, `setimmutable`, `loadimmutable`),

each with the fixtures that exercise it, split into the creation object (the
top-level `object`) and the runtime object (the nested one whose name ends in
`_deployed`).  Nothing is filtered: what the fixtures do not exercise is simply
absent from the result.

The enumeration is per stage, in the order the compiler's pipeline produces
them: `ir`, then `irOptimized` with the optimizer off, then `irOptimized` with
the optimizer on at the profile's run count.  The compiler prints the two
artifacts through different paths, so `irOptimized` is not the same text as
`ir` even with the optimizer off, and the report keeps all three rather than
treating any one of them as another's input.  Each fixture is compiled once per
optimizer setting, both its artifacts at once.

The parser accepts the Yul dialect of the compiler's IR printer: identifiers
(including `.`-qualified and `$`-escaped ones), hex/binary/decimal numbers,
string and `hex"..."` literals, `true`/`false`, and the doc comments the printer
emits (`/// @use-src`, `/// @src`).  Anything else is a syntax error rather than
a silent skip, so the enumeration fails closed.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import hashlib
from pathlib import Path
import re
import sys
from typing import Any, Iterator

sys.path.insert(0, str(Path(__file__).resolve().parent))

from export_solc_artifacts import (  # noqa: E402
    DEFAULT_PROFILE,
    PIN_FILE,
    ROOT,
    compile_standard_json,
    compiler_identity,
    read_json,
    write_json_atomic,
)

FIXTURE_DIRS = (ROOT / "testdata" / "frontend", ROOT / "testdata" / "differential")
# Both artifacts are requested in one compile, so each fixture is compiled once
# per optimizer setting and the stages below pick their artifact out of it.
ARTIFACTS = ("ir", "irOptimized")
OUTPUT_SELECTION: dict[str, dict[str, list[str]]] = {"*": {"*": list(ARTIFACTS)}}


@dataclass(frozen=True)
class Stage:
    """One point of the compiler's Yul pipeline that the report enumerates."""

    id: str
    artifact: str
    optimizer_enabled: bool


# The stages, in pipeline order: the unoptimized artifact, then the optimized
# one with the Yul optimizer off and on.  `irOptimized` differs from `ir` even
# with the optimizer off, so no stage stands in for another's input.
STAGES = (
    Stage(id="ir", artifact="ir", optimizer_enabled=False),
    Stage(id="ir-optimized-off", artifact="irOptimized", optimizer_enabled=False),
    Stage(id="ir-optimized-on", artifact="irOptimized", optimizer_enabled=True),
)

# The EVM dialect's builtin set, from the Solidity documentation's "Yul / EVM
# dialect" list plus the object-level builtins.  A call to a name outside it
# would mean the parser mis-attributed something to the dialect, so the report
# carries those names separately instead of quietly counting them as builtins.
EVM_DIALECT_BUILTINS = frozenset(
    """stop add sub mul div sdiv mod smod addmod mulmod exp signextend lt gt slt sgt
    eq iszero and or xor not byte shl shr sar keccak256 address balance selfbalance
    origin caller callvalue calldataload calldatasize calldatacopy codesize codecopy
    gasprice extcodesize extcodecopy returndatasize returndatacopy extcodehash
    create create2 call callcode delegatecall staticcall mload mstore mstore8 mcopy
    sload sstore tload tstore msize gas blockhash coinbase timestamp number
    difficulty prevrandao gaslimit chainid basefee blobhash blobbasefee log0 log1
    log2 log3 log4 return revert selfdestruct invalid pop memoryguard linkersymbol
    setimmutable loadimmutable datasize dataoffset datacopy""".split()
)

VERBATIM_RE = re.compile(r"verbatim_\d+i_\d+o")

# The object-level forms reported one by one, present or absent.
OBJECT_LEVEL_FORMS = ("datasize", "dataoffset", "datacopy", "verbatim", "data", "subobject")

ROLES = ("creation", "runtime", "subobject")

IDENT_START = set("ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz_$")
IDENT_CONT = IDENT_START | set("0123456789.")
NUMBER_RE = re.compile(r"0[xX][0-9a-fA-F]+|0[bB][01]+|[0-9]+")
IDENT_RE = re.compile(r"[A-Za-z_$][A-Za-z_$0-9.]*")

NODE_KINDS = (
    "block",
    "functionDefinition",
    "variableDeclaration",
    "assignment",
    "if",
    "switch",
    "case",
    "default",
    "for",
    "break",
    "continue",
    "leave",
    "expressionStatement",
    "functionCall",
    "identifier",
    "literal",
)
LITERAL_KINDS = ("number", "string", "hexString", "bool")


class YulSyntaxError(Exception):
    """The fixture is outside the Yul dialect this parser accepts."""


@dataclass(frozen=True)
class Token:
    kind: str
    text: str
    line: int


def tokenize(text: str) -> list[Token]:
    tokens: list[Token] = []
    i = 0
    n = len(text)
    line = 1
    while i < n:
        c = text[i]
        if c == "\n":
            line += 1
            i += 1
        elif c in " \t\r":
            i += 1
        elif text.startswith("//", i):
            newline = text.find("\n", i)
            i = n if newline < 0 else newline
        elif text.startswith("/*", i):
            end = text.find("*/", i + 2)
            if end < 0:
                raise YulSyntaxError(f"unterminated comment opened on line {line}")
            line += text.count("\n", i, end)
            i = end + 2
        elif text.startswith(":=", i):
            tokens.append(Token("punct", ":=", line))
            i += 2
        elif text.startswith("->", i):
            tokens.append(Token("punct", "->", line))
            i += 2
        elif c in "{}()[],:":
            tokens.append(Token("punct", c, line))
            i += 1
        elif c == '"':
            end = i + 1
            while end < n and text[end] != '"':
                end += 2 if text[end] == "\\" else 1
            if end >= n:
                raise YulSyntaxError(f"unterminated string opened on line {line}")
            tokens.append(Token("string", text[i : end + 1], line))
            line += text.count("\n", i, end)
            i = end + 1
        elif c.isdigit():
            match = NUMBER_RE.match(text, i)
            assert match is not None
            tokens.append(Token("number", match.group(0), line))
            i = match.end()
        elif c in IDENT_START:
            match = IDENT_RE.match(text, i)
            assert match is not None
            word = match.group(0)
            end = match.end()
            if word == "hex" and end < n and text[end] == '"':
                close = text.find('"', end + 1)
                if close < 0:
                    raise YulSyntaxError(f"unterminated hex string on line {line}")
                tokens.append(Token("hexString", text[i : close + 1], line))
                i = close + 1
            else:
                tokens.append(Token("ident", word, line))
                i = end
        else:
            raise YulSyntaxError(f"unexpected character {c!r} on line {line}")
    tokens.append(Token("eof", "", line))
    return tokens


class Parser:
    """Recursive descent over the Yul grammar, including object sections."""

    def __init__(self, tokens: list[Token]) -> None:
        self.tokens = tokens
        self.pos = 0

    def peek(self) -> Token:
        return self.tokens[self.pos]

    def take(self) -> Token:
        token = self.tokens[self.pos]
        self.pos += 1
        return token

    def at_punct(self, text: str) -> bool:
        token = self.peek()
        return token.kind == "punct" and token.text == text

    def at_keyword(self, text: str) -> bool:
        token = self.peek()
        return token.kind == "ident" and token.text == text

    def expect_punct(self, text: str) -> None:
        token = self.take()
        if token.kind != "punct" or token.text != text:
            raise YulSyntaxError(
                f"expected {text!r} on line {token.line}, found {token.text!r}"
            )

    def expect_ident(self) -> str:
        token = self.take()
        if token.kind != "ident":
            raise YulSyntaxError(
                f"expected an identifier on line {token.line}, found {token.text!r}"
            )
        return token.text

    def take_literal(self) -> dict[str, Any]:
        token = self.take()
        if token.kind == "number":
            return {"kind": "literal", "literalKind": "number", "value": token.text}
        if token.kind == "string":
            return {"kind": "literal", "literalKind": "string",
                    "value": string_value(token.text)}
        if token.kind == "hexString":
            return {"kind": "literal", "literalKind": "hexString", "value": token.text}
        if token.kind == "ident" and token.text in ("true", "false"):
            return {"kind": "literal", "literalKind": "bool", "value": token.text}
        raise YulSyntaxError(f"expected a literal on line {token.line}")

    # -- statements --------------------------------------------------------

    def parse_block(self) -> dict[str, Any]:
        self.expect_punct("{")
        statements = []
        while not self.at_punct("}"):
            statements.append(self.parse_statement())
        self.expect_punct("}")
        return {"kind": "block", "statements": statements}

    def parse_statement(self) -> dict[str, Any]:
        if self.at_punct("{"):
            return self.parse_block()
        token = self.peek()
        if token.kind == "ident":
            keyword = token.text
            if keyword == "function":
                return self.parse_function_definition()
            if keyword == "let":
                self.take()
                return self.parse_variable_declaration()
            if keyword == "if":
                self.take()
                condition = self.parse_expression()
                return {"kind": "if", "condition": condition, "body": self.parse_block()}
            if keyword == "switch":
                return self.parse_switch()
            if keyword == "for":
                return self.parse_for()
            if keyword in ("break", "continue", "leave"):
                self.take()
                return {"kind": keyword}
        if self.looks_like_assignment():
            return self.parse_assignment()
        return {"kind": "expressionStatement", "expression": self.parse_expression()}

    def looks_like_assignment(self) -> bool:
        i = self.pos
        while True:
            if self.tokens[i].kind != "ident":
                return False
            i += 1
            token = self.tokens[i]
            if token.kind == "punct" and token.text == ":=":
                return True
            if token.kind == "punct" and token.text == ",":
                i += 1
                continue
            return False

    def parse_typed_identifiers(self, terminator: str) -> list[str]:
        names: list[str] = []
        while not self.at_punct(terminator):
            names.append(self.expect_ident())
            if self.at_punct(":"):
                self.take()
                self.expect_ident()
            if self.at_punct(","):
                self.take()
                continue
            break
        return names

    def parse_function_definition(self) -> dict[str, Any]:
        self.take()  # function
        name = self.expect_ident()
        self.expect_punct("(")
        parameters = self.parse_typed_identifiers(")")
        self.expect_punct(")")
        returns: list[str] = []
        if self.at_punct("->"):
            self.take()
            returns = self.parse_typed_identifiers("{")
        return {
            "kind": "functionDefinition",
            "name": name,
            "parameters": parameters,
            "returns": returns,
            "body": self.parse_block(),
        }

    def parse_variable_declaration(self) -> dict[str, Any]:
        names = self.parse_typed_identifiers(":=")
        value = None
        if self.at_punct(":="):
            self.take()
            value = self.parse_expression()
        return {"kind": "variableDeclaration", "names": names, "value": value}

    def parse_assignment(self) -> dict[str, Any]:
        names = []
        while True:
            names.append(self.expect_ident())
            if self.at_punct(","):
                self.take()
                continue
            break
        self.expect_punct(":=")
        return {"kind": "assignment", "names": names, "value": self.parse_expression()}

    def parse_switch(self) -> dict[str, Any]:
        self.take()  # switch
        expression = self.parse_expression()
        cases = []
        default = None
        while self.at_keyword("case") or self.at_keyword("default"):
            if self.at_keyword("case"):
                self.take()
                value = self.take_literal()
                cases.append({"kind": "case", "value": value, "body": self.parse_block()})
            else:
                self.take()
                default = {"kind": "default", "body": self.parse_block()}
        return {
            "kind": "switch",
            "expression": expression,
            "cases": cases,
            "default": default,
        }

    def parse_for(self) -> dict[str, Any]:
        self.take()  # for
        init = self.parse_block()
        condition = self.parse_expression()
        post = self.parse_block()
        return {
            "kind": "for",
            "init": init,
            "condition": condition,
            "post": post,
            "body": self.parse_block(),
        }

    # -- expressions -------------------------------------------------------

    def parse_expression(self) -> dict[str, Any]:
        token = self.peek()
        if token.kind != "ident":
            return self.take_literal()
        if token.text in ("true", "false"):
            return self.take_literal()
        if self.tokens[self.pos + 1].kind == "punct" and \
                self.tokens[self.pos + 1].text == "(":
            return self.parse_function_call()
        self.take()
        return {"kind": "identifier", "name": token.text}

    def parse_function_call(self) -> dict[str, Any]:
        name = self.expect_ident()
        self.expect_punct("(")
        arguments = []
        while not self.at_punct(")"):
            arguments.append(self.parse_expression())
            if self.at_punct(","):
                self.take()
                continue
            break
        self.expect_punct(")")
        return {"kind": "functionCall", "functionName": name, "arguments": arguments}

    # -- objects -----------------------------------------------------------

    def parse_object(self) -> dict[str, Any]:
        if not self.at_keyword("object"):
            raise YulSyntaxError(
                f"expected 'object' on line {self.peek().line}, found {self.peek().text!r}"
            )
        self.take()
        name = self.take_literal()
        self.expect_punct("{")
        code: dict[str, Any] | None = None
        data: list[dict[str, Any]] = []
        objects: list[dict[str, Any]] = []
        while not self.at_punct("}"):
            if self.at_keyword("code"):
                self.take()
                if code is not None:
                    raise YulSyntaxError("object has more than one code section")
                code = self.parse_block()
            elif self.at_keyword("object"):
                objects.append(self.parse_object())
            elif self.at_keyword("data"):
                self.take()
                section_name = self.take_literal()
                section_value = self.take_literal()
                data.append(
                    {
                        "kind": "data",
                        "name": section_name["value"],
                        "value": section_value["value"],
                    }
                )
            else:
                token = self.peek()
                raise YulSyntaxError(
                    f"unexpected {token.text!r} in object body on line {token.line}"
                )
        self.expect_punct("}")
        return {"kind": "object", "name": name["value"], "code": code, "data": data,
                "objects": objects}

    def parse_object_file(self) -> list[dict[str, Any]]:
        objects = []
        while self.peek().kind != "eof":
            objects.append(self.parse_object())
        return objects


def parse_object_file(text: str) -> list[dict[str, Any]]:
    """The Yul objects in an `ir` artifact, in source order."""
    parser = Parser(tokenize(text))
    objects = parser.parse_object_file()
    if not objects:
        raise YulSyntaxError("the artifact contains no Yul object")
    return objects


# -- enumeration ----------------------------------------------------------


CHILD_KEYS = ("statements", "arguments", "cases", "value", "condition", "expression",
              "body", "init", "post", "default", "code")


def iter_nodes(node: dict[str, Any]) -> Iterator[dict[str, Any]]:
    """The node and everything under it, but not a nested object's own code."""
    yield node
    for key in CHILD_KEYS:
        child = node.get(key)
        if isinstance(child, dict):
            yield from iter_nodes(child)
        elif isinstance(child, list):
            for item in child:
                if isinstance(item, dict):
                    yield from iter_nodes(item)


def string_value(text: str) -> str:
    """The value of a string literal, without its quotes."""
    if len(text) < 2 or not text.startswith('"') or not text.endswith('"'):
        return text
    body = text[1:-1]
    escapes = {"n": "\n", "t": "\t", "r": "\r", '"': '"', "\\": "\\", "'": "'"}
    return re.sub(r"\\(.)", lambda m: escapes.get(m.group(1), m.group(1)), body)


def defined_functions(code: dict[str, Any] | None) -> set[str]:
    if code is None:
        return set()
    return {
        node["name"]
        for node in iter_nodes(code)
        if node["kind"] == "functionDefinition"
    }


@dataclass
class ObjectFacts:
    name: str
    depth: int
    node_kinds: dict[str, int]
    builtins: dict[str, int]
    data_sections: int
    subobjects: int

    @property
    def role(self) -> str:
        return "creation" if self.depth == 0 else "runtime"


def object_facts(obj: dict[str, Any], depth: int = 0) -> list[ObjectFacts]:
    """Facts for this object and its subobjects, depth first."""
    code = obj["code"]
    defined = defined_functions(code)
    node_kinds: dict[str, int] = {}
    builtins: dict[str, int] = {}
    for node in iter_nodes(obj) if code is not None else []:
        if node is obj:
            continue
        kind = node["kind"]
        if kind == "literal":
            kind = f"literal:{node['literalKind']}"
        node_kinds[kind] = node_kinds.get(kind, 0) + 1
        if kind == "functionCall" and node["functionName"] not in defined:
            builtins[node["functionName"]] = builtins.get(node["functionName"], 0) + 1
    facts = [
        ObjectFacts(
            name=obj["name"],
            depth=depth,
            node_kinds=node_kinds,
            builtins=builtins,
            data_sections=len(obj["data"]),
            subobjects=len(obj["objects"]),
        )
    ]
    for child in obj["objects"]:
        facts.extend(object_facts(child, depth + 1))
    return facts


def role_of(facts: list[ObjectFacts], runtime_names: set[str]) -> str:
    if facts.depth == 0:
        return "creation"
    if facts.name in runtime_names:
        return "runtime"
    return "subobject"


def analyse_artifact(ir: str) -> list[dict[str, Any]]:
    """The role, node kinds and builtins of each object in one `ir` artifact."""
    all_facts = [fact for obj in parse_object_file(ir) for fact in object_facts(obj)]
    runtime_names = {fact.name for fact in all_facts if fact.name.endswith("_deployed")}
    return [
        {
            "name": fact.name,
            "role": role_of(fact, runtime_names),
            "depth": fact.depth,
            "nodeKinds": fact.node_kinds,
            "builtins": fact.builtins,
            "dataSections": fact.data_sections,
            "subobjects": fact.subobjects,
        }
        for fact in all_facts
    ]


# -- driver ---------------------------------------------------------------


def fixture_sources() -> list[Path]:
    sources = sorted(
        path for directory in FIXTURE_DIRS for path in directory.glob("*.sol")
    )
    if not sources:
        raise SystemExit("no fixtures found under testdata/")
    return sources


def source_name(path: Path) -> str:
    return path.resolve().relative_to(ROOT).as_posix()


def optimizer_settings(settings: dict[str, Any], enabled: bool) -> dict[str, Any]:
    """The profile's optimizer settings with `enabled` forced: the run count
    and everything else about the optimizer stay the profile's."""
    optimizer = dict(settings.get("optimizer") or {})
    optimizer["enabled"] = enabled
    return optimizer


def compile_fixture(
    solc: Path, path: Path, profile_path: Path, optimizer_enabled: bool
) -> dict[str, dict[str, str]]:
    """Both Yul artifacts of every contract in one fixture, from one compile."""
    profile = read_json(profile_path)
    settings = profile.get("settings")
    if not isinstance(settings, dict):
        raise SystemExit(f"{profile_path} must contain a settings object")
    name = source_name(path)
    compiler_input = {
        "language": "Solidity",
        "sources": {name: {"content": path.read_text(encoding="utf-8")}},
        "settings": {
            **settings,
            "optimizer": optimizer_settings(settings, optimizer_enabled),
            "outputSelection": OUTPUT_SELECTION,
        },
    }
    output = compile_standard_json(solc, compiler_input)
    # A source that only declares types and free functions for the fixtures
    # importing it compiles to no contract.
    contracts = output.get("contracts", {}).get(name, {})
    artifacts: dict[str, dict[str, str]] = {}
    for contract, section in sorted(contracts.items()):
        if not any(section.get(artifact) for artifact in ARTIFACTS):
            continue  # an interface or abstract contract has no code
        text_of = {}
        for artifact in ARTIFACTS:
            text = section.get(artifact)
            if not isinstance(text, str) or not text.strip():
                raise SystemExit(f"solc produced no {artifact} for {name}:{contract}")
            text_of[artifact] = text
        artifacts[contract] = text_of
    return artifacts


def add_counts(
    counts: dict[str, dict[str, Any]],
    role: str,
    source: str,
    occurrences: dict[str, int],
) -> None:
    for name, count in occurrences.items():
        entry = counts.setdefault(name, dict.fromkeys(ROLES, 0) | {"fixtures": set()})
        entry[role] += count
        entry["fixtures"].add(source)


def build_report(fixtures: list[dict[str, Any]]) -> dict[str, Any]:
    nodes: dict[str, dict[str, Any]] = {}
    builtins: dict[str, dict[str, Any]] = {}
    for fixture in fixtures:
        for contract in fixture["contracts"]:
            for obj in contract["objects"]:
                add_counts(nodes, obj["role"], fixture["source"], obj["nodeKinds"])
                add_counts(builtins, obj["role"], fixture["source"], obj["builtins"])

    def table(counts: dict[str, dict[str, Any]]) -> dict[str, Any]:
        out = {}
        for name in sorted(counts):
            entry = counts[name]
            out[name] = {
                **{role: entry[role] for role in ROLES},
                "fixtures": sorted(entry["fixtures"]),
            }
        return out

    return {
        "nodeKinds": table(nodes),
        "builtins": table(builtins),
        "objectLevelForms": object_level_forms(fixtures),
        "unknownBuiltins": {
            name: entry
            for name, entry in table(builtins).items()
            if name not in EVM_DIALECT_BUILTINS and not VERBATIM_RE.fullmatch(name)
        },
    }


def add_occurrences(
    counts: dict[str, dict[str, Any]],
    role: str,
    source: str,
    name: str,
    count: int,
) -> None:
    entry = counts.setdefault(name, dict.fromkeys(ROLES, 0) | {"fixtures": set()})
    entry[role] += count
    entry["fixtures"].add(source)


def object_level_forms(fixtures: list[dict[str, Any]]) -> dict[str, Any]:
    forms: dict[str, dict[str, Any]] = {
        name: dict.fromkeys(ROLES, 0) | {"fixtures": set()}
        for name in OBJECT_LEVEL_FORMS
    }
    for fixture in fixtures:
        for contract in fixture["contracts"]:
            for obj in contract["objects"]:
                role = obj["role"]
                if obj["dataSections"]:
                    add_occurrences(forms, role, fixture["source"], "data",
                                    obj["dataSections"])
                if obj["subobjects"] and obj["depth"] == 0:
                    add_occurrences(forms, role, fixture["source"], "subobject",
                                    obj["subobjects"])
                for name, count in obj["builtins"].items():
                    key = "verbatim" if VERBATIM_RE.fullmatch(name) else name
                    if key in forms:
                        add_occurrences(forms, role, fixture["source"], key, count)
    return {
        name: {**entry, "fixtures": sorted(entry["fixtures"])}
        for name, entry in sorted(forms.items())
    }


def fixtures_for_stage(
    fixtures: list[dict[str, Any]], stage: str
) -> list[dict[str, Any]]:
    """The fixtures with each contract's objects narrowed to one stage."""
    return [
        {
            **fixture,
            "contracts": [
                {
                    **contract,
                    "objects": [
                        obj for obj in contract["objects"] if obj["stage"] == stage
                    ],
                }
                for contract in fixture["contracts"]
            ],
        }
        for fixture in fixtures
    ]


def build_artifact(solc: Path, profile_path: Path) -> dict[str, Any]:
    pin = PIN_FILE.read_text(encoding="ascii").strip()
    if re.fullmatch(r"[0-9a-f]{40}", pin) is None:
        raise SystemExit(f"{PIN_FILE} must contain one lowercase 40-character SHA")
    profile = read_json(profile_path)
    expected_version = profile.get("compilerVersion")
    settings = profile.get("settings")
    if not isinstance(expected_version, str) or not isinstance(settings, dict):
        raise SystemExit("profile must contain compilerVersion and a settings object")
    identity = compiler_identity(solc, expected_version, pin)

    fixtures = []
    for path in fixture_sources():
        compiled = {
            enabled: compile_fixture(solc, path, profile_path, enabled)
            for enabled in (False, True)
        }
        contracts = []
        for name in sorted(compiled[False]):
            objects = []
            for stage in STAGES:
                text = compiled[stage.optimizer_enabled][name][stage.artifact]
                objects.extend(
                    {"stage": stage.id, **obj} for obj in analyse_artifact(text)
                )
            contracts.append({"contract": name, "objects": objects})
        fixtures.append(
            {
                "source": source_name(path),
                # The source's own hash, so a test can tell that the numbers
                # below still describe the fixture on disk without a compiler.
                "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
                "contracts": contracts,
            }
        )
    return {
        "format": "solidity-hol-yul-reconnaissance-v2",
        "compiler": {"pin": pin, "reportedVersion": identity},
        "profile": profile,
        "outputSelection": OUTPUT_SELECTION,
        "stages": [
            {
                "id": stage.id,
                "artifact": stage.artifact,
                "optimizer": optimizer_settings(settings, stage.optimizer_enabled),
            }
            for stage in STAGES
        ],
        "fixtures": fixtures,
        "summary": {
            stage.id: build_report(fixtures_for_stage(fixtures, stage.id))
            for stage in STAGES
        },
    }


def stage_title(stage: dict[str, Any]) -> str:
    optimizer = stage["optimizer"]
    if optimizer.get("enabled"):
        setting = f"optimizer on, `runs: {optimizer.get('runs')}`"
    else:
        setting = "optimizer off"
    return f"`{stage['id']}`: the `{stage['artifact']}` artifact, {setting}"


def role_table(caption: str, label: str, counts: dict[str, Any]) -> list[str]:
    """One stage's counts, a row per name and a column per object role."""
    lines = [
        f"### {caption}",
        "",
        f"| {label} | creation | runtime | subobject | fixtures |",
        "| --- | ---: | ---: | ---: | --- |",
    ]
    for name, entry in counts.items():
        lines.append(
            f"| `{name}` | {entry['creation']} | {entry['runtime']} | "
            f"{entry['subobject']} | {len(entry['fixtures'])} |"
        )
    return lines


def render_markdown(artifact: dict[str, Any]) -> str:
    lines = [
        "# Yul reconnaissance: the pinned compiler's Yul, unoptimized and optimized",
        "",
        "Generated by `tools/yul_reconnaissance.py`; do not edit by hand.",
        "",
        f"- compiler pin: `{artifact['compiler']['pin']}`",
        f"- fixtures: {len(artifact['fixtures'])}",
        "",
        "`creation` is the top-level `object`, `runtime` the nested `_deployed` one.",
    ]
    for stage in artifact["stages"]:
        summary = artifact["summary"][stage["id"]]
        lines += ["", f"## {stage_title(stage)}", ""]
        lines += role_table("Node kinds", "node kind", summary["nodeKinds"])
        lines += [""]
        lines += role_table("Builtins", "builtin", summary["builtins"])
        lines += [
            "",
            "Unclassified builtin names (must be empty): "
            + (
                ", ".join(f"`{name}`" for name in summary["unknownBuiltins"])
                or "none"
            )
            + ".",
            "",
        ]
        lines += role_table(
            "Object-level forms", "form", summary["objectLevelForms"]
        )
        lines += ["", "### Builtins by fixture", ""]
        for fixture in artifact["fixtures"]:
            for contract in fixture["contracts"]:
                for obj in contract["objects"]:
                    if obj["stage"] != stage["id"] or obj["role"] != "runtime":
                        continue
                    names = ", ".join(f"`{name}`" for name in sorted(obj["builtins"]))
                    kinds = ", ".join(f"`{kind}`" for kind in sorted(obj["nodeKinds"]))
                    lines.append(
                        f"- `{fixture['source']}` `{contract['contract']}` "
                        f"({obj['name']})"
                    )
                    lines.append(f"  - kinds: {kinds}")
                    lines.append(f"  - builtins: {names}")
    return "\n".join(lines) + "\n"


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--solc", required=True, type=Path)
    parser.add_argument("--profile", type=Path, default=DEFAULT_PROFILE)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--report", type=Path)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    artifact = build_artifact(args.solc, args.profile)
    write_json_atomic(args.output, artifact)
    if args.report is not None:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(render_markdown(artifact), encoding="utf-8")


if __name__ == "__main__":
    main()
