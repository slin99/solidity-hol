#!/usr/bin/env python3
"""Differential fuzzing of admitted contracts against their compiled bytecode.

Each target contract (by default every differential suite's) gets seeded
calls: ABI-typed calldata (70%), structurally mutated encodings (20%) and raw
calldata (10%), with initial storage seeded from the storage layout and
immutables by name. pyrevm runs every candidate on the contract's runtime code
in the differential transaction's world and records the outcome, the written
storage and the logs; a stratified K per contract become cases in the
differential suite format, with that recording as their expectation. With
--sequences a candidate is 2 to 4 calls on one deployment, each screened from
the storage the call before it left and each a case of its own.

HOL batches on the fleet prepare each contract once and evaluate the source
on its cases (solidityDifferentialLib.run_fuzz_cases). Every difference from
the recording, and every 20th case, is confirmed against Verifereum's run of
the same bytecode: a disagreement is the bytecode and the source differing;
both agreeing against the recording is a pyrevm mismatch. Disagreements whose
recording Verifereum's bytecode run matches are shrunk and written as suite
JSON under <output>/minimized/.

pyrevm needs Python 3.11:

  uv run --python 3.11 --with pyrevm tools/run_differential_fuzz.py --output DIR
"""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict, deque
from dataclasses import dataclass, replace
from functools import lru_cache
import hashlib
import itertools
import json
import os
from pathlib import Path
import random
import re
import shutil
import subprocess
import sys
from typing import Any, Callable, Iterator

import run_semantic_expectations as fleet

ROOT = Path(__file__).resolve().parents[1]
PREFIX = "fuzz-result: "
# One contract per action: contracts sharing a HOL process ran out of memory.
SCRIPT = fleet.BatchScript(ROOT / "tools" / "differential_fuzz.sml", "contracts",
                           "DIFFERENTIAL_FUZZ_MANIFEST", batch_size=1)
CORPUS = ROOT / "testdata" / "differential" / "corpus.json"
SUITES = ROOT / "testdata" / "differential" / "suites"
ECHO_PEER = {"source": "testdata/differential/fuzz/echo_peer.sol", "contract": "EchoPeer",
             "artifact": "testdata/differential/fuzz/echo_peer.json"}
CONFIRM_EVERY = 20  # every 20th case of a contract, its first included: at least 5%
STORAGE_STATES = 12  # initial storages per contract, shared by its candidates
RAW = "<raw>"

# The world of solidityBytecode's differential transaction.
CONTRACT = 0x1000
SENDER = 0x2000
PEER = 0x5000
SENDER_BALANCE = 2 ** 128
CHAIN_ID = 5
BLOCK_NUMBER = 11
TIMESTAMP = 1700000000
COINBASE = 0xC0FFEE
BASE_FEE = 7
BLOCK_GAS_LIMIT = 30000000
TX_GAS = 10000000
GAS_PRICE = 9
# Calls that use more are dropped: HOL's runs of them take minutes each.
GAS_BUDGET = 1000000

WORD = 1 << 256
# Shared by calldata, storage values and mapping keys, so calls find seeded state.
ADDRESSES = [CONTRACT, SENDER, PEER, 0, 1, COINBASE, 0xDEADBEEF, (1 << 160) - 1]
# Accounts the cases may send from: not the contract, the peer or a precompile.
SENDERS = [SENDER, 0xDEADBEEF, COINBASE]
SMALL = [0, 1, 2, 3, 31, 32, 33, 255, 256]


# Keccak-256, with the original padding Ethereum uses

_ROUND_CONSTANTS = [
    0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000,
    0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
    0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
    0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003,
    0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
    0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008]
_ROTATIONS = [[0, 36, 3, 41, 18], [1, 44, 10, 45, 2], [62, 6, 43, 15, 61],
              [28, 55, 25, 21, 56], [27, 20, 39, 8, 14]]
_LANE = (1 << 64) - 1


def _rotate(x: int, n: int) -> int:
    return ((x << n) | (x >> (64 - n))) & _LANE if n else x


def _permute(a: list[list[int]]) -> None:
    for constant in _ROUND_CONSTANTS:
        c = [a[x][0] ^ a[x][1] ^ a[x][2] ^ a[x][3] ^ a[x][4] for x in range(5)]
        d = [c[(x - 1) % 5] ^ _rotate(c[(x + 1) % 5], 1) for x in range(5)]
        b = [[0] * 5 for _ in range(5)]
        for x in range(5):
            for y in range(5):
                b[y][(2 * x + 3 * y) % 5] = _rotate(a[x][y] ^ d[x], _ROTATIONS[x][y])
        for x in range(5):
            for y in range(5):
                a[x][y] = b[x][y] ^ (~b[(x + 1) % 5][y] & b[(x + 2) % 5][y] & _LANE)
        a[0][0] ^= constant


@lru_cache(maxsize=1 << 16)
def keccak256(data: bytes) -> bytes:
    rate = 136
    padded = bytearray(data) + b"\x01" + bytes(-(len(data) + 1) % rate)
    padded[-1] |= 0x80
    state = [[0] * 5 for _ in range(5)]
    for start in range(0, len(padded), rate):
        for i in range(rate // 8):
            lane = padded[start + 8 * i:start + 8 * i + 8]
            state[i % 5][i // 5] ^= int.from_bytes(lane, "little")
        _permute(state)
    return b"".join(state[i % 5][i // 5].to_bytes(8, "little") for i in range(4))


def hash_word(data: bytes) -> int:
    return int.from_bytes(keccak256(data), "big")


def word(n: int) -> bytes:
    return (n % WORD).to_bytes(32, "big")


def address(n: int) -> str:
    return f"0x{n:040x}"


# ABI types as the artifact's ABI writes them: {"type": ..., "components": [...]}

AbiType = dict[str, Any]


def array_parts(t: AbiType) -> tuple[AbiType, int | None] | None:
    """An array type's element type and length (None if dynamic)."""
    m = re.fullmatch(r"(.*)\[(\d*)\]", t["type"])
    if not m:
        return None
    return {**t, "type": m.group(1)}, int(m.group(2)) if m.group(2) else None


def is_dynamic(t: AbiType) -> bool:
    parts = array_parts(t)
    if parts:
        return parts[1] is None or is_dynamic(parts[0])
    if t["type"] == "tuple":
        return any(is_dynamic(c) for c in t["components"])
    return t["type"] in ("bytes", "string")


def head_size(t: AbiType) -> int:
    if is_dynamic(t):
        return 32
    parts = array_parts(t)
    if parts:
        return parts[1] * head_size(parts[0])
    if t["type"] == "tuple":
        return sum(head_size(c) for c in t["components"])
    return 32


def encode_value(t: AbiType, v: Any) -> bytes:
    parts = array_parts(t)
    if parts:
        body = encode_tuple([parts[0]] * len(v), v)
        return body if parts[1] is not None else word(len(v)) + body
    if t["type"] == "tuple":
        return encode_tuple(t["components"], v)
    if t["type"] in ("bytes", "string"):
        return word(len(v)) + v + bytes(-len(v) % 32)
    if t["type"] == "function" or re.fullmatch(r"bytes\d+", t["type"]):
        return v.ljust(32, b"\0")
    return word(int(v))


def encode_tuple(types: list[AbiType], values: list[Any]) -> bytes:
    heads, tails = [], []
    offset = sum(head_size(t) for t in types)
    for t, v in zip(types, values, strict=True):
        encoded = encode_value(t, v)
        if is_dynamic(t):
            heads.append(word(offset))
            tails.append(encoded)
            offset += len(encoded)
        else:
            heads.append(encoded)
    return b"".join(heads + tails)


def canonical(t: AbiType) -> str:
    """The type as a function signature writes it."""
    parts = array_parts(t)
    if parts:
        return canonical(parts[0]) + t["type"][len(parts[0]["type"]):]
    if t["type"] == "tuple":
        return "(" + ",".join(canonical(c) for c in t["components"]) + ")"
    return t["type"]


def signature(f: dict[str, Any]) -> str:
    return f["name"] + "(" + ",".join(canonical(t) for t in f["inputs"]) + ")"


def int_value(rng: random.Random, name: str) -> int:
    """An intN or uintN value, biased to boundaries and the shared pools."""
    m = re.fullmatch(r"(u?)int(\d*)", name)
    if m is None:
        raise ValueError(f"not an integer type: {name}")
    bits = int(m.group(2) or 256)
    if not m.group(1):
        low, high = -(1 << (bits - 1)), (1 << (bits - 1)) - 1
        return rng.choice([0, 1, -1, low, high, low + 1, high - 1,
                           rng.randint(low, high), rng.randint(max(low, -300), min(high, 300))])
    high = (1 << bits) - 1
    return rng.choice([*(n for n in SMALL + ADDRESSES if n <= high), high, high - 1,
                       1 << (bits - 1), rng.randint(0, high), rng.randint(0, min(high, 1000))])


def random_bytes(rng: random.Random, n: int) -> bytes:
    fill = rng.choice([0, 0x61, 0xFF, None])
    return bytes(rng.randrange(256) if fill is None else fill for _ in range(n))


def random_value(rng: random.Random, t: AbiType) -> Any:
    parts = array_parts(t)
    if parts:
        n = parts[1] if parts[1] is not None else rng.choice([0, 1, 1, 2, 3])
        return [random_value(rng, parts[0]) for _ in range(n)]
    name = t["type"]
    if name == "tuple":
        return [random_value(rng, c) for c in t["components"]]
    if name in ("bytes", "string"):
        return random_bytes(rng, rng.choice([0, 1, 4, 31, 32, 33, 64, rng.randrange(80)]))
    if name == "bool":
        return rng.random() < 0.5
    if name == "address":
        return rng.choice(ADDRESSES)
    if name == "function":
        # An external function value: address then selector, encoded like bytes24.
        return rng.choice(ADDRESSES).to_bytes(20, "big") + random_bytes(rng, 4)
    if name.startswith("bytes"):
        return random_bytes(rng, int(name[5:]))
    return int_value(rng, name)


def mutate(rng: random.Random, data: bytes) -> bytes:
    """A structural mutation of an encoding after its selector: a word (an
    offset, a length or a value) replaced, dirty high bits, truncation,
    trailing bytes or an inserted word."""
    selector, body = data[:4], bytearray(data[4:])
    words = len(body) // 32
    choice = rng.randrange(5)
    if choice == 0 and words:
        i = rng.randrange(words)
        body[32 * i:32 * i + 32] = word(rng.choice(
            [0, 1, 31, 32, 64, 0xFFFFFFFF, WORD - 1, WORD - 32, len(body), rng.randrange(WORD)]))
    elif choice == 1 and words:
        body[32 * rng.randrange(words)] = rng.randrange(1, 256)
    elif choice == 2 and body:
        del body[rng.randrange(len(body)):]
    elif choice == 3:
        body += random_bytes(rng, rng.choice([1, 31, 32, 64]))
    else:
        cut = 32 * rng.randrange(words + 1)
        body[cut:cut] = word(rng.randrange(WORD))
    return selector + bytes(body)


def raw_calldata(rng: random.Random, selectors: list[bytes]) -> bytes:
    """Empty, short, junk-argument or selector-free calldata."""
    choice = rng.randrange(4)
    if choice == 0:
        return b""
    if choice == 1:
        return random_bytes(rng, rng.randrange(1, 4))
    if choice == 2 and selectors:
        return rng.choice(selectors) + random_bytes(rng, rng.randrange(70))
    return random_bytes(rng, 4 + 32 * rng.randrange(3))


# The contract under test

def ast_nodes(value: Any) -> Iterator[dict[str, Any]]:
    if isinstance(value, dict):
        if "nodeType" in value:
            yield value
        for v in value.values():
            yield from ast_nodes(v)
    elif isinstance(value, list):
        for v in value:
            yield from ast_nodes(v)


@dataclass(frozen=True)
class Immutable:
    name: str
    type_string: str
    offsets: list[int]


class Target:
    """A contract and what fuzzing it needs from its compiler artifact. suite
    is a differential suite (name, source, contract, artifact, optional peer
    and fuel); its cases are ignored. A suite without a peer gets the echo
    peer, so calls to 0x5000 return their arguments."""

    def __init__(self, suite: dict[str, Any], fuel: int):
        self.name = suite["name"]
        if not re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*", self.name):
            raise SystemExit(f"target name is not an identifier: {self.name!r}")
        peer = suite.get("peer", ECHO_PEER)
        self.entry: dict[str, Any] = {
            **{k: suite[k] for k in ("name", "source", "contract", "artifact")},
            "peer": peer, "fuel": suite.get("fuel", fuel)}
        artifact = json.loads((ROOT / suite["artifact"]).read_text())
        output = artifact["output"]
        contract = output["contracts"][suite["source"]][suite["contract"]]
        evm = contract["evm"]
        self.functions = [f for f in contract["abi"] if f["type"] == "function"]
        self.selectors = {signature(f): bytes.fromhex(evm["methodIdentifiers"][signature(f)])
                          for f in self.functions}
        self.code = bytes.fromhex(evm["deployedBytecode"]["object"])
        self.layout = contract.get("storageLayout") or {"storage": [], "types": {}}
        nodes = list(ast_nodes(output["sources"]))
        self.enum_sizes = {n["id"]: len(n["members"]) for n in nodes
                           if n["nodeType"] == "EnumDefinition"}
        references = evm["deployedBytecode"].get("immutableReferences", {})
        self.immutables = [
            Immutable(n["name"], n["typeDescriptions"]["typeString"],
                      [r["start"] for r in references[str(n["id"])]])
            for n in nodes if n["nodeType"] == "VariableDeclaration"
            and n.get("mutability") == "immutable" and str(n["id"]) in references]
        self.libraries = []
        for source, names in artifact["input"]["settings"].get("libraries", {}).items():
            for name, where in names.items():
                library = output["contracts"][source][name]["evm"]["deployedBytecode"]
                code = bytearray.fromhex(library["object"])
                for ref in library.get("immutableReferences", {}).get("library_deploy_address", []):
                    code[ref["start"]:ref["start"] + 32] = word(int(where, 16))
                self.libraries.append((int(where, 16), bytes(code)))
        peer_output = json.loads((ROOT / peer["artifact"]).read_text())["output"]
        self.peer_code = bytes.fromhex(peer_output["contracts"][peer["source"]][
            peer["contract"]]["evm"]["deployedBytecode"]["object"])

    def code_with(self, immutables: dict[str, int | bool]) -> bytes:
        code = bytearray(self.code)
        for immutable in self.immutables:
            if immutable.name in immutables:
                patch = word(int(immutables[immutable.name]))
                for start in immutable.offsets:
                    code[start:start + 32] = patch
        return bytes(code)


# Initial storage, from the layout: clean values of each variable's type

MAX_ELEMENTS = 3
MAX_DEPTH = 4


class StorageSeed:
    """Builds one initial storage. Mappings get slots for keys from the shared
    pools, arrays and byte strings are short."""

    def __init__(self, rng: random.Random, target: Target):
        self.rng = rng
        self.target = target
        self.slots: dict[int, int] = {}

    def put(self, slot: int, offset: int, size: int, value: int) -> None:
        shift = 8 * offset
        mask = ((1 << (8 * size)) - 1) << shift
        slot %= WORD
        self.slots[slot] = (self.slots.get(slot, 0) & ~mask) | ((value << shift) & mask)

    def seed(self, type_id: str, slot: int, offset: int, depth: int = 0) -> None:
        if depth > MAX_DEPTH:
            return
        t = self.target.layout["types"][type_id]
        size = int(t["numberOfBytes"])
        if t["encoding"] == "mapping":
            keys = self.keys(t["key"])
            for key in self.rng.sample(keys, k=min(2, len(keys))):
                self.seed(t["value"], hash_word(key + word(slot)), 0, depth + 1)
        elif t["encoding"] == "dynamic_array":
            n = self.rng.choice([0, 1, 2, MAX_ELEMENTS])
            self.put(slot, 0, 32, n)
            self.elements(t["base"], hash_word(word(slot)), n, depth)
        elif t["encoding"] == "bytes":
            data = random_bytes(self.rng, self.rng.choice([0, 1, 5, 31, 32, 40]))
            if len(data) < 32:
                self.put(slot, 0, 32,
                         int.from_bytes(data.ljust(31, b"\0"), "big") << 8 | 2 * len(data))
            else:
                self.put(slot, 0, 32, 2 * len(data) + 1)
                start = hash_word(word(slot))
                for i in range(0, len(data), 32):
                    chunk = data[i:i + 32].ljust(32, b"\0")
                    self.put(start + i // 32, 0, 32, int.from_bytes(chunk, "big"))
        elif "members" in t:
            for member in t["members"]:
                self.seed(member["type"], slot + int(member["slot"]), member["offset"], depth + 1)
        elif "base" in t:
            length = int(re.search(r"\[(\d+)\]$", t["label"]).group(1))
            self.elements(t["base"], slot, min(length, MAX_ELEMENTS), depth)
        else:
            self.put(slot, offset, size, self.scalar(type_id, t["label"], size))

    def elements(self, base: str, start: int, n: int, depth: int) -> None:
        size = int(self.target.layout["types"][base]["numberOfBytes"])
        per_slot = 32 // size if size <= 16 else 0
        for i in range(n):
            if per_slot:
                self.seed(base, start + i // per_slot, (i % per_slot) * size, depth + 1)
            else:
                self.seed(base, start + i * ((size + 31) // 32), 0, depth + 1)

    def scalar(self, type_id: str, label: str, size: int) -> int:
        """A clean value; anything else (a user-defined value type, a function
        pointer) stays zero."""
        if label == "bool":
            return self.rng.randrange(2)
        if label.startswith("enum "):
            enum_id = int(re.search(r"(\d+)$", type_id).group(1))
            return self.rng.randrange(self.target.enum_sizes[enum_id])
        if label in ("address", "address payable") or label.startswith("contract "):
            return self.rng.choice(ADDRESSES)
        if re.fullmatch(r"u?int\d+", label):
            return int_value(self.rng, label) % (1 << (8 * size))
        if re.fullmatch(r"bytes\d+", label):
            return int.from_bytes(random_bytes(self.rng, size), "big")
        return 0

    def keys(self, type_id: str) -> list[bytes]:
        """Mapping keys from the shared pools, as the slot hash encodes them."""
        label = self.target.layout["types"][type_id]["label"]
        if label in ("string", "bytes"):
            return [b"", b"a", b"key"]
        if label in ("address", "address payable") or label.startswith("contract "):
            return [word(a) for a in ADDRESSES]
        if label == "bool":
            return [word(0), word(1)]
        if re.fullmatch(r"bytes\d+", label):
            return [word(0), (b"\xff" * int(label[5:])).ljust(32, b"\0")]
        return [word(n) for n in (0, 1, 2, WORD - 1)]


def initial_storage(rng: random.Random, target: Target) -> dict[int, int]:
    seed = StorageSeed(rng, target)
    for variable in target.layout["storage"]:
        if rng.random() < 0.8:
            seed.seed(variable["type"], int(variable["slot"]), variable["offset"])
    return {k: v for k, v in seed.slots.items() if v}


def immutable_values(rng: random.Random, target: Target) -> dict[str, int | bool]:
    """Values for the address, integer and bool immutables."""
    values: dict[str, int | bool] = {}
    for immutable in target.immutables:
        t = immutable.type_string
        if t in ("address", "address payable") or t.startswith("contract "):
            values[immutable.name] = rng.choice(ADDRESSES)
        elif t == "bool":
            values[immutable.name] = rng.random() < 0.5
        elif re.fullmatch(r"u?int\d+", t):
            values[immutable.name] = int_value(rng, t)
    return values


# Calls, recordings and cases

@dataclass(frozen=True)
class Call:
    function: str  # the targeted function, or RAW
    mode: str  # typed, mutated or raw
    calldata: bytes
    sender: int
    value: int
    storage: dict[int, int]
    immutables: dict[str, int | bool]

    def size(self) -> tuple[int, ...]:
        """What shrinking reduces, most significant first."""
        return (len(self.storage), len(self.immutables), int(self.value > 0),
                int(self.sender != SENDER), sum(b != 0 for b in self.calldata),
                len(self.calldata))

    def key(self) -> str:
        return json.dumps([self.calldata.hex(), self.sender, self.value,
                           sorted(self.storage.items()), sorted(self.immutables.items())])


@dataclass(frozen=True)
class Recording:
    """What pyrevm observed: the expectation, changed slots and logs."""
    expect: dict[str, Any]
    final_storage: dict[int, int]
    logs: list[dict[str, Any]]

    def shape(self) -> tuple[Any, ...]:
        """The outcome's kind and detail: a revert's first 36 bytes (an error
        selector and its first word, or a panic code), a return's length."""
        (kind, data), = self.expect.items()
        detail = data[:74] if kind == "revert" else len(data) if kind == "returned" else ""
        return (kind, detail, bool(self.final_storage), len(self.logs))


class Halt(Exception):
    """pyrevm stopped the call in a way no case expectation can say (out of
    gas, a stack error), or it used more than GAS_BUDGET: the candidate is
    discarded."""


@dataclass(frozen=True)
class Case:
    name: str
    call: Call
    recording: Recording
    confirm: bool = False
    # (sequence, step) for a call of a sequence, numbered from 0.
    position: tuple[int, int] | None = None

    def suite_case(self, *, metadata: bool = True) -> dict[str, Any]:
        """The case in differential suite format; metadata keeps the fuzzer's
        fields ("fuzz", "confirm"), which the HOL side ignores."""
        result: dict[str, Any] = {"name": self.name, "calldata": "0x" + self.call.calldata.hex()}
        if self.call.sender != SENDER:
            result["sender"] = self.call.sender
        if self.call.value:
            result["value"] = str(self.call.value)
        if self.call.immutables:
            result["immutables"] = {k: v if isinstance(v, bool) else str(v)
                                    for k, v in sorted(self.call.immutables.items())}
        result["storage"] = {str(k): str(v) for k, v in sorted(self.call.storage.items())}
        result["expect"] = self.recording.expect
        result["final_storage"] = {str(k): str(v)
                                   for k, v in sorted(self.recording.final_storage.items())}
        result["logs"] = self.recording.logs
        if metadata:
            result["fuzz"] = {"function": self.call.function, "mode": self.call.mode}
            if self.position is not None:
                result["fuzz"]["sequence"], result["fuzz"]["step"] = self.position
            if self.confirm:
                result["confirm"] = True
        return result


def call_from_case(case: dict[str, Any]) -> Call:
    return Call(function=case["fuzz"]["function"], mode=case["fuzz"]["mode"],
                calldata=bytes.fromhex(case["calldata"][2:]),
                sender=int(case.get("sender", SENDER)), value=int(case.get("value", 0)),
                storage={int(k): int(v) for k, v in case["storage"].items()},
                immutables={k: v if isinstance(v, bool) else int(v)
                            for k, v in case.get("immutables", {}).items()})


def draw_call(rng: random.Random, target: Target, f: dict[str, Any] | None,
              states: list[dict[int, int]]) -> Call:
    """A call to f: ABI-typed (70%), mutated (20%) or raw (10%) calldata; raw
    always when f is None."""
    payable = f is None or f["stateMutability"] == "payable"
    roll = rng.random()
    if f is None or roll >= 0.9:
        function, mode, data = RAW, "raw", raw_calldata(rng, list(target.selectors.values()))
    else:
        typed = target.selectors[signature(f)] + encode_tuple(
            f["inputs"], [random_value(rng, t) for t in f["inputs"]])
        function = signature(f)
        mode, data = ("typed", typed) if roll < 0.7 else ("mutated", mutate(rng, typed))
    value = rng.choice([1, 10 ** 18]) if rng.random() < (0.5 if payable else 0.1) else 0
    return Call(function=function, mode=mode, calldata=data,
                sender=SENDER if rng.random() < 0.9 else rng.choice(SENDERS),
                value=value, storage=rng.choice(states),
                immutables=immutable_values(rng, target))


def initial_states(rng: random.Random, target: Target) -> list[dict[int, int]]:
    return [{}] + [initial_storage(rng, target) for _ in range(STORAGE_STATES)]


def generate_calls(seed: int, target: Target, per_function: int) -> list[Call]:
    """per_function candidates for each function: 70% typed, 20% mutated and
    10% raw. A contract without functions gets per_function raw ones."""
    rng = random.Random(f"{seed}:{target.name}")
    states = initial_states(rng, target)
    return [draw_call(rng, target, f, states)
            for f in target.functions or [None] for _ in range(per_function)]


def generate_sequences(seed: int, target: Target, per_function: int) -> list[list[Call]]:
    """per_function sequences of 2 to 4 calls starting with each function, the
    later calls to any function. The calls of a sequence share its first
    call's immutables, as one deployment; screening gives each later call the
    storage the one before it left."""
    rng = random.Random(f"{seed}:{target.name}:sequences")
    states = initial_states(rng, target)
    functions = target.functions or [None]
    sequences = []
    for f in functions:
        for _ in range(per_function):
            first = draw_call(rng, target, f, states)
            rest = [draw_call(rng, target, rng.choice(functions), states)
                    for _ in range(rng.randint(1, 3))]
            sequences.append([first] + [replace(c, storage={}, immutables=first.immutables)
                                        for c in rest])
    return sequences


# Screening with pyrevm

_WRITE = re.compile(r"StorageChange \{ address: (0x[0-9a-fA-F]{40}), key: (\d+)")
_REVERT = re.compile(r"Revert \{ gas_used: (\d+), output: 0x([0-9a-fA-F]*) \}")
_HALT = re.compile(r"Halt \{ reason: (\w+)")


def screen(pyrevm: Any, target: Target, call: Call) -> Recording:
    """pyrevm's run of a call in the differential transaction's world. pyrevm's
    message_call takes the block gas limit from the EVM's and zeroes the base
    fee; a call reading the base fee differs, which confirmation reports as a
    pyrevm mismatch."""
    env = pyrevm.Env(cfg=pyrevm.CfgEnv(chain_id=CHAIN_ID),
                     block=pyrevm.BlockEnv(number=BLOCK_NUMBER, timestamp=TIMESTAMP,
                                           coinbase=address(COINBASE), prevrandao=bytes(32),
                                           basefee=BASE_FEE, gas_limit=BLOCK_GAS_LIMIT))
    evm = pyrevm.EVM(env=env, gas_limit=BLOCK_GAS_LIMIT)
    evm.insert_account_info(address(CONTRACT),
                            pyrevm.AccountInfo(code=target.code_with(call.immutables)))
    for slot, value in call.storage.items():
        evm.insert_account_storage(address(CONTRACT), slot, value)
    evm.insert_account_info(address(PEER), pyrevm.AccountInfo(code=target.peer_code))
    for where, code in target.libraries:
        evm.insert_account_info(address(where), pyrevm.AccountInfo(code=code))
    evm.set_balance(address(call.sender), SENDER_BALANCE)
    try:
        output = evm.message_call(address(call.sender), address(CONTRACT), call.calldata,
                                  value=call.value, gas=TX_GAS, gas_price=GAS_PRICE)
        expect: dict[str, Any] = {"returned": "0x" + bytes(output).hex()}
        gas = evm.result.gas_used
        logs = [{"logger": "0x" + log.address[2:].lower(),
                 "topics": ["0x" + bytes(t).hex() for t in log.data[0]],
                 "data": "0x" + bytes(log.data[1]).hex()} for log in evm.result.logs]
    except RuntimeError as error:
        message = str(error)
        revert = _REVERT.fullmatch(message)
        halt = _HALT.match(message)
        if revert:
            expect = {"revert": "0x" + revert.group(2).lower()}
            gas = int(revert.group(1))
        elif halt and halt.group(1) == "InvalidFEOpcode":
            expect = {"abort": True}
            gas = 0
        else:
            raise Halt(halt.group(1) if halt else message) from error
        logs = []
    if gas > GAS_BUDGET:
        raise Halt("OverGasBudget")
    written = {int(k) for a, k in _WRITE.findall(evm.journal_str) if int(a, 16) == CONTRACT}
    final = {}
    for slot in sorted(written):
        value = int(evm.storage(address(CONTRACT), slot))
        if value != call.storage.get(slot, 0):
            final[slot] = value
    return Recording(expect, final, logs)


Step = tuple[Call, Recording]


def carried_storage(call: Call, recording: Recording) -> dict[int, int]:
    """The contract's complete storage after a call, zero slots left out."""
    return {k: v for k, v in {**call.storage, **recording.final_storage}.items() if v}


def stratify(seed: int, name: str, screened: list[list[Step]], k: int) -> list[list[Step]]:
    """Sequences (a single call is one of one) up to K calls, taking their
    functions in turn and, within the same functions, their distinct outcome
    shapes in turn, so rare outcomes come before repeats."""
    rng = random.Random(f"{seed}:{name}:stratify")
    by_function: dict[tuple[str, ...], dict[tuple[Any, ...], list[list[Step]]]] = defaultdict(dict)
    for sequence in screened:
        functions = tuple(call.function for call, _ in sequence)
        shapes = tuple(recording.shape() for _, recording in sequence)
        by_function[functions].setdefault(shapes, []).append(sequence)
    queues = []
    for function in sorted(by_function):
        groups = [by_function[function][s] for s in sorted(by_function[function], key=repr)]
        for group in groups:
            rng.shuffle(group)
        queues.append(deque(x for row in itertools.zip_longest(*groups) for x in row if x))
    # With more functions than k, a seed decides which are left out.
    rng.shuffle(queues)
    chosen: list[list[Step]] = []
    calls = 0
    while calls < k and any(queues):
        for queue in queues:
            # A sequence longer than the calls left is skipped, so K bounds the calls.
            if queue and len(queue[0]) <= k - calls:
                chosen.append(queue.popleft())
                calls += len(chosen[-1])
            elif queue:
                queue.popleft()
    return chosen


def make_cases(selected: list[list[Step]]) -> list[Case]:
    """A case per call: fuzz_NNNN for a single call, seq_NNNN_S for step S of
    a longer sequence; every CONFIRM_EVERY-th call is confirmed."""
    cases = []
    for n, sequence in enumerate(selected):
        for step, (call, recording) in enumerate(sequence):
            i = len(cases)
            if len(sequence) == 1:
                cases.append(Case(f"fuzz_{n:04d}", call, recording, confirm=i % CONFIRM_EVERY == 0))
            else:
                cases.append(Case(f"seq_{n:04d}_{step}", call, recording,
                                  confirm=i % CONFIRM_EVERY == 0, position=(n, step)))
    return cases


# Results

def records(path: Path) -> list[dict[str, Any]]:
    """A batch's records; a truncated last one, from an interrupted run, is dropped."""
    return fleet.result_records(path.read_text(encoding="utf-8", errors="replace"), PREFIX)


def batch_records(work: Path) -> list[dict[str, Any]]:
    """Every batch's records, less the failed actions of contracts run again since."""
    found = [r for path in fleet.result_files(work) for r in records(path)]
    rerun = {r["contract"] for r in found if r["kind"] == "contract" and r["status"] != "action-failed"}
    return [r for r in found if not (r["kind"] == "contract" and r["status"] == "action-failed"
                                     and r["contract"] in rerun)]


def completed_contracts(results: list[dict[str, Any]],
                        manifests: dict[str, dict[str, Any]]) -> set[str]:
    """Contracts with a result for every case, or a preparation failure; a
    failed action (a worker or network failure among them) is run again."""
    seen: dict[str, set[str]] = defaultdict(set)
    failed = set()
    for r in results:
        if r["kind"] == "contract" and r["status"] not in ("ok", "action-failed"):
            failed.add(r["contract"])
        elif r["kind"] == "case":
            seen[r["contract"]].add(r["case"])
    return {name for name, entry in manifests.items()
            if name in failed or {c["name"] for c in entry["cases"]} <= seen[name]}


def report(manifests: dict[str, dict[str, Any]], results: list[dict[str, Any]]) -> dict[str, Any]:
    """Totals by status; inconclusives by (contract, function, reason); the
    functions whose every ABI-typed case ended in InvalidCompletion; and the
    cases needing attention, each with its fuzz metadata."""
    metadata = {(name, c["name"]): c["fuzz"] for name, m in manifests.items() for c in m["cases"]}
    cases = {(r["contract"], r["case"]): r for r in results
             if r["kind"] == "case" and (r["contract"], r["case"]) in metadata}
    contracts = {r["contract"]: r for r in results
                 if r["kind"] == "contract" and r["contract"] in manifests}
    inconclusive: Counter[tuple[str, str, str]] = Counter()
    typed: dict[tuple[str, str], list[str]] = defaultdict(list)
    for key, r in sorted(cases.items()):
        fuzz = metadata[key]
        if r["status"] == "inconclusive":
            inconclusive[(key[0], fuzz["function"], r["reason"])] += 1
        if fuzz["mode"] == "typed":
            typed[(key[0], fuzz["function"])].append(r.get("reason", r["status"]))
    failed = {n for n, r in contracts.items() if r["status"] != "ok"}
    # A sequence agrees only if every step in its manifest has an agree result.
    sequences: dict[tuple[str, int], list[str | None]] = defaultdict(list)
    for key, fuzz in metadata.items():
        if "sequence" in fuzz and key[0] not in failed:
            sequences[(key[0], fuzz["sequence"])].append(cases[key]["status"] if key in cases else None)

    def listed(status: str) -> list[dict[str, Any]]:
        return [{**r, **metadata[k]} for k, r in sorted(cases.items()) if r["status"] == status]

    return {
        "contracts": len(manifests),
        "cases": len(cases),
        "missing": sorted(f"{c}/{n}" for c, n in metadata.keys() - cases.keys() if c not in failed),
        "totals": dict(sorted(Counter(r["status"] for r in cases.values()).items())),
        "confirmed": sum(1 for r in cases.values() if r.get("confirmed")),
        "sequences": {"evaluated": sum(any(sequence) for sequence in sequences.values()),
                      "every_call_agrees": sum(all(s == "agree" for s in statuses)
                                               for statuses in sequences.values())},
        "contract_failures": {n: contracts[n] for n in sorted(failed)},
        "unsupported": {n: r["unsupported"] for n, r in sorted(contracts.items())
                        if r.get("unsupported")},
        "inconclusive": [{"contract": c, "function": f, "reason": why, "cases": n}
                         for (c, f, why), n in sorted(inconclusive.items())],
        "invalid_completion_functions": [
            {"contract": c, "function": f} for (c, f), reasons in sorted(typed.items())
            if all(why == "InvalidCompletion" for why in reasons)],
        "disagree": listed("disagree"),
        "pyrevm_mismatch": listed("pyrevm-mismatch"),
        "error": listed("error"),
        "screening": {n: m["screening"] for n, m in sorted(manifests.items())},
    }


def markdown(summary: dict[str, Any]) -> str:
    lines = ["# Differential fuzzing", "",
             f"{summary['cases']} cases over {summary['contracts']} contracts; "
             f"{summary['confirmed']} confirmed against the bytecode in Verifereum.", "",
             *([f"{summary['sequences']['evaluated']} call sequences, "
                f"{summary['sequences']['every_call_agrees']} agreeing after every call.", ""]
               if summary["sequences"]["evaluated"] else []),
             "| Status | Cases |", "| --- | ---: |"]
    lines += [f"| {status} | {n} |" for status, n in summary["totals"].items()]
    for title, key in (("Disagreements", "disagree"), ("pyrevm mismatches", "pyrevm_mismatch"),
                       ("Errors", "error")):
        if summary[key]:
            lines += ["", f"## {title}", ""]
            lines += [f"- `{r['contract']}` `{r['case']}` ({r['function']}, {r['mode']})"
                      for r in summary[key]]
    if summary.get("unminimized"):
        lines += ["", "## Disagreements not minimized (pyrevm's recording differs from the bytecode run)", ""]
        lines += [f"- `{r['contract']}` `{r['case']}`" for r in summary["unminimized"]]
    if summary["contract_failures"]:
        lines += ["", "## Contracts that failed (preparation or their HOL action)", ""]
        lines += [f"- `{n}`: {r['status']}" + (f" ({r['message']})" if r.get("message") else "")
                  for n, r in summary["contract_failures"].items()]
    if summary["missing"]:
        lines += ["", f"## Cases without a result: {len(summary['missing'])}"]
    if summary.get("unreported"):
        lines += ["", "## Contracts sent to HOL with no result", ""]
        lines += [f"- `{n}`" for n in summary["unreported"]]
    if summary.get("no_cases"):
        lines += ["", "## Contracts with no case (every candidate halted or ran over the gas budget)", ""]
        lines += [f"- `{n}`: {summary['screening'][n]['halted']}" for n in summary["no_cases"]]
    if summary["inconclusive"]:
        lines += ["", "## Inconclusive", "", "| Contract | Function | Reason | Cases |",
                  "| --- | --- | --- | ---: |"]
        lines += [f"| {r['contract']} | {r['function']} | {r['reason']} | {r['cases']} |"
                  for r in summary["inconclusive"]]
    if summary["invalid_completion_functions"]:
        lines += ["", "## Functions whose every ABI-typed case is an invalid completion", ""]
        lines += [f"- `{r['contract']}.{r['function']}`"
                  for r in summary["invalid_completion_functions"]]
    return "\n".join(lines) + "\n"


# Shrinking

def reproducible(r: dict[str, Any]) -> bool:
    """A disagreement a suite case can reproduce: the recording, which becomes
    its expectation, matches Verifereum's run of the bytecode."""
    return r["status"] == "disagree" and r.get("recording_matches") is True


def variants(call: Call) -> list[Call]:
    """Smaller calls: all storage dropped, a quarter of it (when there are
    many entries) or one entry, immutables dropped, value and sender reset,
    calldata words after the selector zeroed, or its last word dropped."""
    found: list[Call] = [replace(call, storage={})] if len(call.storage) > 1 else []
    slots = sorted(call.storage)
    drops = [[s] for s in slots]
    if len(slots) > 8:
        quarter = (len(slots) + 3) // 4
        drops = [slots[i:i + quarter] for i in range(0, len(slots), quarter)] + drops
    found += [replace(call, storage={k: v for k, v in call.storage.items() if k not in drop})
              for drop in drops]
    found += [replace(call, immutables={k: v for k, v in call.immutables.items() if k != name})
              for name in call.immutables]
    if call.value:
        found.append(replace(call, value=0))
    if call.sender != SENDER:
        found.append(replace(call, sender=SENDER))
    data = call.calldata
    for start in range(4, len(data), 32):
        if any(data[start:start + 32]):
            found.append(replace(call, calldata=data[:start] + bytes(len(data[start:start + 32]))
                                 + data[start + 32:]))
    if len(data) > 4:
        found.append(replace(call, calldata=data[:max(4, len(data) - 32)]))
    return [c for c in found if c.size() < call.size()]


Evaluator = Callable[[dict[str, list[Call]]], dict[str, list[bool]]]


def shrink(failing: dict[str, Call], still_fails: Evaluator, rounds: int) -> dict[str, Call]:
    """Greedy reduction: each round evaluates every unsettled call's variants
    together and keeps the smallest that still fails; a call none of whose
    variants fails is settled."""
    current = dict(failing)
    active = set(failing)
    for _ in range(rounds):
        proposals = {key: variants(current[key]) for key in sorted(active)}
        proposals = {key: calls for key, calls in proposals.items() if calls}
        if not proposals:
            break
        verdicts = still_fails(proposals)
        active = set()
        for key, calls in proposals.items():
            failing_variants = [c for c, bad in zip(calls, verdicts[key], strict=True) if bad]
            if failing_variants:
                current[key] = min(failing_variants, key=Call.size)
                active.add(key)
    return current


# Driver

def suite_targets(names: list[str]) -> list[Target]:
    fuel = json.loads(CORPUS.read_text())["fuel"]
    suites = [json.loads(path.read_text()) for path in sorted(SUITES.glob("*.json"))]
    if names:
        unknown = set(names) - {s["name"] for s in suites}
        if unknown:
            raise SystemExit(f"no differential suite named {', '.join(sorted(unknown))}")
        suites = [s for s in suites if s["name"] in names]
    return [Target(s, fuel) for s in suites]


def manifest_targets(path: Path) -> list[Target]:
    """Targets from a JSON object {"targets": [...]}, each entry shaped like a
    suite (name, source, contract, artifact, optional peer and fuel); relative
    artifact paths are from the repository root. Paths are kept relative to it,
    as HOL reads them from there."""
    def from_root(artifact: str) -> str:
        return os.path.relpath(ROOT / artifact, ROOT)

    fuel = json.loads(CORPUS.read_text())["fuel"]
    entries = json.loads(path.read_text())["targets"]
    names = [e["name"] for e in entries]
    if duplicates := sorted({n for n in names if names.count(n) > 1}):
        raise SystemExit(f"{path}: target names must be unique; repeated: {', '.join(duplicates)}")
    return [Target({**e, "artifact": from_root(e["artifact"]),
                    **({"peer": {**e["peer"], "artifact": from_root(e["peer"]["artifact"])}}
                       if "peer" in e else {})}, fuel)
            for e in entries]


def semantic_targets(solidity: Path, coverage_path: Path, solc: Path, work: Path,
                     shard: tuple[int, int]) -> list[Target]:
    """The contracts of a coverage report's admitted semanticTests (those of
    this shard), each compiled into work and named st_<test path>."""
    fuel = json.loads(CORPUS.read_text())["fuel"]
    index, count = shard
    # A partially admitted contract is fuzzed too: calls to its unsupported
    # functions end inconclusive, and its report lists them.
    tests = fleet.admitted_tests(solidity, solc, coverage_path,
                                 (fleet.coverage.ADMITTED, fleet.coverage.PARTIALLY_ADMITTED))[index::count]
    tests_root = solidity / fleet.coverage.TESTS_DIR
    work.mkdir(parents=True, exist_ok=True)
    targets = []
    for name in tests:
        entry, _ = fleet.compile_admitted(solc, tests_root, name, work)
        targets.append(Target({**entry, "artifact": os.path.relpath(entry["artifact"], ROOT),
                               "name": "st_" + re.sub(r"\W", "_", name.removesuffix(".sol"))},
                              fuel))
    names = [t.name for t in targets]
    if duplicates := sorted({n for n in names if names.count(n) > 1}):
        raise SystemExit(f"semanticTests with the same target name: {', '.join(duplicates)}")
    return targets


def parse_shard(text: str) -> tuple[int, int]:
    m = re.fullmatch(r"(\d+)/(\d+)", text)
    if m is None or not int(m[1]) < int(m[2]):
        raise argparse.ArgumentTypeError(f"expected I/N with 0 <= I < N, got {text!r}")
    return int(m[1]), int(m[2])


def run_inputs(targets: list[Target], seed: int, candidates: int, k: int, *,
               sequences: bool) -> dict[str, Any]:
    """What a run's results depend on: its generation settings, the targets
    with their artifacts, and the runner's and the evaluator's sources."""
    fingerprint = hashlib.sha256()
    for name in subprocess.check_output(["git", "ls-files"], cwd=ROOT, text=True).splitlines():
        path = ROOT / name
        if path.suffix in (".sml", ".sig", ".py", ".toml") or name == "SOLIDITY_PIN":
            fingerprint.update(name.encode())
            fingerprint.update(path.read_bytes())
    for t in targets:
        fingerprint.update((ROOT / t.entry["artifact"]).read_bytes())
        fingerprint.update((ROOT / t.entry["peer"]["artifact"]).read_bytes())
    return {"source_hash": fingerprint.hexdigest(), "seed": seed, "candidates": candidates,
            "k": k, "sequences": sequences, "targets": [t.entry for t in targets]}


def check_inputs(output: Path, inputs: dict[str, Any], *, resume: bool) -> None:
    """Record a new run's inputs, or resume one whose inputs are unchanged."""
    path = output / "inputs.json"
    if not resume:
        fleet.exporter.write_json_atomic(path, inputs)
    elif not path.is_file() or json.loads(path.read_text()) != inputs:
        raise SystemExit("cannot resume: the generation settings, targets, artifacts or "
                         "runner/evaluator sources changed")


def import_pyrevm() -> Any:
    try:
        import pyrevm  # type: ignore[import-not-found]
    except ImportError as error:
        raise SystemExit("pyrevm is missing; run under "
                         "`uv run --python 3.11 --with pyrevm`") from error
    return pyrevm


def run_fleet(holbuild: str, work: Path, entries: list[dict[str, Any]]) -> list[dict[str, Any]]:
    """Evaluate manifest entries on the fleet under work, one contract per
    action; a failed action (out of memory or time) fails only its contract."""
    def failed(failure: fleet.ActionFailed, batch: list[dict[str, Any]]) -> None:
        (failure.batch / "results.jsonl").write_text("".join(PREFIX + json.dumps(
            {"kind": "contract", "contract": entry["name"], "status": "action-failed",
             "message": failure.reason}) + "\n" for entry in batch))

    work.mkdir(parents=True, exist_ok=True)
    fleet.run_batches(holbuild, work, entries, SCRIPT, failed)
    return batch_records(work)


class Fuzzer:
    """One run's output directory: cases/<contract>.json (each a HOL manifest
    entry with its screening counts), work/ (the HOL batches), shrink/,
    minimized/ and the report. evaluate runs manifest entries in HOL into a
    directory and returns its results; screen runs a call in pyrevm."""

    def __init__(self, output: Path, *, seed: int, candidates: int, k: int,
                 evaluate: Callable[[Path, list[dict[str, Any]]], list[dict[str, Any]]],
                 screen: Callable[[Target, Call], Recording] | None = None,
                 sequences: bool = False):
        self.output = output
        self.seed = seed
        self.candidates = candidates
        self.k = k
        self.sequences = sequences
        self.evaluate = evaluate
        self._screen = screen

    def screen(self, target: Target, call: Call) -> Recording:
        if self._screen is None:
            pyrevm = import_pyrevm()
            self._screen = lambda t, c: screen(pyrevm, t, c)
        return self._screen(target, call)

    def screen_sequence(self, target: Target, calls: list[Call]) -> tuple[list[Step], str | None]:
        """Each call screened from the storage the one before it left; a call
        that halts ends the sequence, and its reason is returned."""
        steps: list[Step] = []
        storage = calls[0].storage
        for call in calls:
            call = replace(call, storage=storage)
            try:
                recording = self.screen(target, call)
            except Halt as halt:
                return steps, str(halt)
            steps.append((call, recording))
            storage = carried_storage(call, recording)
        return steps, None

    def manifest(self, target: Target) -> dict[str, Any]:
        """The target's manifest entry: its cases and screening counts, made
        once and reused on resume."""
        path = self.output / "cases" / f"{target.name}.json"
        if path.is_file():
            return json.loads(path.read_text())
        halts: Counter[str] = Counter()
        seen = set()
        screened = []
        candidates = (generate_sequences(self.seed, target, self.candidates) if self.sequences
                      else [[c] for c in generate_calls(self.seed, target, self.candidates)])
        for calls in candidates:
            key = tuple(c.key() for c in calls)
            if key in seen:
                continue
            seen.add(key)
            steps, halt = self.screen_sequence(target, calls)
            if halt is not None:
                halts[halt] += 1
            if steps:
                screened.append(steps)
        cases = make_cases(stratify(self.seed, target.name, screened, self.k))
        stats = {"candidates": len(candidates), "distinct": len(seen), "halted": dict(halts),
                 "shapes": len({tuple((c.function, r.shape()) for c, r in steps)
                                for steps in screened}),
                 "selected": len(cases)}
        entry = {**target.entry, "screening": stats, "cases": [c.suite_case() for c in cases]}
        fleet.exporter.write_json_atomic(path, entry)
        print(f"{target.name}: {len(cases)} cases from {len(seen)} distinct candidates",
              file=sys.stderr, flush=True)
        return entry

    def still_disagree(self, targets: dict[str, Target], round_dir: Path,
                       proposals: dict[str, list[Call]]) -> dict[str, list[bool]]:
        """Which variants still disagree, with a recording the bytecode run
        matches: each is screened afresh and confirmed in HOL. Variants are
        named by position, so the round starts from an empty directory: an
        interrupted run's records are about other calls."""
        shutil.rmtree(round_dir, ignore_errors=True)
        entries: dict[str, dict[str, Any]] = {}
        names: dict[str, list[str | None]] = {}
        for key, calls in proposals.items():
            contract, case = key.split("/")
            entry = entries.setdefault(contract, {**targets[contract].entry, "cases": []})
            names[key] = []
            for i, call in enumerate(calls):
                try:
                    recording = self.screen(targets[contract], call)
                except Halt:
                    names[key].append(None)
                    continue
                name = f"{case}_v{i:03d}"
                entry["cases"].append(Case(name, call, recording, confirm=True).suite_case())
                names[key].append(name)
        results = self.evaluate(round_dir, list(entries.values()))
        disagree = {f"{r['contract']}/{r['case']}" for r in results
                    if r["kind"] == "case" and reproducible(r)}
        return {key: [name is not None and f"{key.split('/')[0]}/{name}" in disagree
                      for name in names[key]] for key in proposals}

    def minimize(self, targets: dict[str, Target], manifests: dict[str, dict[str, Any]],
                 disagreements: list[dict[str, Any]], rounds: int) -> list[Path]:
        """Shrink each disagreement and write them, by contract, as suites."""
        failing = {}
        for r in disagreements:
            case = next(c for c in manifests[r["contract"]]["cases"] if c["name"] == r["case"])
            failing[f"{r['contract']}/{r['case']}"] = call_from_case(case)
        counter = itertools.count()
        minimal = shrink(failing, lambda proposals: self.still_disagree(
            targets, self.output / "shrink" / f"round-{next(counter):02d}", proposals), rounds)
        by_contract: dict[str, list[Case]] = defaultdict(list)
        for key, call in sorted(minimal.items()):
            contract, name = key.split("/")
            by_contract[contract].append(Case(name, call, self.screen(targets[contract], call)))
        written = []
        for contract, cases in sorted(by_contract.items()):
            entry = targets[contract].entry
            path = self.output / "minimized" / f"{contract}.json"
            fleet.exporter.write_json_atomic(path, {
                "name": f"fuzz_{contract}",
                **{k: entry[k] for k in ("source", "contract", "artifact")},
                "peer": entry["peer"], "fuel": entry["fuel"],
                "cases": [c.suite_case(metadata=False) for c in cases]})
            written.append(path)
        return written

    def run(self, targets: list[Target], *, max_batches: int | None,
            shrink_rounds: int) -> dict[str, Any]:
        by_name = {t.name: t for t in targets}
        manifests = {t.name: self.manifest(t) for t in targets}
        work = self.output / "work"
        done = completed_contracts(batch_records(work), manifests)
        pending = [manifests[n] for n in manifests if n not in done]
        if max_batches is not None:
            pending = pending[:max_batches * SCRIPT.batch_size]
        results = self.evaluate(work, pending) if pending else batch_records(work)
        # A contract with any result is reported, its cases without one as missing.
        evaluated = {r["contract"] for r in results}
        summary = report({n: m for n, m in manifests.items() if n in evaluated}, results)
        summary["unevaluated"] = sorted(manifests.keys() - evaluated)
        # Sent to HOL and nothing came back: unlike a deferred contract, a failure.
        summary["unreported"] = sorted({m["name"] for m in pending} - evaluated)
        summary["screening"] = {n: m["screening"] for n, m in sorted(manifests.items())}
        # Every candidate halted or ran over the gas budget: nothing was compared.
        summary["no_cases"] = sorted(n for n, m in manifests.items() if not m["cases"])
        # The others' expectation would be pyrevm's mistake: report, don't write.
        summary["unminimized"] = [r for r in summary["disagree"] if not reproducible(r)]
        written = [r for r in summary["disagree"] if reproducible(r)]
        if written:
            summary["minimized"] = [str(p) for p in self.minimize(
                by_name, manifests, written, shrink_rounds)]
        fleet.exporter.write_json_atomic(self.output / "report.json", summary)
        (self.output / "report.md").write_text(markdown(summary))
        return summary


def failed(summary: dict[str, Any]) -> bool:
    """A disagreement, an error, a case without a result, a contract that
    couldn't be prepared, one sent to HOL with no result, or one with no case
    to compare fails the run."""
    return any(summary.get(k) for k in ("disagree", "error", "missing", "contract_failures",
                                        "unreported", "no_cases"))


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--output", type=Path, required=True,
                        help="run directory: cases, HOL batches, report, minimized suites")
    parser.add_argument("--suite", action="append", default=[],
                        help="fuzz only this differential suite (repeatable)")
    parser.add_argument("--targets", type=Path,
                        help='fuzz the contracts of a JSON {"targets": [suite-shaped entries]} '
                             "instead of the suites")
    parser.add_argument("--semantic-tests", type=Path, metavar="SOLIDITY",
                        help="fuzz the admitted semanticTests of --coverage, from this checkout "
                             "of the Solidity repository at SOLIDITY_PIN")
    parser.add_argument("--coverage", type=Path, help="semanticTests coverage report (JSON)")
    parser.add_argument("--solc", type=Path, help="the pinned solc, for --semantic-tests")
    parser.add_argument("--shard", type=parse_shard, default=(0, 1), metavar="I/N",
                        help="fuzz only every Nth target from the Ith (counting from 0)")
    parser.add_argument("--sequences", action="store_true",
                        help="candidates are sequences of 2 to 4 calls instead of single calls")
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--candidates", type=int, default=200,
                        help="candidates screened per function")
    parser.add_argument("-k", type=int, default=32, help="cases kept per contract")
    parser.add_argument("--max-batches", type=int,
                        help="evaluate at most this many pending contracts (one HOL action each)")
    parser.add_argument("--resume", action="store_true",
                        help="reuse the output's cases and finished contracts; refused if the "
                             "settings, targets or sources changed")
    parser.add_argument("--shrink-rounds", type=int, default=8)
    parser.add_argument("--holbuild", default="holbuild")
    args = parser.parse_args(argv)
    # HOL runs from the repository root, so paths under the output must be absolute.
    args.output = args.output.resolve()
    if not args.resume and args.output.exists() and any(args.output.iterdir()):
        raise SystemExit(f"{args.output} is not empty; pass --resume to continue its run")
    fuzzer = Fuzzer(args.output, seed=args.seed, candidates=args.candidates, k=args.k,
                    evaluate=lambda work, entries: run_fleet(args.holbuild, work, entries),
                    sequences=args.sequences)
    if sum(map(bool, (args.targets, args.suite, args.semantic_tests))) > 1:
        raise SystemExit("--targets, --suite and --semantic-tests are exclusive")
    if args.semantic_tests:
        if not (args.coverage and args.solc):
            raise SystemExit("--semantic-tests needs --coverage and --solc")
        targets = semantic_targets(args.semantic_tests, args.coverage, args.solc,
                                   args.output / "artifacts", args.shard)
    else:
        targets = manifest_targets(args.targets) if args.targets else suite_targets(args.suite)
        targets = targets[args.shard[0]::args.shard[1]]
    check_inputs(args.output, run_inputs(targets, args.seed, args.candidates, args.k,
                                         sequences=args.sequences),
                 resume=args.resume)
    summary = fuzzer.run(targets, max_batches=args.max_batches,
                         shrink_rounds=args.shrink_rounds)
    print(markdown(summary))
    for path in summary.get("minimized", []):
        print(f"minimized disagreements: {path}", file=sys.stderr)
    return 1 if failed(summary) else 0


if __name__ == "__main__":
    sys.exit(main())
