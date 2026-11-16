#!/usr/bin/env python3
"""Random Solidity programs inside solidity-hol's admitted subset.

Layer 2 of the differential fuzzing: each seed gives one source with one
deployable contract, Gen, over a chain of abstract bases. Its public
functions take typed parameters, which the Layer 1 runner
(run_differential_fuzz.py) fuzzes, and are built from typed templates aimed at
interactions hand-written tests miss: side effects inside operands, indices
and arguments (evaluation order); packed state, storage pointers and copies
between storage and memory (aliasing); virtual functions, super calls and
virtual modifiers (dispatch); try/catch on external calls back into the
contract; abi.encode*/decode round trips; and checked against unchecked
arithmetic. Every expression is generated at a known type, and only forms the
differential suites already exercise are used, so the core admits the
programs by construction.

  python3 tools/generate_solidity_programs.py --seeds 7             # print one
  python3 tools/generate_solidity_programs.py --seeds 0:100 --output DIR
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass, field
from pathlib import Path
import random
import re
import sys

UINTS = ["uint8", "uint16", "uint32", "uint64", "uint128", "uint256"]
INTS = ["int8", "int16", "int64", "int128", "int256"]
INTEGERS = UINTS + INTS
SCALARS = INTEGERS + ["bool", "address", "bytes4", "bytes32"]
# Struct members and array elements: small, so they pack.
SMALL = ["uint8", "uint16", "uint32", "uint64", "int8", "int16", "bool", "address", "bytes4"]

MAX_DEPTH = 3  # expression nesting
MAX_LOCALS = 6  # keeps functions clear of stack-too-deep without the optimizer


def bits(t: str) -> int:
    return int(re.sub(r"\D", "", t) or 256)


def signed(t: str) -> bool:
    return t.startswith("int")


def convertible(source: str, target: str) -> bool:
    """An explicit integer conversion solc allows: size or sign, not both."""
    return source != target and (signed(source) == signed(target) or bits(source) == bits(target))


# Types of variables: a scalar name, or one of these.

@dataclass(frozen=True)
class Struct:
    name: str
    members: tuple[tuple[str, str], ...]


@dataclass(frozen=True)
class Array:
    element: "Type"
    length: int | None  # None: dynamic


@dataclass(frozen=True)
class Mapping:
    key: str
    value: "Type"


Type = str | Struct | Array | Mapping


def type_name(t: Type, location: str = "") -> str:
    suffix = f" {location}" if location else ""
    if isinstance(t, str):
        return t
    if isinstance(t, Struct):
        return t.name + suffix
    if isinstance(t, Array):
        return f"{type_name(t.element)}[{'' if t.length is None else t.length}]" + suffix
    return f"mapping({t.key} => {type_name(t.value)})"


@dataclass
class Var:
    name: str
    type: Type
    location: str  # "storage", "memory" or "" for a value
    writable: bool = True


@dataclass
class Function:
    """What callers need: the name, parameter and return types."""
    name: str
    params: list[str]
    returns: str


@dataclass
class Scope:
    vars: list[Var] = field(default_factory=list)
    unchecked: bool = False

    def child(self, *extra: Var, unchecked: bool = False) -> "Scope":
        """A block's scope: its declarations stay inside it."""
        return Scope(self.vars + list(extra), self.unchecked or unchecked)


Step = tuple[str, "str | int | None"]


def paths(vt: Type, t: str, depth: int = 0) -> list[list[Step]]:
    """The ways from a variable of type vt to a scalar of type t, at most two
    steps deep: members, array indices (with the length) and mapping keys."""
    if vt == t:
        return [[]]
    if depth > 1 or isinstance(vt, str):
        return []
    if isinstance(vt, Struct):
        return [[("member", name)] + rest for name, mt in vt.members
                for rest in paths(mt, t, depth + 1)]
    if isinstance(vt, Array):
        return [[("index", vt.length)] + rest for rest in paths(vt.element, t, depth + 1)]
    return [[("key", vt.key)] + rest for rest in paths(vt.value, t, depth + 1)]


class Program:
    """One seed's program, generated on construction; source() renders it."""

    def __init__(self, seed: int):
        self.seed = seed
        self.rng = random.Random(seed)
        self.counter = 0
        self.helpers: list[str] = []  # internal functions with side effects
        self.features: set[str] = set()
        rng = self.rng
        self.struct = Struct("P", tuple((f"f{i}", rng.choice(SMALL))
                                        for i in range(rng.randint(2, 5))))
        self.state: list[Var] = [Var("trace", "uint256", "storage")]
        self.bases = rng.randint(0, 2)
        self.state_decls: list[list[str]] = [[] for _ in range(self.bases + 1)]
        self.declare_state()
        self.externals: list[Function] = []
        self.bodies: list[str] = []
        self.generate()

    # Names and choices

    def fresh(self, prefix: str) -> str:
        self.counter += 1
        return f"{prefix}{self.counter}"

    def chance(self, p: float) -> bool:
        return self.rng.random() < p

    # State

    def declare_state(self) -> None:
        rng = self.rng
        kinds: list[Type] = [rng.choice(SCALARS) for _ in range(rng.randint(3, 7))]
        kinds += [self.struct, Array(self.struct, None), Mapping("uint256", self.struct),
                  Array(rng.choice(SMALL), rng.randint(2, 4)),
                  Array(rng.choice(INTEGERS[:5]), None),
                  Mapping(rng.choice(["address", "uint256", "bool"]), rng.choice(INTEGERS))]
        rng.shuffle(kinds)
        for t in kinds:
            name = self.fresh("s")
            self.state.append(Var(name, t, "storage"))
            # Spread the declarations over the bases, so the layout spans them.
            where = rng.randint(0, self.bases)
            self.state_decls[where].append(f"{type_name(t)} internal {name};")
        self.state_decls[0].insert(0, "uint256 internal trace;")

    # Expressions

    def literal(self, t: str) -> str:
        rng = self.rng
        if t == "bool":
            return rng.choice(["true", "false"])
        if t == "address":
            return f"address(uint160({rng.choice([0, 1, 0x1000, 0x2000, 0xdeadbeef])}))"
        if t.startswith("bytes"):
            n = int(t[5:])
            return f"{t}(0x{rng.getrandbits(8 * n):0{2 * n}x})"
        b = bits(t)
        if signed(t):
            low, high = -(1 << (b - 1)), (1 << (b - 1)) - 1
            value = (rng.randint(-9, 9) if self.chance(0.6) else
                     rng.choice([low, high, low + 1, rng.randint(max(low, -200), min(high, 200))]))
        else:
            high = (1 << b) - 1
            value = (rng.randint(0, 9) if self.chance(0.6) else
                     rng.choice([high, high - 1, 1 << (b - 1), rng.randint(0, 300) & high]))
        if t != "uint256" and t != "int256":
            return f"{t}({value})"
        return f"{t}({value})" if value >= 0 else f"int256({value})"

    def place(self, scope: Scope, t: str, depth: int,
              writable: bool = False) -> tuple[str, list[str]] | None:
        """A scalar place of type t: a variable, struct member, array element
        or mapping entry reachable from the scope, and the conditions under
        which its dynamic array indices are in bounds. One is picked, and only
        its indices and keys are generated, as expressions at depth + 1; at
        the maximum depth, only places without them."""
        leaf = depth >= MAX_DEPTH
        # A pointer, a copy or a loop counter can't be assigned; its members can.
        found = [(v.name, steps) for v in scope.vars + self.state for steps in paths(v.type, t)
                 if (v.writable or steps or not writable)
                 and not (leaf and any(kind != "member" for kind, _ in steps))]
        if not found:
            return None
        base, steps = self.rng.choice(found)
        guards = []
        for kind, arg in steps:
            if kind == "member":
                base += "." + arg
            elif kind == "index" and arg is None and self.chance(0.75):
                k = self.rng.randrange(3)
                guards.append(f"{base}.length > {k}")
                base += f"[{k}]"
            elif kind == "index":
                base += f"[{self.index(scope, arg, depth + 1)}]"
            else:
                base += f"[{self.expr(scope, arg, depth + 1)}]"
        return base, guards

    def index(self, scope: Scope, length: int | None, depth: int) -> str:
        """An index: mostly in range of a fixed array, anything otherwise."""
        rng = self.rng
        if length is not None and self.chance(0.8):
            return str(rng.randrange(length))
        if length is None and self.chance(0.5):
            return str(rng.randrange(3))
        # Not a constant: solc rejects a constant index past a fixed length.
        return f"uint256({self.expr(scope, 'uint8', max(depth, MAX_DEPTH - 1))}) % 4"

    def expr(self, scope: Scope, t: str, depth: int = 0) -> str:
        """An expression of type t."""
        rng = self.rng
        leaf = depth >= MAX_DEPTH
        options = ["literal", "place", "place"]
        if not leaf:
            options += ["helper"]
            if t in INTEGERS:
                options += ["arith", "arith", "convert", "ternary", "bound"]
            elif t == "bool":
                options += ["compare", "compare", "logic", "not"]
            elif t == "bytes32":
                options += ["hash"]
            elif t == "address":
                options += ["this"]
        choice = rng.choice(options)
        if choice == "place":
            found = self.place(scope, t, depth)
            if found and found[1]:
                return f"({' && '.join(found[1])} ? {found[0]} : {self.literal(t)})"
            if found:
                return found[0]
            choice = "literal"
        if choice == "literal":
            return self.literal(t)
        if choice == "helper":
            self.features.add("evaluation-order")
            return f"{self.helper(t)}({self.expr(scope, 'uint256', depth + 1)})"
        if choice == "arith":
            return self.arith(scope, t, depth)
        if choice == "convert":
            sources = [s for s in INTEGERS if convertible(s, t)]
            return f"{t}({self.expr(scope, rng.choice(sources), depth + 1)})"
        if choice == "ternary":
            return (f"({self.expr(scope, 'bool', depth + 1)} ? {self.expr(scope, t, depth + 1)}"
                    f" : {self.expr(scope, t, depth + 1)})")
        if choice == "bound":
            return f"type({t}).{rng.choice(['max', 'min'])}"
        if choice == "compare":
            u = rng.choice(INTEGERS)
            op = rng.choice(["<", "<=", ">", ">=", "==", "!="])
            return f"({self.expr(scope, u, depth + 1)} {op} {self.expr(scope, u, depth + 1)})"
        if choice == "logic":
            self.features.add("evaluation-order")
            op = rng.choice(["&&", "||"])
            return f"({self.expr(scope, 'bool', depth + 1)} {op} {self.expr(scope, 'bool', depth + 1)})"
        if choice == "not":
            return f"!{self.expr(scope, 'bool', depth + 1)}"
        if choice == "hash":
            self.features.add("abi")
            return f"keccak256({self.encode(scope, depth + 1)})"
        if choice == "this":
            return rng.choice(["address(this)", "msg.sender"])
        raise AssertionError(choice)

    def arith(self, scope: Scope, t: str, depth: int) -> str:
        rng = self.rng
        self.features.add("unchecked" if scope.unchecked else "checked")
        ops = ["+", "-", "*", "/", "%", "&", "|", "^", "<<", ">>", "**"]
        if signed(t):
            ops.append("neg")
        op = rng.choice(ops)
        left = self.expr(scope, t, depth + 1)
        if op == "neg":
            return f"(-{left})"
        if op in ("<<", ">>"):
            return f"({left} {op} {self.expr(scope, 'uint8', depth + 1)})"
        if op == "**":
            return f"({left} ** {rng.randint(0, 3)})"
        if op in ("/", "%", "*") and self.chance(0.6):
            # A small nonzero operand: fewer reverts, so more of the body runs.
            return f"({left} {op} {t}({rng.randint(1, 9)}))"
        return f"({left} {op} {self.expr(scope, t, depth + 1)})"

    def encode(self, scope: Scope, depth: int) -> str:
        rng = self.rng
        args = [self.expr(scope, rng.choice(SCALARS), depth) for _ in range(rng.randint(1, 3))]
        form = rng.choice(["abi.encode", "abi.encodePacked", "selector"])
        if form == "selector":
            return f"abi.encodeWithSelector({self.literal('bytes4')}, {', '.join(args)})"
        return f"{form}({', '.join(args)})"

    def helper(self, t: str) -> str:
        """An internal function returning t that writes state: calls to it in
        operands, indices and arguments make the evaluation order visible."""
        rng = self.rng
        name = self.fresh("fx")
        target = rng.choice([v for v in self.state if v.type in INTEGERS and v.name != "trace"]
                            or [None])
        k = rng.randint(2, 97)
        if signed(t):
            result = f"{t}(int256(trace % 1000) - 500)"
        elif t in UINTS:
            result = f"{t}(trace)"
        elif t == "bool":
            result = "trace % 2 == 1"
        elif t == "address":
            result = "address(uint160(trace))"
        else:
            result = f"{t}(uint{8 * int(t[5:])}(trace))"
        body = [mix(k, "v % 1000")]
        if target is not None:
            # Also changes state the caller's other operands may read.
            change = (f"{target.type}(int256(trace))" if signed(target.type)
                      else f"{target.name} + {target.type}(trace % 7)")
            body.append(f"unchecked {{ {target.name} = {change}; }}")
        self.helpers.append(f"function {name}(uint256 v) internal returns ({t}) {{\n"
                            + "\n".join(indent(body + [f"return {result};"])) + "\n}")
        return name

    # Statements

    def statements(self, scope: Scope, n: int, depth: int = 0) -> list[str]:
        return [s for _ in range(n) for s in self.statement(scope, depth)]

    def statement(self, scope: Scope, depth: int) -> list[str]:
        rng = self.rng
        options = ["local", "assign", "assign", "compound", "emit"]
        if depth < 2:
            options += ["if", "loop", "pointer", "copy", "array", "abi", "require"]
            if not scope.unchecked:
                options += ["unchecked"]
            if self.externals:
                options += ["try"]
        choice = rng.choice(options)
        if choice == "local" and sum(v.location == "" for v in scope.vars) < MAX_LOCALS:
            t = rng.choice(SCALARS)
            name = self.fresh("v")
            line = f"{t} {name} = {self.expr(scope, t)};"
            scope.vars.append(Var(name, t, ""))
            return [line]
        if choice in ("assign", "compound", "local"):
            t = rng.choice(INTEGERS if choice == "compound" else SCALARS)
            found = self.place(scope, t, 1, writable=True)
            if not found:
                return [mix(3, f"uint256({self.expr(scope, 'uint8')})")]
            place, guards = found
            guard = f"if ({' && '.join(guards)}) " if guards else ""
            if choice == "compound":
                op = rng.choice(["+=", "-=", "*=", "|=", "&=", "^="])
                self.features.add("unchecked" if scope.unchecked else "checked")
                return [f"{guard}{place} {op} {self.expr(scope, t)};"]
            return [f"{guard}{place} = {self.expr(scope, t)};"]
        if choice == "emit":
            return [f"emit Trace({self.expr(scope, 'uint256')}, {self.expr(scope, 'int256')});"]
        if choice == "if":
            then = self.statements(scope.child(), rng.randint(1, 2), depth + 1)
            lines = [f"if ({self.expr(scope, 'bool')}) {{", *indent(then), "}"]
            if self.chance(0.5):
                other = self.statements(scope.child(), rng.randint(1, 2), depth + 1)
                lines[-1:] = ["} else {", *indent(other), "}"]
            return lines
        if choice == "loop":
            i = self.fresh("i")
            inner = scope.child(Var(i, "uint256", "", writable=False))
            body = self.statements(inner, rng.randint(1, 2), depth + 1)
            return [f"for (uint256 {i} = 0; {i} < {rng.randint(1, 3)}; {i}++) {{", *indent(body), "}"]
        if choice == "unchecked":
            self.features.add("unchecked")
            body = self.statements(scope.child(unchecked=True), rng.randint(1, 3), depth + 1)
            return ["unchecked {", *indent(body), "}"]
        if choice == "require":
            if self.chance(0.5):
                return [f'require({self.expr(scope, "bool")}, "r{self.fresh("")}");']
            return [f"if ({self.expr(scope, 'bool')}) revert Failed({self.expr(scope, 'uint256')});"]
        if choice == "pointer":
            return self.pointer(scope, depth)
        if choice == "copy":
            return self.copy(scope)
        if choice == "array":
            return self.array(scope)
        if choice == "abi":
            return self.abi(scope)
        if choice == "try":
            return self.try_call(scope, depth)
        raise AssertionError(choice)

    def struct_place(self, scope: Scope) -> tuple[list[str], str]:
        """A storage struct: the state one, a mapping entry or an array
        element (mostly after a push that makes it exist), with the
        statements that must come first."""
        v = self.rng.choice([v for v in self.state if self.struct in (
            v.type, getattr(v.type, "element", None), getattr(v.type, "value", None))])
        if v.type == self.struct:
            return [], v.name
        if isinstance(v.type, Mapping):
            return [], f"{v.name}[{self.expr(scope, v.type.key, MAX_DEPTH - 1)}]"
        if self.chance(0.8):
            return [f"if ({v.name}.length == 0) {v.name}.push();"], f"{v.name}[0]"
        return [], f"{v.name}[{self.index(scope, None, MAX_DEPTH - 1)}]"

    def pointer(self, scope: Scope, depth: int) -> list[str]:
        """Two storage pointers, perhaps to the same struct, written through."""
        self.features.add("aliasing")
        rng = self.rng
        p, q = self.fresh("p"), self.fresh("q")
        lines, first = self.struct_place(scope)
        lines.append(f"P storage {p} = {first};")
        if self.chance(0.5):
            lines.append(f"P storage {q} = {p};")
        else:
            before, second = self.struct_place(scope)
            lines += before + [f"P storage {q} = {second};"]
        scope.vars += [Var(p, self.struct, "storage", writable=False),
                       Var(q, self.struct, "storage", writable=False)]
        for _ in range(rng.randint(1, 3)):
            name, mt = rng.choice(self.struct.members)
            target = rng.choice([p, q])
            lines.append(f"{target}.{name} = {self.expr(scope, mt)};")
        return lines

    def copy(self, scope: Scope) -> list[str]:
        """A storage struct or array copied to memory, changed, copied back."""
        self.features.add("copies")
        rng = self.rng
        m = self.fresh("m")
        arrays = [v for v in self.state if isinstance(v.type, Array) and v.type.element != self.struct]
        if arrays and self.chance(0.4):
            v = rng.choice(arrays)
            t = v.type
            lines = [f"{type_name(t, 'memory')} {m} = {v.name};"]
            idx = str(rng.randrange(t.length)) if t.length else "0"
            guard = "" if t.length else f"if ({m}.length > 0) "
            lines.append(f"{guard}{m}[{idx}] = {self.expr(scope, t.element)};")
            lines.append(f"{v.name} = {m};")
            return lines
        lines, source = self.struct_place(scope)
        lines.append(f"P memory {m} = {source};")
        scope.vars.append(Var(m, self.struct, "memory", writable=False))
        for _ in range(rng.randint(1, 2)):
            name, mt = rng.choice(self.struct.members)
            lines.append(f"{m}.{name} = {self.expr(scope, mt)};")
        if self.chance(0.7):
            before, target = self.struct_place(scope)
            lines += before + [f"{target} = {m};"]
        return lines

    def array(self, scope: Scope) -> list[str]:
        rng = self.rng
        self.features.add("copies")
        arrays = [v for v in self.state if isinstance(v.type, Array) and v.type.length is None]
        v = rng.choice(arrays)
        if v.type.element == self.struct:
            if self.chance(0.5):
                return [f"{v.name}.push();"]
            m = self.fresh("m")
            name, mt = rng.choice(self.struct.members)
            return [f"P memory {m};", f"{m}.{name} = {self.expr(scope, mt)};", f"{v.name}.push({m});"]
        if self.chance(0.6):
            return [f"{v.name}.push({self.expr(scope, v.type.element)});"]
        return [f"if ({v.name}.length > {rng.randint(0, 1)}) {v.name}.pop();"]

    def abi(self, scope: Scope) -> list[str]:
        """A round trip through abi.encode and abi.decode, or a hash."""
        self.features.add("abi")
        rng = self.rng
        types = [rng.choice(SCALARS) for _ in range(rng.randint(1, 3))]
        names = [self.fresh("d") for _ in types]
        values = [self.expr(scope, t) for t in types]
        encoded = self.fresh("e")
        lines = [f"bytes memory {encoded} = abi.encode({', '.join(values)});",
                 f"({', '.join(f'{t} {n}' for t, n in zip(types, names))}) = "
                 f"abi.decode({encoded}, ({', '.join(types)}));"]
        scope.vars += [Var(n, t, "") for t, n in zip(types, names)]
        return lines

    def try_call(self, scope: Scope, depth: int) -> list[str]:
        """A try on one of the earlier external functions, through the contract's address."""
        self.features.add("try")
        rng = self.rng
        f = rng.choice(self.externals)
        args = ", ".join(self.expr(scope, t) for t in f.params)
        r = self.fresh("r")
        lines = [f"try IGen(address(this)).{f.name}({args}) returns ({f.returns} {r}) {{"]
        inner = scope.child(Var(r, f.returns, "", writable=False))
        lines += indent(self.statements(inner, rng.randint(1, 2), depth + 1))
        clauses = rng.sample(["error", "panic", "bytes", "bare"], k=rng.randint(1, 3))
        if "bytes" in clauses and "bare" in clauses:
            clauses.remove("bare")
        for clause in clauses:
            if clause == "error":
                e = self.fresh("why")
                lines.append(f"}} catch Error(string memory {e}) {{")
                lines.append("    " + mix(5, f"bytes({e}).length"))
            elif clause == "panic":
                c = self.fresh("code")
                lines.append(f"}} catch Panic(uint256 {c}) {{")
                lines.append("    " + mix(7, f"{c} % 1000"))
            elif clause == "bytes":
                b = self.fresh("raw")
                lines.append(f"}} catch (bytes memory {b}) {{")
                lines.append("    " + mix(11, f"{b}.length"))
            else:
                lines.append("} catch {")
                lines.append("    " + mix(13, "1"))
        lines.append("}")
        return lines

    # Functions and contracts

    def generate(self) -> None:
        rng = self.rng
        # Virtual hooks: declared in the first base, overridden down the chain.
        self.hooks = [self.fresh("hook") for _ in range(rng.randint(1, 2))] if self.bases else []
        self.modifiers = [self.fresh("mod") for _ in range(rng.randint(1, 2))]
        for _ in range(rng.randint(3, 6)):
            self.external()

    def external(self) -> None:
        rng = self.rng
        name = self.fresh("f")
        params = [rng.choice(SCALARS) for _ in range(rng.randint(1, 3))]
        returns = rng.choice(SCALARS)
        scope = Scope([Var(f"a{i}", t, "") for i, t in enumerate(params)])
        mods = ""
        if self.chance(0.5):
            self.features.add("dispatch")
            chosen = rng.sample(self.modifiers, k=rng.randint(1, len(self.modifiers)))
            mods = " " + " ".join(f"{m}({self.expr(scope, 'uint256', MAX_DEPTH - 1)})" for m in chosen)
        body = self.statements(scope, rng.randint(2, 6))
        if self.hooks and self.chance(0.6):
            self.features.add("dispatch")
            hook = rng.choice(self.hooks)
            body.append(mix(3, f"{hook}({self.expr(scope, 'uint256')}) % 1000"))
        body.append(f"return {self.expr(scope, returns)};")
        signature = ", ".join(f"{t} a{i}" for i, t in enumerate(params))
        self.bodies.append(
            f"function {name}({signature}) public{mods} returns ({returns}) {{\n"
            + "\n".join(indent(body)) + "\n}")
        self.externals.append(Function(name, params, returns))

    def hook_bodies(self) -> list[list[str]]:
        """Each hook per contract of the chain: the first base declares it,
        each later contract overrides it and maybe calls super."""
        chain: list[list[str]] = [[] for _ in range(self.bases + 1)]
        for hook in self.hooks:
            for level in range(self.bases + 1):
                last = level == self.bases
                if level > 0 and not last and self.chance(0.4):
                    continue
                k = self.rng.randint(2, 50)
                call = "super." + hook + "(x + 1)" if level > 0 and self.chance(0.6) else "x"
                virtual = "" if last else " virtual"
                override = " override" if level > 0 else ""
                chain[level].append(
                    f"function {hook}(uint256 x) internal{virtual}{override} returns (uint256) {{\n"
                    f"    {mix(k, str(level + 1))}\n"
                    f"    return {call};\n"
                    f"}}")
        return chain

    def modifier_bodies(self) -> list[list[str]]:
        """Modifiers: declared in the first contract, overridden in the last
        perhaps, with the placeholder before, after or between effects."""
        chain: list[list[str]] = [[] for _ in range(self.bases + 1)]
        for m in self.modifiers:
            levels = [0] if self.bases == 0 else [0, self.bases] if self.chance(0.6) else [0]
            for level in levels:
                last = level == self.bases
                virtual = "" if last else " virtual"
                override = " override" if level > 0 else ""
                k = self.rng.randint(2, 50)
                shape = self.rng.choice(["before", "after", "around", "guard", "twice"])
                pre = mix(k, "n % 100")
                post = f"trace = trace + {level + 1};"
                body = {"before": ["_;", pre], "after": [pre, "_;"], "around": [pre, "_;", post],
                        "guard": [f'require(n % {k} != 1, "m{level}");', "_;", post],
                        "twice": [pre, "_;", "_;"]}[shape]
                chain[level].append(f"modifier {m}(uint256 n){virtual}{override} {{\n"
                                    + "\n".join(indent(body)) + "\n}")
        return chain

    def source(self) -> str:
        names = [f"Base{i}" for i in range(self.bases)] + ["Gen"]
        hooks = self.hook_bodies()
        modifiers = self.modifier_bodies()
        out = ["// SPDX-License-Identifier: MIT",
               "pragma solidity 0.8.37;",
               f"// Generated by tools/generate_solidity_programs.py, seed {self.seed}.",
               "",
               f"struct P {{ {'; '.join(f'{t} {n}' for n, t in self.struct.members)}; }}",
               "",
               "interface IGen {"]
        out += [f"    function {f.name}({', '.join(f.params)}) external returns ({f.returns});"
                for f in self.externals]
        out += ["}", ""]
        for level, name in enumerate(names):
            last = level == self.bases
            head = ("contract Gen" if last else f"abstract contract {name}")
            if level > 0:
                head += f" is {names[level - 1]}"
            out.append(head + " {")
            body: list[str] = []
            if level == 0:
                body += ["event Trace(uint256 a, int256 b);", "error Failed(uint256 code);"]
            body += self.state_decls[level]
            body += hooks[level] + modifiers[level]
            if last:
                body += self.helpers + self.bodies
            out += indent(body)
            out += ["}", ""]
        return "\n".join(out)


def mix(k: int, term: str) -> str:
    """A statement folding a value into trace, which every program keeps as
    a record of the order effects happened in; it can't overflow."""
    return f"trace = trace % 1000003 * {k} + {term};"


def indent(lines: list[str], levels: int = 1) -> list[str]:
    pad = "    " * levels
    return [pad + line if line else line for line in "\n".join(lines).split("\n")] if lines else []


def generate(seed: int) -> str:
    return Program(seed).source()


def parse_seeds(text: str) -> range:
    """START:STOP, or one seed."""
    start, _, stop = text.partition(":")
    return range(int(start), int(stop) if stop else int(start) + 1)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--seeds", type=parse_seeds, default=range(1), help="START:STOP or SEED")
    parser.add_argument("--output", type=Path, help="write gen_<seed>.sol files here")
    args = parser.parse_args(argv)
    for seed in args.seeds:
        if args.output is None:
            print(generate(seed))
        else:
            args.output.mkdir(parents=True, exist_ok=True)
            (args.output / f"gen_{seed:06d}.sol").write_text(generate(seed))
    return 0


if __name__ == "__main__":
    sys.exit(main())
