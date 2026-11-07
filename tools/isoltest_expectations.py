"""Strict supported subset of the pinned isoltest Scanner/TestFileParser grammar."""

from __future__ import annotations

from dataclasses import dataclass
import re


class UnsupportedExpectation(ValueError):
    """The complete expectation block must be rejected before replay."""


def scan_string(source: str, start: int) -> tuple[int, bytes]:
    """Read the pinned scanner's escapes, including its one-digit hex rule."""
    result = bytearray()
    i = start + 1
    escapes = {"\\": b"\\", "n": b"\n", "r": b"\r", "t": b"\t", "0": b"\0"}
    while i < len(source):
        c = source[i]
        i += 1
        if c == '"':
            return i, bytes(result)
        if c in "\r\n":
            raise UnsupportedExpectation("multiline string literals are not supported")
        if c != "\\":
            result.extend(c.encode("utf-8"))
            continue
        if i == len(source):
            break
        c = source[i]
        i += 1
        if c == "x":
            if i == len(source) or source[i] not in "0123456789abcdefABCDEF":
                raise UnsupportedExpectation("hex escape needs a hex digit")
            value = int(source[i], 16)
            i += 1
            if i == len(source):
                break
            if source[i] != '"':
                if source[i] in "\r\n":
                    raise UnsupportedExpectation("multiline string literals are not supported")
                if not source[i].isascii():
                    raise UnsupportedExpectation("non-ASCII hex-escape continuations are not supported")
                value = value * 16 + (int(source[i], 16) if source[i] in "0123456789abcdefABCDEF" else 0)
                i += 1
            result.append(value)
        elif c in escapes:
            result.extend(escapes[c])
        else:
            raise UnsupportedExpectation(f"unsupported string escape: {c}")
    raise UnsupportedExpectation("unterminated string literal")


def decode_string(text: str) -> bytes:
    source = '"' + text + '"'
    end, result = scan_string(source, 0)
    if end != len(source):
        raise UnsupportedExpectation("unexpected text after string literal")
    return result


@dataclass(frozen=True)
class Token:
    kind: str
    text: str
    start: int
    end: int


def tokenize(source: str, *, comments: bool = True) -> list[Token]:
    """Scan contiguously; unknown characters cannot be silently skipped."""
    result = []
    i = 0
    while i < len(source):
        start = i
        c = source[i]
        if c in " \t\r\v\f":
            i += 1
            continue
        if c == "\n":
            i, kind = i + 1, "newline"
        elif c == "#" and comments:
            end = source.find("#", i + 1)
            if end == -1:
                raise UnsupportedExpectation("unterminated expectation comment")
            i, kind = end + 1, "comment"
        elif c == "~":
            end = source.find("\n", i)
            i, kind = (len(source) if end == -1 else end), "effect"
            if "/" in source[start:i]:
                raise UnsupportedExpectation("slashes in side-effect observations are not supported")
        elif c == '"':
            i, _ = scan_string(source, i)
            kind = "string"
        elif source.startswith("->", i):
            i, kind = i + 2, "->"
        elif source.startswith("0x", i):
            match = re.match(r"0x[0-9a-fA-F]+", source[i:])
            if not match:
                raise UnsupportedExpectation("hex literal needs a digit")
            i, kind = i + len(match[0]), "hex"
        elif c.isascii() and c.isdigit():
            match = re.match(r"[0-9.]+", source[i:])
            assert match is not None
            i, kind = i + len(match[0]), "number"
        elif c.isascii() and (c.isalpha() or c in "_$"):
            match = re.match(r"[A-Za-z_$][A-Za-z0-9_$]*", source[i:])
            assert match is not None
            i, kind = i + len(match[0]), "id"
        elif c in "(),:[]-" or (c == "#" and not comments):
            i, kind = i + 1, c
        else:
            raise UnsupportedExpectation(f"unsupported expectation character: {c!r}")
        result.append(Token(kind, source[start:i], start, i))
    result.append(Token("end", "", len(source), len(source)))
    return result


RESERVED = {"true", "false", "ether", "wei", "left", "right", "hex", "FAILURE", "gas", "library"}


class Parser:
    """Structural signatures and byte parameters shared by calls and events."""

    def __init__(self, source: str, *, comments: bool = True):
        self.source = source
        self.tokens = tokenize(source, comments=comments)
        self.position = 0
        self.end = 0

    @property
    def current(self) -> Token:
        return self.tokens[self.position]

    def take(self) -> Token:
        token = self.current
        if token.kind != "end":
            self.position += 1
            self.end = token.end
        return token

    def accept(self, text: str) -> bool:
        if self.current.text != text:
            return False
        self.take()
        return True

    def expect(self, text: str) -> None:
        if not self.accept(text):
            raise UnsupportedExpectation(f"expected {text!r}, got {self.current.text!r}")

    def identifier(self) -> str:
        if self.current.kind != "id" or self.current.text in RESERVED:
            raise UnsupportedExpectation(f"expected identifier, got {self.current.text!r}")
        return self.take().text

    def decimal(self) -> str:
        if self.current.kind != "number" or not self.current.text.isdigit():
            raise UnsupportedExpectation("only integral decimal parameters are supported")
        if len(self.current.text) > 1 and self.current.text.startswith("0"):
            raise UnsupportedExpectation("leading-zero numerals are not supported")
        if len(self.current.text) > 78:
            raise UnsupportedExpectation("decimal literal exceeds the supported 256-bit range")
        return self.take().text

    def type_name(self) -> str:
        if self.accept("("):
            parts = [self.type_name()]
            while self.accept(","):
                parts.append(self.type_name())
            self.expect(")")
            result = "(" + ",".join(parts) + ")"
        else:
            result = self.identifier()
        while self.accept("["):
            size = "" if self.current.text == "]" else self.decimal()
            self.expect("]")
            result += "[" + size + "]"
        return result

    def signature(self) -> str:
        name = "" if self.current.text == "(" else self.identifier()
        self.expect("(")
        parts = []
        if self.current.text != ")":
            parts.append(self.type_name())
            while self.accept(","):
                parts.append(self.type_name())
        self.expect(")")
        if not name and parts:
            raise UnsupportedExpectation("raw call signatures cannot have parameter types")
        return name + "(" + ",".join(parts) + ")"

    def newline(self) -> None:
        if self.current.kind == "newline":
            self.take()

    def parameter(self, *, newline: bool = True) -> str | None:
        if newline:
            self.newline()
        if self.current.text in ("left", "right"):
            side = self.take().text
            self.expect("(")
            if self.current.kind not in ("number", "hex") and self.current.text not in ("true", "false"):
                raise UnsupportedExpectation("only unsigned literal alignment is supported")
            value = self.parameter(newline=False)
            self.expect(")")
            return f"{side}({value})"
        if self.accept("-"):
            return "-" + self.decimal()
        if self.current.text == "hex":
            self.take()
            if self.current.kind != "string":
                raise UnsupportedExpectation("hex must precede a string literal")
            return "hex" + self.take().text
        if self.current.kind == "number":
            return self.decimal()
        if self.current.kind in ("string", "hex") or self.current.text in ("true", "false", "FAILURE"):
            if self.current.kind == "hex" and len(self.current.text) > 66:
                raise UnsupportedExpectation("numeric hex parameter exceeds one word")
            return self.take().text
        return None

    def parameters(self, *, required: bool = False) -> list[str]:
        value = self.parameter()
        if value is None:
            if required:
                raise UnsupportedExpectation(f"expected byte parameter, got {self.current.text!r}")
            return []
        values = [value]
        while self.accept(","):
            value = self.parameter()
            if value is None:
                raise UnsupportedExpectation("missing byte parameter after comma")
            values.append(value)
        return values

    def comment(self) -> None:
        if self.current.kind == "comment":
            self.take()

    def finish(self) -> None:
        if self.current.kind != "end":
            raise UnsupportedExpectation(f"unconsumed expectation token: {self.current.text!r}")
