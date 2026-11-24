# SPDX-License-Identifier: Apache-2.0
"""Instruction records of a decoded kernel, read from the decoder's printed output.

`Tools/export_decoded.py` writes `Kernels/<K>/Data/Decoded.lean` with the derived `Repr` of the
decoder's result. `instructions` reads those records back as terms: a constructor application is
an `App`, a structure literal a `dict`, a bracketed list a `list`, a pair a `tuple`, a number an
`int` and a string a `str`. The generators of liveness tables read the instruction's family
constructor and its fields from these terms instead of matching the printed text.
"""

import re
from dataclasses import dataclass, field
from pathlib import Path

from code_table import items

TOKEN = re.compile(
    r"""\s*(?:
        (?P<str>"(?:[^"\\]|\\.)*")
      | (?P<num>-?\d+)
      | (?P<punct>:=|[{}()\[\],])
      | (?P<id>[^\s{}()\[\],:"]+)
    )""",
    re.X,
)


@dataclass
class App:
    """A constructor or function applied to arguments; `head` is the name as printed."""

    head: str
    args: list = field(default_factory=list)

    @property
    def name(self) -> str:
        """The last component of the name: `PTX.Op.int` is `int`."""
        return self.head.rsplit(".", 1)[-1]


def tokens(text: str) -> list[tuple[str, str]]:
    out, pos = [], 0
    while pos < len(text):
        m = TOKEN.match(text, pos)
        if m is None:
            if text[pos:].strip() == "":
                break
            raise ValueError(f"cannot read {text[pos : pos + 40]!r}")
        kind = m.lastgroup
        out.append((kind, m.group(kind)))
        pos = m.end()
    return out


class Parser:
    def __init__(self, text: str):
        self.toks = tokens(text)
        self.i = 0

    def peek(self):
        return self.toks[self.i] if self.i < len(self.toks) else (None, None)

    def take(self, value=None):
        kind, text = self.peek()
        if value is not None and text != value:
            raise ValueError(f"expected {value!r}, found {text!r}")
        self.i += 1
        return kind, text

    def atom(self):
        kind, text = self.take()
        if kind == "str":
            return bytes(text[1:-1], "utf-8").decode("unicode_escape")
        if kind == "num":
            return int(text)
        if kind == "id":
            return App(text)
        if text == "(":
            first = self.term()
            if self.peek()[1] == ",":
                items_ = [first]
                while self.peek()[1] == ",":
                    self.take(",")
                    items_.append(self.term())
                self.take(")")
                return tuple(items_)
            self.take(")")
            return first
        if text == "[":
            out = []
            while self.peek()[1] != "]":
                out.append(self.term())
                if self.peek()[1] == ",":
                    self.take(",")
            self.take("]")
            return out
        if text == "{":
            out = {}
            while self.peek()[1] != "}":
                _, name = self.take()
                self.take(":=")
                out[name] = self.term()
                if self.peek()[1] == ",":
                    self.take(",")
            self.take("}")
            return out
        raise ValueError(f"unexpected {text!r}")

    def term(self):
        head = self.atom()
        if not isinstance(head, App):
            return head
        while self.peek()[1] not in (None, ",", ")", "]", "}", ":="):
            head.args.append(self.atom())
        return head


def parse(text: str):
    """The term a printed value denotes."""
    parser = Parser(text)
    value = parser.term()
    if parser.i != len(parser.toks):
        raise ValueError("trailing text after a term")
    return value


def instructions(path: Path) -> list[dict]:
    """The instruction records (`guard`, `op`) of a decoded kernel file, in program order."""
    records = [parse(text) for text in items(path.read_text())]
    if not records:
        raise ValueError(f"{path} contains no instruction records")
    return records


def walk(term):
    """Every sub-term, the term itself first."""
    yield term
    if isinstance(term, App):
        for a in term.args:
            yield from walk(a)
    elif isinstance(term, (list, tuple)):
        for a in term:
            yield from walk(a)
    elif isinstance(term, dict):
        for a in term.values():
            yield from walk(a)


def op_family(op: App) -> str:
    """The `Op` constructor: `int`, `move`, `cvt`, `mem`, `addr`, `warp`, `bra`, ..."""
    return op.name


def sub_name(term) -> str | None:
    """The constructor name of a term that is an `App`, else none."""
    return term.name if isinstance(term, App) else None


def operand_regs(op: App) -> list[int]:
    """The ids of every `Opnd.reg` the instruction mentions, in order."""
    return [
        t.args[0] for t in walk(op) if isinstance(t, App) and t.head.endswith("Opnd.reg") and t.args
    ]


def option_value(term):
    """`some x` as `x`, `none` as `None`."""
    if isinstance(term, App) and term.name == "none":
        return None
    if isinstance(term, App) and term.name == "some":
        return term.args[0]
    raise ValueError(f"not an option: {term}")


def dest_ids(fields: dict) -> list[int | None]:
    """The destination register ids of a family structure (`None` for `_`)."""
    if "dsts" in fields:
        return [option_value(d) for d in fields["dsts"]]
    if "d" in fields:
        return [fields["d"]]
    raise ValueError("instruction has no destination field")
