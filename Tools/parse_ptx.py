# SPDX-License-Identifier: Apache-2.0
"""Parse PTX source text into a syntax tree.

The parser knows PTX's statement and operand syntax, not individual instructions: an
opcode stays one string (`tcgen05.mma.cta_group::1.kind::i8`) and its meaning is decided by
the Lean decoder (`Core/Source/Decode.lean`), which rejects any form it does not support.
`export_lean.py` writes the tree as Lean data.
"""

import hashlib
import re
from dataclasses import dataclass, field


@dataclass
class Operand:
    kind: str
    text: str = ""
    children: list["Operand"] = field(default_factory=list)


@dataclass
class Statement:
    kind: str
    text: str = ""
    opcode: str = ""
    predicate: str = ""
    negated: bool = False
    operands: list[Operand] = field(default_factory=list)
    tokens: list[str] = field(default_factory=list)
    body: list["Statement"] = field(default_factory=list)


@dataclass
class Function:
    name: str
    header: list[str]
    declaration: bool
    body: list[Statement]


@dataclass
class Program:
    schema: str
    source_sha256: str
    directives: list[list[str]]
    globals: list[list[str]]
    functions: list[Function]


@dataclass
class Token:
    text: str
    line: int


_TOKEN = re.compile(
    r"(?P<space>\s+)|(?P<comment>//[^\n]*|/\*[\s\S]*?\*/)"
    r'|(?P<string>"(?:\\.|[^"\\])*")'
    r"|(?P<number>0[fFdD][0-9a-fA-F]+|0[xX][0-9a-fA-F]+[uU]?|"
    r"(?:[0-9]+(?:\.[0-9]*)?|\.[0-9]+)(?:[eE][+-]?[0-9]+)?[uU]?)"
    r"|(?P<name>\.?[%A-Za-z_$][%A-Za-z_0-9$]*(?:(?:\.|::)[A-Za-z_0-9$]+)*)"
    r"|(?P<punct>[{}\[\](),;:@!+\-|=<>])"
)
_PAIRS = {"(": ")", "[": "]", "{": "}"}
_DECL = {
    ".reg",
    ".param",
    ".shared",
    ".local",
    ".global",
    ".const",
    ".align",
    ".extern",
}


def tokenize(source: str) -> list[Token]:
    result, pos, line = [], 0, 1
    while pos < len(source):
        match = _TOKEN.match(source, pos)
        if match is None:
            raise ValueError(f"line {line}: unsupported PTX syntax near {source[pos : pos + 30]!r}")
        text = match.group()
        if match.lastgroup not in ("space", "comment"):
            result.append(Token(text, line))
        line += text.count("\n")
        pos = match.end()
    return result


def split_top(tokens: list[str], separator: str) -> list[list[str]]:
    result, current, stack = [], [], []
    for token in tokens:
        if token in _PAIRS:
            stack.append(_PAIRS[token])
        elif token in _PAIRS.values():
            if not stack or stack.pop() != token:
                raise ValueError("unbalanced PTX operand delimiters")
        if token == separator and not stack:
            result.append(current)
            current = []
        else:
            current.append(token)
    if stack:
        raise ValueError("unbalanced PTX operand delimiters")
    result.append(current)
    return result


def parse_operand(tokens: list[str]) -> Operand:
    if not tokens:
        raise ValueError("empty operand")
    parts = split_top(tokens, "|")
    if len(parts) > 1:
        return Operand("pair", children=[parse_operand(p) for p in parts])
    if tokens[0] in ("[", "{"):
        if tokens[-1] != _PAIRS[tokens[0]]:
            raise ValueError("unbalanced PTX operand group")
        return Operand(
            "address" if tokens[0] == "[" else "vector",
            children=[parse_operand(p) for p in split_top(tokens[1:-1], ",")],
        )
    if tokens[0] == "!":
        return Operand("not", children=[parse_operand(tokens[1:])])
    # Keep literal spellings exact: no host float conversion or integer truncation.
    if len(tokens) == 2 and tokens[0] in ("+", "-"):
        return Operand("literal", "".join(tokens))
    if len(tokens) == 3 and tokens[1] in ("+", "-"):
        return Operand("offset", tokens[1], [parse_operand(tokens[:1]), parse_operand(tokens[2:])])
    # `[%rd+-8]`: the offset is a signed literal.
    if len(tokens) == 4 and tokens[1] in ("+", "-") and tokens[2] in ("+", "-"):
        return Operand("offset", tokens[1], [parse_operand(tokens[:1]), parse_operand(tokens[2:])])
    if len(tokens) != 1:
        raise ValueError(f"unsupported operand expression: {' '.join(tokens)}")
    text = tokens[0]
    if text == "_":
        return Operand("sink", text)
    if text.startswith("%"):
        return Operand("register", text)
    if re.fullmatch(r"[A-Za-z_$][A-Za-z_0-9$]*(?:\.[A-Za-z_0-9$]+)*", text):
        return Operand("symbol", text)
    return Operand("literal", text)


class Parser:
    def __init__(self, source):
        self.tokens = tokenize(source)
        self.pos = 0

    def peek(self):
        return self.tokens[self.pos].text if self.pos < len(self.tokens) else ""

    def take(self):
        if not self.peek():
            raise ValueError("unexpected end of PTX input")
        token = self.tokens[self.pos]
        self.pos += 1
        return token.text

    def record(self, line_only=False):
        line, result, stack = self.tokens[self.pos].line, [], []
        while self.peek():
            if line_only and not stack and self.tokens[self.pos].line != line:
                break
            token = self.take()
            if token == ";" and not stack:
                return result
            if token in _PAIRS:
                stack.append(_PAIRS[token])
            elif token in _PAIRS.values():
                if not stack or stack.pop() != token:
                    raise ValueError("unbalanced statement delimiters")
            result.append(token)
        if stack or (not line_only):
            raise ValueError("unterminated PTX statement")
        return result

    def body(self):
        result = []
        while self.peek() and self.peek() != "}":
            token = self.peek()
            if token == "{":
                self.take()
                result.append(Statement("scope", body=self.body()))
            elif self.pos + 1 < len(self.tokens) and self.tokens[self.pos + 1].text == ":":
                result.append(Statement("label", text=self.take()))
                self.take()
            elif token.startswith("."):
                declaration = token in _DECL
                result.append(
                    Statement(
                        "declaration" if declaration else "directive",
                        tokens=self.record(line_only=not declaration and token != ".branchtargets"),
                    )
                )
            else:
                tokens = self.record()
                predicate, negated = "", False
                if not tokens:
                    raise ValueError("empty PTX instruction")
                if tokens[0] == "@":
                    tokens = tokens[1:]
                    if tokens and tokens[0] == "!":
                        negated, tokens = True, tokens[1:]
                    if not tokens:
                        raise ValueError("missing predicate after @")
                    predicate, tokens = tokens[0], tokens[1:]
                if not tokens:
                    raise ValueError("missing instruction after predicate")
                opcode = tokens[0]
                operands = (
                    [parse_operand(p) for p in split_top(tokens[1:], ",")] if tokens[1:] else []
                )
                result.append(
                    Statement(
                        "instruction",
                        opcode=opcode,
                        predicate=predicate,
                        negated=negated,
                        operands=operands,
                    )
                )
        if self.take() != "}":
            raise ValueError("unterminated function or scope")
        return result

    def program(self, source):
        directives, globals_, functions = [], [], []
        while self.peek():
            if self.peek() == ".section":
                # Debug sections are non-executable module metadata. Keep every
                # token, including the delimiters, as written in the PTX.
                section = [self.take()]
                if not self.peek().startswith("."):
                    raise ValueError("missing PTX section name")
                section.append(self.take())
                if self.take() != "{":
                    raise ValueError("missing PTX section body")
                section.append("{")
                depth = 1
                while self.peek() and depth:
                    token = self.take()
                    section.append(token)
                    depth += (token == "{") - (token == "}")
                if depth:
                    raise ValueError("unterminated PTX section")
                directives.append(section)
                continue
            if self.peek() in (".version", ".target", ".address_size", ".file"):
                directives.append(self.record(line_only=True))
                continue
            header, parens = [], 0
            while self.peek():
                token = self.take()
                if token in ("{", ";") and parens == 0:
                    break
                header.append(token)
                parens += (token == "(") - (token == ")")
            else:
                raise ValueError("unterminated module declaration")
            kinds = [i for i, value in enumerate(header) if value in (".entry", ".func")]
            if not kinds:
                if token != ";":
                    raise ValueError("global initializers with braces are not supported yet")
                globals_.append(header)
                continue
            i = kinds[0] + 1
            if i >= len(header):
                raise ValueError("missing PTX function name")
            if header[i] == "(":  # Optional device-function return parameter list.
                depth = 1
                i += 1
                while i < len(header) and depth:
                    depth += (header[i] == "(") - (header[i] == ")")
                    i += 1
            if i >= len(header):
                raise ValueError("missing PTX function name")
            name = header[i]
            functions.append(
                Function(name, header, token == ";", [] if token == ";" else self.body())
            )
        if len({f.name for f in functions}) != len(functions):
            raise ValueError("duplicate function declarations are not supported yet")
        result = Program(
            "ptx-source-v1",
            hashlib.sha256(source.encode()).hexdigest(),
            directives,
            globals_,
            functions,
        )
        validate_labels(result)
        return result


def validate_labels(program: Program):
    def visit(body, parents):
        labels = [s.text for s in body if s.kind == "label"]
        if len(set(labels)) != len(labels):
            raise ValueError("duplicate label in one PTX scope")
        visible = set(labels) | parents
        for statement in body:
            if statement.kind == "scope":
                visit(statement.body, visible)
            elif statement.kind == "instruction":
                if statement.negated and not statement.predicate:
                    raise ValueError("negated instruction without a predicate")
                if (
                    statement.opcode.split(".")[0] == "bra"
                    and statement.operands[0].text not in visible
                ):
                    raise ValueError(f"unresolved branch target {statement.operands[0].text}")

    for function in program.functions:
        visit(function.body, set())


def parse(source: str) -> Program:
    return Parser(source).program(source)
