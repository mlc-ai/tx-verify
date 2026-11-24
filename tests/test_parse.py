# SPDX-License-Identifier: Apache-2.0
"""PTX parsing: statement and operand syntax, scopes and labels.

Which instructions are supported is decided by the Lean decoder, not by the parser.
"""

import importlib
import os
import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
HEADER = ".version 9.2\n.target sm_100a\n.address_size 64\n"


@pytest.fixture
def parser(monkeypatch):
    monkeypatch.syspath_prepend(str(ROOT / "Tools"))
    return importlib.import_module("parse_ptx")


def test_predication_groups_and_exact_literals(parser):
    source = (
        HEADER
        + """
    .visible .entry kernel(.param .u64 base) {
      .reg .pred %p<3>;
      .reg .b32 %r<5>;
      .reg .b64 %rd<3>;
      ld.param.b64 %rd1, [base];
      @!%p1 bra.uni Done;
      ld.global.v2.b32 {%r1, %r2}, [%rd1 + 16];
      setp.eq.u32 %p1|%p2, %r1, %r2;
      mov.b64 %rd2, 0xffffffffffffffff;
      mov.b32 %r3, 0f80000000;
      cp.async.ca.shared.global [%r4], [%rd1], 16;
      cp.async.commit_group;
      cp.async.wait_group 0;
      bar.sync 0;
    Done:
      ret;
    }
    """
    )
    result = parser.parse(source)
    ops = [s for s in result.functions[0].body if s.kind == "instruction"]
    assert ops[0].opcode == "ld.param.b64"
    assert (ops[1].predicate, ops[1].negated, ops[1].opcode) == ("%p1", True, "bra.uni")
    assert ops[2].operands[0].kind == "vector"
    offset = ops[2].operands[1].children[0]
    assert (offset.kind, offset.text, offset.children[1].text) == ("offset", "+", "16")
    assert ops[3].operands[0].kind == "pair"
    assert ops[4].operands[1].text == "0xffffffffffffffff"
    assert ops[5].operands[1].text == "0f80000000"
    assert [op.opcode for op in ops[6:10]] == [
        "cp.async.ca.shared.global",
        "cp.async.commit_group",
        "cp.async.wait_group",
        "bar.sync",
    ]


def test_lexical_scopes_and_debug_directives(parser):
    source = (
        HEADER
        + """
    .file 1 "a//b.cu"
    .visible .entry kernel() {
      .loc 1 42 0
      {
        .reg .pred %p;
      Again:
        @%p bra Again;
        bra Done;
      }
      {
      Again:
        bra Again;
      }
    Done:
      exit;
    }
    """
    )
    result = parser.parse(source)
    assert result.directives[-1][-1] == '"a//b.cu"'
    body = result.functions[0].body
    assert body[0].tokens == [".loc", "1", "42", "0"]
    assert body[1].kind == body[2].kind == "scope"
    assert body[1].body[1].text == body[2].body[0].text == "Again"


def test_survey_syntax(parser):
    """Spellings of compiler-emitted PTX: an unsigned hexadecimal literal, a negative address
    offset written `+-`, a branch table over several lines and a debug section."""
    source = (
        HEADER
        + """
    .visible .entry kernel() {
      .reg .b32 %r<3>;
      .reg .b64 %rd<2>;
      prmt.b32 %r1, %r2, 0, 0x7772U;
      ld.global.b32 %r1, [%rd1+-8];
      ld.global.b32 %r1, [%rd1 - -8];
    Targets: .branchtargets
        Left,
        Right;
      brx.idx %r1, Targets;
    Left:
      ret;
    Right:
      ret;
    }
    .section .debug_info {
    L: .b8 1
    }
    """
    )
    result = parser.parse(source)
    body = result.functions[0].body
    ops = [s for s in body if s.kind == "instruction"]
    assert ops[0].operands[3].kind == "literal"
    assert ops[0].operands[3].text == "0x7772U"
    for op, sign in [(ops[1], "+"), (ops[2], "-")]:
        offset = op.operands[1].children[0]
        assert (offset.kind, offset.text) == ("offset", sign)
        assert [(c.kind, c.text) for c in offset.children] == [
            ("register", "%rd1"),
            ("literal", "-8"),
        ]
    table = [s for s in body if s.kind == "directive"]
    assert [t.tokens for t in table] == [[".branchtargets", "Left", ",", "Right"]]
    assert ops[3].opcode == "brx.idx"
    assert result.directives[-1] == [".section", ".debug_info", "{", "L", ":", ".b8", "1", "}"]


@pytest.mark.parametrize(
    "body, error",
    [
        ("bra Missing;", "unresolved branch target"),
        ("Label: Label: ret;", "duplicate label"),
        ("{ Inside: ret; } bra Inside;", "unresolved branch target"),
        ("bra %r1;", "unresolved branch target"),
        ("@;", "missing predicate"),
        ("@!;", "missing predicate"),
        ("ret", "unbalanced statement"),
        ("mov.b32 %r1, [%rd1;", "unbalanced statement"),
    ],
)
def test_rejects_unsupported_or_broken_programs(parser, body, error):
    with pytest.raises(ValueError, match=error):
        parser.parse(HEADER + f".visible .entry kernel() {{ {body} }}")


def test_export_needs_no_external_packages(tmp_path):
    """The exporter runs with only the standard library on the path."""
    env = {k: v for k, v in os.environ.items() if k != "PYTHONPATH"}
    out = tmp_path / "Ptx.lean"
    subprocess.run(
        [
            sys.executable,
            "-S",
            str(ROOT / "Tools/export_lean.py"),
            str(ROOT / "Kernels/TcGemm/tc_gemm.ptx"),
            "-o",
            str(out),
            "--namespace",
            "PTX.Generated.TcGemm",
        ],
        check=True,
        env=env,
        capture_output=True,
        text=True,
    )
    assert out.read_text() == (ROOT / "Kernels/TcGemm/Ptx.lean").read_text()
