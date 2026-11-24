# SPDX-License-Identifier: Apache-2.0
"""Reading the decoder's printed output (`Tools/decoded_ops.py`) and the tools that use it."""

import importlib
import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
TOOLS = ROOT / "Tools"

# The shape of `Tools/export_decoded.py` output for a program that sets a predicate, branches on
# it, shuffles, elects, and converts a pair of registers to `f16x2`.
DECODED = """\
def code0 : List Instr :=
[{ guard := none,
   op := PTX.Op.int
           { op := PTX.IntOp.setp (PTX.Cmp.lt) none,
             ty := PTX.DType.int (PTX.IType.u) 32,
             sat := false,
             dsts := [some 7],
             srcs := [PTX.Opnd.reg 1, PTX.Opnd.imm (-4)] } },
 { guard := some (7, false), op := PTX.Op.bra 3 false },
 { guard := none,
   op := PTX.Op.warp
           { kind := PTX.WarpKind.elect,
             ty := none,
             dsts := [none, some 8],
             srcs := [],
             mask := some (PTX.Opnd.imm (-1)) } },
 { guard := none,
   op := PTX.Op.cvt
           { dst := PTX.DType.packed (PTX.DType.float (PTX.FType.f16)) 2,
             src := PTX.DType.float (PTX.FType.f32),
             rnd := some (PTX.CvtRnd.rn),
             ftz := false,
             sat := false,
             relu := false,
             satfinite := false,
             pzo := false,
             scaled := false,
             pack := false,
             d := 4,
             srcs := [PTX.Opnd.reg 5, PTX.Opnd.reg 6] } },
 { guard := none, op := PTX.Op.ret }]

def metadata : Kernel :=
{ name := "k",
  regNames := ["%r0", "%p0"],
  code := [] }
"""


@pytest.fixture
def mods(monkeypatch):
    monkeypatch.syspath_prepend(str(TOOLS))
    return importlib.import_module("decoded_ops"), importlib.import_module("code_table")


def test_parse_terms(mods):
    ops, _ = mods
    term = ops.parse(
        "PTX.Op.int { op := PTX.IntOp.add, dsts := [some 7], srcs := [PTX.Opnd.imm (-4)] }"
    )
    assert term.name == "int"
    fields = term.args[0]
    assert fields["op"].name == "add"
    assert ops.dest_ids(fields) == [7]
    assert ops.operand_regs(term) == []
    assert ops.parse('("a\\"b", some (3, true))') == ('a"b', ops.parse("some (3, true)"))


def test_instructions(mods, tmp_path):
    ops, _ = mods
    path = tmp_path / "Decoded.lean"
    path.write_text(DECODED)
    records = ops.instructions(path)
    assert [r["op"].name for r in records] == ["int", "bra", "warp", "cvt", "ret"]
    assert ops.option_value(records[1]["guard"])[0] == 7
    assert ops.operand_regs(records[3]["op"]) == [5, 6]
    assert ops.dest_ids(records[2]["op"].args[0]) == [None, 8]


def test_cvt_runs(mods, tmp_path):
    _, table = mods
    path = tmp_path / "Decoded.lean"
    path.write_text(DECODED)
    instrs = table.items(path.read_text())
    assert table.cvt_runs(instrs) == [(3, [("4", "5", "6")])]


def write_kernel(root: Path, text: str):
    kernel = root / "Kernels" / "Fp16Gemm8192"
    (kernel / "Data").mkdir(parents=True)
    (kernel / "Proof").mkdir()
    (kernel / "Data" / "Decoded.lean").write_text(text)
    return kernel


def run(script: str, root: Path):
    return subprocess.run(
        [sys.executable, str(TOOLS / script), "--root", str(root)],
        capture_output=True,
        text=True,
    )


def test_guard_live_reads_new_forms(tmp_path):
    kernel = write_kernel(tmp_path, DECODED)
    result = run("generate_guard_live.py", tmp_path)
    assert result.returncode == 0, result.stdout + result.stderr
    table = (kernel / "Proof/ProductionSourceGuardSafetyTable.lean").read_text()
    # The branch at pc 1 reads predicate 7, which the `setp` at pc 0 writes.
    assert "[[],[7],[],[],[]]" in table.replace(" ", "")


def test_guard_live_rejects_indexed_branch(tmp_path):
    write_kernel(
        tmp_path, DECODED.replace("PTX.Op.bra 3 false", "PTX.Op.brx (PTX.Opnd.reg 1) [3] false")
    )
    result = run("generate_guard_live.py", tmp_path)
    assert result.returncode != 0 and "indexed branch" in result.stderr


def test_integer_live_reads_new_forms(tmp_path):
    text = DECODED.replace(
        '["%r0", "%p0"]', '["%rd9", "%r724", "%r744", "%r764", "%r704"]'
    ).replace(
        "[{ guard := none,",
        "[{ guard := none, op := PTX.Op.move { kind := PTX.MoveKind.scalar,"
        " ty := PTX.DType.int (PTX.IType.u) 32, dsts := [some 1], srcs := [PTX.Opnd.imm 0] } },\n"
        " { guard := none,",
        1,
    )
    kernel = write_kernel(tmp_path, text)
    result = run("generate_integer_live.py", tmp_path)
    assert result.returncode == 0, result.stdout + result.stderr
    table = (kernel / "Proof/ProductionSourceIntegerLiveTable.lean").read_text()
    # The `setp` reads register 1, which the move writes; the `f16x2` conversion is not an
    # integer operation.
    assert "[[[],[1],[],[],[],[]]]" in table.replace(" ", "")
