# SPDX-License-Identifier: Apache-2.0
"""Tools/machine_gen.py: value tables generated from the PTX, and their freshness."""

import importlib
import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
TOOLS = ROOT / "Tools"
DECLS = sorted((ROOT / "Tests" / "Gen").glob("*.json")) + sorted(ROOT.glob("Kernels/*/Gen/*.json"))


@pytest.fixture(scope="module")
def mg():
    sys.path.insert(0, str(TOOLS))
    return importlib.import_module("machine_gen")


@pytest.mark.parametrize("decl", DECLS, ids=lambda p: str(p.relative_to(ROOT)))
def test_generated_tables_are_fresh(decl):
    r = subprocess.run(
        [sys.executable, str(TOOLS / "machine_gen.py"), str(decl), "--check"],
        capture_output=True,
        text=True,
    )
    assert r.returncode == 0, r.stdout + r.stderr


def ins(pc, opcode, operands, writes, event=False):
    return {
        "pc": pc,
        "opcode": opcode,
        "operands": operands,
        "guard": None,
        "event": event,
        "target": None,
        "table": None,
        "writes": writes,
        "reads": [],
    }


def test_terms_mirror_the_code(mg):
    code = [
        ins(0, "setp.eq.b32", ["%p1", "%r1", "0"], ["%p1"]),
        ins(1, "selp.b32", ["%r2", "0", "%r3", "%p1"], ["%r2"]),
        ins(2, "add.s32", ["%r4", "%r2", "%r5"], ["%r4"]),
        ins(3, "shfl.sync.up.b32", ["%r6", "%r4", "1", "0", "-1"], ["%r6"], event=True),
        ins(4, "add.s32", ["%r7", "%r4", "31"], ["%r7"]),
    ]
    ids = {"%p1": 1, "%r2": 2, "%r4": 4, "%r7": 7}
    st = mg.Stretch(code, ids, {"%r1": "lane", "%r3": "u", "%r5": "t"})
    rows = st.entries(0, 5)
    assert [(i, v) for i, v, _ in rows] == [
        (1, ".pred (scmpi .eq .b lane 0)"),
        (2, ".bits 32 (sel (scmpi .eq .b lane 0) (i32 0) u)"),
        (4, ".bits 32 (add32 (sel (scmpi .eq .b lane 0) (i32 0) u) t)"),
        (7, ".bits 32 (addi (add32 (sel (scmpi .eq .b lane 0) (i32 0) u) t) 31)"),
    ]


def test_unknown_operand_is_reported(mg):
    code = [ins(0, "add.s32", ["%r4", "%r2", "%r5"], ["%r4"])]
    st = mg.Stretch(code, {"%r4": 4}, {"%r2": "a"})
    with pytest.raises(mg.GenError, match="%r5 needs a declared term"):
        st.entries(0, 1)


def test_branch_is_reported(mg):
    code = [dict(ins(0, "bra", ["$L"], []), target=3)]
    st = mg.Stretch(code, {}, {})
    with pytest.raises(mg.GenError, match="leaves the stretch"):
        st.entries(0, 1)


def test_declared_branch_path(mg):
    br = dict(ins(1, "bra", ["$L"], []), target=3, guard={"register": "%p1", "negated": False})
    code = [
        ins(0, "add.s32", ["%r2", "%r1", "1"], ["%r2"]),
        br,
        ins(2, "add.s32", ["%r3", "%r2", "2"], ["%r3"]),
        ins(3, "add.s32", ["%r4", "%r2", "3"], ["%r4"]),
    ]
    ids = {"%r2": 2, "%r3": 3, "%r4": 4}
    taken = mg.Stretch(code, ids, {"%r1": "x"}).entries(0, 4, {"1": True})
    assert [i for i, _, _ in taken] == [2, 4]
    fall = mg.Stretch(code, ids, {"%r1": "x"}).entries(0, 4, {"1": False})
    assert [i for i, _, _ in fall] == [2, 3, 4]
    with pytest.raises(mg.GenError, match="declared direction"):
        mg.Stretch(code, ids, {"%r1": "x"}).entries(0, 4)


def test_wide_and_narrow_forms(mg):
    code = [
        ins(0, "mul.wide.s32", ["%rd1", "%r1", "4"], ["%rd1"]),
        ins(1, "add.s64", ["%rd2", "%rd9", "%rd1"], ["%rd2"]),
        ins(2, "cvt.s64.s32", ["%rd3", "%r1"], ["%rd3"]),
        ins(3, "shl.b64", ["%rd4", "%rd3", "2"], ["%rd4"]),
        ins(4, "mov.u16", ["%rs1", "1"], ["%rs1"]),
        ins(5, "xor.b16", ["%rs2", "%rs1", "1"], ["%rs2"]),
        ins(6, "cvt.u32.u16", ["%r2", "%rs2"], ["%r2"]),
        ins(7, "cvt.s32.s8", ["%r3", "%r1"], ["%r3"]),
        ins(8, "max.s32", ["%r4", "%r3", "%r2"], ["%r4"]),
    ]
    ids = {
        "%rd1": 1,
        "%rd2": 2,
        "%rd3": 3,
        "%rd4": 4,
        "%rs1": 5,
        "%rs2": 6,
        "%r2": 7,
        "%r3": 8,
        "%r4": 9,
    }
    st = mg.Stretch(code, ids, {"%r1": "x", "%rd9": "b"})
    rows = st.entries(0, 9)
    assert [(i, v) for i, v, _ in rows] == [
        (1, ".bits 64 (mulWide .s x 4)"),
        (2, ".bits 64 (add64 b (mulWide .s x 4))"),
        (3, ".bits 64 (sext x)"),
        (4, ".bits 64 (shl64 (sext x) 2)"),
        (5, ".bits 16 (i16 1)"),
        (6, ".bits 16 (xor16 (i16 1))"),
        (7, ".bits 32 (zext16 (xor16 (i16 1)))"),
        (8, "(cvts8 x)"),
        (9, ".bits 32 (max32 (cvts8w x) (zext16 (xor16 (i16 1))))"),
    ]


def test_guarded_write(mg):
    code = [
        dict(
            ins(0, "add.s32", ["%r2", "%r1", "1"], ["%r2"]),
            guard={"register": "%p1", "negated": True},
        )
    ]
    st = mg.Stretch(code, {"%r2": 2}, {"%r1": "x", "%p1": "c"}, {"%r2": "old"})
    rows = st.entries(0, 1)
    assert [(i, v) for i, v, _ in rows] == [(2, ".bits 32 (sel (!c) (addi x 1) old)")]
    st = mg.Stretch(code, {"%r2": 2}, {"%r1": "x", "%p1": "c"})
    with pytest.raises(mg.GenError, match="before the stretch"):
        st.entries(0, 1)
