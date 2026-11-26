# SPDX-License-Identifier: Apache-2.0
"""Tools/out_gen.py: straight-line runs as pieces with stated values, and their freshness."""

import copy
import importlib
import json
import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
TOOLS = ROOT / "Tools"
DECLS = sorted((ROOT / "Tests" / "Gen" / "Out").glob("*.json")) + sorted(
    ROOT.glob("Kernels/*/Gen/Out/*.json")
)
EXPO = ROOT / "Tests" / "Gen" / "Out" / "expo.json"


@pytest.fixture(scope="module")
def og():
    sys.path.insert(0, str(TOOLS))
    return importlib.import_module("out_gen")


@pytest.fixture
def decl():
    return json.loads(EXPO.read_text())


@pytest.mark.parametrize("path", DECLS, ids=lambda p: str(p.relative_to(ROOT)))
def test_generated_runs_are_fresh(path):
    r = subprocess.run(
        [sys.executable, str(TOOLS / "out_gen.py"), str(path), "--check"],
        capture_output=True,
        text=True,
    )
    assert r.returncode == 0, r.stdout + r.stderr


def with_run(decl, **kw):
    d = copy.deepcopy(decl)
    d["runs"][0].update(kw)
    return d


def test_pieces_and_values(og, decl):
    text = og.render(with_run(decl, start=4399, end=4404, cut=2, outputs=[]))
    # three pieces of 2, 2 and 1 items, composed into one run of 5
    assert "theorem expo_piece2 " in text and "theorem expo_piece3 " not in text
    assert "L g 5 4399 (expo_facts0 V) 4404" in " ".join(text.split())
    # the product's value is the term the code computes from the start values
    assert "def expo_v4399 (V : Nat → Value) : Value :=\n  okVal (.bits 32 0) (mulE false" in text
    # the packed fma reads the defs of the moves before it
    assert "(fma2E (expo_v4401 V) (expo_v4402 V) (expo_v4400 V))" in text


def test_live_facts(og, decl):
    text = og.render(with_run(decl, start=4399, end=4401, cut=32, outputs=[]))
    facts0 = text.split("def expo_facts0")[1].split("]")[0]
    # the product's operands are live at the start; its result is not (written in the run)
    assert facts0.count("V 3685") == 1 and facts0.count("V 1230") == 1
    assert "3686" not in facts0


def test_event_stops(og, decl):
    with pytest.raises(og.GenError, match="not an unguarded local instruction"):
        og.render(with_run(decl, end=4827))


def test_undeclared_reading(og, decl):
    with pytest.raises(og.GenError, match="has no item"):
        og.render(with_run(decl, fn={}))


def test_missing_rule(og, decl):
    rules = dict(decl["runs"][0]["rules"])
    del rules["ex2"]
    with pytest.raises(og.GenError, match="no rule declared for the item kind ex2"):
        og.render(with_run(decl, rules=rules))


def test_max_items(og):
    decl = json.loads((ROOT / "Tests" / "Gen" / "Out" / "max.json").read_text())
    d = copy.deepcopy(decl)
    d["runs"][0].update(start=5662, end=5666, outputs=[])
    text = " ".join(og.render(d).split())
    # three- and two-source `max.f32` are `fn` items with the library's outcome `maxE`
    assert ".fn (maxOp 4558 [4546, 4556, 4557]) 4558 [4546, 4556, 4557] maxE" in text
    assert ".fn (maxOp 4559 [4549, 4552]) 4559 [4549, 4552] maxE" in text
    assert "rule_max3 5663 rfl" in text and "rule_max2 5664 rfl" in text


def test_options(og, decl):
    d = with_run(decl, start=4399, end=4401, cut=32, outputs=[])
    d["options"] = {"maxRecDepth": 100000}
    assert "noncomputable section\nset_option maxRecDepth 100000\n" in og.render(d)
    assert "set_option maxRecDepth" not in og.render(with_run(decl, start=4399, end=4401))


INKLING = {
    "ptx": "Kernels/InklingRelDecode/rel_verify_sm100a.ptx",
    "namespace": "PTX.Tests.Gen.Ink",
    "output": "unused.lean",
    "kernel": "K",
    "code": "C",
    "assumptions": "A",
    "decoded": "Kernels/InklingRelDecode/Data/Decoded.lean",
}


def ink_run(**kw):
    run = {"name": "r", "cut": 32, "outputs": [], "segfree": "S {pc}", "rules": {}}
    run.update(kw)
    return {**INKLING, "runs": [run]}


def test_core_forms(og):
    # Inkling's softmax: integer compare, subtract, select and bf16 widening are Core forms
    rules = {
        "core": "{lemma} {pc} {cls} {checks}",
        "pack": "P",
        "fma2": "F",
        "mov": "M",
        "selp": "SL",
        "max2": "X",
        "max3": "X",
    }
    text = " ".join(og.render(ink_run(start=1564, end=1566, rules=rules)).split())
    assert "def r_op1564 : Op := PTX.Op.int { op := PTX.IntOp.setp (PTX.Cmp.gt) none" in text
    assert ".fn r_op1564 98 [1138] (coreF r_op1564 [1138])" in text
    assert "PTX.Flow.XItem.core_setp 1564 Int rfl" in text
    # the decoded term is defined once and shared by the item and its value
    assert text.count("PTX.Op.int {") == text.count("def r_op") == 2


def test_scoped_registers_and_immediates(og):
    # the software exponent of Inkling: block-scoped registers, `0f` operands through `fn`
    fn = {
        op: {"op": "R.op {d} {srcs} [{o1}, {o2}]", "f": "R.f [{o2}]", "rule": "R.rule {pc}"}
        for op in ("max.ftz.f32", "add.rm.ftz.f32", "sub.rn.ftz.f32")
    }
    rules = {"core": "{lemma} {pc} {cls} {checks}", "mov": "M"}
    text = " ".join(og.render(ink_run(start=1913, end=1916, fn=fn, rules=rules)).split())
    assert ".fn (R.op 2512 [1312] [(.reg 1312), (.f32imm 3271426048)])" in text
    assert "R.rule 1913" in text


def test_selp_literal(og):
    rules = {"core": "{lemma} {pc} {cls} {checks}", "selp": "SL {pc}"}
    text = " ".join(og.render(ink_run(start=1629, end=1630, rules=rules)).split())
    assert ".base (.selp 1142 (.reg 1141) (.f32imm 4286578688) 160)" in text
    assert "opndVal V (.f32imm 4286578688)" in text


def test_header_wrap(og):
    assert og.header("Kernels/K/k.ptx") == [
        "-- Generated by Tools/out_gen.py from Kernels/K/k.ptx; do not edit."
    ]
    long = "Kernels/FlashMlaSparseDecodeH64/v41_h64_no_split_plain.ptx"
    lines = og.header(long)
    assert len(lines) == 2 and all(len(x) <= 100 for x in lines) and long in lines[1]


def test_fn_by_pc(og):
    # a reading at one pc of an opcode takes precedence over the opcode's
    fn = {
        "setp.gt.s32": {"op": "R.a {d} {srcs}", "f": "R.fa", "rule": "RA {pc}"},
        "setp.gt.s32@1565": {"op": "R.b {d} {srcs}", "f": "R.fb", "rule": "RB {pc}"},
    }
    text = " ".join(og.render(ink_run(start=1564, end=1566, fn=fn, rules={})).split())
    assert "RA 1564" in text and "RB 1565" in text


@pytest.mark.skipif(
    not (ROOT / "Tests/Gen/Out/prmt.json").exists(), reason="the FlashMLA tree is not in this tree"
)
def test_prmt_default_mode(og):
    # FlashMLA's scale unpack `prmt.b32 d, a, 0, 0x7772U` decodes to `prmt none`: a Core form
    d = json.loads((ROOT / "Tests" / "Gen" / "Out" / "prmt.json").read_text())
    d["runs"][0].update(start=2696, end=2697, outputs=[], rules={"core": "{lemma} {pc} {checks}"})
    text = " ".join(og.render(d).split())
    assert "op := PTX.IntOp.prmt none" in text
    assert "PTX.Flow.XItem.core_prmt 2696 rfl" in text


FAMILY_DECL = "Kernels/FlashMlaSparseDecodeH64/Gen/Out/dequant_runs1.json"
needs_family_decl = pytest.mark.skipif(
    not (ROOT / FAMILY_DECL).exists(), reason="the FlashMLA declarations are not in this tree"
)


def family(tmp_path, template, **inst):
    t = tmp_path / "t.tmpl"
    t.write_text(template)
    i = {"decl": FAMILY_DECL, "run": "dr2730"}
    i.update(inst)
    return {
        "ptx": "Kernels/FlashMlaSparseDecodeH64/v41_h64_no_split_plain.ptx",
        "namespace": "N",
        "output": "X.lean",
        "template": str(t),
        "instances": [i],
    }


RAW = "-- shape: " + " ".join(["cvt.u16.u64", "shr.u64"] * 3 + ["cvt.u16.u64"]) + "\n"


@needs_family_decl
def test_family_instances(og, tmp_path):
    # one copy of the template per instance, with its names and register ids
    tmpl = RAW + "theorem ${name} : ${v6} = ${v6} ∧ ${s0_0} = ${d1} + 0 ∧ ${out0} < ${in0} := rfl\n"
    d = family(tmp_path, tmpl, prefix="Gen.", params={"name": "raw00"})
    text = og.render(d)
    assert "-- Template: " in text
    assert "theorem raw00 : Gen.dr2730_v2736 = Gen.dr2730_v2736 ∧ 3837 = 3838 + 0" in text
    # the facts' registers in ascending order: the first halfword at the end, the word at the start
    assert "∧ 192 < 3837 :=" in text


@needs_family_decl
def test_family_errors(og, tmp_path):
    with pytest.raises(og.GenError, match="shape"):
        og.render(family(tmp_path, "-- shape: mov.b32\n", params={"name": "x"}))
    with pytest.raises(og.GenError, match="no value"):
        og.render(family(tmp_path, RAW + "${nope}\n"))
    with pytest.raises(og.GenError, match="first line"):
        og.render(family(tmp_path, "theorem x : True := trivial\n"))
