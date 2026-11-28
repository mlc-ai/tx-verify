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


def test_at_theorems_are_separate(og, decl):
    base = dict(start=4399, end=4404, cut=2, outputs=[])
    plain = og.render(with_run(decl, **base))
    sep = og.render(with_run(decl, at=True, **base))
    assert "expo_at0" not in plain
    for j in range(3):
        assert f"theorem expo_at{j} (L : Launch) (g : Nat) :" in sep
        assert f"({'expo_at' + str(j)} L g)" in sep
    # the piece proof is the same term, only named
    assert plain.count("codeB_of") == sep.count("codeB_of")


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


def test_unpack32_runs(og):
    # Inkling's `mov.b32 {lo, hi}, a`: the run is a `YItem` run, the other items wrapped in `.x`
    rules = {"core": "{lemma} {pc} {cls} {checks}", "unpack32": "U {pc}", "fn": "F"}
    d = ink_run(start=1303, end=1305, rules=rules, yunpack=True)
    text = " ".join(og.render(d).split())
    assert "List YItem := [ .unpack 32 397 398 1947, .x (.fn ink_op1304" not in text
    assert ".unpack 32" in text and "SegD.outs_litY" in text and "yCond" in text
    assert "public import Lemmas.Flow.OutUnpack" in text


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


# ---- typed mode (Tools/typed_gen.py) ---------------------------------------------------------


@pytest.fixture(scope="module")
def tg():
    sys.path.insert(0, str(TOOLS))
    return importlib.import_module("typed_gen")


def ins(opcode, ops, writes=(), reads=(), pc=0, guard=None, event=False, target=None):
    return {
        "pc": pc,
        "opcode": opcode,
        "operands": list(ops),
        "guard": guard,
        "event": event,
        "target": target,
        "table": None,
        "writes": list(writes),
        "reads": list(reads),
    }


def test_tag_lattice(tg):
    b32, b16, nz, p = ("bits", 32), ("bits", 16), ("nz", 32), ("pred",)
    d32, d64 = ("dat32",), ("dat64",)
    # a bit pattern of 32 bits serves a datum, a nonzero one a pattern; never the other way
    assert tg.sat(b32, d32) and tg.sat(nz, b32) and not tg.sat(b32, nz)
    assert tg.sat(("bits", 64), d64) and not tg.sat(b32, d64) and not tg.sat(d32, b32)
    assert tg.sat(p, p) and not tg.sat(p, b32) and not tg.sat(None, p)
    assert tg.meet(b32, d32) == d32 and tg.meet(nz, b32) == b32 and tg.meet(b32, b16) is None
    assert tg.meet(d32, d32) == d32 and tg.meet(None, p) is None
    assert tg.lean_tag(nz) == ".old (.nz 32)" and tg.lean_tag(d64) == ".dat64"
    assert tg.lean_tag(p) == ".old .pred"


def test_typed_transfer_float_family(tg):
    an = tg.Analysis([], {f"%r{i}": i for i in range(9)}, [])
    env = {"%r1": ("bits", 32), "%r2": ("dat32",), "%r3": ("dat64",), "%r4": ("bits", 16)}
    lo = an.local(env, ins("mov.b32", ["{%r5,%r6}", "%r1"], pc=1))
    assert lo == [("%r5", ("bits", 16)), ("%r6", ("bits", 16))]
    assert an.local(env, ins("mov.b64", ["{%r5,%r6}", "%r3"])) == [
        ("%r5", ("dat32",)),
        ("%r6", ("dat32",)),
    ]
    assert an.local(env, ins("mov.b64", ["%r7", "{%r1,%r2}"])) == [("%r7", ("dat64",))]
    assert an.local(env, ins("mov.b32", ["%r7", "{%r4,%r4}"])) == [("%r7", ("bits", 32))]
    assert an.local(env, ins("cvt.f32.bf16", ["%r8", "%r4"])) == [("%r8", ("dat32",))]
    assert an.local(env, ins("cvt.f32.bf16", ["%r8", "%r1"])) is None
    assert an.local(env, ins("max.f32", ["%r7", "%r1", "%r2"])) == [("%r7", ("dat32",))]
    assert an.local(env, ins("fma.rn.f32x2", ["%r7", "%r3", "%r3", "%r3"])) == [("%r7", ("dat64",))]
    assert an.local(env, ins("fma.rn.f32x2", ["%r7", "%r3", "%r3", "%r1"])) is None
    assert an.local(env, ins("max.f32", ["%r7", "%r1", "%r3"])) is None


def test_typed_cut_window(tg):
    code = [
        ins("mov.b32", ["%r1", "0"], pc=0),
        ins("mov.b32", ["%r2", "0"], pc=1),
        ins("bra", ["L"], pc=2, guard={"register": "%p1", "negated": False}, target=9),
        ins("mov.b32", ["%r3", "0"], pc=3),
        ins("shfl.sync.bfly.b32", ["%r4", "%r3"], pc=4, event=True),
    ]
    w = {"name": "w", "start": 0, "end": 4, "branches": {"2": False}}
    assert tg.cut_window(code, w) == [("run", 0, 2), ("bra", 2, False, 9, "%p1"), ("run", 3, 4)]
    assert tg.window_cuts(tg.cut_window(code, w), w) == [0, 2, 3, 4]
    taken = {"name": "w", "start": 0, "end": 3, "branches": {"2": True}}
    with pytest.raises(tg.TypedError, match="overshoots|not a local"):
        tg.cut_window(code, taken)
    with pytest.raises(tg.TypedError, match="not a local instruction"):
        tg.cut_window(code, {"name": "w", "start": 0, "end": 5, "branches": {"2": False}})


def test_typed_lean_list_width(tg):
    lines = tg.lean_list([f"({i}, .old (.bits 32))" for i in range(40)], 4)
    assert all(len(ln) <= 100 for ln in lines) and lines[0].startswith("[")
    assert lines[-1].endswith("]") and tg.lean_list([], 4) == ["[]"]


def test_typed_softmax_window_renders(og):
    decl = json.loads((ROOT / "Kernels/InklingRelDecode/Gen/Out/typed_softmax.json").read_text())
    text = og.render(decl)
    # one theorem per run, one for the window, two branch hypotheses
    for name in ("sm1_run_1299", "sm1_run_1303", "sm1_run_1467"):
        assert f"theorem {name} " in text
    assert "theorem sm1 " in text and "hB1" in text and "hB2" in text
    assert "SegQF.bra false" in text
    assert all(len(ln) <= 100 for ln in text.splitlines())


def test_typed_single_cut(tg):
    code = [
        ins("mov.b32", ["%r1", "0"], pc=0),
        ins("mul.f32", ["%r2", "%r1", "0f3F800000"], pc=1, writes=["%r2"], reads=["%r1"]),
        ins("cvt.rn.bf16x2.f32", ["%r3", "%r2", "%r2"], pc=2, writes=["%r3"], reads=["%r2"]),
        ins("mul.rn.f32", ["%r4", "%r1", "%r2"], pc=3, writes=["%r4"]),
        ins("mov.b32", ["%r5", "0"], pc=4),
    ]
    w = {"name": "w", "start": 0, "end": 5, "branches": {}}
    assert tg.cut_window(code, w) == [
        ("run", 0, 1),
        ("single", 1, 2, "%r2", ("dat32",)),
        ("single", 2, 3, "%r3", ("dat32",)),
        ("run", 3, 5),
    ]
    assert tg.window_cuts(tg.cut_window(code, w), w) == [0, 1, 2, 3, 5]
    assert tg.single_need(code[1]) == "dat32" and tg.single_need(code[2]) == "none"
    assert tg.single_need(code[3]) is False  # a rounding modifier: the exact rule applies


def test_typed_single_window_renders(og):
    decl = json.loads((ROOT / "Kernels/InklingRelDecode/Gen/Out/typed_softmax.json").read_text())
    t = decl["typed"]
    t["family"], t["namespace"] = 3, "PTX.Kernels.InklingRelDecode.Gen.TypedT"
    t["results"] = [{"from": 1913, "step": 11, "count": 16, "offset": 10, "tag": "dat32"}]
    t["windows"] = [{"name": "t2", "start": 2199, "end": 2207, "branches": {}}]
    text = og.render(decl)
    assert "t2_singles : List Nat := [2201, 2202, 2203, 2204, 2205, 2206]" in text
    assert "segQ_single" in text and "hS : ∀ pc ∈ t2_singles" in text
    assert "SegQ.tauAll R" in text and "segQF3_runW" in text
    assert all(len(ln) <= 100 for ln in text.splitlines())
    t["windows"] = [{"name": "t2", "start": 2199, "end": 2205, "branches": {}}]
    t["results"] = []
    with pytest.raises(og.GenError, match="is no dat64"):
        og.render(decl)


def test_typed_const_move_and_unordered_setp(og):
    decl = json.loads((ROOT / "Kernels/InklingRelDecode/Gen/Out/typed_softmax.json").read_text())
    t = decl["typed"]
    t["family"], t["namespace"] = 4, "PTX.Kernels.InklingRelDecode.Gen.TypedT"
    # mov.b32 of a 0f constant, then setp.equ.f32 (pc 2568) of a register it tags
    t["windows"] = [{"name": "t1", "start": 944, "end": 947, "branches": {}}]
    text = og.render(decl)
    assert "segQF4_runW" in text and "TypedMovImmG" in text and "FloatPlain3 A L g 944" in text
    t["windows"] = [{"name": "t2", "start": 2567, "end": 2570, "branches": {}}]
    assert "t2_run_2567" in og.render(decl)


def test_typed_run_takes_code_lemmas(og):
    decl = json.loads((ROOT / "Kernels/InklingRelDecode/Gen/Out/typed_softmax.json").read_text())
    t = decl["typed"]
    t["family"], t["namespace"] = 4, "PTX.Kernels.InklingRelDecode.Gen.TypedT"
    t["windows"] = [{"name": "t1", "start": 944, "end": 947, "branches": {}}]
    text = og.render(decl)
    assert "checkW_ops" in text and "takeCode PTX.Kernels.InklingRelDecode.Flow.code_944" in text
    assert "drop" not in text and "SegQFCode" in text


def test_typed_auto_windows_and_demand(og, tg):
    decl = json.loads((ROOT / "Kernels/InklingRelDecode/Gen/Out/typed_softmax.json").read_text())
    t = decl["typed"]
    t["family"], t["namespace"] = 4, "PTX.Kernels.InklingRelDecode.Gen.TypedT"
    t["windows"] = []
    t["auto"] = {"prefix": "z", "from": 574, "to": 600}
    text = og.render(decl)
    assert "theorem z5" in text
    t["auto"]["part"] = [0, 3]
    assert "theorem z5" in og.render(decl)
    assert [len(p) for p in tg.auto_parts([{"start": 0, "end": 2}] * 3, 3)] == [1, 1, 1]


def test_typed_exact_flips_and_dispatch(tg):
    code = [
        {"writes": ["%a"], "reads": [], "pc": 0},
        {"writes": ["%b"], "reads": ["%a"], "pc": 1},
        {"writes": ["%c"], "reads": [], "pc": 2},
    ]
    ids = {"%a": 1, "%b": 2, "%c": 3}
    live = [set(), set(), set(), {"%b", "%c"}]
    assert tg.exact_flips(code, ids, live, 0, 3, {2}) == [2]
    tree = tg.dispatch_tree([(0, "a"), (5, "b"), (9, "c")], 0)
    assert tree[0] == "if pc < 5 then" and "c pc" in tree[-1]
