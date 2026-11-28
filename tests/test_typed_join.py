# SPDX-License-Identifier: Apache-2.0
"""The typed analysis at a join: the tag is served by every predecessor (`tagsSatF`), and the result
of an mbarrier wait is a predicate."""

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "Tools"))
import flow_gen  # noqa: E402
import parse_ptx  # noqa: E402
import typed_gen  # noqa: E402


def _sat(have, need):
    return typed_gen.sat(have, need)


def test_join_tags_are_served_by_every_predecessor():
    decl = json.loads((ROOT / "Kernels/InklingRelDecode/Gen/Out/typed_late_02.json").read_text())[
        "typed"
    ]
    program = parse_ptx.parse((ROOT / decl["ptx"]).read_text())
    function = next(f for f in program.functions if not f.declaration)
    code = flow_gen.flatten(function)
    ids = flow_gen.register_ids(function)
    typed_gen.HALF["on"] = True
    an = typed_gen.Analysis(code, ids, decl.get("events", []), decl.get("results", []))
    env = an.run()
    preds = {}
    for ins in code:
        for q in flow_gen.all_successors(ins, len(code)):
            preds.setdefault(q, []).append(ins["pc"])
    for q, ps in preds.items():
        if len(ps) < 2 or env[q] is None:
            continue
        for p in ps:
            if env[p] is None:
                continue
            out = an.step(env[p], code[p])
            for r, t in env[q].items():
                assert _sat(out.get(r), t), (q, p, r)
    wait = next(i for i, c in enumerate(code) if c["opcode"].startswith("mbarrier.try_wait"))
    assert env[wait + 1][code[wait]["writes"][0]] == ("pred",)


# The tags of the events' results in the lane's pcs (the softmax 574..2331, the epilogue
# 2560..2853), each with the fact of the lane that justifies it (a Core rule gives none of the
# data tags: a load or a shuffle returns the stored or sent value whole).
EVENT_TAGS = {
    "ld.global.b16": (None, "bias_half: a bf16 number, untagged (the half chain)"),
    "mbarrier.try_wait": (("pred",), "the wait writes `.pred ok` (Core)"),
    "shfl.sync.idx.b32": (("bits", 32), "LWf.idx at the pcs 1261 and 2603"),
    "tcgen05.ld": (("dat32",), "LateValues.tcLd and LWf.tc"),
    "shfl.sync.bfly.b32": (("dat32",), "LateValues.bfly"),
    "ld.shared.b32": (("dat32",), "the assembly's word at 2252 (hDat)"),
}
IDX_PCS = {1261, 2603}


def test_event_result_tags_in_the_lane():
    decl = json.loads((ROOT / "Kernels/InklingRelDecode/Gen/Out/typed_late_02.json").read_text())[
        "typed"
    ]
    program = parse_ptx.parse((ROOT / decl["ptx"]).read_text())
    function = next(f for f in program.functions if not f.declaration)
    code = flow_gen.flatten(function)
    ids = flow_gen.register_ids(function)
    typed_gen.HALF["on"] = True
    an = typed_gen.Analysis(code, ids, decl.get("events", []), decl.get("results", []))
    env = an.run()
    for pc in [*range(574, 2331), *range(2560, 2853)]:
        ins = code[pc]
        if not (ins["event"] and ins["writes"]) or env[pc] is None:
            continue
        op = ins["opcode"]
        key = next((k for k in EVENT_TAGS if op.startswith(k)), None)
        assert key is not None, (pc, op)
        if key == "shfl.sync.idx.b32":
            assert pc in IDX_PCS, pc
        for _, tag in an.event(env[pc], ins):
            assert tag == EVENT_TAGS[key][0], (pc, op, tag)
