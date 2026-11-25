# SPDX-License-Identifier: Apache-2.0
"""Tables and generated Lean files of the Producer phase of the reference layer.

The Producer phase (instructions 1403 to 2105) is the tile loop of the load leader (thread 128
of a thread block): per tile a poll, an arrival and 70 tensor loads. The compiler laid the loop
out as three copies of the tile body (called A, B and C here: the two halves of the loop
unrolled by two, and the remainder for an odd number of tiles). The 70 loads of a copy differ
only in constants, so the reference invariant states them through tables and the per-site
lemmas are generated.

This script reads the frozen PTX (through `analysis.load`). It

* builds the table of the 210 tensor-load sites: for the load at position `i < 70` of copy
  `c < 3`, the site ordinal, the instruction index, the registers of its operands (shared
  destination, tensor map, coordinates, completion mbarrier, cache policy), the parameter
  object of its tensor map and the destination offset in the stage's input buffer; it checks
  that the three copies have the same structure;
* writes the table to `Gen/Tables/ref_producer.json` and the generated Lean files of
  `Proof/Ref/Producer/` (`Tables.lean`, and `Steps<X>.lean` and `Loads<X>.lean` for each copy
  `X` of the tile body);
* with `--check` writes nothing. It fails if one of these eight files is stale. Then it runs
  the control-flow simulator (`simulate.py`) for thread 128 on several launches and compares
  every event of the phase with the closed forms the invariant states (the polled and the
  completed mbarrier, the parity, the byte count, the destination and the coordinates of every
  load, the tail polls);
* with `--print` also prints the table.

Nothing here is trusted: Lean checks the generated files against the generated thread machine.

    python3 Kernels/FlashKdaFwd/Gen/ref_producer.py            # write the table and the Lean files
    python3 Kernels/FlashKdaFwd/Gen/ref_producer.py --check    # write nothing; fail if a file is
                                                               # stale or the simulator disagrees
"""

import argparse
import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import analysis  # noqa: E402
import outputs  # noqa: E402
import simulate  # noqa: E402

KERNEL = Path(__file__).resolve().parents[1]
OUT = KERNEL / "Proof" / "Ref" / "Producer"
TABLE = KERNEL / "Gen" / "Tables" / "ref_producer.json"

FIRST = 16  # ordinal of the first tensor-load site of the phase among the tensor-copy sites
POLL_PC = [1443, 1650, 1869]
ARRIVE_PC = [1451, 1658, 1877]
TAIL_PC = [2081, 2092, 2103]

# The 70 loads of a tile, in order: (first position, count, parameter object, rank, name).
FAMILIES = [
    (0, 16, 0, 3, "v"),
    (16, 1, 1, 1, "beta"),
    (17, 16, 2, 3, "k_decayed"),
    (33, 16, 3, 3, "q_decayed"),
    (49, 16, 4, 3, "k_restored"),
    (65, 1, 5, 2, "g_total"),
    (66, 2, 6, 3, "INV"),
    (68, 2, 7, 3, "Mqk"),
]


def family(i):
    for first, count, obj, rank, name in FAMILIES:
        if first <= i < first + count:
            return first, count, obj, rank, name
    raise ValueError(i)


def dst_off(i):
    """Offset of the destination of the load at position `i` in the input buffer of its
    stage (which starts at byte `32768 + 18048 * stage` of the shared window)."""
    first, _, _, _, name = family(i)
    base = {"v": 0, "beta": 4096, "k_decayed": 4224, "q_decayed": 8320, "k_restored": 12416,
            "g_total": 16512, "INV": 17024, "Mqk": 17536}[name]  # fmt: skip
    return base + 256 * (i - first)


def load_bytes(i):
    return {"beta": 64, "g_total": 512}.get(family(i)[4], 256)


def first_coord(i):
    """The first coordinate of the load at position `i`, when it is a constant (`None` for
    `beta`, whose coordinate depends on the tile)."""
    first, _, _, _, name = family(i)
    if name == "beta":
        return None
    if name == "g_total":
        return 0
    return 8 * (i - first)


def build():
    code, ids, _ = analysis.load()
    copies = [ins for ins in code if ins["opcode"].startswith("cp.async.bulk.tensor")]
    sites = copies[FIRST : FIRST + 210]
    assert sites[0]["pc"] == 1470 and sites[-1]["pc"] == 2067, "the phase's tensor loads moved"
    maps = {}  # register of a generic parameter-object address -> parameter index
    owner = {}
    for ins in code:
        if ins["opcode"] == "mov.b64" and ins["operands"][1].startswith("PARAM"):
            owner[ins["operands"][0]] = int(ins["operands"][1][5:])
        if ins["opcode"].startswith("cvta.param"):
            maps[ins["operands"][0]] = owner[ins["operands"][1]]
    rows = []
    for k, ins in enumerate(sites):
        c, i = divmod(k, 70)
        first, _, obj, rank, name = family(i)
        m = re.fullmatch(
            r"cp\.async\.bulk\.tensor\.(\d)d\.shared::cluster\.global\.mbarrier::complete_tx"
            r"::bytes\.L2::cache_hint",
            ins["opcode"],
        )
        assert m and int(m.group(1)) == rank, (ins["pc"], ins["opcode"])
        dst, tmap, mbar, policy = ins["operands"]
        dst_r = dst.strip("[]")
        mm = re.fullmatch(r"\[(%rd\d+),\{([^}]*)\}\]", tmap)
        map_r, coords = mm.group(1), [x.strip() for x in mm.group(2).split(",")]
        assert maps[map_r] == obj and len(coords) == rank, (ins["pc"], map_r, coords)
        rows.append({
            "site": FIRST + k, "pc": ins["pc"], "copy": c, "position": i, "array": name,
            "object": obj, "rank": rank, "bytes": load_bytes(i), "dstOffset": dst_off(i),
            "dst": dst_r, "map": map_r, "coords": coords, "mbar": mbar.strip("[]"),
            "policy": policy,
            "ids": {r: ids[r] for r in [dst_r, map_r, mbar.strip("[]"), policy] + coords},
        })  # fmt: skip
    # The three copies have one structure: the same body-level register in the same role.
    body = []
    for c in range(3):
        rs = rows[70 * c : 70 * c + 70]
        token, head = rs[0]["coords"][1], rs[0]["coords"][2]
        zero, slot = rs[17]["coords"][1], rs[17]["coords"][2]
        mbar, policy = rs[0]["mbar"], rs[0]["policy"]
        consts = [rs[17 + k]["coords"][0] for k in range(1, 16)]
        for r in rs:
            i = r["position"]
            first, _, _, rank, name = family(i)
            assert r["mbar"] == mbar and r["policy"] == policy
            want = {
                "v": [zero if i == 0 else r["coords"][0], token, head],
                "beta": [r["coords"][0]],
                "g_total": [zero, slot],
            }.get(name, [zero if i == first else consts[i - first - 1], zero, slot])
            assert r["coords"] == want, (r["pc"], r["coords"], want)
        body.append({"token": token, "head": head, "zero": zero, "slot": slot, "mbar": mbar,
                     "policy": policy, "consts": consts,
                     "ids": {r: ids[r] for r in [token, head, zero, slot, mbar, policy] + consts}})  # fmt: skip
    return code, ids, rows, body


# -- the closed forms, tested against the simulator -------------------------------------------


def par(t):
    """The parity of the load leader's poll for tile `t` (also for the tail, `t >= tiles`)."""
    return (t // 3 + 1) % 2


def expected(lengths, heads, seq, head):
    """The events of thread 128 from instruction 1403 to 2105, as the invariant states them."""
    cu = [sum(lengths[:i]) for i in range(len(lengths) + 1)]
    total, tiles = cu[-1], simulate.tiles(lengths[seq])
    total_tiles = sum(simulate.tiles(n) for n in lengths)
    first_tile = sum(simulate.tiles(n) for n in lengths[:seq])
    shared, out = simulate.SHARED, []
    for t in range(tiles):
        c = 2 if t == tiles - 1 and tiles % 2 == 1 else t % 2
        s = t % 3
        out.append((POLL_PC[c], "poll", shared + 98328 + 8 * s, par(t)))
        out.append((ARRIVE_PC[c], "arrive", shared + 98304 + 8 * s, 17984))
        token, slot = cu[seq] + 16 * t, head * total_tiles + first_tile + t
        for i in range(70):
            first, _, obj, _, name = family(i)
            c0 = first_coord(i)
            coords = {
                "v": [c0, token, head],
                "beta": [(total * head + token) // 8 * 8],
                "g_total": [0, slot],
            }.get(name, [c0, 0, slot])
            dst = shared + 32768 + 18048 * s + dst_off(i)
            out.append((None, "load", c, i, dst, simulate.OBJECT + 4096 * obj, coords,
                        shared + 98304 + 8 * s))  # fmt: skip
    for j in range(3):
        t = tiles + j
        out.append((TAIL_PC[j], "poll", shared + 98328 + 8 * (t % 3), par(t)))
    return out


def check(rows):
    code, _, _ = analysis.load()
    launches = [
        ([0], 1), ([1], 1), ([16], 1), ([17], 1), ([32], 1), ([33], 2), ([48], 1), ([49], 1),
        ([64], 3), ([100], 2), ([112], 1), ([5, 37, 0, 100], 3), ([37, 5], 2), ([3, 160], 2),
    ]  # fmt: skip
    by_pc = {r["pc"]: r for r in rows}
    runs = 0
    for lengths, heads in launches:
        for seq in range(len(lengths)):
            for head in sorted({0, heads - 1}):
                for fail in (0, 1):
                    th = simulate.Thread(code, 128, seq, head, lengths, heads, fail)
                    th.run()
                    got = []
                    for e in th.events:
                        if not 1403 <= e["pc"] <= 2105:
                            continue
                        if e["op"].startswith("mbarrier.try_wait"):
                            if e["ok"]:
                                got.append((e["pc"], "poll", e["mbar"], e["parity"]))
                        elif e["op"].startswith("mbarrier.arrive"):
                            got.append((e["pc"], "arrive", e["mbar"], e["tx"]))
                        else:
                            r, o = by_pc[e["pc"]], e["operands"]
                            got.append((None, "load", r["copy"], r["position"], o[r["dst"]],
                                        o[r["map"]], [o[x] for x in r["coords"]], o[r["mbar"]]))  # fmt: skip
                    want = expected(lengths, heads, seq, head)
                    assert got == want, (lengths, heads, seq, head, fail,
                                         next((a, b) for a, b in zip(got, want) if a != b))  # fmt: skip
                    bars = [e["pc"] for e in th.events if e["op"] == "bar.sync"]
                    assert bars.index(3113) == 6 and bars[5] == 1402
                    runs += 1
        # The other lanes of the load warp make no event in the phase.
        th = simulate.Thread(code, 137, 0, 0, lengths, heads, 0)
        th.run()
        assert not [e for e in th.events if 1403 <= e["pc"] <= 2105]
    print(f"check: {runs} runs of thread 128 agree with the closed forms")


# -- the generated Lean files -------------------------------------------------------------------

HEADER = """-- SPDX-License-Identifier: Apache-2.0
-- Generated by Kernels/FlashKdaFwd/Gen/ref_producer.py; do not edit.
module

{imports}

@[expose] public section

{doc}

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Producer
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Recurrence

noncomputable section
"""

FOOTER = """
end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Producer
"""


def wrap(items, indent, width=100):
    """A comma-separated list, wrapped."""
    lines, cur = [], " " * indent
    for k, it in enumerate(items):
        piece = it + ("," if k + 1 < len(items) else "")
        if len(cur) + len(piece) + 1 > width and cur.strip():
            lines.append(cur.rstrip())
            cur = " " * indent
        cur += piece + " "
    lines.append(cur.rstrip())
    return "\n".join(lines)


def table(name, doc, values):
    return (f"/-- {doc} -/\ndef {name} (k : Nat) : Nat :=\n  [\n"
            + wrap([str(v) for v in values], 4) + "\n  ].getD k 0\n")  # fmt: skip


def emit_tables(rows, body):
    doc = """/-! # Tables of the 210 tensor-load sites of the Producer phase

The tile loop of the load leader is compiled as three copies of the tile body (copy 0 and
copy 1 are the two halves of the loop unrolled by two, copy 2 is the remainder for an odd number
of tiles). Each copy issues the same 70 tensor loads, at *positions* 0 to 69: 16 loads of the
values `v`, one of the gate logits `beta`, 16 each of the workspace arrays `k_decayed`,
`q_decayed` and `k_restored`, one of `g_total`, two of `INV` and two of `Mqk`. The copies differ
in the registers that hold the operands. A table indexed by a position has 70 entries; a table
indexed by a site has 210 entries, at index `70 * copy + position`.

`Consts c i d` says which of the fifteen registers of the constants 8, 16, ..., 120 (the
first coordinate of the loads of a 16-row array, written by `mov` before the loads of
`k_decayed` and read again by the later arrays) hold their constant at position `i` of
copy `c`. -/"""
    out = HEADER.format(
        imports="public import Kernels.FlashKdaFwd.Proof.Ref.Producer.Interface", doc=doc
    )
    out += "\n" + table("dstAbs", "The offset in the block's shared memory, for stage 0, of the "
                        "destination of the load at\nposition `k` (stage `s` adds `18048 * s`).",
                        [32768 + r["dstOffset"] for r in rows[:70]])  # fmt: skip
    out += "\n" + table("c0Tab", "The first coordinate of the load at position `k` (the feature "
                        "or column index of its\n8-element box; for `beta`, position 16, the "
                        "coordinate depends on the tile and the entry is 0).",
                        [first_coord(i) or 0 for i in range(70)])  # fmt: skip
    out += "\n" + table("mapOf", "The parameter object (0 to 7) that holds the tensor map of the "
                        "load at position `k`.", [r["object"] for r in rows[:70]])  # fmt: skip
    out += "\n" + table("loadSize", "The bytes the load at position `k` moves.",
                        [r["bytes"] for r in rows[:70]])  # fmt: skip
    out += "\n" + table("dstReg", "The register that holds the shared destination address of the "
                        "load at site `k`.", [r["ids"][r["dst"]] for r in rows])  # fmt: skip
    out += "\n" + table("c0Reg", "The register that holds the first coordinate of the load at "
                        "site `k`.", [r["ids"][r["coords"][0]] for r in rows])  # fmt: skip
    out += "\n" + table("loadPc", "The instruction index of the load at site `k`.",
                        [r["pc"] for r in rows])  # fmt: skip
    out += ("\n/-- **The registers of the constants** at position `i` of copy `c`: the register "
            "of the constant\n`8 k` (`k` from 1 to 15) is written before position `17 + k` and "
            "holds it from there on. -/\n"
            "def Consts (c : Fin 3) (i : Nat) (d : D) : Prop :=\n  match c.val with\n")  # fmt: skip
    for c in range(3):
        regs = [body[c]["ids"][r] for r in body[c]["consts"]]
        conj = [f"({17 + k} ≤ i → d.w {r} = W {8 * k})" for k, r in enumerate(regs, start=1)]
        text, cur = [], "    "
        for k, cj in enumerate(conj):
            piece = cj + (" ∧" if k + 1 < len(conj) else "")
            if len(cur) + len(piece) + 1 > 100:
                text.append(cur.rstrip())
                cur = "      "
            cur += piece + " "
        text.append(cur.rstrip())
        out += f"  | {'_' if c == 2 else c} =>\n" + "\n".join(text) + "\n"
    return out + FOOTER


STEP_OPTIONS = """set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option maxRecDepth 4000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
  {w : Nat → BitVec 64} {p : Nat → Bool} {x : Nat → Value}
"""


def emit_steps(rows, c):
    """The steps of the loads at the positions 0 to 68 of copy `c`."""
    letter = "ABC"[c]
    doc = f"""/-! # The Producer invariant is kept by the tensor loads of copy {c} of the tile body

One lemma per tensor load that is followed by another load of the same body (positions 0 to
68; the last load of a body is in `Steps.lean`): from the invariant at position `i`, the state
the generated transition function gives is at position `i + 1`. The transition writes the
destination register and the first-coordinate register of the next load (and, before the loads
of `k_decayed`, the register of the next constant). Every proof is `load_step`
(`Steps.lean`); the step to the load of `beta` (position 16) also uses the closed form of its
coordinate (`beta_word`). The ledger of the step is `led_load` (`Ledger.lean`). -/"""
    out = HEADER.format(
        imports="public import Kernels.FlashKdaFwd.Proof.Ref.Producer.Steps", doc=doc
    )
    out += STEP_OPTIONS
    tile = "u + 1" if c == 1 else "u"
    for r in rows[70 * c : 70 * c + 69]:
        n, i = r["site"], r["position"]
        out += f"""
theorem st_load_{n} (hpre : Pre P L mem0) (hg : g < L.threads) {{u : Nat}}
    (h : RefAt P g (.load {c} u {i}) ⟨.tensorCopy {n}, w, p, x⟩) :
    RefAt P g (.load {c} u {i + 1}) (after_tensorCopy_{n} L g ⟨.tensorCopy {n}, w, p, x⟩) := by
"""
        if i + 1 == 16:
            out += f"""  obtain ⟨-, h⟩ := h
  have hs := shared_lt hpre
  load_facts
  have eb := beta_word hpre hg (t := {tile}) (by omega)
  refine ⟨rfl, ?_⟩
  prod_pos [after_tensorCopy_{n}, h, eb]
  prod_close
"""
        else:
            out += f"  load_step [after_tensorCopy_{n}]\n"
    return f"Steps{letter}.lean", out + FOOTER


def emit_loads(rows, c):
    """The event of each load site of copy `c`, and the case analysis over its 70 positions."""
    letter = "ABC"[c]
    doc = f"""/-! # The tensor loads of copy {c} of the tile body: events and steps

For each of the 70 load sites of the copy, `ev_load_<site>` reads the operand registers of the
`cp.async.bulk.tensor` instruction off the concrete state (`reg_w`, `reg_g`: the registers are
live at the site and have the kinds the instruction needs), rewrites them with the closed forms
of the invariant and concludes the event in closed form by `ev_tile` (`Shapes.lean`).
`good_load{letter}` is the case analysis over the 70 positions: the event, the machine's
successor (`next_tensorCopy_<site>`), the step lemma of the site and the ledger. -/"""
    out = HEADER.format(
        imports="public import Kernels.FlashKdaFwd.Proof.Ref.Producer.Glue\n"
        f"public import Kernels.FlashKdaFwd.Proof.Ref.Producer.Steps{letter}",
        doc=doc,
    )
    out += STEP_OPTIONS.replace(
        "{x : Nat → Value}", "{x : Nat → Value}\n  {t : TState} {ins : Instr} {e : Event} "
        "{o : Option TState}")  # fmt: skip
    tile = "u + 1" if c == 1 else "u"
    for r in rows[70 * c : 70 * c + 70]:
        n, i, ids = r["site"], r["position"], r["ids"]
        cs = [ids[x] for x in r["coords"]]
        names = " ".join(f"r{k}" for k in range(len(cs)))
        chain = "".join(f"(.cons r{k} " for k in range(len(cs))) + ".nil" + ")" * len(cs)
        out += f"""
theorem ev_load_{n} (hpre : Pre P L mem0) (hg : g < L.threads) {{u : Nat}}
    (h : RefAt P g (.load {c} u {i}) ⟨.tensorCopy {n}, w, p, x⟩)
    (hat : (code L g).AtD ⟨.tensorCopy {n}, w, p, x⟩ t)
    (hc : kernel.code[(Site.tensorCopy {n}).pc]? = some ins)
    (hf : Fires (Site.tensorCopy {n}).pc (eventTmpl Assumptions.all L g t ins.op) e o) :
    Ev P L g (.load {c} u {i}) e := by
  obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
  obtain ⟨-, h⟩ := h
  load_facts
  have rd := reg_w hat (r := {ids[r["dst"]]}) (by lit_mem) (n := 32) rfl
  have rm := reg_g hat (r := {ids[r["map"]]}) (by lit_mem) (i := {r["object"]}) rfl
  have rb := reg_w hat (r := {ids[r["mbar"]]}) (by lit_mem) (n := 32) rfl
  have rp := reg_w hat (r := {ids[r["policy"]]}) (by lit_mem) (n := 64) rfl
"""
        for k, reg in enumerate(cs):
            out += f"  have r{k} := reg_w hat (r := {reg}) (by lit_mem) (n := 32) rfl\n"
        out += f"""  simp only [h] at rd rb {names}
  exact ev_tile hpre hg (i := {i}) (by decide) (tt := {tile}) (by omega) (rs := {cs}) hf
    rm rd rb rp {chain}
"""
    out += f"""
set_option maxRecDepth 8000 in
/-- **Every load position of copy {c} is good for the event fired at it.** -/
theorem good_load{letter} (hpre : Pre P L mem0) (hg : g < L.threads) (u : Nat) (i : Fin 70)
    (h : RefAt P g (.load {c} u i) ⟨(Pos.load {c} u i).site, w, p, x⟩)
    (hat : (code L g).AtD ⟨(Pos.load {c} u i).site, w, p, x⟩ t)
    (hc : kernel.code[(Pos.load {c} u i).site.pc]? = some ins)
    (hf : Fires (Pos.load {c} u i).site.pc (eventTmpl Assumptions.all L g t ins.op) e o) :
    Good P L g (.load {c} u i) w p x e := by
  fin_cases i
"""
    for r in rows[70 * c : 70 * c + 70]:
        n, i = r["site"], r["position"]
        if i < 69:
            out += (f"  · exact good_issue hpre (by decide) (ev_load_{n} hpre hg h hat hc hf)\n"
                    f"      (next_tensorCopy_{n} w p x e) (st_load_{n} hpre hg h)\n")  # fmt: skip
        else:
            out += (f"  · have hev := ev_load_{n} hpre hg h hat hc hf\n"
                    f"    exact good_plain hev (next_tensorCopy_{n} w p x e) (st_last{c} hpre h)\n"
                    f"      (ledEv_issue hpre hev)\n")  # fmt: skip
    return f"Loads{letter}.lean", out + FOOTER


def emit(rows, body):
    files = {"Tables.lean": emit_tables(rows, body)}
    for c in range(3):
        for name, text in (emit_steps(rows, c), emit_loads(rows, c)):
            files[name] = text
    return files


def main():
    cli = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    cli.add_argument(
        "--check",
        action="store_true",
        help="write nothing; fail if a file is stale or the simulator disagrees",
    )
    cli.add_argument("--print", action="store_true", help="print the table")
    args = cli.parse_args()
    _, ids, rows, body = build()
    if args.print:
        for r in rows:
            print(r["site"], r["pc"], r["copy"], r["position"], r["array"], r["dst"], r["map"],
                  r["coords"], r["mbar"], r["dstOffset"])  # fmt: skip
        for b in body:
            print(b)
    files = {TABLE: json.dumps({"loads": rows, "copies": body}, indent=1) + "\n"}
    files.update({OUT / name: text for name, text in emit(rows, body).items()})
    outputs.write_or_check(files, args.check)
    if args.check:
        check(rows)


if __name__ == "__main__":
    main()
