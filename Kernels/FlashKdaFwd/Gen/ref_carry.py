# SPDX-License-Identifier: Apache-2.0
"""Tables and generated Lean files of the CarryLoad phase of the reference layer.

The CarryLoad phase (instructions 622 to 1402) is the stretch between the conversion loop and
the tile loops. A compute thread (index below 128 in its thread block) executes 128 generic
`ld.b32` there (instructions 765, 770, ..., 1400), each through a pointer that the four
instructions before it compute from the thread's base pointer `%rd4`:

    add.s64 %rdA, %rd4, K      the base pointer moved by a constant of the instruction
    shr.u64 %rdB, %rdA, 3      the swizzle: bit 4 of the address is flipped when bit 7 is set
    and.b64 %rdC, %rdB, 16
    xor.b64 %rdD, %rdC, %rdA
    ld.b32  %rN, [%rdD]        the load of one FP32 entry of the state into a carry register

Every thread then executes `fence.proxy.async.shared::cta` (1401) and `bar.sync 0` (1402). The
128 loads differ only in constants, so the reference invariant states them through tables and
the per-site lemmas are generated.

This script reads the frozen PTX (through `analysis.load`), the register table
`Gen/Tables/matrix_table.json` (written by `matrix_table.py`) and the value layer's
`Proof/Values/Ends/Gen/Tables.lean` (written by `values_ends.py`). It

* builds the table of the 128 loads: for load `j`, the instruction index (`765 + 5 j`), the
  ordinal of its site among the load sites (`31 + j`), the constant `K`, the id of the pointer
  register it reads through, the id of the carry register it writes and the name of the data
  run that follows it in the generated thread machine (`r<pc + 1>`, none after the last load);
  it checks the five-instruction pattern, and the constants and carry registers against
  `matrix_table.json` (key `carries`) and against the value layer's table (`carryTable`);
* writes the table to `Gen/Tables/ref_carry.json` and the generated Lean files of
  `Proof/Ref/CarryLoad/` (`Tables.lean`: the constants; `Sites.lean`: per load the machine's
  successor and the event, then the same statements for the family);
* with `--check` writes nothing. It fails if one of these three files is stale. Then it runs
  the control-flow simulator (`simulate.py`) for all 192 thread indices, on several launches
  and on shared bases with both values of bit 7, and compares the events between the second
  `bar.sync 0` of the conversion (621) and the tile loops with the closed forms the invariant
  states: a compute thread makes the 128 loads in order, load `j` of four bytes at the
  swizzled address of `base + K j` with
  `base = shared + 1024 warp + 64 (lane % 4) + 4 (lane / 4)`, then the fence, then the barrier;
  a thread of the other two warps makes the fence and the barrier only; five `bar.sync 0`
  precede the barrier at 1402; every load address is a multiple of four inside the FP32 state
  buffer (window offsets 32768 to 98304).

Nothing here is trusted: Lean checks the generated files against the generated thread machine.

    python3 Kernels/FlashKdaFwd/Gen/ref_carry.py            # write the table and the Lean files
    python3 Kernels/FlashKdaFwd/Gen/ref_carry.py --check    # write nothing; fail if a file is
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
OUT = KERNEL / "Proof" / "Ref" / "CarryLoad"
TABLE = KERNEL / "Gen" / "Tables" / "ref_carry.json"
MATRIX = KERNEL / "Gen" / "Tables" / "matrix_table.json"
VALUES = KERNEL / "Proof" / "Values" / "Ends" / "Gen" / "Tables.lean"

LOADS = 128  # carry loads of a compute thread
FIRST_PC = 765  # instruction of the first carry load
FIRST_SITE = 31  # ordinal of its site among the `load` sites of the thread machine
FENCE_PC, BAR_PC = 1401, 1402
BASE_REG = "%rd4"  # the base pointer of the carry loads
BASE_ID = 2250  # its register id in the thread machine (checked in `build`)
WIDTH = 100


def swz(a):
    """The kernel's swizzle of a shared address: bit 4 is flipped when bit 7 is set."""
    return a ^ ((a >> 3) & 16)


def carry_base(shared, tid):
    """The base pointer `%rd4` of the carry loads of the thread with index `tid`."""
    warp, lane = tid // 32, tid % 32
    return shared + 1024 * warp + 64 * (lane % 4) + 4 * (lane // 4)


def build():
    """The table of the 128 carry loads, read off the program."""
    code, ids, _ = analysis.load()
    base_id = ids[BASE_REG]
    assert base_id == BASE_ID, base_id
    rows = []
    for j in range(LOADS):
        pc = FIRST_PC + 5 * j
        add, shr, land, xor, ld = (code[pc - 4 + i] for i in range(5))
        # the five-instruction pattern
        assert add["opcode"] == "add.s64" and add["operands"][1] == BASE_REG, (j, add)
        k = int(add["operands"][2])
        moved = add["operands"][0]
        assert shr["opcode"] == "shr.u64" and shr["operands"][1:] == [moved, "3"], (j, shr)
        assert land["opcode"] == "and.b64" and land["operands"][1:] == [shr["operands"][0], "16"]
        assert xor["opcode"] == "xor.b64" and xor["operands"][1:] == [land["operands"][0], moved]
        ptr = xor["operands"][0]
        assert ld["opcode"] == "ld.b32" and ld["operands"][1] == f"[{ptr}]" and ld["event"]
        dst = ld["operands"][0]
        # no other event between two loads, and the pointer registers are fresh
        assert not any(code[pc - 4 + i]["event"] for i in range(4)), j
        rows.append(
            {
                "j": j,
                "pc": pc,
                "site": FIRST_SITE + j,
                "const": k,
                "ptr": ids[ptr],
                "ptr_name": ptr,
                "dst": ids[dst],
                "dst_name": dst,
                "run": f"r{pc + 1}" if j + 1 < LOADS else None,
            }
        )
    assert code[FENCE_PC]["opcode"] == "fence.proxy.async.shared::cta"
    assert code[BAR_PC]["opcode"] == "bar.sync" and code[BAR_PC]["operands"] == ["0"]
    # closed forms of the register ids
    for r in rows:
        j = r["j"]
        assert r["ptr"] == 2362 + 4 * j, r
        assert r["dst"] == (2213 - j if j < 96 else 2118 + j), r
        assert r["const"] % 32 == 0 and 32768 <= r["const"] <= 95008, r
    assert len({r["dst"] for r in rows}) == LOADS and len({r["ptr"] for r in rows}) == LOADS
    # against the table of the tile loop (the entry each carry register holds)
    carries = json.loads(MATRIX.read_text())["carries"]
    by_pc = {c["load_pc"]: c for c in carries.values()}
    assert len(by_pc) == LOADS
    for r in rows:
        c = by_pc[r["pc"]]
        assert c["id"] == r["dst"] and 32768 + c["buffer_offset"] == r["const"], (r, c)
    # against the value layer's copy
    if VALUES.exists():
        text = VALUES.read_text()
        body = text[text.index("def carryTable") :]
        body = body[: body.index("]") + 1]
        tuples = re.findall(r"\((\d+), \d+, \d+, \d+, \d+, (\d+)\)", body)
        assert len(tuples) == LOADS, len(tuples)
        for r, (reg, k) in zip(rows, tuples, strict=True):
            assert int(reg) == r["dst"] and int(k) == r["const"], (r, reg, k)
    return {"base": base_id, "rows": rows}


# -- the simulator check --------------------------------------------------------------------


def check(table):
    """Compare the closed forms with the simulator; returns the number of thread runs."""
    code, _, _ = analysis.load()
    rows = table["rows"]
    runs = 0
    launches = [([37, 0, 5], 2, 0, 1), ([0, 1, 16, 17], 1, 3, 0), ([16], 1, 0, 0)]
    saved = simulate.SHARED
    try:
        for shared in (0, 128, 4096, 4224, 163712, 163840):
            simulate.SHARED = shared
            for lengths, heads, seq, head in launches:
                # the stretch does not depend on the launch: all threads on the first launch,
                # a sample of every warp on the others
                full = lengths == launches[0][0]
                tids = (
                    range(192) if full else (0, 1, 5, 31, 37, 63, 64, 95, 127, 128, 159, 160, 191)
                )
                for tid in tids:
                    th = simulate.Thread(code, tid, seq, head, lengths, heads)
                    th.run()
                    runs += 1
                    ev = th.events
                    pcs = [e["pc"] for e in ev]
                    i621 = pcs.index(621)
                    i1402 = pcs.index(BAR_PC)
                    assert pcs.count(BAR_PC) == 1 and pcs.count(621) == 1
                    mid = ev[i621 + 1 : i1402 + 1]
                    bars = sum(1 for e in ev[:i1402] if e["op"] == "bar.sync" and e["id"] == 0)
                    assert bars == 5, (tid, bars)
                    assert all(e["op"] != "bar.sync" or e["id"] == 0 for e in ev[:i1402])
                    if tid < 128:
                        assert len(mid) == LOADS + 2, (tid, len(mid))
                        base = carry_base(shared, tid)
                        for r, e in zip(rows, mid, strict=False):
                            assert e["pc"] == r["pc"] and e["op"] == "ld.b32", (tid, r, e)
                            addr = swz(base + r["const"])
                            assert e["addr"] == addr, (shared, tid, r, e, addr)
                            assert addr % 4 == 0 and shared + 32768 <= addr, (tid, r)
                            assert addr + 4 <= shared + 98304, (tid, r)
                    else:
                        assert len(mid) == 2, (tid, len(mid))
                    assert mid[-2]["pc"] == FENCE_PC and mid[-2]["op"].startswith("fence.proxy")
                    assert mid[-1]["pc"] == BAR_PC and mid[-1]["id"] == 0
                    assert mid[-1]["count"] is None
                    # the event after the barrier is at a later instruction
                    assert ev[i1402 + 1]["pc"] > BAR_PC, (tid, ev[i1402 + 1])
    finally:
        simulate.SHARED = saved
    return runs


# -- the generated Lean files ----------------------------------------------------------------

NS = "PTX.Kernels.FlashKdaFwd.Proof.Ref.CarryLoad"
HEAD = """-- SPDX-License-Identifier: Apache-2.0
-- Generated by Kernels/FlashKdaFwd/Gen/ref_carry.py; do not edit.
module
"""


def wrap(items, indent, width=WIDTH):
    """Comma-separated items as lines of at most `width` characters."""
    lines, cur = [], " " * indent
    for i, it in enumerate(items):
        piece = it + ("," if i + 1 < len(items) else "")
        if len(cur) + len(piece) + 1 > width and cur.strip():
            lines.append(cur.rstrip())
            cur = " " * indent
        cur += piece + " "
    lines.append(cur.rstrip())
    return "\n".join(lines)


def tables_lean(table):
    rows = table["rows"]
    consts = wrap([str(r["const"]) for r in rows], 3)
    return f"""{HEAD}
@[expose] public section

/-! # The constants of the 128 carry loads

Generated from the frozen PTX: carry load `j` (instruction `765 + 5 j`) reads through the
pointer `swizzle (%rd4 + kTab[j])`, where `%rd4` is the base pointer of the thread's carry
loads. The constant is 32768 (the offset of the FP32 state buffer in the block's shared window)
plus four times an element offset; in the order of the loads it is
`32768 + 8192 (j / 16) + 512 (j / 8 % 2) + 256 (j / 4 % 2) + 4096 (j % 4 / 2) + 32 (j % 2)`
(`kOf_eq`). The table agrees with `Gen/Tables/matrix_table.json` (key `carries`:
`buffer_offset + 32768` of the register loaded at that instruction) and with the value layer's
`Values.Ends.Gen.carryTable`; the generator checks both. -/

namespace {NS}

/-- **The constants of the carry loads**, in the order of the loads: what the instruction
`add.s64` before load `j` adds to the base pointer `%rd4`. -/
def kTab : List Nat :=
  [{consts.strip()}]

/-- The constant of carry load `j` (0 for `j ≥ 128`). -/
def kOf (j : Nat) : Nat := kTab.getD j 0

/-- The constants in closed form: the order of the loads enumerates, from the slowest index to
the fastest, the key block, the value block, the half and the accumulator register of the
entry. -/
theorem kOf_eq : ∀ j < 128, kOf j =
    32768 + 8192 * (j / 16) + 512 * (j / 8 % 2) + 256 * (j / 4 % 2) + 4096 * (j % 4 / 2) +
      32 * (j % 2) := by
  decide +kernel

end {NS}
"""


OPEN = f"""namespace {NS}
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Recurrence
open PTX.Kernels.FlashKdaFwd.Proof.Ref.Conversion

noncomputable section
set_option linter.unusedVariables false

variable {{P : Params}} {{L : Launch}} {{mem0 : Mem0}} {{g : Nat}}
  {{w : Nat → BitVec 64}} {{p : Nat → Bool}} {{x : Nat → Value}}
  {{t : TState}} {{ins : Instr}} {{e : Event}} {{o : Option TState}} {{a q : Nat}}
"""
CLOSE = f"""
end

end {NS}
"""


def site_lemmas(r, nxt):
    """The two lemmas of carry load `r`: the machine's successor and the event."""
    j, pc, site, dst, ptr = r["j"], r["pc"], r["site"], r["dst"], r["ptr"]
    ins = f"`ld.b32 {r['dst_name']}, [{r['ptr_name']}]`"
    out = [f"/-- Carry load {j} (instruction {pc}, {ins}): the successor. -/"]
    if nxt is None:
        out += [
            f"theorem nx_{j} (e : Event) :",
            f"    Thread.next L g ⟨.load {site}, w, p, x⟩ e = ldNext0 e fun v =>",
            f"      ⟨.fenceProxy 1, w, p, valueEx x [({dst}, v)]⟩ :=",
            f"  ldNext_last (Thread.next_load_{site} w p x e)",
        ]
    else:
        k, ptr2, run = nxt["const"], nxt["ptr"], r["run"]
        out += [
            f"theorem nx_{j} (hx : x {BASE_ID} = sptr g a) (ha : a + {k} < 2 ^ 32) (e : Event) :",
            f"    Thread.next L g ⟨.load {site}, w, p, x⟩ e = ldNext0 e fun v =>",
            f"      ⟨.load {site + 1}, w, p,",
            f"        valueEx (valueEx x [({dst}, v)]) [({ptr2}, sptr g (swzN (a + {k})))]⟩ :=",
            "  ldNext_run",
            f"    (c := fun v => Run.{run}_cond (valueOf ⟨.load {site}, w, p, valueEx x [({dst}, v)]⟩))",
            f"    (f := after_load_{site} L g ⟨.load {site}, w, p, x⟩) (Thread.next_load_{site} w p x e)",
            f"    fun _ => run_at {k} (fun h1 h2 => {run}_ptr h1 h2) (by decide) hx ha",
        ]
    out += [
        "",
        f"/-- Carry load {j}: the event is the read of four bytes at the pointer's address. -/",
        f"theorem ev_{j} (hpre : Pre P L mem0) (hg : g < L.threads)",
        f"    (hat : (code L g).AtD ⟨.load {site}, w, p, x⟩ t) (hc : kernel.code[{pc}]? = some ins)",
        f"    (hf : Fires {pc} (eventTmpl Assumptions.all L g t ins.op) e o)",
        f"    (hx : x {ptr} = sptr g q) (h1 : q < 2 ^ 32) (h2 : q % 4 = 0) :",
        f"    ∃ bs, bs.length = 4 ∧ e = ⟨{pc}, .rd {{ loc := ⟨.shared, cta g, q⟩, size := 4 }} bs⟩ := by",
        "  obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))",
        f"  exact ev_gld hpre hg (d := {dst}) hf",
        f"    ((reg_x hat (r := {ptr}) (by lit_mem) rfl).trans (congrArg some hx)) h1 h2 hat.2.1",
        "",
    ]
    return out


def sites_lean(table):
    rows = table["rows"]
    body = []
    for r in rows:
        nxt = rows[r["j"] + 1] if r["j"] + 1 < LOADS else None
        body += site_lemmas(r, nxt)
    nx = "\n".join(f"  · exact nx_{j} hx ha e" for j in range(LOADS - 1))
    ev = "\n".join(f"  · exact ev_{j} hpre hg hat hc hf hx h1 h2" for j in range(LOADS))
    doc = """/-! # The 128 carry loads: the machine's successor and the event, per site and as a family

Generated from the frozen PTX. Two lemmas per load `j` (instruction `765 + 5 j`, site
`load_(31 + j)`):

* `nx_j`: the successor of the thread machine across the load's event, in the form
  `ldNext0 e f` ("the event is a read whose four bytes have a value `v`, the next state is
  `f v`"). The transition of the load writes `v` into the carry register and runs the pointer
  code of the next load; the lemma evaluates that run on the base pointer `sptr g a` in the
  slot of `%rd4` (`Lib.lean: run_at` with the run's lemma `r<pc>_ptr` of `Thread/RunPtr.lean`),
  so its hypothesis is "`a` plus the next load's constant is inside the window" and the next
  state has the pointer to the swizzled address in the next pointer slot. The slot file `x`
  stays a variable: no data register is unfolded.
* `ev_j`: the event fired at the site, from the pointer `sptr g q` in the load's pointer slot:
  a read of the four bytes at `q` in the window of the thread's own block
  (`Conversion.ev_gld`).

Then the same statements once for load `j`, with the site, the registers and the constant as
functions of `j` (`ldSite`, `dstReg`, `ptrReg`, `kOf`): `next_ld`, `next_last`, `ev_ld`. Their
proofs are case analyses over `j` that apply the lemma of the site; that the functions take the
values of the program at each `j` is checked there, by evaluation. -/
"""
    family = f"""/-! ### The loads as one family -/

/-- **The successor at carry load `j < 127`**: the event is a read whose four bytes have a
value `v`; the next state is at load `j + 1`, with `v` in the carry register of load `j` and
the pointer to the swizzled address of the base plus the constant of load `j + 1` in the
pointer slot of load `j + 1`. Hypotheses: the slot of `%rd4` holds the base pointer `sptr g a`,
and the address before the swizzle is inside the window. -/
theorem next_ld {{j : Nat}} (hj : j < 127) (hx : x {BASE_ID} = sptr g a)
    (ha : a + kOf (j + 1) < 2 ^ 32) (e : Event) :
    Thread.next L g ⟨ldSite j, w, p, x⟩ e = ldNext0 e fun v =>
      ⟨ldSite (j + 1), w, p, valueEx (valueEx x [(dstReg j, v)])
        [(ptrReg (j + 1), sptr g (swzN (a + kOf (j + 1))))]⟩ := by
  interval_cases j
{nx}

/-- **The successor at the last carry load**: the next state is at the proxy fence, with the
loaded value in the last carry register. -/
theorem next_last (e : Event) :
    Thread.next L g ⟨ldSite 127, w, p, x⟩ e = ldNext0 e fun v =>
      ⟨.fenceProxy 1, w, p, valueEx x [(dstReg 127, v)]⟩ :=
  nx_127 e

/-- **The event at carry load `j`**: with the pointer `sptr g q` in the load's pointer slot,
`q` a multiple of four inside the window, the event is the read of the four bytes at `q` of
the shared window of the thread's own block. It is never undefined behaviour. -/
theorem ev_ld (hpre : Pre P L mem0) (hg : g < L.threads) {{j : Nat}} (hj : j < 128)
    (hat : (code L g).AtD ⟨ldSite j, w, p, x⟩ t)
    (hc : kernel.code[(ldSite j).pc]? = some ins)
    (hf : Fires (ldSite j).pc (eventTmpl Assumptions.all L g t ins.op) e o)
    (hx : x (ptrReg j) = sptr g q) (h1 : q < 2 ^ 32) (h2 : q % 4 = 0) :
    ∃ bs, bs.length = 4 ∧
      e = ⟨(ldSite j).pc, .rd {{ loc := ⟨.shared, cta g, q⟩, size := 4 }} bs⟩ := by
  interval_cases j
{ev}
"""
    return (
        HEAD
        + f"""
public import Kernels.FlashKdaFwd.Proof.Ref.CarryLoad.Lib

@[expose] public section

{doc}
{OPEN}
/-! ### Per site -/

"""
        + "\n".join(body).rstrip()
        + "\n\n"
        + family
        + CLOSE
    )


def main():
    cli = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    cli.add_argument(
        "--check",
        action="store_true",
        help="write nothing; fail if a file is stale or the simulator disagrees",
    )
    args = cli.parse_args()
    table = build()
    rows = table["rows"]
    print(f"{len(rows)} carry loads, constants {rows[0]['const']} .. "
          f"{max(r['const'] for r in rows)}; base register id {table['base']}")  # fmt: skip
    lean = {"Tables.lean": tables_lean(table), "Sites.lean": sites_lean(table)}
    for name, text in lean.items():
        for line in text.splitlines():
            assert len(line) <= WIDTH, (name, line)
    files = {TABLE: json.dumps(table, indent=1) + "\n"}
    files.update({OUT / name: text for name, text in lean.items()})
    outputs.write_or_check(files, args.check)
    if args.check:
        print(f"simulator: {check(table)} thread runs agree with the closed forms")


if __name__ == "__main__":
    main()
