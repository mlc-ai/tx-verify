# SPDX-License-Identifier: Apache-2.0
"""The registers the index warp (pcs 2332-2588) carries between its event sites.

Reads the PTX, numbers the instructions as `Core/Source/Decode.lean` does (labels and scopes
flattened), computes the live registers at each site by a backward pass over the region's
branches, and splits them into data (written from an index pair load or a shuffle, forward
closure) and the control registers the value statements need (parameters, lane words, loop
addresses). Output: one line per site. The design of `Proof/Index/Data/Machine.lean` is read
from this table.

    python3 Kernels/FlashMlaSparseDecodeH64/Gen/ix_data_live.py
"""

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "Tools"))

import parse_ptx  # noqa: E402

LO, HI = 2332, 2589
SITES = [
    2360,
    2365,
    2403,
    2429,
    2446,
    2464,
    2467,
    2471,
    2474,
    2476,
    2501,
    2517,
    2534,
    2553,
    2556,
    2560,
    2563,
    2565,
    2585,
]
WATCH = {
    "%rd22",
    "%rd23",
    "%rd24",
    "%rd25",
    "%rd1040",
    "%r2521",
    "%r2513",
    "%r32",
    "%r33",
    "%r38",
    "%r39",
    "%r40",
    "%r44",
    "%r48",
    "%r51",
    "%r2510",
    "%r2511",
}
REG = re.compile(r"%[a-z]+\d+|\bP1\b")


def operand(o) -> str:
    if o.children:
        inner = ",".join(operand(c) for c in o.children)
        return "{" + inner + "}" if o.kind == "vector" else f"{o.text}[{inner}]"
    return o.text


def listing():
    prog = parse_ptx.parse(
        (ROOT / "Kernels/FlashMlaSparseDecodeH64/v41_h64_no_split_plain.ptx").read_text()
    )
    flat = []

    def walk(body):
        for s in body:
            if s.kind in ("instruction", "label"):
                flat.append(s)
            elif s.kind == "scope":
                walk(s.body)

    walk(prog.functions[0].body)
    ins, labels, pc, pending = {}, [], 0, []
    for s in flat:
        if s.kind == "label":
            pending.append(s.text.strip())
            continue
        for name in pending:
            labels.append((name, pc))
        pending = []
        if LO <= pc < HI:
            ins[pc] = (s.predicate, s.opcode, ", ".join(operand(o) for o in s.operands))
        pc += 1
    return ins, labels


def main():
    ins, labels = listing()

    def target(pc, name):
        cands = [p for (n, p) in labels if n == name]
        return min(cands, key=lambda p: abs(p - pc)) if cands else None

    info, succ = {}, {}
    for pc, (pred, op, args) in ins.items():
        rs = REG.findall(args)
        if op.startswith(("st.", "bra", "mbarrier.arrive", "barrier")):
            d, u = [], rs
        elif op.startswith("mbarrier.try_wait"):
            d, u = ["P1"], rs[1:]
        elif op.startswith("shfl"):
            d, u = rs[:2], rs[2:]
        elif op.startswith("ld.") and "{" in args:
            k = args.index("}")
            d, u = REG.findall(args[:k]), REG.findall(args[k:])
        else:
            d, u = rs[:1], rs[1:]
        if pred:
            u = u + [pred]
        info[pc] = (op, d, u, pred)
        nxt = []
        if op.startswith("bra"):
            t = target(pc, args.strip())
            nxt = ([t] if t is not None else []) + ([pc + 1] if pred else [])
        else:
            nxt = [pc + 1]
        succ[pc] = [q for q in nxt if q in ins]
    live = {pc: set() for pc in ins}
    changed = True
    while changed:
        changed = False
        for pc in sorted(ins, reverse=True):
            op, d, u, pred = info[pc]
            out = set().union(*(live[q] for q in succ[pc])) if succ[pc] else set()
            new = (out - (set() if pred and not op.startswith("bra") else set(d))) | set(u)
            if new != live[pc]:
                live[pc], changed = new, True
    data, changed = set(), True
    while changed:
        changed = False
        for pc in sorted(ins):
            op, d, u, _ = info[pc]
            src = op.startswith(("ld.global.nc.v2", "shfl"))
            if src or (set(u) & data and not op.startswith(("st.", "bra"))):
                for r in d:
                    if r not in data and r != "P1":
                        data.add(r)
                        changed = True

    def key(r):
        return (r[:3], int(re.sub(r"\D", "", r)))

    for s in SITES:
        lv = live[s] | set(info[s][2])
        print(
            s,
            info[s][0][:20].ljust(20),
            "data:",
            " ".join(sorted(lv & data, key=key)),
            "| ctl:",
            " ".join(sorted(lv & WATCH, key=key)),
        )


if __name__ == "__main__":
    main()
