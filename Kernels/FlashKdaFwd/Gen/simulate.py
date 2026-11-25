# SPDX-License-Identifier: Apache-2.0
"""Run the control flow of one thread of the kernel on concrete launch numbers.

A checking aid for the proof layers above the thread machine, not a proof input. The integer
(control) instructions are executed on concrete numbers; every value that comes from data memory
or from a floating-point instruction is "unknown" and is only propagated. A branch on an unknown
value stops the run with an error (the kernel's control flow depends on no data). The result is
the thread's sequence of events (instruction index, opcode, the integer operands) and, on
request, the integer registers before each event. With it one can test, before proving it, a
closed form of a register, a count of events or a schedule. The script reads the frozen PTX
(through `analysis.load`) and writes no file. `ref_carry.py`, `ref_producer.py`,
`ref_compute.py`, `ref_store.py` and `ref_epilogue.py` use it as a library in their `--check`.

What is assumed about the events that return a value:
* `elect.sync` elects lane 0 (the assumption `electZero`);
* `shfl.sync.idx` with lane index 0 returns the executing lane's own operand (the kernel shuffles
  the warp index, which all lanes of a warp share);
* a load of the packed-offsets array returns its entry;
* an `mbarrier.try_wait` fails `--fail-polls` times at each visit of its loop and then succeeds;
* `mapa` returns the address unchanged (no clusters).

    python3 Kernels/FlashKdaFwd/Gen/simulate.py --lengths 37,5 --heads 2 --summary
    python3 Kernels/FlashKdaFwd/Gen/simulate.py --lengths 37,5 --seq 0 --tid 128 --events
    python3 Kernels/FlashKdaFwd/Gen/simulate.py --lengths 37 --tid 3 --registers 2144 --limit 2
"""

import argparse
import collections
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import analysis  # noqa: E402

# Launch numbers (any values that satisfy `Spec.Pre`'s ranges and alignments).
SHARED = 4096  # `Launch.sharedBase`: a multiple of 128, window below 2^18
OFFSETS = 0x7F00_0000_1000  # address of `cu_seqlens`
OUTPUT = 0x7F10_0000_0000  # address of the output array
OBJECT = 0x10_0000  # address of parameter object i is OBJECT + 4096 * i (never dereferenced)


class Stop(Exception):
    pass


def bits(op):
    kind = op.split(".")[-1]
    return {"pred": 1}.get(kind, int(kind[1:]) if kind[1:].isdigit() else 32)


def signed(v, w):
    return v - (1 << w) if v >> (w - 1) else v


def tiles(length):
    return (length + 15) // 16


class Thread:
    def __init__(self, code, tid, seq, head, lengths, heads, fail_polls=0):
        self.code, self.tid, self.seq, self.head = code, tid, seq, head
        self.lengths, self.heads, self.fail = lengths, heads, fail_polls
        self.cu = [sum(lengths[:i]) for i in range(len(lengths) + 1)]
        self.env = {}
        self.events = []
        self.polls = collections.Counter()
        self.sreg = {
            "%tid.x": tid, "%tid.y": 0, "%tid.z": 0,
            "%ntid.x": 192, "%ntid.y": 1, "%ntid.z": 1,
            "%ctaid.x": seq, "%ctaid.y": head, "%ctaid.z": 0,
            "%nctaid.x": len(lengths), "%nctaid.y": heads, "%nctaid.z": 1,
            "%cluster_ctarank": 0, "%cluster_ctaid.x": 0, "%cluster_ctaid.y": 0,
            "%cluster_ctaid.z": 0, "%cluster_nctaid.x": 1, "%cluster_nctaid.y": 1,
            "%cluster_nctaid.z": 1, "%cluster_nctarank": 1, "%is_explicit_cluster": 0,
        }  # fmt: skip
        total = self.cu[-1]
        self.params = {
            11: OUTPUT, 12: total, 13: heads, 14: len(lengths), 15: OFFSETS,
            16: sum(tiles(n) for n in lengths),
        }  # fmt: skip

    # -- operands -------------------------------------------------------------------------

    def value(self, o, names):
        o = o.strip()
        if re.fullmatch(r"-?\d+", o):
            return int(o)
        if re.fullmatch(r"0[fFdD][0-9A-Fa-f]+", o):
            return None
        if o in self.sreg:
            return self.sreg[o]
        if o == "shared_mem":
            return SHARED
        m = re.fullmatch(r"PARAM(\d+)", o)
        if m:
            return OBJECT + 4096 * int(m.group(1))
        return self.env.get(names.get(o, o))

    def address(self, o, names):
        """The integer address of a memory operand `[x]` or `[x+k]` (None when unknown)."""
        inner = o.strip()[1:-1]
        m = re.fullmatch(r"([^+,\[\]{}]+)(?:\+(-?\d+))?", inner)
        if not m:
            return None
        base = self.value(m.group(1), names)
        return None if base is None else base + int(m.group(2) or 0)

    # -- local instructions ---------------------------------------------------------------

    def local(self, ins, names):
        op, ops = ins["opcode"], ins["operands"]
        parts = op.split(".")
        base, w = parts[0], bits(op)
        mask = (1 << w) - 1
        vals = [self.value(o, names) for o in ops[1:]] if not ops[1:2] or "[" not in ops[1] else []

        def out(v):
            for wr in ins["writes"]:
                self.env[wr] = v

        if base == "ld" and parts[1] == "param":
            m = re.fullmatch(r"\[PARAM(\d+)\]", ops[1])
            if m:
                return out(self.params[int(m.group(1))] & mask)
            # A field of a by-value parameter object: the two element strides the kernel reads
            # are 1 (`Spec.Pre.scaleV`, `scaleOut`).
            return out(1)
        if base == "mapa":
            return out(vals[0])
        if base == "cvta":
            return out(vals[0])
        if any(v is None for v in vals) or not vals:
            return out(None)
        if base == "mov":
            return out(vals[0] & mask if w > 1 else int(vals[0] != 0))
        if base in ("add", "sub", "and", "or", "xor"):
            a, b = vals
            f = {"add": a + b, "sub": a - b, "and": a & b, "or": a | b, "xor": a ^ b}[base]
            return out(f & mask)
        if base == "not":
            return out((~vals[0]) & mask)
        if base == "neg":
            return out((-vals[0]) & mask)
        if base == "mul":
            if parts[1] == "wide":
                w2 = 2 * w
                a, b = vals
                if parts[2].startswith("s"):
                    a, b = signed(a & mask, w), signed(b & mask, w)
                else:
                    a, b = a & mask, b & mask
                return out((a * b) & ((1 << w2) - 1))
            return out((vals[0] * vals[1]) & mask)
        if base == "mad":
            return out((vals[0] * vals[1] + vals[2]) & mask)
        if base == "shl":
            return out((vals[0] << vals[1]) & mask if vals[1] < w else 0)
        if base == "shr":
            a = vals[0] & mask
            if parts[1].startswith("s"):
                return out((signed(a, w) >> min(vals[1], w - 1)) & mask)
            return out(a >> vals[1] if vals[1] < w else 0)
        if base in ("min", "max"):
            a, b = vals[0] & mask, vals[1] & mask
            if parts[1].startswith("s"):
                a, b = signed(a, w), signed(b, w)
            return out((min(a, b) if base == "min" else max(a, b)) & mask)
        if base == "selp":
            return out(vals[0] if vals[2] else vals[1])
        if base == "setp":
            cmp, ty = parts[1], parts[2]
            w = int(ty[1:])
            a, b = vals[0] & ((1 << w) - 1), vals[1] & ((1 << w) - 1)
            if ty.startswith("s"):
                a, b = signed(a, w), signed(b, w)
            table = {"lt": a < b, "gt": a > b, "le": a <= b, "ge": a >= b, "eq": a == b,
                     "ne": a != b}  # fmt: skip
            return out(int(table[cmp]))
        if base == "cvt":
            dst, src = parts[-2], parts[-1]
            if dst[0] not in "su" or src[0] not in "su":
                return out(None)
            ws, wd = int(src[1:]), int(dst[1:])
            a = vals[0] & ((1 << ws) - 1)
            if src.startswith("s"):
                a = signed(a, ws)
            return out(a & ((1 << wd) - 1))
        return out(None)

    # -- events ---------------------------------------------------------------------------

    def event(self, pc, ins, names):
        op, ops = ins["opcode"], ins["operands"]
        base = op.split(".")[0]
        rec = {"pc": pc, "op": op}
        if base == "elect":
            rx, px = ins["writes"]
            self.env[rx] = 0
            self.env[px] = int(self.tid % 32 == 0)
            rec["mask"] = self.value(ops[1], names)
        elif base == "shfl":
            dst, pred = ins["writes"]
            self.env[dst] = self.value(ops[1], names)
            self.env[pred] = 1
            rec["value"] = self.env[dst]
        elif op.startswith("mbarrier.try_wait"):
            self.polls[pc] += 1
            ok = int(self.polls[pc] > self.fail)
            if ok:
                self.polls[pc] = 0
            self.env[ins["writes"][0]] = ok
            rec.update(mbar=self.address(ops[1], names), parity=self.value(ops[2], names), ok=ok)
        elif op.startswith("mbarrier.init"):
            rec.update(mbar=self.address(ops[0], names), count=self.value(ops[1], names))
        elif op.startswith("mbarrier.arrive"):
            rec["mbar"] = self.address(ops[1], names)
            if "expect_tx" in op:
                rec["tx"] = self.value(ops[2], names)
        elif op == "ld.global.b64":
            addr = self.address(ops[1], names)
            index, rem = divmod(addr - OFFSETS, 8)
            if rem or not 0 <= index < len(self.cu):
                raise Stop(f"pc {pc}: load of the offsets array at entry {index} rem {rem}")
            self.env[ins["writes"][0]] = self.cu[index]
            rec["entry"] = index
        elif base in ("ld", "st"):
            which = ops[1] if base == "ld" else ops[0]
            rec["addr"] = self.address(which, names)
            for wr in ins["writes"]:
                self.env[wr] = None
        elif base in ("ldmatrix", "stmatrix"):
            which = ops[1] if base == "ldmatrix" else ops[0]
            rec["addr"] = self.address(which, names)
            for wr in ins["writes"]:
                self.env[wr] = None
        elif base == "bar":
            rec["id"] = self.value(ops[0], names)
            rec["count"] = self.value(ops[1], names) if len(ops) > 1 else None
        elif op.startswith("cp.async.bulk.tensor"):
            regs = [self.env.get(r) for r in ins["reads"]]
            rec["operands"] = dict(zip(ins["reads"], regs, strict=True))
        else:
            for wr in ins["writes"]:
                self.env[wr] = None
        return rec

    def run(self, limit=5_000_000, watch=None):
        pc, steps = 0, 0
        snapshots = []
        while True:
            steps += 1
            if steps > limit:
                raise Stop(f"more than {limit} instructions")
            ins = self.code[pc]
            op = ins["opcode"]
            names = {n.split("#")[-1]: n for n in ins["reads"] + ins["writes"]}
            take = True
            if ins["guard"] is not None:
                g = self.env.get(ins["guard"]["register"])
                if g is None:
                    raise Stop(f"pc {pc}: guard {ins['guard']['register']} is unknown")
                take = bool(g) != ins["guard"]["negated"]
            if op.split(".")[0] == "bra":
                pc = ins["target"] if take else pc + 1
                continue
            if not take:
                pc += 1
                continue
            if op == "ret":
                self.events.append({"pc": pc, "op": op})
                return snapshots
            if op in ("brkpt", "trap"):
                self.events.append({"pc": pc, "op": op})
                raise Stop(f"pc {pc}: breakpoint reached")
            if ins["event"]:
                if watch is not None and pc == watch:
                    snapshots.append({k: v for k, v in self.env.items() if v is not None})
                self.events.append(self.event(pc, ins, names))
            else:
                self.local(ins, names)
            pc += 1


def role(tid):
    return "compute" if tid < 128 else ("load" if tid < 160 else "store")


def kind(op):
    for prefix, name in [
        ("cp.async.bulk.tensor", None), ("mbarrier.try_wait", "poll"), ("mbarrier.init", "init"),
        ("mbarrier.arrive", "arrive"), ("fence.mbarrier_init", "fenceInit"),
        ("fence.proxy", "fenceProxy"), ("cp.async.bulk.commit", "commit"),
        ("cp.async.bulk.wait", "groupWait"), ("ld.global", "offsetLoad"),
    ]:  # fmt: skip
        if op.startswith(prefix):
            if name is None:
                return "tensorStore" if ".global.shared" in op else "tensorLoad"
            return name
    return op.split(".")[0]


def main():
    cli = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    cli.add_argument("--lengths", default="37,5", help="tokens of each sequence, e.g. 37,5")
    cli.add_argument("--heads", type=int, default=1)
    cli.add_argument("--seq", type=int, default=None, help="one sequence (default: all)")
    cli.add_argument("--head", type=int, default=0)
    cli.add_argument("--tid", type=int, default=None, help="one thread index (default: all)")
    cli.add_argument("--fail-polls", type=int, default=0)
    cli.add_argument("--summary", action="store_true", help="event counts per role")
    cli.add_argument("--events", action="store_true", help="print the event sequence")
    cli.add_argument("--registers", type=int, default=None, metavar="PC",
                     help="print the known registers before each event at this instruction")  # fmt: skip
    cli.add_argument("--limit", type=int, default=3, help="how many snapshots to print")
    args = cli.parse_args()
    lengths = [int(x) for x in args.lengths.split(",")]
    code, _, _ = analysis.load()
    seqs = range(len(lengths)) if args.seq is None else [args.seq]
    tids = range(192) if args.tid is None else [args.tid]
    failures = 0
    for seq in seqs:
        groups = collections.defaultdict(list)
        for tid in tids:
            thread = Thread(code, tid, seq, args.head, lengths, args.heads, args.fail_polls)
            try:
                snaps = thread.run(watch=args.registers)
            except Stop as stop:
                failures += 1
                print(f"seq {seq} tid {tid}: STOPPED: {stop}")
                snaps = []
            counts = collections.Counter(kind(e["op"]) for e in thread.events)
            lane0 = tid % 32 == 0
            groups[(role(tid), lane0, tuple(sorted(counts.items())))].append(tid)
            if args.events:
                for i, e in enumerate(thread.events):
                    rest = {k: v for k, v in e.items() if k not in ("pc", "op")}
                    print(f"{i:5d} pc {e['pc']:4d} {e['op'][:44]:44s} {rest}")
            for snap in snaps[: args.limit]:
                print(f"seq {seq} tid {tid} before pc {args.registers}:")
                print("  " + " ".join(f"{k}={v}" for k, v in sorted(snap.items())))
        if args.summary:
            print(f"== sequence {seq}: {lengths[seq]} tokens, {tiles(lengths[seq])} tiles")
            for (r, lane0, counts), members in sorted(groups.items()):
                span = f"{members[0]}..{members[-1]}" if len(members) > 1 else f"{members[0]}"
                who = f"{r}{' lane 0' if lane0 else ''} ({len(members)} threads: {span})"
                print(f"  {who}: " + ", ".join(f"{k} {n}" for k, n in counts))
    sys.exit(1 if failures else 0)


if __name__ == "__main__":
    main()
