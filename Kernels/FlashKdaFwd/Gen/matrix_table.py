# SPDX-License-Identifier: Apache-2.0
"""The register table of the tile loop: what every matrix instruction and data register means.

The tile loop of the compute threads is instructions 2135..2944 of the frozen PTX. This script
interprets one iteration of it symbolically for all 32 lanes of each of the four compute warps
and assigns a mathematical meaning to each of the 182 warp matrix instructions (`ldmatrix`,
`mma.sync`, `movmatrix`, `stmatrix`) and to every register that holds data, in the vocabulary
of `Math/Fragments.lean` (the real matrices `keyBlock`, `stateBlock`, `project`, `residual`,
`correction`, `output`, `update`, `nextState`) and of the fragment layouts of
`Lemmas/Matrix/Mma.lean` (`regA`, `regB`, `regC`: which entry lane `l` holds in register `r`).

How the meaning is found (nothing is assumed about the order of the code):

1. Control registers (addresses) are evaluated as 32-bit words for every thread index, input
   stage, output stage and gate offset; every memory address is checked to have the form
   `shared_mem + constant + 18048 * input stage + 4096 * output stage + 2 * gate offset +
   (a sum of weights of the bits of the thread index)` and is decoded to an array element with
   the layout tables below.
2. Data registers hold symbolic values. A load gives every lane the elements of its rows through
   the byte maps of `Lemmas/Matrix/Move.lean` (`ldByte`, `stByte`, `movByte`); the scalar
   instructions build expression trees; a multiply-accumulate collects its A, B and C operands
   from the 32 lanes through `aRow/aCol`, `bRow/bCol`, `cRow/cCol`, recognizes each as one named
   matrix (every one of its entries is compared) and names its result by the equations of
   `Math/Fragments.lean`.
3. Every register is then described without reference to the lane (a layout, a matrix, an
   index), and the description is expanded again and compared with the symbolic value for all
   32 lanes of all four warps.

The script stops with an error on anything it cannot classify.

Reads the frozen PTX (through `analysis.load`). Writes

* `Gen/Tables/matrix_table.json`, the table: `matrix` has one entry per matrix instruction,
  `scalar` one per scalar data instruction, `registers` one per data register and `carries` one
  per carry register (a register that holds an FP32 entry of the state across the tiles). The
  keys `variables`, `forms` and `layouts` explain the vocabulary of the entries, and `checks`
  lists what the script verified;
* `Math/FragmentsTable.lean`: each of the 104 multiply-accumulates as an equation between terms
  of `Math/Fragments.lean`, checked by Lean with `rfl`.

    python3 Kernels/FlashKdaFwd/Gen/matrix_table.py            # write the table and the Lean file
    python3 Kernels/FlashKdaFwd/Gen/matrix_table.py --check    # write nothing; fail if one is stale
"""

import argparse
import collections
import json
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import analysis  # noqa: E402  (read-only use: loading the code, reachability, liveness)
import outputs  # noqa: E402

KERNEL = HERE.parent
# Not in `Gen/Out/`: the files there are run declarations for `Tools/out_gen.py`.
OUT_JSON = HERE / "Tables" / "matrix_table.json"
OUT_LEAN = KERNEL / "Math" / "FragmentsTable.lean"

LO, HI = 2135, 2944  # the tile loop body: loop head .. back edge
M32 = (1 << 32) - 1

# ---------------------------------------------------------------------------------------------
# The layout of shared memory (offsets from `shared_mem`). These are the facts the script takes
# as given; each is the export of another part of the proof:
# the stage arrays are where the 70 tensor loads of a tile put them (checked below against the
# destinations of the load leader's instructions), `state_acc` is in the layout the conversion
# loop writes, and the output stage is where the tensor stores read it.

STATE_ACC = (0, 32768)  # bf16 [value channel][key feature], 8 x 8 atoms of 128 bytes
STAGE0, STAGE = 32768, 18048  # input stage `s` starts at STAGE0 + STAGE * s
OUT0, OUT = 86912, 4096  # output stage `o` starts at OUT0 + OUT * o
# name: (offset in the stage, bytes, element bytes)
ARRAYS = {
    "v": (0, 4096, 2),
    "beta": (4096, 64, 2),
    "kd": (4224, 4096, 2),
    "qd": (8320, 4096, 2),
    "kr": (12416, 4096, 2),
    "gt": (16512, 512, 4),
    "inv": (17024, 512, 2),
    "mqk": (17536, 512, 2),
}
SOURCE_NAME = {
    "v": "v",
    "beta": "beta",
    "kd": "k_decayed",
    "qd": "q_decayed",
    "kr": "k_restored",
    "gt": "g_total",
    "inv": "INV",
    "mqk": "Mqk",
    "state_acc": "state_acc",
    "out": "out",
}
MULTIPLIER = 0xBFB8AA3B  # the binary32 constant of the gate, `Recurrence.multiplier`
ONE = 0x3F800000  # binary32 1.0


class Fail(Exception):
    pass


def need(cond, msg):
    if not cond:
        raise Fail(msg)


# ---------------------------------------------------------------------------------------------
# The fragment layouts, transcribed from the library (lane `l`, register `r`, half `h`).


def a_row(l, r):  # noqa: E741  WarpMatrix.aRow
    return l // 4 + 8 * (r % 2)


def a_col(l, r, h):  # noqa: E741  WarpMatrix.aCol
    return 2 * (l % 4) + h + 8 * (r // 2)


def b_row(l, r, h):  # noqa: E741  WarpMatrix.bRow
    return 8 * r + 2 * (l % 4) + h


def b_col(l):  # noqa: E741  WarpMatrix.bCol
    return l // 4


def c_row(l, r):  # noqa: E741  WarpMatrix.cRow
    return l // 4 + 8 * (r // 2)


def c_col(l, r):  # noqa: E741  WarpMatrix.cCol
    return 2 * (l % 4) + r % 2


def ld_source(trans, l, r, h):  # noqa: E741
    """`WarpMatrix.ldByte` in 16-bit elements: half `h` of register `r` of lane `l` after a load
    is element (second component) of the row of lane (first component)."""
    return (8 * r + 2 * (l % 4) + h, l // 4) if trans else (8 * r + l // 4, 2 * (l % 4) + h)


def st_source(trans, s, j):
    """`WarpMatrix.stByte` in 16-bit elements: element `j` of the row lane `s` writes is half
    (third) of register (second) of lane (first)."""
    return (4 * j + (s % 8) // 2, s // 8, s % 2) if trans else (4 * (s % 8) + j // 2, s // 8, j % 2)


def mov_source(l, h):  # noqa: E741
    """`WarpMatrix.movByte` in 16-bit elements: half `h` of the result of lane `l` is half
    (second) of the source register of lane (first)."""
    g, t = l // 4, l % 4
    return (4 * (2 * t + h) + g // 2, g % 2)


# ---------------------------------------------------------------------------------------------
# Loading the loop body.


def load_body():
    code, ids, widths = analysis.load()
    envs = analysis.reachable(code, "compute")
    need(code[HI]["opcode"] == "bra.uni" and code[HI]["target"] == LO, "2944 is not the back edge")
    body = []
    for pc in range(LO, HI + 1):
        ins = code[pc]
        if pc not in envs:
            need(ins["opcode"] == "brkpt", f"pc {pc}: unreachable instruction {ins['opcode']}")
            continue
        if ins["opcode"].split(".")[0] == "bra":
            # The only branches of the body: a skip over one `brkpt`, the two branches of a
            # poll loop, the loop exit and the back edge. So one iteration executes every other
            # reachable instruction of the body exactly once, in the order of the listing.
            t = ins["target"]
            skip = t == pc + 2 and code[pc + 1]["opcode"] == "brkpt"
            poll_done = t == pc + 2 and code[pc - 1]["opcode"].startswith("mbarrier.try_wait")
            poll_again = t == pc - 2 and code[t]["opcode"].startswith("mbarrier.try_wait")
            leave = pc == HI - 1 and t > HI
            back = pc == HI
            need(skip or poll_done or poll_again or leave or back, f"pc {pc}: unexpected branch")
            continue
        body.append(pc)
    for pc in range(len(code)):
        t = code[pc].get("target")
        if t is not None and LO < t <= HI and not (LO <= pc <= HI):
            raise Fail(f"pc {pc} jumps into the loop body at {t}")
    return code, envs, body, ids


def operand_regs(o):
    return re.findall(r"%\w+", o)


def parse_addr(o):
    m = re.fullmatch(r"\[(%\w+)(?:\+(\d+))?\]", o)
    need(m is not None, f"address operand {o}")
    return m.group(1), int(m.group(2) or 0)


# ---------------------------------------------------------------------------------------------
# Control registers: 32-bit words as functions of the thread index and the loop-carried indices.


def ctl_step(ins, env, tid, base):
    """Evaluate one control instruction; unknown inputs give an unknown result (`None`)."""
    op, ops = ins["opcode"], ins["operands"]

    def val(o):
        if o == "shared_mem":
            return base
        if o == "%tid.x":
            return tid
        if re.fullmatch(r"-?\d+", o):
            return int(o) & M32
        need(o.startswith("%"), f"pc {ins['pc']}: operand {o}")
        return env.get(o)

    def out(v):
        for w in ins["writes"]:
            env[w] = None if v is None else v & M32

    if op.startswith("mapa."):
        # the address of an mbarrier for the arrival that follows: no data address reads it
        return out(None)
    args = [val(o) for o in ops[1:]]
    if any(a is None for a in args):
        return out(None)
    if op in ("mov.u32", "mov.b32"):
        return out(args[0])
    if op == "add.s32":
        return out(args[0] + args[1])
    if op == "shl.b32":
        return out(args[0] << args[1] if args[1] < 32 else 0)
    if op == "shr.u32":
        return out(args[0] >> args[1] if args[1] < 32 else 0)
    if op == "and.b32":
        return out(args[0] & args[1])
    if op == "or.b32":
        return out(args[0] | args[1])
    if op == "xor.b32":
        return out(args[0] ^ args[1])
    if op == "mad.lo.s32":
        return out(args[0] * args[1] + args[2])
    if op == "setp.lt.u32":
        return out(int(args[0] < args[1]))
    if op == "setp.eq.b32":
        return out(int(args[0] == args[1]))
    if op == "selp.b32":
        return out(args[0] if args[2] else args[1])
    raise Fail(f"pc {ins['pc']}: control instruction {op} is not interpreted")


MEM_OPS = ("ldmatrix", "stmatrix", "ld.shared.b16", "ld.shared.b32")


def is_mem(ins):
    return ins["opcode"].startswith(MEM_OPS)


def addr_operand(ins):
    return ins["operands"][0] if ins["opcode"].startswith("stmatrix") else ins["operands"][1]


def check_preloop(code):
    """The two loop-invariant facts the interpretation of addresses starts from, read off the
    instructions before the loop: `%r1641 = 2 * ((gate offset) + (tid / 4) % 8)` and the initial
    values of the stage indices."""
    text = {pc: (code[pc]["opcode"], code[pc]["operands"]) for pc in range(2117, 2135)}
    want = {
        2120: ("mad.lo.s32", ["%r839", "%r1786", "%r837", "%r838"]),
        2121: ("and.b32", ["%r840", "%r839", "7"]),
        2122: ("shr.u32", ["%r841", "%r18", "2"]),
        2123: ("and.b32", ["%r842", "%r841", "7"]),
        2124: ("add.s32", ["%r19", "%r840", "%r842"]),
        2129: ("mov.b32", ["%r1801", "0"]),
        2131: ("shl.b32", ["%r1641", "%r19", "1"]),
        2133: ("mov.b32", ["%r1802", "%r1801"]),
        2134: ("mov.b32", ["%r1804", "%r1801"]),
    }
    for pc, w in want.items():
        need(text[pc] == w, f"pc {pc}: expected {w}, found {text[pc]}")
    need(code[2106]["operands"] == ["%r18", "%tid.x"], "pc 2106 does not read the thread index")
    # The stage indices advance cyclically at the end of the body (2931..2938).
    tail = {
        2931: ("add.s32", ["%r1732", "%r1802", "1"]),
        2932: ("setp.eq.b32", ["%p74", "%r1732", "3"]),
        2933: ("selp.b32", ["%r1802", "0", "%r1732", "%p74"]),
        2936: ("add.s32", ["%r1734", "%r1804", "1"]),
        2937: ("setp.eq.b32", ["%p75", "%r1734", "2"]),
        2938: ("selp.b32", ["%r1804", "0", "%r1734", "%p75"]),
    }
    for pc, w in tail.items():
        got = (code[pc]["opcode"], code[pc]["operands"])
        need(got == w, f"pc {pc}: expected {w}, found {got}")


def address_table(code, body, data):
    """`table[pc][(tid, s, o, k)]` = offset from `shared_mem` of the address of the memory
    instruction at `pc`, for thread `tid`, input stage `s`, output stage `o`, gate offset `k`."""
    mem_pcs = [pc for pc in body if is_mem(code[pc])]
    control = [
        pc
        for pc in body
        if not code[pc]["event"]
        and not (set(code[pc]["writes"]) | set(code[pc]["reads"])) & data
        and code[pc]["writes"]
    ]
    table = {pc: {} for pc in mem_pcs}
    steps = sorted(control + mem_pcs)

    def run(tid, s, o, k, base):
        env = {"%r1802": s, "%r1804": o, "%r1641": 2 * (k + ((tid >> 2) & 7))}
        got = {}
        for pc in steps:
            ins = code[pc]
            if is_mem(ins):
                reg, off = parse_addr(addr_operand(ins))
                v = env.get(reg)
                need(v is not None, f"pc {pc}: address register {reg} is not determined")
                got[pc] = (v + off - base) & M32
            else:
                ctl_step(ins, env, tid, base)
        return got

    for tid in range(128):
        for s in range(3):
            for o in range(2):
                for k in range(8):
                    if (s, o, k) != (0, 0, 0) and tid % 37 != 0 and (s, o, k) not in SPOT:
                        continue
                    got = run(tid, s, o, k, 0)
                    for pc in mem_pcs:
                        table[pc][(tid, s, o, k)] = got[pc]
        # Addresses are `shared_mem` plus an offset: the offset does not depend on the base.
        other = run(tid, 2, 1, 5, 0x00470080)
        base0 = run(tid, 2, 1, 5, 0)
        need(other == base0, f"thread {tid}: an address is not shared_mem + offset")
    return table, mem_pcs


# For every thread the dependence on (stage, stage, gate offset) is checked on these points; a
# few threads (`tid % 37 == 0`) are checked on the whole grid.
SPOT = {(1, 0, 0), (2, 0, 0), (0, 1, 0), (0, 0, 1), (0, 0, 7), (2, 1, 7)}


def address_form(pc, col):
    """Check and return the symbolic form of one address column.

    offset = const + cs * s + co * o + ck * k + sum_b weight[b] * bit_b(tid)."""
    base = col[(0, 0, 0, 0)]
    cs = col[(0, 1, 0, 0)] - base
    co = col[(0, 0, 1, 0)] - base
    ck = col[(0, 0, 0, 1)] - base
    weights = [col[(1 << b, 0, 0, 0)] - base for b in range(7)]
    for (tid, s, o, k), v in col.items():
        want = (
            base + cs * s + co * o + ck * k + sum(w for b, w in enumerate(weights) if tid >> b & 1)
        )
        need(v == want, f"pc {pc}: address is not of the expected form at {(tid, s, o, k)}")
    need(cs in (0, STAGE) and co in (0, OUT) and ck in (0, 2), f"pc {pc}: stage coefficients")
    return {"const": base, "stage": cs, "out_stage": co, "gate_offset": ck, "tid_bits": weights}


def form_text(f):
    parts = ["shared_mem", str(f["const"])]
    if f["stage"]:
        parts.append(f"{f['stage']}*s")
    if f["out_stage"]:
        parts.append(f"{f['out_stage']}*o")
    if f["gate_offset"]:
        parts.append(f"{f['gate_offset']}*k")
    names = ["l%2", "l/2%2", "l/4%2", "l/8%2", "l/16", "w%2", "w/2"]
    w = f["tid_bits"]
    # Group bits whose weights double into one field.
    groups = [
        ("l", 0, 5),
        ("l%8", 0, 3),
        ("l/4", 2, 3),
        ("l/4%2", 2, 1),
        ("w", 5, 2),
    ]
    used = [False] * 7
    for name, lo, n in groups:
        if any(used[lo : lo + n]):
            continue
        if w[lo] and all(w[lo + i] == w[lo] << i for i in range(n)):
            parts.append(f"{w[lo]}*({name})")
            for i in range(n):
                used[lo + i] = True
    for b in range(7):
        if not used[b] and w[b]:
            parts.append(f"{w[b]}*({names[b]})")
    return " + ".join(parts)


def decode(off, elem):
    """The array element at byte offset `off` (at stage indices 0): (array, index...)."""
    if STATE_ACC[0] <= off < STATE_ACC[1]:
        need(off % 2 == 0, f"odd state_acc offset {off}")
        e = off // 2
        n = 8 * ((e // 64) % 16) + (e // 8) % 8  # value channel
        k = 8 * (e // 1024) + e % 8  # key feature
        return ("state_acc", n, k)
    if OUT0 <= off < OUT0 + OUT:
        r = off - OUT0
        return ("out", (r % 256) // 16, 8 * (r // 256) + (r % 16) // 2)
    r = off - STAGE0
    need(0 <= r < STAGE, f"offset {off} is in no known region")
    for name, (start, size, eb) in ARRAYS.items():
        if start <= r < start + size:
            q = r - start
            need(q % eb == 0 and eb == elem, f"offset {off}: element size of {name}")
            if name in ("beta", "gt"):
                return (name, q // eb)
            return (name, (q % 256) // 16, 8 * (q // 256) + (q % 16) // 2)
    raise Fail(f"offset {off} is in padding of the input stage")


def check_load_destinations(code):
    """The offsets of `ARRAYS` are the destinations of the 70 tensor loads of a tile (first of
    the three unrolled copies of the load leader's loop), and each 256-byte piece of a workspace
    array is loaded with first coordinate `8 * piece` (the feature index)."""
    arrive = [
        pc for pc in range(1403, 2106) if code[pc]["opcode"].startswith("mbarrier.arrive.expect_tx")
    ]
    need(len(arrive) == 3, "three expect_tx arrivals expected in the load loop")
    defs = {}
    loads = []
    for pc in range(arrive[0], arrive[1]):
        ins = code[pc]
        if ins["opcode"].startswith("cp.async.bulk.tensor"):
            loads.append(ins)
        elif ins["writes"]:
            defs[ins["writes"][0]] = ins
    need(len(loads) == 70, f"{len(loads)} tensor loads in one iteration of the load loop")
    stage_reg = None
    seen = collections.defaultdict(list)
    for ins in loads:
        dst = operand_regs(ins["operands"][0])[0]
        d = defs[dst]
        need(d["opcode"] == "add.s32", f"pc {ins['pc']}: destination is not base + constant")
        stage_reg = stage_reg or d["operands"][1]
        need(d["operands"][1] == stage_reg, f"pc {ins['pc']}: another base register")
        off = int(d["operands"][2]) - STAGE0
        m = re.match(r"\[(%\w+),\{(%\w+)[,}]", ins["operands"][1])
        need(m is not None, f"pc {ins['pc']}: source operand {ins['operands'][1]}")
        coord = defs.get(m.group(2))
        first = None
        if (
            coord is not None
            and coord["opcode"] == "mov.b32"
            and re.fullmatch(r"\d+", coord["operands"][1])
        ):
            first = int(coord["operands"][1])
        seen[m.group(1)].append((off, first, ins["opcode"].split(".")[3]))
    d = defs[stage_reg]
    need(d["opcode"] == "mad.lo.s32" and d["operands"][2] == "18040", "stage base is not 18048 * s")
    found = {}
    for mapreg, items in seen.items():
        offs = sorted(o for o, _, _ in items)
        name = next((n for n, (start, _, _) in ARRAYS.items() if start == offs[0]), None)
        need(name is not None, f"tensor loads to an unknown stage offset {offs[0]}")
        size = ARRAYS[name][1]
        piece = 256 if size >= 256 and name not in ("gt",) else size
        need(
            offs == [ARRAYS[name][0] + piece * i for i in range(size // piece)], f"pieces of {name}"
        )
        if name in ("kd", "qd", "kr", "inv", "mqk"):
            for off, first, _ in items:
                i = (off - ARRAYS[name][0]) // 256
                # The zero coordinate of piece 0 is a shared zero register.
                need(
                    first == 8 * i or (i == 0 and first in (0, None)),
                    f"{name}: coordinate of piece {i}",
                )
        found[name] = len(items)
    need(
        found == {"v": 16, "beta": 1, "kd": 16, "qd": 16, "kr": 16, "gt": 1, "inv": 2, "mqk": 2},
        f"loads {found}",
    )
    return found


def check_carry_io(code, carry):
    """The carries outside the loop: the 128 generic loads that fill them before the first tile
    (positions 765..1400) and the 128 generic stores after the last (3132..3767) address the
    FP32 state buffer at the entry the table gives the register. The buffer holds the state as
    `[value channel n][key feature k]` at the float index `64*(n/8) + 1024*(k/8) + 8*(n%8) + k%8`
    from window offset 32768, before the swizzle that the three instructions in front of each
    access apply to the address (`shr.u64 3; and.b64 16; xor.b64`). Returns, per register, the
    positions of its load and its store and its byte offset from the lane's base entry."""

    def expect(pc, opcode, operands):
        got = (code[pc]["opcode"], code[pc]["operands"])
        need(got == (opcode, operands), f"pc {pc}: expected {(opcode, operands)}, found {got}")

    def base_index(pcs, reg, tid):
        env = {}
        for pc in pcs:
            ctl_step(code[pc], env, tid, 0)
        return env[reg]

    # the lane's base entry: float index 16 * (l % 4) + l / 4 + 256 * w, for the loads ...
    expect(627, "mul.wide.u32", ["%rd110", "%r358", "4"])
    expect(628, "mov.b32", ["%r359", "shared_mem"])
    expect(629, "cvt.u64.u32", ["%rd111", "%r359"])
    expect(630, "cvta.shared.u64", ["%rd112", "%rd111"])
    expect(631, "add.s64", ["%rd4", "%rd112", "%rd110"])
    # ... and for the stores
    expect(3123, "mul.wide.u32", ["%rd648", "%r1744", "4"])
    expect(3124, "mov.b32", ["%r1745", "shared_mem"])
    expect(3125, "cvt.u64.u32", ["%rd649", "%r1745"])
    expect(3126, "cvta.shared.u64", ["%rd650", "%rd649"])
    expect(3127, "add.s64", ["%rd651", "%rd650", "%rd648"])
    for tid in range(128):
        want = 16 * (tid % 4) + (tid % 32) // 4 + 256 * (tid // 32)
        need(
            base_index([13, 14, 388, 392, 622, 623, 624, 625, 626], "%r358", tid) == want,
            f"load base of thread {tid}",
        )
        need(
            base_index([3111, 3115, 3116, 3117, 3118, 3119, 3120, 3121, 3122], "%r1744", tid)
            == want,
            f"store base of thread {tid}",
        )

    def accesses(lo, hi, opcode, base):
        found = {}
        for pc in range(lo, hi + 1):
            ins = code[pc]
            if ins["opcode"] != opcode:
                need(
                    not ins["opcode"].startswith(("ld.", "st.")),
                    f"pc {pc}: unexpected {ins['opcode']}",
                )
                continue
            if opcode == "ld.b32":
                reg, addr = ins["operands"][0], ins["operands"][1]
            else:
                addr, reg = ins["operands"][0], ins["operands"][1]
            a, x, y, z = (code[pc - 4 + i] for i in range(4))
            ok = (
                a["opcode"] == "add.s64"
                and a["operands"][1] == base
                and x["opcode"] == "shr.u64"
                and x["operands"][1:] == [a["operands"][0], "3"]
                and y["opcode"] == "and.b64"
                and y["operands"][1:] == [x["operands"][0], "16"]
                and z["opcode"] == "xor.b64"
                and z["operands"][1:] == [y["operands"][0], a["operands"][0]]
                and addr == f"[{z['operands'][0]}]"
            )
            need(ok, f"pc {pc}: the access is not base + constant through the swizzle")
            need(reg not in found, f"pc {pc}: {reg} accessed twice")
            found[reg] = (pc, int(a["operands"][2]))
        return found

    loads = accesses(761, 1400, "ld.b32", "%rd4")
    stores = accesses(3128, 3767, "st.b32", "%rd651")
    need(
        set(loads) == set(stores) == set(carry),
        "the loads and stores are not those of the 128 carries",
    )
    out = {}
    for reg, (_, m, bh, r) in carry.items():
        k_load, k_store = loads[reg][1], stores[reg][1]
        need(
            k_load == k_store and (k_load - 32768) % 4 == 0,
            f"{reg}: load at {k_load}, store at {k_store}",
        )
        rel = (k_load - 32768) // 4
        for tid in range(128):
            w, l = tid // 32, tid % 32  # noqa: E741
            f = 16 * (l % 4) + l // 4 + 256 * w + rel
            n = 8 * ((f // 64) % 16) + (f // 8) % 8
            k = 8 * (f // 1024) + f % 8
            want = (16 * m + c_row(l, r), 16 * (2 * w + bh[0]) + 8 * bh[1] + c_col(l, r))
            need(
                (k, n) == want,
                f"{reg}: thread {tid} loads state entry {(k, n)}, the loop treats it as {want}",
            )
        out[reg] = {
            "load_pc": loads[reg][0],
            "store_pc": stores[reg][0],
            "buffer_offset": k_load - 32768,
        }
    return out


# ---------------------------------------------------------------------------------------------
# Symbolic values.
#
# A real number is a term (a tuple):
#   ("kd"|"qd"|"kr", row, feature)  ("inv"|"mqk", row, column)  ("v", row, channel)
#   ("logit", row)  ("gt", feature)  ("copy", key, channel)  ("carry", register)
#   ("ent", matrix, i, j)      entry of a named matrix of Math/Fragments.lean
#   ("gate", row)  and the intermediate nodes ("mulK", x)  ("ex2", x)  ("add1", x)  ("sub", x, y)
#
# A register value is one of
#   ("f32", term)       the f32 payload of the number
#   ("zero",)           the 32-bit zero word
#   ("bitsZ", term)     a 32-bit word: the bf16 bit pattern of the number, zero-extended
#   ("bitsH", term)     a 32-bit word: that bit pattern in the high half (reads as the number)
#   ("pair", lo, hi)    two 16-bit halves
#   ("bf16", term)      a 16-bit bf16 payload          ("raw16", term)  a 16-bit bf16 bit pattern


def number(v, pc):
    """The real a 32-bit register reads as, as an f32 operand."""
    if v[0] == "f32" or v[0] == "bitsH":
        return v[1]
    raise Fail(f"pc {pc}: {v} is not read as an f32 number")


def matrix_entry(m, i, j):
    """Entry `(i, j)` of a named matrix, as a term (a memory element where the matrix is one)."""
    if m[0] == "keyBlock":
        return (m[1], i, 16 * m[2] + j)
    if m[0] == "keyBlockT":
        return (m[1], j, 16 * m[2] + i)
    if m[0] in ("inv", "mqk"):
        return (m[0], i, j)
    if m[0] == "stateBlock":
        return ("copy", 16 * m[2] + i, m[1] + j)
    if m[0] == "valueBlock":
        return ("v", i, m[1] + j)
    if m[0] == "zero":
        return None
    return ("ent", m, i, j)


def recognize(cells, rows, cols, what, pc):
    """The named matrix whose entries are the terms `cells[(i, j)]`."""
    need(set(cells) == {(i, j) for i in range(rows) for j in range(cols)}, f"pc {pc}: {what} cells")
    t = cells[(0, 0)]
    cands = []
    if t is None:
        cands = [("zero",)]
    elif t[0] in ("kd", "qd"):
        cands = [("keyBlock", t[0], t[2] // 16)]
    elif t[0] == "kr":
        cands = [("keyBlockT", "kr", t[2] // 16)]
    elif t[0] in ("inv", "mqk"):
        cands = [(t[0],)]
    elif t[0] == "copy":
        cands = [("stateBlock", t[2], t[1] // 16)]
    elif t[0] == "v":
        cands = [("valueBlock", t[2])]
    elif t[0] == "ent":
        cands = [t[1]]
    for m in cands:
        if all(cells[(i, j)] == matrix_entry(m, i, j) for i in range(rows) for j in range(cols)):
            return m
    raise Fail(f"pc {pc}: the {what} operand is no known matrix (entry (0,0) is {t})")


def normalize(t, pc, carry_use):
    """Name the results of the scalar code by the definitions of Math/Fragments.lean."""
    if t[0] == "rcp":
        ok = (
            t[1][0] == "add1"
            and t[1][1][0] == "ex2"
            and t[1][1][1][0] == "mulK"
            and t[1][1][1][1][0] == "logit"
        )
        need(ok, f"pc {pc}: reciprocal of {t[1]} is not the gate")
        return ("gate", t[1][1][1][1][1])
    if t[0] == "mul":
        g, d = t[1], t[2]
        ok = g[0] == "gate" and d[0] == "sub" and d[1][0] == "v" and d[2][0] == "ent"
        need(ok, f"pc {pc}: product {t} is not the residual")
        p = d[2]
        need(p[1][0] == "project" and p[1][1] == "kd" and p[1][3] == 8, f"pc {pc}: residual of {p}")
        c, i, j = p[1][2], p[2], p[3]
        need(g[1] == i and d[1][1] == i and d[1][2] == c + j, f"pc {pc}: residual indices {t}")
        return ("ent", ("residual", c), i, j)
    if t[0] == "fma":
        s, g, a = t[1], t[2], t[3]
        ok = s[0] == "carry" and g[0] == "gt" and a[0] == "ent" and a[1][0] == "update"
        need(ok, f"pc {pc}: fused multiply-add {t} is not the state update")
        c, m, i, j = a[1][1], a[1][2], a[2], a[3]
        need(g[1] == 16 * m + i, f"pc {pc}: decay of feature {g[1]} for entry {(m, i, j)}")
        carry_use.append((s[1], pc, 16 * m + i, c + j, c, m, i, j))
        return ("ent", ("nextState", c, m), i, j)
    return t


class Warp:
    """One iteration of the loop body for the 32 lanes of warp `w`."""

    def __init__(self, code, body, data, addr, w):
        self.code, self.body, self.data, self.addr, self.w = code, body, data, addr, w
        self.regs = [dict() for _ in range(32)]
        self.mem = {}  # byte offset of a 16-bit element -> value written in this iteration
        self.reads = collections.defaultdict(set)  # array -> set of element byte offsets read
        self.carry_use = [[] for _ in range(32)]
        self.records = {}  # pc -> lane-independent record (filled by the describers)
        self.values = {}  # pc -> {register: [value of lane 0..31]}
        self.operands = {}  # mma pc -> (A, B, C, D)
        self.rows = {}  # ld/st matrix pc -> [row offset of lane 0..31]

    def offset(self, pc, lane):
        return self.addr[pc][(32 * self.w + lane, 0, 0, 0)]

    def get(self, lane, reg, pc):
        if reg == "%r862":
            return ("zero",)
        v = self.regs[lane].get(reg)
        if v is None:
            need(
                1812 <= int(reg[2:]) <= 1939 and reg.startswith("%r"),
                f"pc {pc}: {reg} read before written",
            )
            v = ("f32", ("carry", reg))
        return v

    def put(self, pc, lane, reg, v):
        self.regs[lane][reg] = v
        self.values.setdefault(pc, {}).setdefault(reg, [None] * 32)[lane] = v

    def elem(self, off, array_elem, pc):
        """The 16-bit value at byte offset `off` (a state_acc or stage element)."""
        need(off not in self.mem, f"pc {pc}: reads offset {off} written earlier in the iteration")
        d = decode(off, array_elem)
        self.reads[d[0]].add(off)
        if d[0] == "state_acc":
            return ("bf16", ("copy", d[2], d[1]))
        if d[0] == "v":
            return ("raw16", ("v", d[1], d[2]))
        need(d[0] in ("kd", "qd", "kr", "inv", "mqk"), f"pc {pc}: matrix load from {d[0]}")
        return ("bf16", (d[0], d[1], d[2]))

    def run(self):
        for pc in self.body:
            ins = self.code[pc]
            op = ins["opcode"]
            touches = (set(ins["writes"]) | set(ins["reads"])) & self.data
            if op.startswith("ldmatrix"):
                self.ldmatrix(pc, ins)
            elif op.startswith("stmatrix"):
                self.stmatrix(pc, ins)
            elif op.startswith("movmatrix"):
                self.movmatrix(pc, ins)
            elif op.startswith("mma."):
                self.mma(pc, ins)
            elif op in ("ld.shared.b16", "ld.shared.b32"):
                self.scalar_load(pc, ins)
            elif touches:
                need(not ins["event"], f"pc {pc}: event {op} on data registers")
                for lane in range(32):
                    self.scalar(pc, ins, lane)
            # every other instruction is control code or an event without data

    # -- matrix instructions ---------------------------------------------------------------

    def ldmatrix(self, pc, ins):
        trans = ".trans." in ins["opcode"]
        need(
            ins["opcode"] == f"ldmatrix.sync.aligned.x4.{'trans.' if trans else ''}m8n8.shared.b16",
            f"pc {pc}: form",
        )
        dsts = operand_regs(ins["operands"][0])
        need(len(dsts) == 4, f"pc {pc}: four destinations")
        self.rows[pc] = [self.offset(pc, s) for s in range(32)]
        need(all(r % 16 == 0 for r in self.rows[pc]), f"pc {pc}: row not 16-byte aligned")
        rows = [[self.elem(self.rows[pc][s] + 2 * j, 2, pc) for j in range(8)] for s in range(32)]
        for lane in range(32):
            for r, d in enumerate(dsts):
                halves = []
                for h in range(2):
                    s, j = ld_source(trans, lane, r, h)
                    halves.append(rows[s][j])
                self.put(pc, lane, d, ("pair", halves[0], halves[1]))

    def stmatrix(self, pc, ins):
        trans = ".trans." in ins["opcode"]
        need(
            ins["opcode"] == f"stmatrix.sync.aligned.x4.{'trans.' if trans else ''}m8n8.shared.b16",
            f"pc {pc}: form",
        )
        srcs = operand_regs(ins["operands"][1])
        need(len(srcs) == 4, f"pc {pc}: four sources")
        self.rows[pc] = [self.offset(pc, s) for s in range(32)]
        need(all(r % 16 == 0 for r in self.rows[pc]), f"pc {pc}: row not 16-byte aligned")
        for s in range(32):
            for j in range(8):
                lane, r, h = st_source(trans, s, j)
                v = self.get(lane, srcs[r], pc)
                need(v[0] == "pair", f"pc {pc}: source {srcs[r]} is not a pair")
                off = self.rows[pc][s] + 2 * j
                need(off not in self.mem, f"pc {pc}: offset {off} written twice")
                self.mem[off] = (v[1 + h], pc, s)

    def movmatrix(self, pc, ins):
        need(ins["opcode"] == "movmatrix.sync.aligned.m8n8.trans.b16", f"pc {pc}: form")
        dst, src = ins["operands"]
        vals = [self.get(lane, src, pc) for lane in range(32)]
        need(all(v[0] == "pair" for v in vals), f"pc {pc}: source {src} is not a pair")
        for lane in range(32):
            halves = []
            for h in range(2):
                s, hh = mov_source(lane, h)
                halves.append(vals[s][1 + hh])
            self.put(pc, lane, dst, ("pair", halves[0], halves[1]))

    def mma(self, pc, ins):
        need(
            ins["opcode"] == "mma.sync.aligned.m16n8k16.row.col.f32.bf16.bf16.f32", f"pc {pc}: form"
        )
        d, a, b, c = (operand_regs(o) for o in ins["operands"])
        need((len(d), len(a), len(b), len(c)) == (4, 4, 2, 4), f"pc {pc}: operand counts")
        ca, cb, cc = {}, {}, {}
        for lane in range(32):
            for r in range(4):
                v = self.get(lane, a[r], pc)
                need(v[0] == "pair", f"pc {pc}: A register {a[r]} is not a pair")
                for h in range(2):
                    x = v[1 + h]
                    need(x[0] == "bf16", f"pc {pc}: A element {x} is not a bf16 payload")
                    key = (a_row(lane, r), a_col(lane, r, h))
                    need(key not in ca, f"pc {pc}: A cell {key} twice")
                    ca[key] = x[1]
            for r in range(2):
                v = self.get(lane, b[r], pc)
                need(v[0] == "pair", f"pc {pc}: B register {b[r]} is not a pair")
                for h in range(2):
                    x = v[1 + h]
                    need(x[0] == "bf16", f"pc {pc}: B element {x} is not a bf16 payload")
                    key = (b_row(lane, r, h), b_col(lane))
                    need(key not in cb, f"pc {pc}: B cell {key} twice")
                    cb[key] = x[1]
            for r in range(4):
                v = self.get(lane, c[r], pc)
                need(v[0] in ("f32", "zero"), f"pc {pc}: C register {c[r]} holds {v}")
                key = (c_row(lane, r), c_col(lane, r))
                need(key not in cc, f"pc {pc}: C cell {key} twice")
                cc[key] = None if v[0] == "zero" else v[1]
        ma = recognize(ca, 16, 16, "A", pc)
        mb = recognize(cb, 16, 8, "B", pc)
        mc = recognize(cc, 16, 8, "C", pc)
        md = product(ma, mb, mc, pc)
        self.operands[pc] = (ma, mb, mc, md)
        for lane in range(32):
            for r in range(4):
                self.put(pc, lane, d[r], ("f32", ("ent", md, c_row(lane, r), c_col(lane, r))))

    # -- scalar instructions ---------------------------------------------------------------

    def scalar_load(self, pc, ins):
        dst = ins["operands"][0]
        for lane in range(32):
            off = self.offset(pc, lane)
            if ins["opcode"] == "ld.shared.b16":
                d = decode(off, 2)
                need(d[0] == "beta" and d[1] < 16, f"pc {pc}: gate logit load from {d}")
                self.reads["beta"].add(off)
                # with gate offset k the element is k + row: `decode` ran at k = 0
                self.put(pc, lane, dst, ("bitsZ", ("logit", d[1])))
            else:
                d = decode(off, 4)
                need(d[0] == "gt", f"pc {pc}: f32 load from {d}")
                self.reads["gt"].add(off)
                self.put(pc, lane, dst, ("f32", ("gt", d[1])))

    def scalar(self, pc, ins, lane):
        op, ops = ins["opcode"], ins["operands"]
        get = lambda r: self.get(lane, r, pc)  # noqa: E731
        put = lambda r, v: self.put(pc, lane, r, v)  # noqa: E731
        norm = lambda t: normalize(t, pc, self.carry_use[lane])  # noqa: E731
        if op == "mov.b32" and ops[0].startswith("{"):
            lo, hi = operand_regs(ops[0])
            v = get(ops[1])
            need(v[0] == "pair", f"pc {pc}: unpack of {v}")
            put(lo, v[1])
            put(hi, v[2])
        elif op == "mov.b32" and ops[1].startswith("{"):
            lo, hi = (get(r) for r in operand_regs(ops[1]))
            need(lo[0] == "bf16" and hi[0] == "bf16", f"pc {pc}: pack of {lo}, {hi}")
            put(ops[0], ("pair", lo, hi))
        elif op == "cvt.u32.u16":
            v = get(ops[1])
            need(v[0] == "raw16", f"pc {pc}: zero extension of {v}")
            put(ops[0], ("bitsZ", v[1]))
        elif op == "shl.b32":
            v = get(ops[1])
            need(v[0] == "bitsZ" and ops[2] == "16", f"pc {pc}: shift of {v} by {ops[2]}")
            put(ops[0], ("bitsH", v[1]))
        elif op == "mul.ftz.f32" and ops[2].startswith("0f"):
            need(int(ops[2][2:], 16) == MULTIPLIER, f"pc {pc}: constant {ops[2]}")
            put(ops[0], ("f32", ("mulK", number(get(ops[1]), pc))))
        elif op == "add.ftz.f32" and ops[2].startswith("0f"):
            need(int(ops[2][2:], 16) == ONE, f"pc {pc}: constant {ops[2]}")
            put(ops[0], ("f32", ("add1", number(get(ops[1]), pc))))
        elif op == "ex2.approx.ftz.f32":
            put(ops[0], ("f32", ("ex2", number(get(ops[1]), pc))))
        elif op == "rcp.approx.ftz.f32":
            put(ops[0], ("f32", norm(("rcp", number(get(ops[1]), pc)))))
        elif op == "sub.ftz.f32":
            put(ops[0], ("f32", ("sub", number(get(ops[1]), pc), number(get(ops[2]), pc))))
        elif op == "mul.ftz.f32":
            put(ops[0], ("f32", norm(("mul", number(get(ops[1]), pc), number(get(ops[2]), pc)))))
        elif op == "fma.rn.ftz.f32":
            a, b, c = (number(get(r), pc) for r in ops[1:])
            need(ops[0] == ops[1], f"pc {pc}: fused multiply-add does not update its first operand")
            put(ops[0], ("f32", norm(("fma", a, b, c))))
        elif op == "cvt.rn.bf16.f32":
            t = number(get(ops[1]), pc)
            need(t[0] == "ent", f"pc {pc}: narrowing of the unnamed number {t}")
            put(ops[0], ("bf16", t))
        else:
            raise Fail(f"pc {pc}: data instruction {op} is not interpreted")


def product(a, b, c, pc):
    """The result of one multiply-accumulate, by the equations of Math/Fragments.lean."""
    if a[0] == "keyBlock" and b[0] == "stateBlock":
        arr, m, ch = a[1], a[2], b[1]
        need(b[2] == m, f"pc {pc}: key block {m} times state block {b[2]}")
        if m == 0:
            need(c == ("zero",), f"pc {pc}: first key block onto {c}")
        else:
            need(c == ("project", arr, ch, m), f"pc {pc}: key block {m} onto {c}")
        return ("project", arr, ch, m + 1)
    if a == ("inv",) and b[0] == "residual" and c == ("zero",):
        return ("correction", b[1])
    if a == ("mqk",) and b[0] == "correction" and c == ("project", "qd", b[1], 8):
        return ("output", b[1])
    if a[0] == "keyBlockT" and b[0] == "correction" and c == ("zero",):
        return ("update", b[1], a[2])
    raise Fail(f"pc {pc}: multiply-accumulate of {a}, {b}, {c} is not a term of the tile")


# ---------------------------------------------------------------------------------------------
# Lane-independent descriptions. A description is (shape, form, parameters); `expand` gives the
# value it denotes in lane `l` of warp `w`, and every description is checked against all lanes.


def half_of(c, w, pc):
    r = c - 32 * w
    need(0 <= r < 32 and r % 8 == 0, f"pc {pc}: channel base {c} is not a half of warp {w}")
    return (r // 16, (r % 16) // 8)


def sym_matrix(m, w, pc):
    """Replace the absolute channel base of a matrix term by its (block, half) in the warp."""
    if m[0] == "stateBlock":
        return ("stateBlock", half_of(m[1], w, pc), m[2])
    if m[0] == "project":
        return ("project", m[1], half_of(m[2], w, pc), m[3])
    if m[0] in ("residual", "correction", "output"):
        return (m[0], half_of(m[1], w, pc))
    if m[0] in ("update", "nextState"):
        return (m[0], half_of(m[1], w, pc), m[2])
    if m[0] == "valueBlock":
        r = m[1] - 32 * w
        need(r in (0, 16), f"pc {pc}: value block base {m[1]}")
        return ("valueBlock", r // 16)
    return m


def abs_matrix(m, w):
    """The inverse of `sym_matrix` for warp `w`."""

    def base(bh):
        return 16 * (2 * w + bh[0]) + 8 * bh[1]

    if m[0] == "stateBlock":
        return ("stateBlock", base(m[1]), m[2])
    if m[0] == "project":
        return ("project", m[1], base(m[2]), m[3])
    if m[0] in ("residual", "correction", "output"):
        return (m[0], base(m[1]))
    if m[0] in ("update", "nextState"):
        return (m[0], base(m[1]), m[2])
    if m[0] == "valueBlock":
        return ("valueBlock", 32 * w + 16 * m[1])
    return m


def bf(t):
    return ("bf16", t)


def expand(desc, w, l):  # noqa: E741
    """The value a description denotes in lane `l` of warp `w`."""
    form = desc[0]
    if form == "zero":
        return ("zero",)
    if form in ("regA", "rawA"):
        _, m, r = desc
        mm = abs_matrix(m, w)
        wrap = (lambda t: ("raw16", t)) if form == "rawA" else bf
        return ("pair",) + tuple(
            wrap(matrix_entry(mm, a_row(l, r), a_col(l, r, h))) for h in range(2)
        )
    if form == "regB":
        _, m, r = desc
        mm = abs_matrix(m, w)
        return ("pair",) + tuple(bf(matrix_entry(mm, b_row(l, r, h), b_col(l))) for h in range(2))
    if form == "regC":
        _, m, r = desc
        return ("f32", matrix_entry(abs_matrix(m, w), c_row(l, r), c_col(l, r)))
    if form == "rowPair":
        _, m, p = desc
        mm = abs_matrix(m, w)
        return ("pair",) + tuple(
            bf(matrix_entry(mm, c_row(l, 2 * p + h), c_col(l, 2 * p + h))) for h in range(2)
        )
    if form == "narrowC":
        _, m, r = desc
        return bf(matrix_entry(abs_matrix(m, w), c_row(l, r), c_col(l, r)))
    if form in ("vRaw16", "vBitsZ", "vBitsH", "diff"):
        _, bh, r = desc
        c = 16 * (2 * w + bh[0]) + 8 * bh[1]
        i, j = c_row(l, r), c_col(l, r)
        v = ("v", i, c + j)
        if form == "diff":
            return ("f32", ("sub", v, ("ent", ("project", "kd", c, 8), i, j)))
        return ({"vRaw16": "raw16", "vBitsZ": "bitsZ", "vBitsH": "bitsH"}[form], v)
    if form in ("logitZ", "logitH", "logitK", "logitE", "logitP", "gate"):
        row = l // 4 + 8 * desc[1]
        x = ("logit", row)
        if form == "logitZ":
            return ("bitsZ", x)
        if form == "logitH":
            return ("bitsH", x)
        if form == "logitK":
            return ("f32", ("mulK", x))
        if form == "logitE":
            return ("f32", ("ex2", ("mulK", x)))
        if form == "logitP":
            return ("f32", ("add1", ("ex2", ("mulK", x))))
        return ("f32", ("gate", row))
    if form == "decay":
        return ("f32", ("gt", 16 * desc[1] + l // 4 + 8 * desc[2]))
    raise Fail(f"description {desc}")


def describe(vals, w, pc, reg):
    """A description of the values `vals[lane]` of one register, from lane 5 (a lane whose
    group and position in the group are both nonzero), to be verified on every lane."""
    l = 5  # noqa: E741
    v = vals[l]
    g = l // 4
    cands = []

    def creg(i, j):
        for r in range(4):
            if (c_row(l, r), c_col(l, r)) == (i, j):
                return r
        raise Fail(f"pc {pc}: entry {(i, j)} is not a C position of lane {l}")

    if v[0] == "zero":
        cands.append(("zero",))
    elif v[0] == "f32":
        t = v[1]
        if t[0] == "ent":
            cands.append(("regC", sym_matrix(t[1], w, pc), creg(t[2], t[3])))
        elif t[0] == "gt":
            cands.append(("decay", t[1] // 16, (t[1] % 16 - g) // 8))
        elif t[0] == "gate":
            cands.append(("gate", (t[1] - g) // 8))
        elif t[0] == "mulK":
            cands.append(("logitK", (t[1][1] - g) // 8))
        elif t[0] == "ex2":
            cands.append(("logitE", (t[1][1][1] - g) // 8))
        elif t[0] == "add1":
            cands.append(("logitP", (t[1][1][1][1] - g) // 8))
        elif t[0] == "sub":
            p = t[2]
            cands.append(("diff", half_of(p[1][2], w, pc), creg(p[2], p[3])))
    elif v[0] in ("bitsZ", "bitsH", "raw16"):
        t = v[1]
        if t[0] == "logit":
            cands.append(({"bitsZ": "logitZ", "bitsH": "logitH"}[v[0]], (t[1] - g) // 8))
        elif t[0] == "v":
            c = 8 * (t[2] // 8)
            form = {"raw16": "vRaw16", "bitsZ": "vBitsZ", "bitsH": "vBitsH"}[v[0]]
            cands.append((form, half_of(c, w, pc), creg(t[1], t[2] - c)))
    elif v[0] == "bf16":
        t = v[1]
        need(t[0] == "ent", f"pc {pc}: bf16 payload of {t}")
        cands.append(("narrowC", sym_matrix(t[1], w, pc), creg(t[2], t[3])))
    elif v[0] == "pair":
        lo = v[1]
        t = lo[1]
        if lo[0] == "raw16":
            m = ("valueBlock", (16 * (t[2] // 16) - 32 * w) // 16)
            cands += [("rawA", m, r) for r in range(4)]
        elif t[0] in ("kd", "qd"):
            cands += [("regA", ("keyBlock", t[0], t[2] // 16), r) for r in range(4)]
        elif t[0] == "kr":
            cands += [("regA", ("keyBlockT", "kr", t[2] // 16), r) for r in range(4)]
        elif t[0] in ("inv", "mqk"):
            cands += [("regA", (t[0],), r) for r in range(4)]
        elif t[0] == "copy":
            m = ("stateBlock", half_of(8 * (t[2] // 8), w, pc), t[1] // 16)
            cands += [("regB", m, r) for r in range(2)]
        elif t[0] == "ent":
            m = sym_matrix(t[1], w, pc)
            cands += [("rowPair", m, p) for p in range(2)] + [("regB", m, r) for r in range(2)]
    for d in cands:
        if all(expand(d, w, lane) == vals[lane] for lane in range(32)):
            return d
    raise Fail(f"pc {pc}: no lane-independent description of {reg} (lane {l} holds {v})")


# ---------------------------------------------------------------------------------------------
# Rendering descriptions: Lean terms of Math/Fragments.lean (variables `x : Inputs`, warp `w`,
# lane `l`).

ARRAY_FIELD = {
    "kd": "x.decayedKey",
    "qd": "x.decayedQuery",
    "kr": "x.restoredKey",
    "inv": "x.inverse",
    "mqk": "x.score",
}


def lean_base(bh):
    return f"(halfBase w {bh[0]} {bh[1]})"


def lean_matrix(m):
    if m[0] == "keyBlock":
        return f"keyBlock {ARRAY_FIELD[m[1]]} {m[2]}"
    if m[0] == "keyBlockT":
        return f"keyBlockT {ARRAY_FIELD[m[1]]} {m[2]}"
    if m[0] in ("inv", "mqk"):
        return ARRAY_FIELD[m[0]]
    if m[0] == "stateBlock":
        return f"stateBlock x.copy {lean_base(m[1])} {m[2]}"
    if m[0] == "project":
        return f"project {ARRAY_FIELD[m[1]]} x.copy {lean_base(m[2])} {m[3]}"
    if m[0] in ("residual", "correction", "output"):
        return f"{m[0]} x {lean_base(m[1])}"
    if m[0] in ("update", "nextState"):
        return f"{m[0]} x {lean_base(m[1])} {m[2]}"
    if m[0] == "valueBlock":
        return f"fun i k => x.value i (halfBase w {m[1]} 0 + k)"
    if m[0] == "zero":
        return "fun _ _ => 0"
    raise Fail(f"matrix {m}")


def text_matrix(m):
    """A short reading of a matrix term in the names of the source."""

    def half(bh):
        return f"[block 2w+{bh[0]}, columns {8 * bh[1]}..{8 * bh[1] + 7}]"

    if m[0] == "keyBlock":
        return f"{SOURCE_NAME[m[1]]}[:, keys {16 * m[2]}..{16 * m[2] + 15}]"
    if m[0] == "keyBlockT":
        return f"{SOURCE_NAME[m[1]]}[:, keys {16 * m[2]}..{16 * m[2] + 15}]^T"
    if m[0] in ("inv", "mqk"):
        return SOURCE_NAME[m[0]]
    if m[0] == "stateBlock":
        return f"state copy[keys {16 * m[2]}..{16 * m[2] + 15}]{half(m[1])}"
    if m[0] == "project":
        acc = "u_acc" if m[1] == "kd" else "out_acc"
        return f"{acc}{half(m[2])} after {m[3]} key block{'s' if m[3] != 1 else ''}"
    if m[0] == "residual":
        return f"residual{half(m[1])}"
    if m[0] == "correction":
        return f"U{half(m[1])}"
    if m[0] == "output":
        return f"out{half(m[1])}"
    if m[0] == "update":
        return f"acc{half(m[1])} of key block {m[2]}"
    if m[0] == "nextState":
        return f"new state{half(m[1])} of key block {m[2]}"
    if m[0] == "valueBlock":
        return f"v[:, block 2w+{m[1]}] (bf16 bit patterns)"
    if m[0] == "zero":
        return "0"
    raise Fail(f"matrix {m}")


def lean_desc(desc):
    """(value shape, Lean term(s) of the real number(s), library layout name or None)."""
    form = desc[0]
    if form == "zero":
        return {"shape": "zero word (.bits 32 0)", "real": "0"}
    if form in ("regA", "rawA"):
        _, m, r = desc
        mm = f"({lean_matrix(m)})"
        shape = (
            "pair of bf16 bit patterns (or payload zeros)"
            if form == "rawA"
            else "pair of bf16 payloads"
        )
        return {
            "shape": shape,
            "layout": "WarpMatrix.regA" if form == "regA" else "WarpMatrix.aRow/aCol",
            "matrix": lean_matrix(m),
            "index": r,
            "real": [f"{mm} (aRow l {r}) (aCol l {r} {h})" for h in range(2)],
        }
    if form == "regB":
        _, m, r = desc
        mm = f"({lean_matrix(m)})"
        return {
            "shape": "pair of bf16 payloads",
            "layout": "WarpMatrix.regB",
            "matrix": lean_matrix(m),
            "index": r,
            "real": [f"{mm} (bRow l {r} {h}) (bCol l)" for h in range(2)],
        }
    if form == "regC":
        _, m, r = desc
        return {
            "shape": "f32 payload",
            "layout": "WarpMatrix.regC",
            "matrix": lean_matrix(m),
            "index": r,
            "real": f"({lean_matrix(m)}) (cRow l {r}) (cCol l {r})",
        }
    if form == "rowPair":
        _, m, p = desc
        mm = f"({lean_matrix(m)})"
        return {
            "shape": "pair of bf16 payloads",
            "layout": "Fragments.rowPair",
            "matrix": lean_matrix(m),
            "index": p,
            "real": [f"{mm} (cRow l {2 * p + h}) (cCol l {2 * p + h})" for h in range(2)],
        }
    if form == "narrowC":
        _, m, r = desc
        return {
            "shape": "bf16 payload (16-bit register)",
            "matrix": lean_matrix(m),
            "index": r,
            "real": f"({lean_matrix(m)}) (cRow l {r}) (cCol l {r})",
        }
    if form in ("vRaw16", "vBitsZ", "vBitsH", "diff"):
        _, bh, r = desc
        v = f"x.value (cRow l {r}) ({lean_base(bh)} + cCol l {r})"
        if form == "diff":
            p = f"project x.decayedKey x.copy {lean_base(bh)} 8 (cRow l {r}) (cCol l {r})"
            return {"shape": "f32 payload", "real": f"{v} - {p}"}
        shape = {
            "vRaw16": "bf16 bit pattern (16-bit register), or a payload zero",
            "vBitsZ": "32-bit word: the bf16 bit pattern zero-extended",
            "vBitsH": "32-bit word: the bf16 bit pattern in the high half (reads as the f32 number)",
        }[form]
        return {"shape": shape, "real": v}
    if form in ("logitZ", "logitH", "logitK", "logitE", "logitP", "gate"):
        row = f"(l / 4 + {8 * desc[1]})" if desc[1] else "(l / 4)"
        x = f"x.logit {row}"
        table = {
            "logitZ": ("32-bit word: the bf16 bit pattern zero-extended", x),
            "logitH": (
                "32-bit word: the bf16 bit pattern in the high half (reads as the f32 number)",
                x,
            ),
            "logitK": ("f32 payload", f"{x} * (multiplier : ℝ)"),
            "logitE": ("f32 payload", f"Real.rpow 2 ({x} * (multiplier : ℝ))"),
            "logitP": ("f32 payload", f"Real.rpow 2 ({x} * (multiplier : ℝ)) + 1"),
            "gate": ("f32 payload", f"gate x {row}"),
        }
        return {"shape": table[form][0], "real": table[form][1]}
    if form == "decay":
        return {
            "shape": "f32 payload",
            "real": f"x.totalDecay ({16 * desc[1]} + l / 4 + {8 * desc[2]})",
        }
    raise Fail(f"description {desc}")


def plain(x):
    """A description as nested lists (the structured form `Gen/values.py` reads)."""
    return [plain(y) for y in x] if isinstance(x, (tuple, list)) else x


def json_desc(desc):
    out = {"form": desc[0], "desc": plain(desc)}
    out.update(lean_desc(desc))
    return out


# ---------------------------------------------------------------------------------------------
# The table.


def build():
    code, envs, body, ids = load_body()
    data = analysis.data_registers(code)
    check_preloop(code)
    loads = check_load_destinations(code)
    addr, mem_pcs = address_table(code, body, data)
    forms = {pc: address_form(pc, addr[pc]) for pc in mem_pcs}

    warps = []
    for w in range(4):
        sim = Warp(code, body, data, addr, w)
        sim.run()
        warps.append(sim)

    checks = collections.OrderedDict()
    matrix_pcs = [
        pc
        for pc in body
        if code[pc]["opcode"].startswith(("ldmatrix", "stmatrix", "movmatrix", "mma."))
    ]
    kinds = collections.Counter(code[pc]["opcode"].split(".")[0] for pc in matrix_pcs)
    need(len(matrix_pcs) == 182, f"{len(matrix_pcs)} matrix instructions")
    need(kinds == {"ldmatrix": 44, "mma": 104, "movmatrix": 16, "stmatrix": 18}, f"kinds {kinds}")
    checks["matrix_instructions"] = (
        "182 = 44 ldmatrix + 104 mma + 16 movmatrix + 18 stmatrix, in one straight line"
    )
    checks["tensor_load_destinations"] = (
        "the stage offsets of v, beta, k_decayed, q_decayed, k_restored, g_total, INV, Mqk are the "
        f"destinations of the 70 tensor loads of a tile {dict(loads)}; workspace piece i has first coordinate 8 i"
    )
    checks["address_forms"] = (
        f"{len(mem_pcs)} memory instructions: every address is shared_mem + constant + 18048 s + 4096 o + 2 k "
        "+ weights of the bits of the thread index, for all 128 threads"
    )

    # -- descriptions of all data registers, identical in the four warps ---------------------
    written = collections.defaultdict(list)
    for pc in body:
        for r in code[pc]["writes"]:
            if r in data:
                written[r].append(pc)
    carry_regs = sorted(
        (r for r, pcs in written.items() if code[pcs[0]]["opcode"].startswith("fma")),
        key=lambda r: int(r[2:]),
    )
    for r, pcs in written.items():
        need(len(pcs) == 1, f"{r} is written {len(pcs)} times in the loop body")
    checks["single_assignment"] = (
        f"each of the {len(written)} data registers written in the body is written once"
    )

    reg_desc = {}
    for pc in body:
        if pc not in warps[0].values:
            continue
        for reg in warps[0].values[pc]:
            descs = [describe(wp.values[pc][reg], wp.w, pc, reg) for wp in warps]
            need(
                len(set(descs)) == 1,
                f"pc {pc}: {reg} is described differently in the warps: {descs}",
            )
            reg_desc[reg] = (pc, descs[0])
    need(set(reg_desc) == set(written), "a written data register has no description")
    checks["lane_descriptions"] = (
        f"{len(reg_desc)} registers: the layout description (regA / regB / regC / rowPair / scalar forms) "
        "expands to the simulated value in all 32 lanes of all 4 warps"
    )

    # -- carries -----------------------------------------------------------------------------
    carry = {}
    cover = set()
    for wp in warps:
        for lane in range(32):
            uses = wp.carry_use[lane]
            need(
                len(uses) == 128 and len({u[0] for u in uses}) == 128,
                "128 distinct carries per lane",
            )
            need(len({(u[2], u[3]) for u in uses}) == 128, "carry entries of a lane are distinct")
            for reg, pc, key, ch, c, m, i, j in uses:
                bh = half_of(c, wp.w, pc)
                r = next(r for r in range(4) if (c_row(lane, r), c_col(lane, r)) == (i, j))
                rec = (pc, m, bh, r)
                need(
                    carry.setdefault(reg, rec) == rec, f"{reg}: carry position depends on the lane"
                )
                need((key, ch) not in cover, f"state entry {(key, ch)} is carried twice")
                cover.add((key, ch))
    need(
        sorted(carry, key=lambda r: int(r[2:])) == [f"%r{n}" for n in range(1812, 1940)],
        "carry registers",
    )
    need(
        carry_regs == sorted(carry, key=lambda r: int(r[2:])), "carry registers are the fma targets"
    )
    need(cover == {(k, c) for k in range(128) for c in range(128)}, "the carries cover the state")
    checks["carries"] = (
        "%r1812..%r1939 are each read and written by exactly one fma per tile; the carry of "
        "(key block m, value block bi, half q, C register r) of lane l of warp w is the state entry "
        "(key 16 m + cRow l r, channel halfBase w bi q + cCol l r); the 128 x 128 threads x registers "
        "cover the 128 x 128 state exactly once"
    )

    # -- the raw values ------------------------------------------------------------------------
    raw = [r for r, (_, d) in reg_desc.items() if d[0] == "rawA"]
    need(len(raw) == 8, f"{len(raw)} registers of raw values")
    for wp in warps:
        for r in raw:
            for v in wp.values[reg_desc[r][0]][r]:
                # ("pair", ("raw16", ("v", row, channel)), ("raw16", ("v", row, channel + 1)))
                need(v[1][1][1] == v[2][1][1] and v[1][1][2] + 1 == v[2][1][2], f"{r}: halves {v}")
    checks["value_registers"] = (
        "the two halves of each of the 8 registers loaded from v are neighbouring channels of one token row, "
        "so a register is two bit patterns (a 32-bit word) or, for a token past the end of the array, two "
        "payload zeros; it is never one of each"
    )

    carry_io = check_carry_io(code, carry)
    checks["carry_io"] = (
        "outside the loop: the generic load (positions 765..1400) and the generic store (3132..3767) of each "
        "carry address the FP32 state buffer entry [value channel][key feature] that the loop gives the register"
    )

    # -- memory: what is read, what is written ------------------------------------------------
    acc_read = set().union(*(wp.reads["state_acc"] for wp in warps))
    acc_written = {}
    out_written = {}
    for wp in warps:
        for off, (v, pc, s) in wp.mem.items():
            d = decode(off, 2)
            need(v[0] == "bf16" and v[1][0] == "ent", f"pc {pc}: stored value {v}")
            m, i, j = v[1][1], v[1][2], v[1][3]
            if d[0] == "state_acc":
                need(m[0] == "nextState", f"pc {pc}: {m} stored into state_acc")
                # position (value channel n, key feature k) receives the new state of (k, n)
                need(
                    (16 * m[2] + i, m[1] + j) == (d[2], d[1]),
                    f"pc {pc}: state_acc position {d} gets {(m, i, j)}",
                )
                need(off not in acc_written, f"state_acc offset {off} written by two warps")
                acc_written[off] = (wp.w, s)
            else:
                need(d[0] == "out" and m[0] == "output", f"pc {pc}: {m} stored at {d}")
                need(
                    (i, m[1] + j) == (d[1], d[2]), f"pc {pc}: output position {d} gets {(m, i, j)}"
                )
                need(off not in out_written, f"output offset {off} written by two warps")
                out_written[off] = (wp.w, s)
    need(
        acc_read == set(range(0, 32768, 2)) == set(acc_written),
        "state_acc is read and rewritten whole",
    )
    need(set(out_written) == set(range(OUT0, OUT0 + OUT, 2)), "the output stage is written whole")
    for wp in warps:
        rd = collections.defaultdict(set)
        wr = collections.defaultdict(set)
        for pc, rows in wp.rows.items():
            if decode(rows[0], 2)[0] != "state_acc":
                continue
            for s in range(32):
                (rd if code[pc]["opcode"].startswith("ld") else wr)[s].add(rows[s])
        for s in range(32):
            need(
                rd[s] == wr[s] and len(rd[s]) == 16,
                f"warp {wp.w} lane {s}: state_acc rows read != written",
            )
    first_write = min(
        pc
        for wp in warps
        for pc, rows in wp.rows.items()
        if code[pc]["opcode"].startswith("st") and decode(rows[0], 2)[0] == "state_acc"
    )
    last_read = max(
        pc
        for wp in warps
        for pc, rows in wp.rows.items()
        if code[pc]["opcode"].startswith("ld") and decode(rows[0], 2)[0] == "state_acc"
    )
    need(last_read < first_write, "a state_acc read follows a state_acc write in the body")
    checks["state_acc"] = (
        "each lane reads 16 rows of state_acc (phase 1) and writes the same 16 rows (phase 6, after all reads); "
        "the rows of the 128 lanes partition state_acc; the element at (value channel n, key feature k) is read as "
        "copy[k][n] and rewritten with the bf16 payload of nextState for (k, n)"
    )
    checks["output_stage"] = (
        "the two stmatrix of the four warps write the output stage whole; the element of (row t, channel ch) "
        "is the bf16 payload of output for (t, ch)"
    )
    for name in ("kd", "qd", "kr", "inv", "mqk", "gt"):
        start, size, eb = ARRAYS[name]
        for wp in warps:
            need(
                wp.reads[name] == set(range(STAGE0 + start, STAGE0 + start + size, eb)),
                f"warp {wp.w} reads {name} partly",
            )
    for wp in warps:
        s0 = STAGE0 + 1024 * wp.w
        need(wp.reads["v"] == set(range(s0, s0 + 1024, 2)), f"warp {wp.w}: v elements read")
        need(
            wp.reads["beta"] == set(range(STAGE0 + 4096, STAGE0 + 4096 + 32, 2)),
            f"warp {wp.w}: beta elements read",
        )
    checks["stage_reads"] = (
        "every warp reads k_decayed, q_decayed, k_restored, g_total, INV, Mqk whole, the 16 x 32 block of v "
        "of its channels, and the 16 gate logits at elements k .. k + 15 of the 32-element beta buffer"
    )

    # -- the products ------------------------------------------------------------------------
    products = []
    for pc in matrix_pcs:
        if not code[pc]["opcode"].startswith("mma."):
            continue
        terms = [tuple(sym_matrix(m, wp.w, pc) for m in wp.operands[pc]) for wp in warps]
        need(len(set(terms)) == 1, f"pc {pc}: the product differs between the warps")
        products.append((pc, terms[0]))
    halves = [(bi, q) for bi in range(2) for q in range(2)]
    expected = []
    for m in range(8):  # phase 1: per key block, per value block, u then out, per half
        for bi in range(2):
            for arr in ("kd", "qd"):
                for q in range(2):
                    expected.append(("project", arr, (bi, q), m + 1))
    expected += [("correction", h) for h in halves]  # phase 3
    expected += [("output", h) for h in halves]  # phase 4
    for m in range(8):  # phase 6
        expected += [("update", h, m) for h in halves]
    # Phases 3 and 4 interleave by value block in the code order of the source; compare as the
    # source orders them: (correction block 0 halves, correction block 1 halves) etc.
    need(
        [t[3] for _, t in products] == expected,
        "the order of the products is not that of Math/Fragments.lean",
    )
    checks["products"] = (
        "the 104 multiply-accumulates are, in order: 64 of phase 1 (key block m = 0..7; value block; u then out; "
        "half), 4 corrections, 4 outputs, 32 updates (key block m; value block; half); every A, B and C operand "
        "is recognized entry by entry in all four warps"
    )

    # -- liveness: what an invariant at a matrix instruction has to carry ----------------------
    live = analysis.liveness(code, sorted(envs))
    head = sorted(r for r in live[LO] if r in data)
    need(head == sorted(carry), f"data registers live at the loop head: {head[:8]}…")
    order = {pc: i for i, pc in enumerate(body)}
    for pc in matrix_pcs:
        for r in live[pc]:
            if r in data and r not in carry:
                need(
                    r in reg_desc and order[reg_desc[r][0]] < order[pc],
                    f"pc {pc}: live register {r} has no meaning yet",
                )
    checks["liveness"] = (
        "the only data registers live around the back edge are the 128 carries; every data register live at "
        "a matrix instruction was given its meaning by an earlier instruction of the same iteration"
    )

    # -- assemble ------------------------------------------------------------------------------
    def region(pc):
        return decode(warps[0].rows[pc][0], 2)[0]

    def desc_of(r):
        return ("zero",) if r == "%r862" else reg_desc[r][1]

    def reg_key(r):
        return (r[1:3] == "rs", int(re.sub(r"\D", "", r)))

    # which stmatrix rewrites the rows a state_acc load reads (the same rows, lane by lane)
    acc_store = {}
    for pc in matrix_pcs:
        if code[pc]["opcode"].startswith("stmatrix") and region(pc) == "state_acc":
            acc_store[tuple(tuple(wp.rows[pc]) for wp in warps)] = pc

    def phase(pc, kind, arr=None):
        """The phase of the source (`fwd_kernel2.cuh`) an instruction belongs to."""
        if kind == "ldmatrix":
            return {"kd": 1, "qd": 1, "state_acc": 1, "v": 2, "inv": 2, "mqk": 4, "kr": 6}[arr]
        if kind == "stmatrix":
            return 5 if arr == "out" else 6
        if kind == "movmatrix":
            return {"residual": 3, "correction": 4}[reg_desc[code[pc]["operands"][1]][1][1][0]]
        return {"project": 1, "correction": 3, "output": 4, "update": 6}[dict(products)[pc][3][0]]

    table = []
    n_mma = 0
    for n, pc in enumerate(matrix_pcs):
        ins = code[pc]
        kind = ins["opcode"].split(".")[0]
        row = {"ordinal": n, "pc": pc, "kind": kind, "opcode": ins["opcode"]}
        arr = None
        if kind in ("ldmatrix", "stmatrix"):
            f = forms[pc]
            arr = region(pc)
            row["trans"] = ".trans." in ins["opcode"]
            row["array"] = SOURCE_NAME[arr]
            row["address"] = {
                "register": parse_addr(addr_operand(ins))[0],
                "form": form_text(f),
                **f,
            }
            text, elem = row_elems(arr, f)
            for wp in warps:
                for lane in range(32):
                    for j in range(8):
                        got = decode(wp.rows[pc][lane] + 2 * j, 2)
                        need(
                            got == elem(wp.w, lane, j),
                            f"pc {pc}: row of lane {lane} of warp {wp.w}",
                        )
            row["row_of_lane"] = text
        if kind == "ldmatrix":
            dsts = operand_regs(ins["operands"][0])
            row["dst"] = dsts
            descs = [reg_desc[r][1] for r in dsts]
            row["meaning"] = load_text(descs)
            if arr == "state_acc":
                st = acc_store.get(tuple(tuple(wp.rows[pc]) for wp in warps))
                need(
                    st is not None,
                    f"pc {pc}: no stmatrix rewrites exactly the rows this load reads",
                )
                row["bytes_from"] = (
                    f"the same lane's stmatrix at position {st} in the previous tile; in the first tile the "
                    "conversion loop (positions 388..618)"
                )
                row["rewritten_at"] = st
            elif arr == "v":
                row["bytes_from"] = (
                    "the tensor loads of v of this tile into input stage s: bf16 bit patterns of the array, "
                    "bf16 payload zeros where the box is past the end of the array"
                )
            else:
                row["bytes_from"] = (
                    f"the tensor loads of {SOURCE_NAME[arr]} of this tile into input stage s: bf16 payloads"
                )
        elif kind == "stmatrix":
            srcs = operand_regs(ins["operands"][1])
            row["src"] = srcs
            descs = [reg_desc[r][1] for r in srcs]
            need(
                [d[0] for d in descs] == ["rowPair"] * 4 and [d[2] for d in descs] == [0, 1, 0, 1],
                f"pc {pc}: stored fragments",
            )
            need(
                descs[0][1] == descs[1][1] and descs[2][1] == descs[3][1],
                f"pc {pc}: stored matrices",
            )
            need(
                descs[0][1][1] == (descs[0][1][1][0], 0)
                and descs[2][1][1] == (descs[0][1][1][0], 1),
                f"pc {pc}: stored halves",
            )
            row["matrices"] = [lean_matrix(descs[0][1]), lean_matrix(descs[2][1])]
            row["meaning"] = f"store {text_matrix(descs[0][1])} and {text_matrix(descs[2][1])}" + (
                " transposed into state_acc" if row["trans"] else " into the output stage"
            )
        elif kind == "movmatrix":
            dst, src = ins["operands"]
            row["dst"] = [dst]
            row["src"] = [src]
            ds, dd = reg_desc[src][1], reg_desc[dst][1]
            need(
                ds[0] == "rowPair" and dd[0] == "regB" and ds[1:] == dd[1:],
                f"pc {pc}: movmatrix {ds} -> {dd}",
            )
            row["meaning"] = (
                f"B register {dd[2]} of {text_matrix(dd[1])}, from the packed C fragment of its rows "
                f"{8 * dd[2]}..{8 * dd[2] + 7}"
            )
        else:
            d, a, b, c = (operand_regs(o) for o in ins["operands"])
            ma, mb, mc, md = dict(products)[pc]
            for regs, m, form in ((a, ma, "regA"), (b, mb, "regB")):
                for r, reg in enumerate(regs):
                    need(
                        desc_of(reg) == (form, m, r),
                        f"pc {pc}: operand register {reg} is {desc_of(reg)}",
                    )
            for r, reg in enumerate(c):
                want = ("zero",) if mc == ("zero",) else ("regC", mc, r)
                need(desc_of(reg) == want, f"pc {pc}: C register {reg} is {desc_of(reg)}")
            for r, reg in enumerate(d):
                need(reg_desc[reg][1] == ("regC", md, r), f"pc {pc}: D register {reg}")
            row["product"] = n_mma
            n_mma += 1
            row["A"] = {"regs": a, "matrix": lean_matrix(ma)}
            row["B"] = {"regs": b, "matrix": lean_matrix(mb)}
            row["C"] = {"regs": c, "matrix": lean_matrix(mc)}
            row["D"] = {"regs": d, "matrix": lean_matrix(md)}
            row["meaning"] = (
                f"{text_matrix(md)} := {text_matrix(mc)} + {text_matrix(ma)} @ {text_matrix(mb)}"
            )
            row["lean"] = f"Math.Fragments.Table.mma_{pc}"
        row["phase"] = phase(pc, kind, arr)
        row["live_data"] = sorted((r for r in live[pc] if r in data), key=reg_key)
        table.append(row)
    need(
        [r["phase"] for r in table] == sorted(r["phase"] for r in table),
        "the phases are not consecutive",
    )
    checks["mma_operands"] = (
        "at each of the 104 mma the four A registers are regA of its A matrix (index 0..3), the two B registers "
        "regB of its B matrix, the four C registers regC of its C matrix or the zero word, the four D registers "
        "regC of the result"
    )
    checks["row_contents"] = (
        "for each of the 62 ldmatrix/stmatrix and every lane of every warp, the eight elements of the lane's "
        "16-byte row are the array elements stated in row_of_lane"
    )
    checks["phases"] = (
        "the six phases of the source are consecutive ranges of matrix instructions: "
        + ", ".join(
            f"phase {ph}: {min(r['ordinal'] for r in table if r['phase'] == ph)}..{max(r['ordinal'] for r in table if r['phase'] == ph)}"
            for ph in range(1, 7)
        )
    )

    scalar = []
    for pc in body:
        ins = code[pc]
        if pc in matrix_pcs or pc not in warps[0].values:
            continue
        row = {"pc": pc, "opcode": ins["opcode"], "operands": ins["operands"]}
        if pc in forms:
            f = forms[pc]
            arr = decode(addr[pc][(0, 0, 0, 0)], 2 if ins["opcode"].endswith("b16") else 4)[0]
            want = (STAGE, 0, 2) if arr == "beta" else (STAGE, 0, 0)
            need(
                (f["stage"], f["out_stage"], f["gate_offset"]) == want,
                f"pc {pc}: stage coefficients of {arr}",
            )
            need(
                f["tid_bits"]
                == ([0, 0, 2, 4, 8, 0, 0] if arr == "beta" else [0, 0, 4, 8, 16, 0, 0]),
                f"pc {pc}: scalar load form",
            )
            row["array"] = SOURCE_NAME[arr]
            row["address"] = {
                "register": parse_addr(addr_operand(ins))[0],
                "form": form_text(f),
                **f,
            }
            row["bytes_from"] = (
                "the tensor load of beta of this tile into input stage s (64 bytes from the element "
                "8 * (index / 8) of the array): bf16 bit patterns, payload zeros past the end of the array"
                if arr == "beta"
                else "the tensor load of g_total of this tile into input stage s: f32 payloads"
            )
            # the invariant of the value induction at a scalar load carries these registers
            row["live_data"] = sorted((r for r in live[pc] if r in data), key=reg_key)
        row["dst"] = ins["writes"]
        scalar.append(row)
    counts = collections.Counter(s["opcode"] for s in scalar)

    carries = {
        reg: {
            "id": ids[reg],
            "fma_pc": pc,
            "key_block": m,
            "value_block": bh[0],
            "half": bh[1],
            "c_register": r,
            "before": f"x.carry ({16 * m} + cRow l {r}) (halfBase w {bh[0]} {bh[1]} + cCol l {r})",
            "after": f"nextState x (halfBase w {bh[0]} {bh[1]}) {m} (cRow l {r}) (cCol l {r})",
            **carry_io[reg],
        }
        for reg, (pc, m, bh, r) in sorted(carry.items(), key=lambda kv: int(kv[0][2:]))
    }
    registers = {
        r: {"id": ids[r], "def_pc": reg_desc[r][0], **json_desc(reg_desc[r][1])}
        for r in sorted(reg_desc, key=lambda r: (reg_desc[r][0], reg_key(r)))
    }
    registers["%r862"] = {
        "id": ids["%r862"],
        "def_pc": 2199,
        **json_desc(("zero",)),
        "note": "a control register: the cleared accumulator",
    }
    need(
        code[2199]["opcode"] == "mov.b32" and code[2199]["operands"] == ["%r862", "0"],
        "pc 2199 is not the zero word",
    )
    out = {
        "source": "Kernels/FlashKdaFwd/packed_fp32_sm100a.ptx, instructions 2135..2944 (compute threads)",
        "variables": {
            "x": "Math.Fragments.Inputs: the real arrays of the tile",
            "w": "warp 0..3 (thread index / 32)",
            "l": "lane 0..31 (thread index % 32)",
            "j": "element 0..7 of a 16-byte row",
            "s": "input stage 0..2 (%r1802)",
            "o": "output stage 0..1 (%r1804)",
            "k": "gate offset 0..7: (T_total * head + first token of the sequence) % 8 (%r840)",
            "halfBase w bi q": "16 * (2 w + bi) + 8 q: first channel of half q of value block bi of warp w",
        },
        "forms": {
            "regA": "pair register r of four: half h holds M (aRow l r) (aCol l r h); WarpMatrix.regA M l r",
            "regB": "pair register r of two: half h holds M (bRow l r h) (bCol l); WarpMatrix.regB M l r",
            "regC": "f32 register r of four: holds M (cRow l r) (cCol l r); WarpMatrix.regC M l r",
            "rowPair": (
                "pair register p of two: half h holds M (cRow l (2 p + h)) (cCol l (2 p + h)): the narrowed C "
                "registers 2 p and 2 p + 1 packed; equal to toFrag1 of rows 8 p .. 8 p + 7 of M (Math.Fragments.Layout)"
            ),
            "rawA": "as regA, but the halves are bf16 bit patterns of v (payload zeros where the load was out of bounds)",
            "narrowC": "16-bit register: the bf16 payload of M (cRow l r) (cCol l r)",
            "vRaw16 / vBitsZ / vBitsH": "one element of v at the C position r of a half: 16 bits / zero-extended / in the high half",
            "diff": "f32 payload of v - u at the C position r of a half",
            "logitZ / logitH / logitK / logitE / logitP / gate": "the steps of the gate of row l / 4 (+ 8)",
            "decay": "f32 payload of g_total of key feature 16 m + l / 4 (+ 8)",
            "zero": "the 32-bit zero word",
        },
        "layouts": {
            "state_acc": "bf16 [value channel n][key feature k] at byte 128*(n/8) + 2048*(k/8) + 16*(n%8) + 2*(k%8)",
            "stage arrays [row t][feature f]": "byte 256*(f/8) + 16*t + 2*(f%8) from the array's offset in input stage s",
            "array offsets in input stage (32768 + 18048 s)": {
                SOURCE_NAME[n]: v[0] for n, v in ARRAYS.items()
            },
            "output stage (86912 + 4096 o) [row t][channel c]": "byte 256*(c/8) + 16*t + 2*(c%8)",
            "FP32 state buffer (32768) [value channel n][key feature k]": (
                "float index 64*(n/8) + 1024*(k/8) + 8*(n%8) + k%8, before the swizzle of the address; the base "
                "entry of lane l of warp w is index 16*(l%4) + l/4 + 256*w, and buffer_offset of a carry is "
                "relative to it"
            ),
        },
        "checks": checks,
        "matrix": table,
        "scalar": scalar,
        "scalar_counts": dict(sorted(counts.items())),
        "carries": carries,
        "registers": registers,
    }
    return out, products


def row_elems(arr, f):
    """Which elements the 16-byte row of lane `l` of warp `w` holds, from the form of its address:
    a text for the table and the same as a function `(w, l, j) -> element` (element `j` of the
    row, `j = 0..7`), which the caller compares with the decoded address for every lane."""
    wts = f["tid_bits"]
    if arr == "state_acc":
        m = f["const"] // 4096
        bi = (f["const"] % 4096) // 256
        need(
            wts == [16, 32, 64, 2048, 128, 512, 1024] and f["const"] % 256 == 0,
            f"state_acc row form {f}",
        )
        need(
            (f["stage"], f["out_stage"], f["gate_offset"]) == (0, 0, 0),
            f"state_acc row depends on a stage {f}",
        )
        text = f"state[key {16 * m} + 8*(l/8%2) + j][channel halfBase w {bi} 0 + 8*(l/16) + l%8]"
        return text, lambda w, l, j: (  # noqa: E741
            "state_acc",
            32 * w + 16 * bi + 8 * (l // 16) + l % 8,
            16 * m + 8 * (l // 8 % 2) + j,
        )
    if arr == "out":
        bi = (f["const"] - OUT0) // 512
        need(wts == [16, 32, 64, 128, 256, 1024, 2048], f"output row form {f}")
        need((f["stage"], f["out_stage"], f["gate_offset"]) == (0, OUT, 0), f"output row stage {f}")
        text = f"out[row l%8 + 8*(l/8%2)][channel halfBase w {bi} 0 + 8*(l/16) + j]"
        return text, lambda w, l, j: (  # noqa: E741
            "out",
            l % 8 + 8 * (l // 8 % 2),
            32 * w + 16 * bi + 8 * (l // 16) + j,
        )
    need((f["stage"], f["out_stage"], f["gate_offset"]) == (STAGE, 0, 0), f"{arr} row stage {f}")
    rel = f["const"] - STAGE0 - ARRAYS[arr][0]
    if arr == "v":
        bi = rel // 512
        need(wts == [16, 32, 64, 128, 256, 1024, 2048], f"v row form {f}")
        text = f"v[row l%8 + 8*(l/8%2)][channel halfBase w {bi} 0 + 8*(l/16) + j]"
        return text, lambda w, l, j: (  # noqa: E741
            "v",
            l % 8 + 8 * (l // 8 % 2),
            32 * w + 16 * bi + 8 * (l // 16) + j,
        )
    m = rel // 512
    if arr == "kr":
        need(wts == [16, 32, 64, 256, 128, 0, 0], f"k_restored row form {f}")
        text = f"k_restored[row l%8 + 8*(l/16)][key {16 * m} + 8*(l/8%2) + j]"
        return text, lambda w, l, j: ("kr", l % 8 + 8 * (l // 16), 16 * m + 8 * (l // 8 % 2) + j)  # noqa: E741
    need(wts == [16, 32, 64, 128, 256, 0, 0], f"{arr} row form {f}")
    if arr in ("kd", "qd"):
        text = f"{SOURCE_NAME[arr]}[row l%8 + 8*(l/8%2)][key {16 * m} + 8*(l/16) + j]"
        return text, lambda w, l, j: (arr, l % 8 + 8 * (l // 8 % 2), 16 * m + 8 * (l // 16) + j)  # noqa: E741
    need(rel == 0, f"{arr} row offset")
    text = f"{SOURCE_NAME[arr]}[row l%8 + 8*(l/8%2)][column 8*(l/16) + j]"
    return text, lambda w, l, j: (arr, l % 8 + 8 * (l // 8 % 2), 8 * (l // 16) + j)  # noqa: E741


def load_text(descs):
    forms = [d[0] for d in descs]
    if forms == ["regA"] * 4:
        need(len({d[1] for d in descs}) == 1 and [d[2] for d in descs] == [0, 1, 2, 3], "A load")
        return f"A operand: {text_matrix(descs[0][1])}"
    if forms == ["rawA"] * 4:
        need(len({d[1] for d in descs}) == 1 and [d[2] for d in descs] == [0, 1, 2, 3], "v load")
        return f"{text_matrix(descs[0][1])} in the layout of an A operand"
    need(forms == ["regB"] * 4 and [d[2] for d in descs] == [0, 1, 0, 1], "B load")
    need(descs[0][1] == descs[1][1] and descs[2][1] == descs[3][1], "B load matrices")
    return f"B operands: {text_matrix(descs[0][1])} and {text_matrix(descs[2][1])}"


# ---------------------------------------------------------------------------------------------
# The Lean rendering of the products.

LEAN_HEAD = """-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Math.Fragments

@[expose] public section

/-!
# The 104 multiply-accumulates of one tile, as equations of `Math/Fragments.lean`

Generated by `Kernels/FlashKdaFwd/Gen/matrix_table.py` from the compiled kernel; do not edit.
For each `mma.sync` of the tile loop (named by its instruction position), in program order: the
result matrix `D` that the register table (`Gen/Tables/matrix_table.json`) assigns to its
destination registers equals `mmaReal A B C` of the matrices it assigns to its operand
registers. Every equation holds by unfolding the definitions (`rfl`), so the order in which the
compiled code accumulates is the order of the definitions of `Math/Fragments.lean`. `x` are the
real arrays of the tile and `w` is the warp; `halfBase w bi q` is the first value channel of
half `q` of value block `bi` of the warp.
-/

namespace PTX.Kernels.FlashKdaFwd.Math.Fragments.Table
open PTX.WarpMatrix (mmaReal)
noncomputable section

variable (x : Inputs) (w : ℕ)
"""

LEAN_TAIL = """
end
end PTX.Kernels.FlashKdaFwd.Math.Fragments.Table
"""


def wrap(prefix, text, width=100, indent="      "):
    """Break `text` at spaces so that no line exceeds `width`."""
    lines, cur = [], prefix
    for word in text.split(" "):
        if len(cur) + 1 + len(word) > width and cur.strip():
            lines.append(cur)
            cur = indent + word
        else:
            cur = cur + (" " if cur.strip() else "") + word
    lines.append(cur)
    return "\n".join(lines)


def render_lean(products, table):
    by_pc = {row["pc"]: row for row in table}
    parts = [LEAN_HEAD.rstrip("\n")]
    for pc, (a, b, c, d) in products:
        row = by_pc[pc]
        doc = f"/-- Matrix instruction {row['ordinal']} (position {pc}): {row['meaning']}. -/"
        parts.append("")
        parts.append(wrap("", doc, indent=""))
        parts.append(f"theorem mma_{pc} :")
        parts.append(wrap("    ", f"{lean_matrix(d)} ="))
        parts.append(
            wrap("      ", f"mmaReal ({lean_matrix(a)}) ({lean_matrix(b)}) ({lean_matrix(c)}) :=")
        )
        parts.append("  rfl")
    parts.append(LEAN_TAIL)
    return "\n".join(parts)


def render_json(out):
    """The table as JSON with one matrix instruction, scalar instruction or register per line."""

    def one(v):
        return json.dumps(v, ensure_ascii=False, separators=(", ", ": "))

    lines = ["{"]
    keys = list(out)
    for n, key in enumerate(keys):
        v = out[key]
        end = "," if n + 1 < len(keys) else ""
        if key in ("matrix", "scalar"):
            lines.append(f" {one(key)}: [")
            lines += [f"  {one(row)}{',' if i + 1 < len(v) else ''}" for i, row in enumerate(v)]
            lines.append(f" ]{end}")
        elif isinstance(v, dict) and key != "scalar_counts":
            lines.append(f" {one(key)}: {{")
            items = list(v.items())
            lines += [
                f"  {one(k)}: {one(x)}{',' if i + 1 < len(items) else ''}"
                for i, (k, x) in enumerate(items)
            ]
            lines.append(f" }}{end}")
        else:
            lines.append(f" {one(key)}: {one(v)}{end}")
    lines.append("}")
    return "\n".join(lines) + "\n"


def main():
    cli = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    cli.add_argument("--check", action="store_true", help="write nothing; fail if one is stale")
    args = cli.parse_args()
    try:
        out, products = build()
    except Fail as e:
        print(f"matrix_table: {e}", file=sys.stderr)
        return 1
    files = {OUT_JSON: render_json(out), OUT_LEAN: render_lean(products, out["matrix"])}
    outputs.write_or_check(files, args.check)
    if args.check:
        print("matrix_table: up to date")
        return 0
    kinds = collections.Counter(r["kind"] for r in out["matrix"])
    print(f"{len(out['matrix'])} matrix instructions {dict(kinds)}")
    print(
        f"{len(out['scalar'])} scalar data instructions, {len(out['registers']) - 1} data registers and the "
        f"zero register, {len(out['carries'])} carries"
    )
    for name, what in out["checks"].items():
        print(f"  ok {name}: {what}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
