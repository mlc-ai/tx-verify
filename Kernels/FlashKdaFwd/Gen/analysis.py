# SPDX-License-Identifier: Apache-2.0
"""Role-specialized control-flow and register-kind analysis of the FlashKDA recurrence entry.

Input: the frozen PTX. Output (`analyze()`): for each role class of a thread (decided by its
index in the block: compute `tid < 128`, load `128 <= tid < 160`, store `160 <= tid`), the code
reachable when the branches on the thread index are folded, the event sites, the local paths
between sites and the content kind of every register that is live at a site.

Nothing here is trusted: the Lean files generated from this analysis are checked by Lean against
the decoded program, so a mistake here makes a proof fail and cannot make a wrong one pass.

A library of the other scripts of this directory (`load` is how each of them reads the PTX). It
makes no file of the repository, so there is nothing to regenerate or to check. Its two
commands are reading aids:

    python3 Kernels/FlashKdaFwd/Gen/analysis.py            # summary
    python3 Kernels/FlashKdaFwd/Gen/analysis.py --json F   # full dump into the file F
"""

import argparse
import collections
import json
import re
import sys
from pathlib import Path

KERNEL = Path(__file__).resolve().parents[1]
ROOT = KERNEL.parents[1]
sys.path.insert(0, str(ROOT / "Tools"))
import flow_gen  # noqa: E402
import parse_ptx  # noqa: E402

PTX = KERNEL / "packed_fp32_sm100a.ptx"
ROLES = {"compute": (0, 127), "load": (128, 159), "store": (160, 191)}
M32 = (1 << 32) - 1
TERMINAL = ("ret", "trap", "brkpt")


def short(text: str) -> str:
    """A mangled parameter name as `PARAM<i>`."""
    return re.sub(r"_Z25_flash_kda\w*_param_(\d+)", r"PARAM\1", text)


def load():
    flow_gen.CORE_EVENTS = True
    program = parse_ptx.parse(PTX.read_text())
    function = next(f for f in program.functions if not f.declaration)
    code = flow_gen.flatten(function)
    for ins in code:
        ins["operands"] = [short(o) for o in ins["operands"]]
    ids = flow_gen.register_ids(function)
    widths = {}

    def walk(body, path):
        for i, s in enumerate(body):
            if s.kind == "declaration" and s.tokens and s.tokens[0] == ".reg":
                for _, count, target in flow_gen.scope_bindings([s], path):
                    names = [target] if count == 0 else [f"{target}{k}" for k in range(count)]
                    for n in names:
                        widths[n] = s.tokens[1]
            elif s.kind == "scope":
                walk(s.body, f"{path}/{i}")

    walk(function.body, "")
    return code, ids, widths


class RoleFold:
    """Values of registers that depend only on the thread index, tabulated over a role's range."""

    def __init__(self, lo, hi):
        self.range = list(range(lo, hi + 1))

    def const(self, v):
        return tuple(v & M32 for _ in self.range)

    def eval(self, ins, env):
        op, ops = ins["opcode"], ins["operands"]

        def val(o):
            if re.fullmatch(r"-?\d+", o):
                return self.const(int(o))
            return env.get(o)

        def lift(f, *args):
            vs = [val(a) for a in args]
            if any(v is None for v in vs):
                return None
            return tuple(f(*xs) for xs in zip(*vs))

        if op == "mov.u32" and ops[1] == "%tid.x":
            return tuple(self.range)
        if op.startswith("setp.") and len(ops) == 3:
            cmp, ty = op.split(".")[1], op.split(".")[2]
            table = {
                "lt": lambda a, b: a < b,
                "gt": lambda a, b: a > b,
                "le": lambda a, b: a <= b,
                "ge": lambda a, b: a >= b,
                "eq": lambda a, b: a == b,
                "ne": lambda a, b: a != b,
            }
            if cmp not in table or (ty.startswith(("s", "f")) and cmp not in ("eq", "ne")):
                return None
            return lift(lambda a, b: int(table[cmp](a, b)), ops[1], ops[2])
        if op == "selp.b32":
            return lift(lambda a, b, c: a if c else b, ops[1], ops[2], ops[3])
        if op in ("mov.b32", "mov.s32", "mov.u32") and len(ops) == 2:
            return val(ops[1])
        if op == "mov.pred" and len(ops) == 2:
            return lift(lambda a: int(a != 0), ops[1])
        if op in ("or.pred", "and.pred"):
            a, b = val(ops[1]), val(ops[2])
            absorbing = all if op == "or.pred" else (lambda x: not any(x))
            for x in (a, b):
                if x is not None and absorbing(x):
                    return self.const(1 if op == "or.pred" else 0)
            f = (lambda p, q: p | q) if op == "or.pred" else (lambda p, q: p & q)
            return lift(f, ops[1], ops[2])
        if op == "not.pred":
            return lift(lambda a: 1 - a, ops[1])
        if op == "and.b32":
            return lift(lambda a, b: a & b, ops[1], ops[2])
        if op == "or.b32":
            return lift(lambda a, b: a | b, ops[1], ops[2])
        if op in ("xor.b32", "xor.pred"):
            return lift(lambda a, b: a ^ b, ops[1], ops[2])
        if op == "shl.b32":
            return lift(lambda a, b: (a << b) & M32 if b < 32 else 0, ops[1], ops[2])
        if op == "shr.u32":
            return lift(lambda a, b: a >> b if b < 32 else 0, ops[1], ops[2])
        if op in ("add.s32", "add.u32"):
            return lift(lambda a, b: (a + b) & M32, ops[1], ops[2])
        if op in ("sub.s32", "sub.u32"):
            return lift(lambda a, b: (a - b) & M32, ops[1], ops[2])
        return None


def successors(code, pc, env):
    """Control successors of `pc` with role-constant guards folded: (target, condition)."""
    ins = code[pc]
    g = ins["guard"]
    if ins["opcode"].startswith(TERMINAL):
        return []
    if ins["opcode"].split(".")[0] == "bra":
        if g is None:
            return [(ins["target"], None)]
        v = env.get(g["register"])
        if v is not None and len(set(v)) == 1:
            taken = bool(v[0]) != g["negated"]
            return [(ins["target"] if taken else pc + 1, None)]
        return [
            (ins["target"], (g["register"], not g["negated"])),
            (pc + 1, (g["register"], g["negated"])),
        ]
    return [(pc + 1, None)] if pc + 1 < len(code) else []


def reachable(code, role):
    """The reachable pcs of a role and the folded environment before each."""
    fold = RoleFold(*ROLES[role])
    envs = {0: {}}
    work = [0]
    while work:
        pc = work.pop()
        env = dict(envs[pc])
        ins = code[pc]
        succ = successors(code, pc, env)
        if not ins["opcode"].startswith(TERMINAL) and ins["opcode"].split(".")[0] != "bra":
            out = None
            if not ins["event"] and ins["guard"] is None:
                out = fold.eval(ins, env)
            for w in ins["writes"]:
                if out is not None:
                    env[w] = out
                else:
                    env.pop(w, None)
        for target, _ in succ:
            if target not in envs:
                envs[target] = dict(env)
                work.append(target)
            else:
                old = envs[target]
                new = {k: v for k, v in old.items() if env.get(k) == v}
                if new != old:
                    envs[target] = new
                    work.append(target)
    return envs


DATA_SOURCES = (
    "ld.b32",
    "ld.shared.b16",
    "ld.shared.b32",
    "ld.shared.v4.b32",
    "ldmatrix",
    "mma.",
    "movmatrix",
)


def data_registers(code):
    """Registers whose content derives from memory-loaded data: the machines keep them as opaque
    values. The others (control registers) are words, predicates and pointers computed from the
    thread index, the parameters, the offsets array, shuffles, elections and polls."""
    data = set()
    changed = True
    while changed:
        changed = False
        for ins in code:
            if ins["opcode"].startswith(DATA_SOURCES) or any(r in data for r in ins["reads"]):
                for w in ins["writes"]:
                    if w not in data:
                        data.add(w)
                        changed = True
    return data


def local_paths(code, envs, start):
    """The local paths from `start` (the instruction after a site, or 0) to the next sites, with
    the guards that are constant in the role folded. Each path is the list of its local
    instruction indices, the branch decisions that are not folded, and the site it reaches
    (`None` when it runs into a terminal instruction, which is itself a site)."""
    out = []

    def walk(pc, pcs, conds, seen):
        while True:
            if pc >= len(code):
                raise ValueError(f"path from {start} runs off the code")
            ins = code[pc]
            if ins["event"]:
                out.append({"pcs": pcs, "conditions": conds, "to": pc})
                return
            if pc in seen:
                raise ValueError(f"local loop at {pc} on a path from {start}")
            seen = seen | {pc}
            pcs = [*pcs, pc]
            succ = successors(code, pc, envs.get(pc, {}))
            if len(succ) == 1:
                pc = succ[0][0]
                continue
            for target, cond in succ:
                walk(target, pcs, [*conds, (cond[0], cond[1], pc)], seen)
            return

    walk(start, [], [], frozenset())
    return out


def liveness(code, pcs):
    """Registers live before each reachable instruction of a role (a guarded write does not
    kill), by backward dataflow over the role's folded control flow."""
    reach = set(pcs)
    succs = {}
    for pc in pcs:
        ins = code[pc]
        if ins["opcode"].startswith(TERMINAL):
            succs[pc] = []
        elif ins["opcode"].split(".")[0] == "bra":
            succs[pc] = [x for x in {ins["target"], pc + 1 if ins["guard"] else None} if x in reach]
        else:
            succs[pc] = [pc + 1] if pc + 1 in reach else []
    live = {pc: frozenset() for pc in pcs}
    changed = True
    while changed:
        changed = False
        for pc in sorted(pcs, reverse=True):
            ins = code[pc]
            after = frozenset().union(*(live[s] for s in succs[pc])) if succs[pc] else frozenset()
            kill = set() if ins["guard"] else set(ins["writes"])
            uses = set(ins["reads"]) | ({ins["guard"]["register"]} if ins["guard"] else set())
            now = frozenset((after - kill) | uses)
            if now != live[pc]:
                live[pc] = now
                changed = True
    return live


def analyze():
    code, ids, widths = load()
    data = data_registers(code)
    out = {"instructions": len(code), "data_registers": sorted(data), "roles": {}}
    for role in ROLES:
        envs = reachable(code, role)
        pcs = sorted(envs)
        # Folded guards make some branch targets unreachable: restrict to what the paths visit.
        sites = [pc for pc in pcs if code[pc]["event"]]
        entry = local_paths(code, envs, 0)
        table = []
        visited = set()
        for pc in sites:
            ins = code[pc]
            paths = [] if ins["opcode"].startswith(TERMINAL) else local_paths(code, envs, pc + 1)
            for path in paths:
                visited.update(path["pcs"])
            table.append(
                {
                    "pc": pc,
                    "kind": flow_gen.kind_name(ins["opcode"]),
                    "opcode": ins["opcode"],
                    "operands": ins["operands"],
                    "paths": paths,
                }
            )
        for path in entry:
            visited.update(path["pcs"])
        live = liveness(code, pcs)
        for row in table:
            regs = sorted(live[row["pc"]], key=lambda r: ids.get(r, 0))
            row["live_control"] = [r for r in regs if r not in data]
            row["live_data"] = [r for r in regs if r in data]
        out["roles"][role] = {
            "reachable": pcs,
            "local": sorted(visited),
            "entry": entry,
            "sites": table,
        }
    return code, ids, widths, out


def main():
    cli = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    cli.add_argument("--json", type=Path)
    args = cli.parse_args()
    code, ids, widths, out = analyze()
    print(f"{len(out['data_registers'])} data registers")
    for role, data in out["roles"].items():
        kinds = collections.Counter(s["kind"] for s in data["sites"])
        traps = [s["pc"] for s in data["sites"] if s["kind"] == "trap"]
        paths = sum(len(s["paths"]) for s in data["sites"])
        longest = max((len(p["pcs"]) for s in data["sites"] for p in s["paths"]), default=0)
        control = max(len(s["live_control"]) for s in data["sites"])
        values = max(len(s["live_data"]) for s in data["sites"])
        print(
            f"{role}: {len(data['reachable'])} instructions, {len(data['sites'])} sites,",
            f"{paths} paths (longest {longest}), reachable brkpt {traps},",
            f"at most {control} control and {values} data registers live at a site",
        )
        print("   ", dict(kinds))
    if args.json:
        args.json.write_text(json.dumps(out, indent=1) + "\n")


if __name__ == "__main__":
    main()
