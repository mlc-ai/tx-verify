# SPDX-License-Identifier: Apache-2.0
"""Control-flow facts of a PTX kernel, for writing its site machines.

Reads only the PTX file. Instructions are numbered as `Core/Source/Decode.lean`
numbers them (statement order, nested scopes flattened). An instruction either performs
an event or is local (`Op.isLocal`); a site is an event instruction. For every site the
generator follows the local instructions after it (both outcomes of a guarded branch)
until the next sites, and records each path's branch conditions and the registers it
writes, as expressions over the registers at the start of the path.

Outputs:
  * `<out>/Sites.lean`: one named constant per site (`<kind>_<ordinal>`), the only place
    where the program counters of the kernel's proof appear;
  * `<out>/flow.json`: sites, local paths between sites, conditions and definitions.

    python Tools/flow_gen.py Kernels/K/k.ptx --namespace PTX.Kernels.K.Flow -o Kernels/K/Flow
    python Tools/flow_gen.py ... --check      # fail if the outputs are stale
"""

import argparse
import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import parse_ptx  # noqa: E402
from lean_wrap import wrap_lines  # noqa: E402

LOCAL_PREFIXES = (
    "mov",
    "add",
    "sub",
    "mul",
    "mad",
    "shl",
    "shr",
    "neg",
    "and",
    "or",
    "xor",
    "not",
    "cvt",
    "cvta",
    "selp",
    "setp",
    "mapa",
    "bra",
    "fma",
    "div",
    "rsqrt",
    "ex2",
    "rcp",
    "max",
    "min",
    "prefetch",
    "cp.async.bulk.prefetch",
)
EVENT_PREFIXES = (
    "ld.global",
    "ld.local",
    "ld.shared",
    "ld.acquire",
    "st.",
    "bar.",
    "barrier.",
    "shfl.",
    "vote.",
    "ret",
    "cp.async",
    "cp.reduce",
    "mbarrier.",
    "fence.",
    "tcgen05.",
    "clusterlaunchcontrol.",
    "setmaxnreg.",
    "elect.",
)
KIND_NAMES = [
    ("mbarrier.try_wait", "mbarWait"),
    ("mbarrier.arrive", "mbarArrive"),
    ("mbarrier.init", "mbarInit"),
    ("mbarrier.inval", "mbarInval"),
    ("cp.async.bulk.tensor", "tensorCopy"),
    ("cp.async.bulk.commit_group", "bulkCommit"),
    ("cp.async.bulk.wait_group", "bulkWait"),
    ("cp.async.bulk", "bulkCopy"),
    ("cp.async.commit_group", "asyncCommit"),
    ("cp.async.wait_", "asyncWait"),
    ("cp.async.mbarrier.arrive", "asyncArrive"),
    ("cp.async.", "asyncCopy"),
    ("tcgen05.mma", "mma"),
    ("tcgen05.commit", "tcCommit"),
    ("tcgen05.ld", "tmemLoad"),
    ("tcgen05.st", "tmemStore"),
    ("tcgen05.wait", "tmemWait"),
    ("tcgen05.alloc", "tmemAlloc"),
    ("tcgen05.dealloc", "tmemDealloc"),
    ("tcgen05.relinquish", "tmemRelinquish"),
    ("tcgen05.fence", "tcFence"),
    ("tcgen05.cp", "tmemCopy"),
    ("clusterlaunchcontrol.try_cancel", "clcIssue"),
    ("clusterlaunchcontrol.query", "clcQuery"),
    ("barrier.cluster.arrive", "clusterArrive"),
    ("barrier.cluster.wait", "clusterWait"),
    ("bar.warp", "warpBar"),
    ("bar.sync", "bar"),
    ("barrier.sync", "bar"),
    ("bar.arrive", "barArrive"),
    ("barrier.arrive", "barArrive"),
    ("ld.acquire", "loadAcquire"),
    ("st.release", "storeRelease"),
    ("ld.", "load"),
    ("st.", "store"),
    ("shfl.", "shfl"),
    ("vote.", "vote"),
    ("fence.proxy", "fenceProxy"),
    ("fence.mbarrier_init", "fenceMbarInit"),
    ("setmaxnreg", "setMaxReg"),
    ("elect", "elect"),
    ("ret", "exit"),
]


def is_event(opcode: str) -> bool:
    if opcode.startswith("ld.param"):
        return False
    if opcode.startswith("cp.async.bulk.prefetch"):
        return False
    return opcode.startswith(EVENT_PREFIXES)


def kind_name(opcode: str) -> str:
    for prefix, name in KIND_NAMES:
        if opcode.startswith(prefix):
            return name
    return re.sub(r"\W", "_", opcode.split(".")[0])


def operand_text(o) -> str:
    if o.kind in ("register", "symbol", "literal"):
        return o.text
    if o.kind == "sink":
        return "_"
    inner = ",".join(operand_text(c) for c in o.children)
    if o.kind == "address":
        return f"[{inner}]"
    if o.kind == "vector":
        return "{" + inner + "}"
    if o.kind == "pair":
        return "|".join(operand_text(c) for c in o.children)
    if o.kind == "offset":
        return operand_text(o.children[0]) + o.text + operand_text(o.children[1])
    return f"{o.kind}({inner})"


SPECIAL = re.compile(
    r"^%(tid|ntid|ctaid|nctaid|clusterid|nclusterid|cluster_ctaid|"
    r"cluster_nctaid|cluster_ctarank|cluster_nctarank|laneid)(\.[xyz])?$"
)


def registers(o) -> list[str]:
    """Register and symbol operands; symbols are kept when a scope declares them registers."""
    if o.kind == "register":
        return [] if SPECIAL.match(o.text) else [o.text]
    if o.kind == "symbol":
        return [o.text]
    return [r for c in o.children for r in registers(c)]


def scope_bindings(body, path):
    """Registers declared in one lexical scope, renamed as `Core/Source/Decode.lean` does."""
    out = []
    for s in body:
        if s.kind != "declaration" or not s.tokens or s.tokens[0] != ".reg":
            continue
        t = s.tokens
        qualify = (lambda n: n) if path == "" else (lambda n: f"#{path}#{n}")
        if len(t) == 6 and t[3] == "<":
            out.append((t[2], int(t[4]), qualify(t[2])))
        else:
            # one name, or a comma list `.reg .t a, b, …` (each one register, §9.3)
            out.extend((n, 0, qualify(n)) for n in t[2:] if n != ",")
    return out


def register_ids(function) -> dict[str, int]:
    """Register ids as `Core/Source/Decode.lean` assigns them: the position of each name in the
    declared-register order (declarations in statement order, scoped ones renamed)."""
    names = []

    def walk_scope(body, path):
        for i, s in enumerate(body):
            if s.kind == "declaration" and s.tokens and s.tokens[0] == ".reg":
                for pre, count, target in scope_bindings([s], path):
                    names.extend([target] if count == 0 else [f"{target}{k}" for k in range(count)])
            elif s.kind == "scope":
                walk_scope(s.body, f"{path}/{i}")

    walk_scope(function.body, "")
    return {n: i for i, n in enumerate(names)}


def is_register(name: str) -> bool:
    return name.startswith("%") or name.startswith("#")


def resolve(name, regenv):
    for bindings in regenv:
        for pre, count, target in bindings:
            if count == 0 and name == pre:
                return target
            if count and name.startswith(pre):
                rest = name[len(pre) :]
                if (
                    rest.isdigit()
                    and (rest == "0" or not rest.startswith("0"))
                    and int(rest) < count
                ):
                    return target + rest
    return name


def flatten(function):
    """Instructions in decoder order with branch targets resolved through lexical scopes."""
    instrs = []

    def collect(body, scopes, path, regenv):
        labels = {}
        pc = len(instrs)
        # labels of this scope point at the next instruction in statement order
        count = pc
        pending = []
        for s in body:
            if s.kind == "label":
                pending.append(s.text)
            elif s.kind == "instruction":
                for name in pending:
                    labels[name] = count
                pending = []
                count += 1
            elif s.kind == "scope":
                for name in pending:
                    labels[name] = count
                pending = []
                count += count_instructions(s.body)
        for name in pending:
            labels[name] = count
        env = [labels] + scopes
        renv = [scope_bindings(body, path)] + regenv
        # `name: .branchtargets t0, t1, ...;` tables of `brx.idx`: the label before the
        # directive names the table, its entries are labels of the function.
        for i, s in enumerate(body):
            if s.kind == "directive" and s.tokens and s.tokens[0] == ".branchtargets":
                prev = body[i - 1] if i > 0 else None
                if prev is None or prev.kind != "label":
                    raise ValueError(".branchtargets without a table label")
                names = [t for t in s.tokens[1:] if t != ","]
                tables[prev.text] = [next(scope[n] for scope in env if n in scope) for n in names]
        for i, s in enumerate(body):
            if s.kind == "instruction":
                instrs.append((s, env, renv))
            elif s.kind == "scope":
                collect(s.body, env, f"{path}/{i}", renv)

    tables = {}
    collect(function.body, [], "", [])
    declared = set(register_ids(function))
    out = []
    for pc, (s, env, renv) in enumerate(instrs):
        target = None
        if s.opcode.split(".")[0] == "bra":
            name = s.operands[0].text
            target = next(scope[name] for scope in env if name in scope)
        table = None
        if s.opcode.split(".")[0] == "brx":
            table = tables[s.operands[1].text]
        guard = None
        if s.predicate:
            guard = {"register": resolve(s.predicate, renv), "negated": s.negated}
        writes, reads = [], []
        ops = s.operands
        if table is not None:
            reads = registers(ops[0])
        elif ops and not is_event(s.opcode) and s.opcode.split(".")[0] not in ("bra", "prefetch"):
            writes = registers(ops[0])
            reads = [r for o in ops[1:] for r in registers(o)]
        elif ops:
            reads = [r for o in ops for r in registers(o)]
            if (
                s.opcode.startswith(
                    (
                        "mbarrier.try_wait",
                        "ld.",
                        "tcgen05.ld",
                        "elect",
                        "shfl",
                        "vote",
                        "mbarrier.arrive",
                        "clusterlaunchcontrol.query",
                    )
                )
                and ops[0].kind != "address"
            ):
                writes = registers(ops[0])
                reads = [r for o in ops[1:] for r in registers(o)]
        writes = [n for n in (resolve(r, renv) for r in writes) if is_register(n) or n in declared]
        reads = [n for n in (resolve(r, renv) for r in reads) if is_register(n) or n in declared]
        out.append(
            {
                "pc": pc,
                "opcode": s.opcode,
                "operands": [operand_text(o) for o in ops],
                "guard": guard,
                "event": is_event(s.opcode),
                "target": target,
                "table": table,
                "writes": writes,
                "reads": reads,
            }
        )
    return out


def count_instructions(body) -> int:
    n = 0
    for s in body:
        if s.kind == "instruction":
            n += 1
        elif s.kind == "scope":
            n += count_instructions(s.body)
    return n


def successors(ins, n):
    """Local successors of a local instruction: (pc, condition) pairs."""
    pc = ins["pc"]
    if ins.get("table") is not None:
        # one edge per table entry, taken when the index equals the entry's position
        index = ins["reads"][0]
        return [(t, (index, ["eq", i])) for i, t in enumerate(ins["table"])]
    if ins["opcode"].split(".")[0] == "bra":
        if ins["guard"] is None:
            return [(ins["target"], None)]
        g = ins["guard"]
        taken = (g["register"], not g["negated"])
        fall = (g["register"], g["negated"])
        return [(ins["target"], taken), (pc + 1, fall)]
    if ins["guard"] is not None:
        g = ins["guard"]
        # a guarded local instruction runs or is skipped; both continue at pc + 1
        return [(pc + 1, None)]
    return [(pc + 1, None)] if pc + 1 < n else []


def paths_from(code, start, limit=4096, *, loop_entries=frozenset(), from_loop=False):
    """Local paths to the next event or loop entry, including a single loop traversal."""
    result = []
    stack = [(start, [], [], {})]
    while stack:
        pc, conds, visited, defs = stack.pop()
        if pc >= len(code):
            result.append({"to": None, "conditions": conds, "length": len(visited), "defs": defs})
            continue
        ins = code[pc]
        if ins["event"] or (pc in loop_entries and (visited or not from_loop)):
            result.append({"to": pc, "conditions": conds, "length": len(visited), "defs": defs})
            continue
        if pc in visited:
            result.append({"to": None, "loop": pc, "conditions": conds, "length": len(visited)})
            continue
        if len(visited) > limit:
            raise ValueError(f"local path from {start} longer than {limit}")
        new_defs = dict(defs)
        if ins["writes"] and ins["opcode"].split(".")[0] != "bra":
            expr = (
                ins["opcode"]
                + "("
                + ",".join(defs.get(a, a) if a in defs else a for a in ins["operands"][1:])
                + ")"
            )
            if ins["guard"]:
                g = ins["guard"]
                expr = f"if {'!' if g['negated'] else ''}{g['register']} then {expr} else old"
            for r in ins["writes"]:
                new_defs[r] = expr
        if ins.get("table") is not None:
            # an index at or beyond the table's length is undefined behaviour (§9.7.14.4)
            index = ins["reads"][0]
            result.append(
                {
                    "to": None,
                    "unsafe": "brx.idx index out of range",
                    "conditions": conds + [[index, ["ge", len(ins["table"])], pc]],
                    "length": len(visited) + 1,
                    "defs": defs,
                }
            )
        for nxt, cond in successors(ins, len(code)):
            stack.append(
                (
                    nxt,
                    conds + ([[cond[0], cond[1], pc]] if cond else []),
                    visited + [pc],
                    new_defs,
                )
            )
    return result


def all_successors(ins, n):
    """Control successors of any instruction (events continue at pc + 1; `ret` ends)."""
    if ins["opcode"].startswith("ret"):
        return []
    if not ins["event"]:
        return [p for p, _ in successors(ins, n)]
    return [ins["pc"] + 1] if ins["pc"] + 1 < n else []


def liveness(code):
    """Registers live before each instruction (backward dataflow over the whole CFG).
    A guarded instruction may be skipped, so its writes do not kill; its guard is read."""
    n = len(code)
    live_in = [set() for _ in range(n)]
    preds = [[] for _ in range(n)]
    for ins in code:
        for q in all_successors(ins, n):
            preds[q].append(ins["pc"])
    work = list(range(n))
    while work:
        pc = work.pop()
        ins = code[pc]
        out = set()
        for q in all_successors(ins, n):
            out |= live_in[q]
        uses = set(ins["reads"]) | ({ins["guard"]["register"]} if ins["guard"] else set())
        kill = set() if ins["guard"] else set(ins["writes"])
        new = uses | (out - kill)
        if new != live_in[pc]:
            live_in[pc] = new
            work.extend(preds[pc])
    return live_in


def sites(code):
    counters = {}
    out = []
    for ins in code:
        if not ins["event"]:
            continue
        k = kind_name(ins["opcode"])
        counters[k] = counters.get(k, 0) + 1
        out.append(
            {
                "name": f"{k}_{counters[k] - 1}",
                "pc": ins["pc"],
                "opcode": ins["opcode"],
                "operands": ins["operands"],
                "guard": ins["guard"],
            }
        )
    return out


def local_loops(code):
    """Back edges whose loop interval [target, pc] contains no event site."""
    out = []
    for ins in code:
        back = [ins["target"]] if ins["opcode"].split(".")[0] == "bra" else (ins.get("table") or [])
        for t in back:
            if t is not None and t <= ins["pc"]:
                body = code[t : ins["pc"] + 1]
                if not any(i["event"] for i in body):
                    out.append((t, ins["pc"]))
    return out


# A kernel with more instructions than this has its live tables split into parts of PART_PCS.
SPLIT_AT = 2000
PART_PCS = 500
LIVE_DOC = "Registers live before instruction `pc`."


def generate(ptx: Path, namespace: str):
    program = parse_ptx.parse(ptx.read_text())
    function = next(f for f in program.functions if not f.declaration)
    code = flatten(function)
    ids = register_ids(function)
    loops = local_loops(code)
    loop_entries = frozenset(entry for entry, _ in loops)
    loop_info = []
    for i, (entry, backedge) in enumerate(loops):
        # A single straight-line body with a conditional backedge has two outgoing paths.
        # Reject other shapes until their cut points can be represented explicitly.
        if (
            code[backedge]["guard"] is None
            or any(ins["target"] is not None for ins in code[entry:backedge])
            or any(entry < ins["target"] <= backedge for ins in code if ins["target"] is not None)
        ):
            raise ValueError(f"{ptx}: unsupported local loop {entry}..{backedge}")
        loop_info.append(
            {"name": f"localLoop_{i}", "entry": entry, "backedge": backedge, "exit": backedge + 1}
        )
    site_list = sites(code)
    by_pc = {s["pc"]: s["name"] for s in site_list}
    by_pc.update((loop["entry"], loop["name"]) for loop in loop_info)
    live = liveness(code)
    flow = {
        "kernel": function.name,
        "instructions": len(code),
        "sites": [],
        "entry": None,
    }
    flow["entry"] = [
        {
            "to": by_pc.get(p["to"]),
            "conditions": p["conditions"],
            "length": p["length"],
            "defs": p.get("defs", {}),
            **({"unsafe": p["unsafe"]} if "unsafe" in p else {}),
        }
        for p in paths_from(code, 0, loop_entries=loop_entries)
    ]
    for s in site_list:
        after = paths_from(code, s["pc"] + 1, loop_entries=loop_entries)
        if s["opcode"] == "ret":
            after = []
        flow["sites"].append(
            {
                **s,
                "live": sorted(
                    live[s["pc"]] - set(code[s["pc"]]["reads"]) | set(code[s["pc"]]["reads"]),
                    key=lambda r: (
                        re.sub(r"\d+", "", r),
                        int(re.sub(r"\D", "", r) or 0),
                    ),
                ),
                "next": [
                    {
                        "to": by_pc.get(p["to"]),
                        "loop": p.get("loop"),
                        "conditions": p["conditions"],
                        "length": p["length"],
                        "defs": p.get("defs", {}),
                        **({"unsafe": p["unsafe"]} if "unsafe" in p else {}),
                    }
                    for p in after
                ],
            }
        )
    if loop_info:
        flow["local_loops"] = [
            {
                **loop,
                "next": [
                    {**path, "to": by_pc.get(path["to"])}
                    for path in paths_from(
                        code, loop["entry"], loop_entries=loop_entries, from_loop=True
                    )
                ],
            }
            for loop in loop_info
        ]
    lines = [
        "-- SPDX-License-Identifier: Apache-2.0",
        f"-- Generated by Tools/flow_gen.py from {ptx.name}; do not edit.",
        "module",
        "",
        "@[expose] public section",
        "",
        "/-! Program counters of the event instructions (sites). Proof files name sites by",
        "these constants; no other proof file mentions a program counter. -/",
        "",
        f"namespace {namespace}",
        "",
    ]
    for s in site_list:
        ops = ", ".join(s["operands"])
        guard = ""
        if s["guard"]:
            guard = ("@!" if s["guard"]["negated"] else "@") + s["guard"]["register"] + " "
        comment = f"{guard}{s['opcode']} {ops}".strip().replace("-/", "- /")
        if len(comment) > 90:
            comment = comment[:87] + "..."
        lines.append(f"/-- `{comment}` -/")
        lines.append(f"abbrev {s['name']} : Nat := {s['pc']}")
    lines += [
        "",
        "/-- All sites, in program order. -/",
        "def all : List Nat := [" + ", ".join(s["name"] for s in site_list) + "]",
        "",
        "/-- Sites of each kind, in program order: `kind[i]` is the site `kind_i`. -/",
    ]
    for loop in loop_info:
        lines.append("")
        for field in ("entry", "backedge", "exit"):
            lines.append(f"abbrev {loop['name']}_{field} : Nat := {loop[field]}")
    branch_pcs_all = {
        c[2] for st in flow["sites"] for path in st["next"] for c in path["conditions"]
    }
    kinds = {}
    for st in site_list:
        k, i = st["name"].rsplit("_", 1)
        kinds.setdefault(k, []).append(st["name"])
    for k, names in kinds.items():
        lines.append(f"def {k} : Array Nat := #[" + ", ".join(names) + "]")
    if branch_pcs_all:
        lines += [
            "",
            "/-- Branch points between sites, named by their position for segment splitting. -/",
        ]
    for b in sorted(branch_pcs_all):
        lines.append(f"abbrev bra_{b} : Nat := {b}")
    lines += [
        "",
        "/-! Registers live before each instruction, by id: read later before being overwritten.",
        "One definition per program counter, found by binary search, so that reading the",
        "entry of a program counter takes logarithmically many steps. -/",
    ]
    n = len(code)

    def live_def(pc):
        regs = ", ".join(str(r) for r in sorted(ids[r] for r in live[pc]))
        return f"noncomputable def live_{pc} : List Nat := [{regs}]"

    def tree(leaf, bound, lo, hi, depth):
        pad = "  " * depth
        if hi - lo == 1:
            return [f"{pad}{leaf(lo)}"]
        mid = (lo + hi) // 2
        return (
            [f"{pad}(bif Nat.blt pc {bound(mid)} then"]
            + tree(leaf, bound, lo, mid, depth + 1)
            + [f"{pad}else"]
            + tree(leaf, bound, mid, hi, depth + 1)
            + [f"{pad})"]
        )

    def search(name, leaf, bound, lo, hi, doc):
        return [
            "",
            f"/-- {doc} -/",
            f"noncomputable def {name} (pc : Nat) : List Nat :=",
            f"  bif Nat.blt pc {bound(hi)} then",
            *tree(leaf, bound, lo, hi, 2),
            "  else []",
        ]

    files = {}
    if n <= SPLIT_AT:
        lines += [live_def(pc) for pc in range(n)]
        lines += search("live", lambda i: f"live_{i}", lambda i: i, 0, n, LIVE_DOC)
        lines += ["", f"end {namespace}", ""]
        files["Sites.lean"] = lines
    else:
        # A large kernel's tables go in parts that Lean compiles separately. `Sites.lean`
        # imports them and keeps the `live` lookup, so every name stays under `Flow.Sites`.
        module = namespace.removeprefix("PTX.") + ".Sites"
        count = -(-n // PART_PCS)
        header, rest = lines[:6], lines[6:]
        for k in range(count):
            lo, hi = k * PART_PCS, min(n, (k + 1) * PART_PCS)
            part = header + (rest if k == 0 else [f"namespace {namespace}", ""])
            part += [live_def(pc) for pc in range(lo, hi)]
            part += search(
                f"liveIn_{k}", lambda i: f"live_{i}", lambda i: i, lo, hi, f"{LIVE_DOC} Part {k}."
            )
            part += ["", f"end {namespace}", ""]
            files[f"Sites/Part{k:03d}.lean"] = part
        top = lines[:3] + [""]
        top += [f"public import {module}.Part{k:03d}" for k in range(count)]
        top += ["", *lines[4:6], f"namespace {namespace}"]
        top += search(
            "live",
            lambda i: f"liveIn_{i} pc",
            lambda i: min(n, i * PART_PCS),
            0,
            count,
            LIVE_DOC,
        )
        top += ["", f"end {namespace}", ""]
        files["Sites.lean"] = top
    texts = {name: "\n".join(wrap_lines("\n".join(ls).split("\n"))) for name, ls in files.items()}
    return texts, json.dumps(flow, indent=1) + "\n"


def main():
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument("ptx", type=Path)
    parser.add_argument("--namespace", required=True)
    parser.add_argument("-o", "--out", type=Path, required=True)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    lean, flow = generate(args.ptx, args.namespace)
    targets = {args.out / name: text for name, text in lean.items()}
    targets[args.out / "flow.json"] = flow
    if args.check:
        stale = [str(p) for p, text in targets.items() if not p.exists() or p.read_text() != text]
        if stale:
            print("stale:", *stale)
            return 1
        return 0
    args.out.mkdir(parents=True, exist_ok=True)
    for path, text in targets.items():
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
    return 0


if __name__ == "__main__":
    sys.exit(main())
