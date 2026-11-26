# SPDX-License-Identifier: Apache-2.0
"""Emit the transition functions of the thread machine from the flow table.

For every event site of `Flow/flow.json` this makes the text of the function that gives the
register file after the site's event and the local instructions that follow it, on each path to
the next site (a decision tree over the file's predicates): `let` bindings in the vocabulary of
`Lemmas/Flow/Arith32.lean`, one comment per instruction, and a final state
`⟨site, setW [...] d.w, setP [...] d.p⟩` that rewrites exactly the assigned registers that are
live at the next site.

A library of `thread.py`, which puts these texts into `Proof/Thread/After/`. It reads the frozen
PTX (through `analysis.load`) and `Flow/flow.json`, and writes no file, so there is nothing to
regenerate or to check here. Its two commands are reading aids:

    python3 Kernels/FlashKdaFwd/Gen/emit.py --show mbarInit_3     # print one site
    python3 Kernels/FlashKdaFwd/Gen/emit.py --coverage            # the sites without a function
"""

import argparse
import collections
import json
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import analysis  # noqa: E402
import pointers  # noqa: E402
import translit  # noqa: E402

FLOW = analysis.KERNEL / "Flow" / "flow.json"


class Sites:
    """The sites of the flow table, by name and by program counter."""

    def __init__(self):
        self.flow = json.loads(FLOW.read_text())
        self.code, self.ids, self.widths = analysis.load()
        # Opaque registers: the data path, every register a load writes, and the cluster
        # address a `mapa` writes. The exception: the 21 loads of the read-only offsets array
        # (`ld.global.b64`), whose destinations are 64-bit words (the machine follows such a
        # load on an integer only, `loadWord`).
        self.data = analysis.data_registers(self.code)
        for ins in self.code:
            if ins["event"] and ins["opcode"].startswith("ld.") and not offset_load(ins):
                self.data.update(ins["writes"])
            if ins["opcode"].startswith("mapa."):
                self.data.update(ins["writes"])
        # Every register derived from a generic shared pointer (`cvta.shared.u64` and the
        # arithmetic on its result) is opaque: the machine carries the pointer as it is.
        self.ptr = pointers.pointer_registers(self.code)
        self.data |= self.ptr
        # The generic addresses of the by-value parameter objects (`cvta.param.u64 d, a` of a
        # parameter address `a`): register -> index of the object.
        self.gparam = {}
        for ins in self.code:
            if ins["opcode"] == "cvta.param.u64":
                src = self.ids[ins["operands"][1]]
                if not 2251 <= src <= 2261:
                    raise translit.Unsupported(
                        f"pc {ins['pc']}: cvta.param of {ins['operands'][1]}"
                    )
                self.gparam[ins["writes"][0]] = src - 2251
        self.liveness = analysis.flow_gen.liveness(self.code)
        self.tails = {}  # pc of a special instruction -> its function (`Tail`)
        self.sites = self.flow["sites"]
        self.by_pc = {s["pc"]: s for s in self.sites}
        self.by_name = {s["name"]: s for s in self.sites}
        self.counts = collections.Counter(s["name"].rsplit("_", 1)[0] for s in self.sites)
        self.runs = {}  # (first pc, pc after the last) -> (run name, index of its end facts)

    def term(self, pc):
        """The Lean term of the site at `pc`: its kind applied to its ordinal."""
        kind, n = self.by_pc[pc]["name"].rsplit("_", 1)
        return f".{kind} {n}"

    def live(self, pc):
        """The registers live at `pc`, with scope-qualified names as in `ids`."""
        if pc in self.by_pc:
            return set(self.by_pc[pc]["live"])
        return set(self.liveness[pc])

    def tail(self, pc):
        """The function of the local code from the special instruction at `pc` (made once)."""
        if pc not in self.tails:
            self.tails[pc] = None  # a cycle of tails would be a local loop without a site
            run = translit.is_run_item(self.code[pc], self.data)
            self.tails[pc] = RunTail(self, pc) if run else Tail(self, pc)
        if self.tails[pc] is None:
            raise translit.Unsupported(f"tail functions in a cycle at {pc}")
        return self.tails[pc]


def offset_load(ins):
    """One of the 21 loads of the read-only offsets array."""
    return ins["event"] and ins["opcode"] == "ld.global.b64"


def leaves(node):
    """The leaves of a decision tree."""
    if node[0] == "if":
        return leaves(node[2]) + leaves(node[3])
    return [node]


def simple(node):
    """Whether the tree is evaluated code only: no special instruction at its start, no tail."""
    return not node[-1].head and all(leaf[0] == "site" for leaf in leaves(node))


def is_outcome(sites, node):
    """Whether the function of this tree has the type `Option (Option D)`: the thread can die
    on its way (a `mapa` at its start, or a tail that can)."""
    if any(h[0] == "mapa" for h in node[-1].head):
        return True
    return any(leaf[0] == "tail" and sites.tail(leaf[1]).outcome for leaf in leaves(node))


def needs_launch(sites, node):
    """Whether the proof of this tree uses the launch facts (`hL`)."""
    if any(h[0] in ("param", "pobj") for h in node[-1].head):
        return True
    return any(leaf[0] == "tail" for leaf in leaves(node))


class Tail:
    """The function `tail_<pc>`: the local code from a special instruction that evaluated code
    precedes on some path, as a function of the file there."""

    def __init__(self, sites, pc):
        self.pc = pc
        terms = translit.PathTerms(sites.code, sites.ids, sites.data)
        self.node = translit.tree(sites.code, sites.ids, sites.data, pc, terms)
        self.calls = [leaf[1] for leaf in leaves(self.node) if leaf[0] == "tail"]
        for q in self.calls:
            sites.tail(q)
        self.outcome = is_outcome(sites, self.node)

    def text(self, sites):
        ins = sites.code[self.pc]
        ty = "Option (Option D)" if self.outcome else "D"
        op = ins["opcode"]
        why = (
            "which evaluation does not run"
            if op.startswith(("ld.param", "mapa."))
            else "where the data run before it ends"
        )
        return "\n".join(
            [
                f"/-- The local code from instruction {self.pc}, {why}",
                f"(`{brief(ins)}`),",
                "to the next cut points, from the file there (the site of `d` is carried along and",
                "not read). -/",
                f"def tail_{self.pc} (L : Launch) (g : Nat) (d : D) : {ty} :=",
                *render(sites, self.node, 2, self.outcome),
            ]
        )


class RunTail:
    """The function `tail_<pc>` of a data run that control code precedes (or that follows an
    event the data recipe does not cover): the run from `pc`, then the local code after it.
    The run continues under its condition and kills the thread otherwise, so the function is
    outcome-valued. A `cvta.shared.u64` is a run of its own: its outcome names the launch and
    the thread, and the run library does not take an address instruction as an item."""

    outcome = True

    def __init__(self, sites, pc):
        code = sites.code
        self.pc = pc
        self.cvta = code[pc]["opcode"] in pointers.POINTER_SOURCES
        b = pc + 1
        if not self.cvta:
            while translit.is_run_item(code[b], sites.data) and (
                code[b]["opcode"] not in pointers.POINTER_SOURCES
            ):
                b += 1
        self.end = b
        self.site = bool(code[b]["event"])
        self.calls = [] if self.site else [b]
        for q in self.calls:
            sites.tail(q)

    def names(self, sites, v):
        """The run's condition, its end facts and its piece, on the values `v`."""
        a = self.pc
        if self.cvta:
            ins = sites.code[a]
            d, s = sites.ids[ins["writes"][0]], sites.ids[ins["reads"][0]]
            return (
                f"Rules.cvtaCond L g {v} {s}",
                f"[({d}, Rules.cvtaVal L g {v} {s})]",
                f"cvta_{a}_run L g {v}",
            )
        name, last = sites.runs[(a, self.end)]
        return f"Run.{name}_cond {v}", f"(Run.{name}_facts{last} {v})", f"Run.{name}_run L g {v}"

    def text(self, sites):
        a, b = self.pc, self.end
        cond, facts, _ = self.names(sites, "(valueOf d)")
        x1 = f"valueEx d.x {facts}"
        if self.site:
            body = f"across ({cond}) ⟨{sites.term(b)}, d.w, d.p, {x1}⟩"
        else:
            rest = f"tail_{b} L g ⟨d.site, d.w, d.p, {x1}⟩"
            if not sites.tail(b).outcome:
                rest = f"some (some ({rest}))"
            body = f"under ({cond}) ({rest})"
        what = "the conversion" if self.cvta else f"the data run from instruction {a} to {b - 1}"
        return "\n".join(
            [
                f"/-- From the file at instruction {a}",
                f"(`{brief(sites.code[a])}`):",
                f"{what}, which continues under its condition,",
                f"then the local code from {b}. -/",
                f"def tail_{a} (L : Launch) (g : Nat) (d : D) : Option (Option D) :=",
                f"  {body}",
            ]
        )


def tail_order(sites):
    """The tail functions, callees first."""
    out, seen = [], set()

    def visit(pc):
        if pc in seen:
            return
        seen.add(pc)
        for q in sites.tails[pc].calls:
            visit(q)
        out.append(pc)

    for pc in sorted(sites.tails):
        visit(pc)
    return out


def seed(sites, site, terms):
    """Give the registers the site's event writes their names in the transition function, and
    return the function's extra arguments (what the event returned)."""
    ins = sites.code[site["pc"]]
    kind = site["name"].rsplit("_", 1)[0]
    args = []
    if kind == "elect":
        rx, px = ins["writes"] if len(ins["writes"]) == 2 else (None, None)
        if rx is None:
            raise translit.Unsupported(f"election at {site['pc']} writes {ins['writes']}")
        terms.bits[rx], terms.preds[px] = "rx", "b"
        terms.assigned += [rx, px]
        args = ["(rx : BitVec 64)", "(b : Bool)"]
    elif kind == "mbarWait":
        (p,) = ins["writes"]
        terms.preds[p] = "ok"
        terms.assigned.append(p)
        args = ["(ok : Bool)"]
    elif kind == "shfl":
        dst = ins["writes"]
        terms.bits[dst[0]] = "x"
        terms.assigned.append(dst[0])
        args = ["(x : BitVec 64)"]
        if len(dst) == 2:
            terms.preds[dst[1]] = "ok"
            terms.assigned.append(dst[1])
            args.append("(ok : Bool)")
    elif kind == "load" and offset_load(ins):
        # A load of the offsets array: the machine follows a 64-bit integer, the word `x`.
        (dst,) = ins["writes"]
        terms.bits[dst] = "y"
        terms.assigned.append(dst)
        args = ["(y : BitVec 64)"]
    elif kind == "load":
        # A load writes an opaque register: the value its bytes rebuild to, whatever it is.
        dst = ins["writes"]
        if len(dst) != 1:
            raise translit.Unsupported(f"vector load at {site['pc']}")
        terms.values[dst[0]] = "v"
        terms.assigned.append(dst[0])
        args = ["(v : Value)"]
    elif ins["writes"]:
        raise translit.Unsupported(f"{kind} at {site['pc']} writes {ins['writes']}")
    return args


def render(sites, node, indent, outcome=False):
    """The Lean text of a decision tree of `translit.tree`: a state (type `D`), or with
    `outcome` an outcome (type `Option (Option D)`: the function can end in a dead thread)."""
    pad = " " * indent
    terms = node[-1]
    out = []
    binders = {h[4]: h for h in terms.head if h[0] == "mapa"}

    def binder(k):
        if k in binders:
            _, _, xa, xr, _, c = binders[k]
            out.append(f"{pad}-- {c}"[:99])
            out.append(f"{pad}mapaThen L g {xa} {xr} fun peer =>")

    for k, (n, ty, t, c) in enumerate(terms.lets):
        binder(k)
        out.append(f"{pad}-- {c}"[:99])
        out.append(f"{pad}let {n} : {ty} := {t}")
    binder(len(terms.lets))
    if node[0] in ("site", "tail"):
        pc = node[1]
        words, preds = terms.updates(sites.live(pc))
        vals = terms.opaque(sites.live(pc))
        w = "d.w" if not words else "setW [" + ", ".join(f"({i}, {t})" for i, t in words) + "] d.w"
        p = "d.p" if not preds else "setP [" + ", ".join(f"({i}, {t})" for i, t in preds) + "] d.p"
        x = "d.x" if not vals else "valueEx d.x [" + ", ".join(f"({i}, {t})" for i, t in vals) + "]"
        if node[0] == "site":
            state, wrap = f"⟨{sites.term(pc)}, {w}, {p}, {x}⟩", outcome
        else:
            state = f"tail_{pc} L g ⟨d.site, {w}, {p}, {x}⟩"
            wrap = outcome and not sites.tail(pc).outcome
            if wrap:
                state = f"({state})"
        out.append(f"{pad}some (some {state})" if wrap else f"{pad}{state}")
        return out
    _, g, taken, other, _ = node
    out.append(f"{pad}if {g} then")
    out += render(sites, taken, indent + 2, outcome)
    out.append(f"{pad}else")
    out += render(sites, other, indent + 2, outcome)
    return out


def prove(sites, node, outcome, indent):
    """The tactic lines that prove the outcome of the local code of a decision tree
    (`Local …`, `Proof/Thread/EventLib.lean`), piece by piece, after the function is unfolded."""
    pad = " " * indent
    out = []
    for h in node[-1].head:
        if h[0] == "param":
            out.append(
                f"{pad}refine Local.ldParam Flow.code_{h[1]} hL.p{h[2]} (by fresh_key) (by asms_none)"
                " segFree rfl rfl ?_"
            )
        elif h[0] == "pobj":
            out += [
                f"{pad}obtain ⟨decl, base, hobj, hin, hal⟩ := hL.obj {h[2]} (by decide)",
                f"{pad}refine Local.ldParamObj Flow.code_{h[1]} (by fact_mem) (by fresh_key) hobj hin",
                f"{pad}  ⟨by decide, by decide, hal⟩ (hL.bytes {h[2]} (by decide)) (by decide)",
                f"{pad}  (by asms_none) segFree rfl rfl ?_",
            ]
        else:
            out.append(
                f"{pad}refine Local.mapa Flow.code_{h[1]} (by fact_mem) (by fact_mem) (by fresh_key)"
                " (by asms_none) segFree fun peer _ => ?_"
            )
    out += prove_tree(sites, node, outcome, indent)
    return out


def prove_tree(sites, node, outcome, indent):
    pad = " " * indent
    if all(leaf[0] == "site" for leaf in leaves(node)) and (node[0] == "site" or not outcome):
        # evaluated code up to the sites: one piece, the walk splits the branches
        return [f"{pad}lsite"]
    if node[0] == "tail":
        return [f"{pad}exact Local.cut (by lseg) (local_tail_{node[1]} hL _ _ _ _)"]
    assert node[0] == "if", node[0]
    lemma = "Local.ite" if outcome else "Local.iteD"
    out = [f"{pad}refine {lemma} (fun _ => ?_) (fun _ => ?_)"]
    for sub in (node[2], node[3]):
        lines = prove_tree(sites, sub, outcome, indent + 2)
        out += [f"{pad}· " + lines[0].lstrip(), *lines[1:]]
    return out


def is_data(sites, ins):
    """A local instruction of the data path: it writes an opaque register."""
    return (
        not ins["event"] and ins["target"] is None and any(w in sites.data for w in ins["writes"])
    )


def straight(sites, start):
    """The straight local code from `start` to the next site, as the data path has it after an
    event: a run of data instructions `(first pc, pc after the last)` or `None`, then the control
    instructions, then the site. A branch, or a data instruction after control code, has no
    recipe here."""
    code = sites.code
    if start >= len(code):
        raise translit.Unsupported("no code after the last instruction")
    pc = start
    while is_data(sites, code[pc]):
        pc += 1
    run = (start, pc) if pc > start else None
    control = []
    while not code[pc]["event"]:
        ins = code[pc]
        if ins["target"] is not None:
            raise translit.Unsupported(f"branch at {pc} after a data event")
        if is_data(sites, ins):
            raise translit.Unsupported(f"data instruction at {pc} after control code")
        control.append(pc)
        pc += 1
    return run, control, pc


def data_after(sites, name, pc, written, arg):
    """The transition function of a data event at `pc` (named `name`) that wrote the opaque
    registers `written` with what `arg` names (`v`: one loaded value; `vs`: the values a matrix
    event's bytes rebuild to; `None`: nothing), over straight code: the slots the event wrote,
    the end facts of the data run that follows, and the words of the control code after it.
    Returns the Lean text and what the step's proof needs."""
    ins = sites.code[pc]
    run, control, q = straight(sites, pc + 1)
    terms = translit.PathTerms(sites.code, sites.ids, sites.data)
    terms.run(control)
    words, preds = terms.updates(sites.live(q))
    ids = [sites.ids[r] for r in written]
    if arg == "v":
        event = f"[({ids[0]}, v)]"
    elif arg == "v0 v1 v2 v":
        event = "([" + ", ".join(map(str, ids)) + "].zip [v0, v1, v2, v])"
    elif arg == "vs":
        event = "([" + ", ".join(map(str, ids)) + "].zip vs)"
    else:
        event = None
    x1 = "d.x" if event is None else f"valueEx d.x {event}"
    x = x1
    info = {"pc": pc, "ids": ids, "event": event, "run": None, "control": control, "next": q}
    if run is not None:
        rname, last = sites.runs[run]
        info["run"] = (rname, last, run[0], run[1])
        x = f"valueEx ({x1}) (Run.{rname}_facts{last} (valueOf ⟨d.site, d.w, d.p, {x1}⟩))"
    w = "d.w" if not words else "setW [" + ", ".join(f"({i}, {t})" for i, t in words) + "] d.w"
    p = "d.p" if not preds else "setP [" + ", ".join(f"({i}, {t})" for i, t in preds) + "] d.p"
    args = {
        "v": " (v : Value)",
        "vs": " (vs : List Value)",
        None: "",
        "v0 v1 v2 v": " (v0 v1 v2 v : Value)",
    }[arg]
    out = [
        f"/-- After `{name}` ({pc}: `{brief(ins)}`). -/",
        f"def after_{name} (L : Launch) (g : Nat) (d : D){args} : D :=",
    ]
    for n, ty, t, c in terms.lets:
        out += [f"  -- {c}"[:99], f"  let {n} : {ty} := {t}"]
    out.append(f"  ⟨{sites.term(q)}, {w}, {p}, {x}⟩")
    return "\n".join(out), info


def brief(ins, width=50):
    """The instruction as text for a comment, cut to `width` characters."""
    text = ins["opcode"] + " " + ", ".join(ins["operands"])
    return text if len(text) <= width else text[: width - 1] + "…"


def after_info(sites, name):
    """The transition function of one site: its Lean text, its decision tree, and whether its
    type is `Option (Option D)` (the thread can die in the code after the event)."""
    site = sites.by_name[name]
    ins = sites.code[site["pc"]]
    terms = translit.PathTerms(sites.code, sites.ids, sites.data)
    args = seed(sites, site, terms)
    node = translit.tree(sites.code, sites.ids, sites.data, site["pc"] + 1, terms)
    for leaf in leaves(node):
        if leaf[0] == "tail":
            sites.tail(leaf[1])
    outcome = is_outcome(sites, node)
    ty = "Option (Option D)" if outcome else "D"
    head = f"/-- After `{name}` ({site['pc']}: `{brief(ins)}`). -/"
    sig = (
        f"def after_{name} (L : Launch) (g : Nat) (d : D) {' '.join(args)}".rstrip() + f" : {ty} :="
    )
    return "\n".join([head, sig, *render(sites, node, 2, outcome)]), node, outcome


def after(sites, name):
    """The transition function of one site, as Lean text."""
    return after_info(sites, name)[0]


def main():
    cli = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    cli.add_argument("--show", nargs="*")
    cli.add_argument("--coverage", action="store_true")
    args = cli.parse_args()
    sites = Sites()
    if args.show:
        for name in args.show:
            print(after(sites, name))
            print()
    if args.coverage:
        ok, bad = collections.Counter(), collections.Counter()
        for s in sites.sites:
            kind = s["name"].rsplit("_", 1)[0]
            if kind in ("exit", "trap"):
                ok[kind] += 1
                continue
            try:
                after(sites, s["name"])
                ok[kind] += 1
            except translit.Unsupported as e:
                why = re.sub("[0-9]+|\\[.*", "", str(e).split(": ", 1)[-1])[:44]
                bad[(kind, why)] += 1
        print("emitted:", sum(ok.values()), dict(ok))
        print("not yet:", sum(bad.values()))
        for (kind, why), n in sorted(bad.items(), key=lambda x: -x[1]):
            print(f"  {n:4d} {kind:14s} {why}")


if __name__ == "__main__":
    main()
