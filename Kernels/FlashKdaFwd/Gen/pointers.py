# SPDX-License-Identifier: Apache-2.0
"""Generic shared pointers of the swizzled addressing: what the thread generator uses.

The kernel addresses its FP32 state buffer through generic pointers: `cvta.shared.u64` makes a
generic pointer of the shared window's base, `add.s64` moves it, and the swizzle `shr.u64`,
`and.b64`, `xor.b64` gives the pointer a generic `ld.b32` or `st.b32` uses. In the thread
machine every such register is an opaque slot and each of these instructions is an item of a
data run (`Proof/Thread/PtrRules.lean`).

A library of `emit.py` and `thread.py`. It writes no file, so there is nothing to regenerate
or to check.

* `pointer_registers(code)`: the registers that hold a generic shared pointer or a word
  computed from one (`emit.Sites` adds them to the opaque registers).
* `FN`: the run items of the pointer forms, in the format of `thread.DATA_FN`
  (`thread.run_files` adds them to the declarations of the runs with pointer arithmetic).
* `classify`, `shape`, `census`: the local code after each site as a string of classes (`C`
  control, `V` `cvta.shared.u64`, `R`/`K` `add.s64` with a register / a constant, `S` shift,
  `A` and, `X` xor, `D` other data, `b` a branch), per path.

Its one command is a reading aid: it reads the frozen PTX and `Flow/flow.json` (through
`emit.Sites`) and prints the shapes of the sites whose local code has a pointer instruction.

    python3 Kernels/FlashKdaFwd/Gen/pointers.py --census
"""

import collections
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

POINTER_SOURCES = ("cvta.shared.u64",)

# opcode (and source shape) -> kind, instruction term, outcome function, reading lemma
FN = {
    "add.s64#imm": ("add64K", "add64KOp", "add64KE", "rule_add64K"),
    "add.s64": ("add64", "add64Op", "add64E", "rule_add64"),
    "shr.u64#imm": ("swShr", "swShrOpK", "swShrEK", "rule_swShrK"),
    "and.b64#imm": ("and64", "and64Op", "and64E", "rule_and64"),
    "xor.b64": ("swXor", "swXorOp", "swXorE", "rule_swXor"),
}
CLASS = {"cvta.shared.u64": "V", "shr.u64": "S", "and.b64": "A", "xor.b64": "X"}


def pointer_registers(code):
    """The registers derived from a generic shared pointer by local instructions."""
    ptr = set()
    for ins in code:
        if ins["opcode"] in POINTER_SOURCES:
            ptr.update(ins["writes"])
    changed = True
    while changed:
        changed = False
        for ins in code:
            if not ins["event"] and any(r in ptr for r in ins["reads"]):
                new = set(ins["writes"]) - ptr
                if new:
                    ptr |= new
                    changed = True
    return ptr


def classify(ins, ptr, data):
    """The class of a local instruction (see the module docstring)."""
    if any(w in ptr for w in ins["writes"]):
        if ins["opcode"] == "add.s64":
            return "R" if ins["operands"][-1].startswith("%") else "K"
        return CLASS[ins["opcode"]]
    if any(w in data for w in ins["writes"]):
        return "D"
    return "C"


def shape(sites, site, ptr):
    """The classes of the local code after `site`, one string per path of the flow table."""
    code, out = sites.code, []
    for row in site["next"]:
        taken = {c[2]: c[1] for c in row["conditions"]}
        pc, text = site["pc"] + 1, ""
        while pc < len(code) and not code[pc]["event"]:
            ins = code[pc]
            if ins["target"] is not None:
                if ins["guard"] is None:
                    pc = ins["target"]
                    continue
                text += "b"
                pc = ins["target"] if taken.get(pc) else pc + 1
                continue
            text += classify(ins, ptr, sites.data)
            pc += 1
        text = re.sub(r"(.)\1+", lambda m: m.group(1) + str(len(m.group(0))), text)
        out.append((text, row["to"]))
    return out


def census(sites):
    """The shapes of the sites whose segment has a pointer instruction, with counts."""
    ptr = pointer_registers(sites.code)
    count, example = collections.Counter(), {}
    for s in sites.sites:
        paths = shape(sites, s, ptr)
        if not any(re.search("[VRKSAX]", t) for t, _ in paths):
            continue
        kind = s["name"].rsplit("_", 1)[0]
        key = (
            kind,
            tuple((re.sub(r"(?<=[CD])\d+", "n", t), to.rsplit("_", 1)[0]) for t, to in paths),
        )
        count[key] += 1
        example.setdefault(key, (s["name"], s["pc"]))
    return count, example


def main():
    if "--census" in sys.argv:
        import emit

        sites = emit.Sites()
        count, example = census(sites)
        for key, n in sorted(count.items(), key=lambda kv: -kv[1]):
            print(n, key[0], list(key[1]), "e.g.", example[key])
        print(sum(count.values()), "sites")


if __name__ == "__main__":
    main()
