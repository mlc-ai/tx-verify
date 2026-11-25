# SPDX-License-Identifier: Apache-2.0
"""Readable listings of the frozen program: a reading aid, not a proof input.

Reads the frozen PTX (through `analysis.load`) and writes two text files into the directory
given on the command line (nothing in the repository, so there is nothing to check):

* `instrs.txt`: every instruction with its 0-based index (the decoder's program counter) and the
  labels in front of it; the mangled parameter names are shortened to `PARAMn`;
* `skeleton.txt`: only the event sites and the branches (with their target index), runs of
  local instructions collapsed to a count.

    python3 Kernels/FlashKdaFwd/Gen/listing.py <directory>
"""

import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import analysis  # noqa: E402  (also puts `Tools/` on the path)
import parse_ptx  # noqa: E402


def labels_by_pc():
    """The labels in front of each instruction index, in source order."""
    program = parse_ptx.parse(analysis.PTX.read_text())
    function = next(f for f in program.functions if not f.declaration)
    out, pending, pc = {}, [], 0

    def walk(body):
        nonlocal pc, pending
        for s in body:
            if s.kind == "label":
                pending.append(s.text)
            elif s.kind == "instruction":
                if pending:
                    out[pc], pending = pending, []
                pc += 1
            elif s.kind == "scope":
                walk(s.body)

    walk(function.body)
    return out


def line(ins, width=170):
    g = ins["guard"]
    guard = ("@" + ("!" if g["negated"] else "") + g["register"] + " ") if g else ""
    return f"{ins['pc']:5d}  {guard}{ins['opcode']} {', '.join(ins['operands'])}"[:width]


def main():
    if len(sys.argv) != 2:
        sys.exit(__doc__)
    out = Path(sys.argv[1])
    out.mkdir(parents=True, exist_ok=True)
    code, _, _ = analysis.load()
    labels = labels_by_pc()
    full, skeleton, run = [], [], 0
    skeleton.append("# Event sites, branches and labels (0-based instruction index = pc).")
    skeleton.append("# Runs of local (register-only) instructions are collapsed to a count.")
    for ins in code:
        for label in labels.get(ins["pc"], []):
            full.append(f"      {label}:")
        full.append(line(ins, 400))
        branch = ins["target"] is not None
        if not (ins["event"] or branch or ins["pc"] in labels):
            run += 1
            continue
        if run:
            skeleton.append(f"        ... {run} local")
            run = 0
        for label in labels.get(ins["pc"], []):
            skeleton.append(f"  {label}:")
        if ins["event"] or branch:
            skeleton.append(line(ins) + (f"   -> {ins['target']}" if branch else ""))
        else:
            run += 1
    (out / "instrs.txt").write_text("\n".join(full) + "\n")
    (out / "skeleton.txt").write_text("\n".join(skeleton) + "\n")
    print(f"{len(code)} instructions -> {out}/instrs.txt, {out}/skeleton.txt")


if __name__ == "__main__":
    main()
