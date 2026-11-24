# SPDX-License-Identifier: Apache-2.0
"""Generate sparse integer liveness; Lean checks all source CFG/producer edges."""

import argparse
import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from decoded_ops import App, dest_ids, instructions, operand_regs, option_value, walk  # noqa: E402

# Instructions after which the program does not continue.
TERMINAL = {"ret", "exit", "trap"}
# The integer operations whose registers the tables follow (`IntOp` constructors).
INT_OPS = {"neg", "add", "sub", "and", "or", "xor", "shl", "shr", "setp"}
# `IntOp.mul` and `IntOp.mad` modes that are followed: the low half, and the widening product.
MUL_MODES = {"mul": {"lo", "wide"}, "mad": {"lo"}}


def int_family(op: App) -> str | None:
    """The kind of an instruction of the integer family, by the PTX it was written as, or none."""
    iop = op.args[0]["op"]
    if iop.name in MUL_MODES:
        return iop.name if iop.args[0].name in MUL_MODES[iop.name] else None
    if iop.name in INT_OPS or iop.name == "selp":
        return iop.name
    return None


def unsigned_conversion(op: App) -> bool:
    """A `cvt` between unsigned integer types."""
    c = op.args[0]
    return all(t.name == "int" and t.args[0].name == "u" for t in (c["dst"], c["src"]))


def classify(op: App) -> str:
    """The name the tables use for an instruction: the family of an integer operation, a scalar
    move, an unsigned conversion, or the constructor."""
    if op.name == "int":
        return int_family(op) or "other"
    if op.name == "move":
        return "mov" if op.args[0]["kind"].name == "scalar" else "other"
    if op.name == "cvt":
        return "cvtUnsigned" if unsigned_conversion(op) else "other"
    if op.name == "warp":
        return op.args[0]["kind"].name if op.args[0]["kind"].name == "shfl" else "other"
    if op.name == "addr":
        return op.args[0].name
    return op.name


def destination(op: App) -> int:
    """The id of the register an instruction writes (its first destination)."""
    if op.name == "clcQuery":
        return op.args[1]
    first = dest_ids(op.args[0])[0]
    if first is None:
        raise ValueError("instruction discards its first destination")
    return first


def generate(root: Path) -> None:
    kernel = root / "Kernels/Fp16Gemm8192"
    decoded = (kernel / "Data/Decoded.lean").read_text()
    records = instructions(kernel / "Data/Decoded.lean")
    names = re.findall(r'"([^"]*)"', decoded[decoded.index("regNames := [") :].split("]")[0])
    integer_ops = {
        "mov",
        "cvtUnsigned",
        "neg",
        "add",
        "sub",
        "mul",
        "and",
        "or",
        "xor",
        "shl",
        "shr",
        "setp",
        "mad",
        "bra",
    }
    pointer_destinations = {names.index(n) for n in ("%rd9", "%r724", "%r744", "%r764", "%r704")}
    rows = []
    for pc, record in enumerate(records):
        guard = option_value(record["guard"])
        op = record["op"]
        kind = classify(op)
        reads = operand_regs(op)
        selected = kind in integer_ops
        if kind == "mov" and any(isinstance(t, App) and t.name == "paramSym" for t in walk(op)):
            selected = False
        if kind in {"add", "sub", "cvtUnsigned"} and destination(op) in pointer_destinations:
            selected = False
        definitions = []
        if selected and kind not in {"setp", "bra"}:
            definitions = [destination(op)]
        if kind == "selp":
            # The first two sources are the values; the third is the selector predicate.
            if operand_regs(op.args[0]["srcs"][:2]):
                raise ValueError("Review non-constant scalar selector before extending")
            definitions = [destination(op)]
        if kind == "shfl" or (
            kind == "clcQuery"
            and any(isinstance(t, App) and t.head.endswith("ClcQuery.first") for t in walk(op))
        ):
            definitions = [destination(op)]
        if kind in TERMINAL:
            successors = []
        elif kind == "bra":
            successors = [op.args[0]]
        elif kind == "brx":
            raise ValueError(f"Instruction {pc} is an indexed branch")
        else:
            successors = [pc + 1]
        guarded = guard is not None
        if guarded:
            successors.append(pc + 1)
        if any(target >= len(records) for target in successors):
            raise ValueError(f"Instruction {pc} has an outside successor")
        required_reads = (
            reads
            if selected
            or (kind == "mapa" and op.args[0].args[0].name == "false" and op.args[0].args[1] == 32)
            else []
        )
        if kind == "cpTensor":
            if len(reads) != 3 or not any(
                isinstance(t, App) and t.name == "none" for t in walk(op)
            ):
                raise ValueError(f"Review tensor operand shape at instruction {pc}")
            # The first register is an opaque map pointer, not integer bits.
            required_reads = reads[1:]
        rows.append((required_reads, definitions, successors, guarded))
    live = [set() for _ in rows]
    while True:
        next_live = []
        for reads, definitions, successors, guarded in rows:
            required = (
                set().union(*(live[target] for target in successors)) if successors else set()
            )
            if not guarded:
                required.difference_update(definitions)
            required.update(reads)
            next_live.append(required)
        if next_live == live:
            break
        live = next_live
    if live[0]:
        raise ValueError(f"Uninitialized integer requirements: {sorted(live[0])}")
    table = json.dumps(
        [
            [sorted(required) for required in live[start : start + 32]]
            for start in range(0, len(live), 32)
        ]
    )
    output = kernel / "Proof/ProductionSourceIntegerLiveTable.lean"
    output.write_text(
        "-- SPDX-License-Identifier: Apache-2.0\n"
        "import Kernels.Fp16Gemm8192.Spec\n"
        "namespace PTX.Kernels.Fp16Gemm8192.ProductionSourceIntegerLive\n"
        "set_option maxHeartbeats 0\nset_option maxRecDepth 100000\n"
        "def requiredBitsTable : List (List (List Nat)) :=\n"
        + table
        + "\ndef requiredBits (pc : Nat) : List Nat :=\n  ((requiredBitsTable[pc/32]?).getD [])[pc%32]?.getD []\n"
        "end PTX.Kernels.Fp16Gemm8192.ProductionSourceIntegerLive\n"
    )
    print(f"Wrote {len(records)} rows; initial integer requirements empty")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    generate(parser.parse_args().root)
