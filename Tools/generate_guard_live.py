# SPDX-License-Identifier: Apache-2.0
"""Generate the guard liveness table; Lean independently checks every CFG edge."""

import argparse
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from decoded_ops import dest_ids, instructions, option_value  # noqa: E402

# Instructions after which the program does not continue.
TERMINAL = {"ret", "exit", "trap"}


def generate(root: Path) -> None:
    kernel = root / "Kernels/Fp16Gemm8192"
    records = instructions(kernel / "Data/Decoded.lean")
    rows = []
    for pc, record in enumerate(records):
        guard = option_value(record["guard"])
        op = record["op"]
        family = op.name
        definitions = []
        if family == "int" and op.args[0]["op"].name == "setp":
            definitions = [dest_ids(op.args[0])[0]]
        if family == "mbarWait":
            definitions = [op.args[0]]
        if family == "warp" and op.args[0]["kind"].name == "elect":
            ids = dest_ids(op.args[0])
            if len(ids) != 2 or ids[0] is not None or ids[1] is None:
                raise ValueError(
                    "Review election destination parsing before extending this generator"
                )
            definitions = [ids[1]]
        successors = []
        if family == "bra":
            if not isinstance(op.args[0], int):
                raise ValueError(f"Instruction {pc} has a nonliteral branch target")
            successors = [op.args[0]]
        elif family == "brx":
            raise ValueError(f"Instruction {pc} is an indexed branch")
        elif family not in TERMINAL:
            successors = [pc + 1]
        if guard is not None:
            successors.append(pc + 1)
        if any(target >= len(records) for target in successors):
            raise ValueError(f"Instruction {pc} has an out-of-code successor")
        rows.append((guard[0] if guard is not None else None, definitions, successors))
    live = [set() for _ in records]
    while True:
        next_live = []
        for guard, definitions, successors in rows:
            required = (
                set().union(*(live[target] for target in successors)) if successors else set()
            )
            if guard is None:
                required.difference_update(definitions)
            else:
                required.add(guard)
            next_live.append(required)
        if next_live == live:
            break
        live = next_live
    if live[0]:
        raise ValueError(f"Initial source state requires predicates: {sorted(live[0])}")
    table = json.dumps([sorted(required) for required in live])
    output = kernel / "Proof/ProductionSourceGuardSafetyTable.lean"
    output.write_text(
        "-- SPDX-License-Identifier: Apache-2.0\n"
        "import Kernels.Fp16Gemm8192.Spec\n"
        "namespace PTX.Kernels.Fp16Gemm8192.ProductionSourceGuardSafety\n"
        "set_option maxHeartbeats 0\n"
        "set_option maxRecDepth 100000\n"
        "def requiredPredTable : List (List Nat) :=\n"
        + table
        + "\ndef requiredPreds (pc : Nat) : List Nat := requiredPredTable[pc]?.getD []\n"
        "end PTX.Kernels.Fp16Gemm8192.ProductionSourceGuardSafety\n"
    )
    print(
        f"Wrote {output}: {len(records)} instructions; {sum(map(len, live))} predicate requirements"
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    generate(parser.parse_args().root)
