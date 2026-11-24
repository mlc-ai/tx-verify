"""Turn a recorded forward into a Lean input table and dyadic state witnesses."""

import json
from fractions import Fraction as F
from pathlib import Path


def generate(record):
    rows = []
    state = [F(1, 4), F(-1, 8), F(1, 16)]
    for q, k, value, word in zip(
        record["query_numerators"],
        record["key_numerators"],
        record["value_numerators"],
        record["output_bf16"],
        strict=True,
    ):
        key = [F(x * 125, 15641) for x in k]
        correction = (F(value, 8) - sum(s * j for s, j in zip(state, key, strict=True))) / 2
        state = [s + correction * j for s, j in zip(state, key, strict=True)]
        approx = [round(s * 2**30) for s in state]

        def triple(v):
            return "⟨" + ", ".join(map(str, v)) + "⟩"

        rows.append(f"  ⟨{triple(q)}, {triple(k)}, {value}, 0x{word:04x}, {triple(approx)}⟩")

    def state_words(words):
        return ", ".join(f"0x{w:08x}" for w in words)

    init = state_words(record["initial_state_fp32"])
    final = state_words(record["tiles"][-1]["measured_exit_fp32"])
    packed = record["packed"]
    packed_final = state_words(packed["final_state_fp32"])
    words = [f"0x{w:04x}" for w in packed["output_bf16"]]
    packed_rows = ",\n".join("  " + ", ".join(words[i : i + 8]) for i in range(0, len(words), 8))
    corrections = [w for block in record["tiles"] for w in block["correction_bf16"]]
    correction_rows = ",\n".join(
        "  " + ", ".join(f"0x{word:04x}" for word in corrections[i : i + 8])
        for i in range(0, len(corrections), 8)
    )
    middle = ",\n".join(
        f"  ({state_words(block['measured_exit_fp32'])})" for block in record["tiles"][:-1]
    )
    gaps = ",\n".join("  " + block["exit_gap_upper"] for block in record["tiles"])
    inverse_words = [w for tile in record["tiles"] for w in tile["inverse"]["words_bf16"]]
    inverse_rows = ",\n".join(
        "  " + ", ".join(f"0x{w:04x}" for w in inverse_words[i : i + 8])
        for i in range(0, len(inverse_words), 8)
    )
    return (
        """-- SPDX-License-Identifier: Apache-2.0
-- Generated from the GB300 measurement by checks/residual_data.py.
module
public import Mathlib.Data.Rat.Defs
@[expose] public section
namespace FlashKda.Sample
structure Triple where
  a : ℚ
  b : ℚ
  c : ℚ
  deriving Inhabited
structure Measurement where
  query : Triple
  key : Triple
  value : ℚ
  outputWord : Nat
  stateNumerator : Triple
  deriving Inhabited
def measurements : Array Measurement := #[
"""
        + ",\n".join(rows)
        + f"]\ndef initialWords : Nat × Nat × Nat := ({init})\n"
        + f"def finalWords : Nat × Nat × Nat := ({final})\n"
        + f"def packedWords : Array Nat := #[\n{packed_rows}]\n"
        + f"def packedFinal : Nat × Nat × Nat := ({packed_final})\n"
        + f"def correctionWords : Array Nat := #[\n{correction_rows}]\n"
        + f"def carryWords : Array (Nat × Nat × Nat) := #[initialWords,\n{middle}, finalWords]\n"
        + f"def gapBounds : Array ℚ := #[\n{gaps}]\n"
        + f"def inverseWords : Array Nat := #[\n{inverse_rows}]\nend FlashKda.Sample\n"
    )


if __name__ == "__main__":
    import sys

    print(generate(json.loads(Path(sys.argv[1]).read_text())), end="")
