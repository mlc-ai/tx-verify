-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Spec
public import Kernels.FlashMlaSparseDecodeH64.Assumptions.Numerics
import Mathlib.Tactic.IntervalCases

@[expose] public section

/-! # Columns of the output and the bytes of a staged pair

An output column `d < 512` is `128 w + off c + i` (warp `w < 2`, chunk `c < 4`, `i < 64`,
`off = [0, 64, 256, 320]`, `col_decomp`). The slot at column `i` and byte `z` reads byte
`(2 (i % 8) + z) % 4` of the staging word `(2 (i % 8) + z) / 4` of the 16-byte chunk `i / 8`; that
word holds the columns `2 (4 (i / 8) + el)` and the next (`col_word`), and the byte is the byte
`z` of the low column for an even `i` and of the high column for an odd one (`pair_byte`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX

/-- **An output column** is a warp's, a chunk's and an index of the 64 columns. -/
theorem col_decomp {d : Nat} (hd : d < 512) :
    ∃ w c i, w < 2 ∧ c < 4 ∧ i < 64 ∧ d = 128 * w + [0, 64, 256, 320].getD c 0 + i := by
  rcases (by omega : d < 64 ∨ (64 ≤ d ∧ d < 128) ∨ (128 ≤ d ∧ d < 192) ∨ (192 ≤ d ∧ d < 256) ∨
      (256 ≤ d ∧ d < 320) ∨ (320 ≤ d ∧ d < 384) ∨ (384 ≤ d ∧ d < 448) ∨ 448 ≤ d) with
    h | h | h | h | h | h | h | h
  · exact ⟨0, 0, d, by omega, by omega, by omega, by simp⟩
  · exact ⟨0, 1, d - 64, by omega, by omega, by omega, by simp; omega⟩
  · exact ⟨1, 0, d - 128, by omega, by omega, by omega, by simp; omega⟩
  · exact ⟨1, 1, d - 192, by omega, by omega, by omega, by simp; omega⟩
  · exact ⟨0, 2, d - 256, by omega, by omega, by omega, by simp; omega⟩
  · exact ⟨0, 3, d - 320, by omega, by omega, by omega, by simp; omega⟩
  · exact ⟨1, 2, d - 384, by omega, by omega, by omega, by simp; omega⟩
  · exact ⟨1, 3, d - 448, by omega, by omega, by omega, by simp; omega⟩

/-- **The word of a slot's byte**: byte `z` of column `i` is byte `s` of the word `el` of the chunk
`i / 8`, whose low column is `i` (even `i`, `s = z`) or `i - 1` (odd `i`, `s = z + 2`). -/
theorem col_word {i z : Nat} (hz : z < 2) :
    ((2 * (i % 8) + z) % 4 = z ∧ i % 2 = 0 ∧ 2 * (4 * (i / 8) + (2 * (i % 8) + z) / 4) = i) ∨
    ((2 * (i % 8) + z) % 4 = z + 2 ∧ i % 2 = 1 ∧
      2 * (4 * (i / 8) + (2 * (i % 8) + z) / 4) + 1 = i) := by
  omega

/-- **A byte of a staged pair** (`bf16Pair`): bytes 0 and 1 of the low number, 2 and 3 of the
high one. -/
theorem pair_byte (x y : ℝ) {s : Nat} (hs : s < 4) :
    (Assumptions.bf16Pair x y).toBytes[s]? =
      some (if s < 2 then (Value.float .bf16 x, s) else (Value.float .bf16 y, s - 2)) := by
  interval_cases s <;>
    simp [Assumptions.bf16Pair, Value.toBytes, Value.bytes, Value.byteAt, FloatFmt.bytes]

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
