-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Data.Nat.Basic

@[expose] public section

/-! Address geometry of the production 8192-square FP16 GEMM.

These are arithmetic facts about the production address formulas, independent of
instruction execution, memory visibility and task ownership. A cluster task selects a
512 x 256 output tile. Two CTAs and two consumers partition its 512 rows; eight
epilogue slices partition its 256 columns. -/
namespace PTX.Kernels.Fp16Gemm8192

/-- Row tile selected by the L2-grouped cluster task permutation. -/
def tileM (task : Nat) : Nat := 8 * (task / 256) + task % 8

/-- Column tile selected by the L2-grouped cluster task permutation. -/
def tileN (task : Nat) : Nat := (task % 256) / 8

/-- Inverse task permutation, for `m < 16` and `n < 32`. -/
def taskOfTile (m n : Nat) : Nat := 256 * (m / 8) + 8 * n + m % 8

theorem tileM_lt {task : Nat} (ht : task < 512) : tileM task < 16 := by
  unfold tileM
  omega

theorem tileN_lt (task : Nat) : tileN task < 32 := by
  unfold tileN
  omega

theorem taskOfTile_lt {m n : Nat} (hm : m < 16) (hn : n < 32) :
    taskOfTile m n < 512 := by
  unfold taskOfTile
  omega

theorem tileM_taskOfTile (m : Nat) {n : Nat} (hn : n < 32) :
    tileM (taskOfTile m n) = m := by
  unfold tileM taskOfTile
  omega

theorem tileN_taskOfTile (m : Nat) {n : Nat} (hn : n < 32) :
    tileN (taskOfTile m n) = n := by
  unfold tileN taskOfTile
  omega

/-- Row written by one consumer lane in one CTA of a cluster tile.
The two CTA pieces of one consumer's rows are not adjacent global row intervals. -/
def outputRow (m rank consumer row : Nat) : Nat :=
  512 * m + 256 * rank + 128 * consumer + row

/-- Column written by one epilogue slice of a cluster tile. -/
def outputCol (n slice col : Nat) : Nat := 256 * n + 32 * slice + col

theorem outputRow_lt {m rank consumer row : Nat} (hm : m < 16) (hr : rank < 2)
    (hg : consumer < 2) (hu : row < 128) : outputRow m rank consumer row < 8192 := by
  unfold outputRow
  omega

theorem outputCol_lt {n slice col : Nat} (hn : n < 32) (hs : slice < 8)
    (hv : col < 32) : outputCol n slice col < 8192 := by
  unfold outputCol
  omega

theorem outputRow_injective {m rank consumer row m' rank' consumer' row' : Nat}
    (hr : rank < 2) (hg : consumer < 2) (hu : row < 128)
    (hr' : rank' < 2) (hg' : consumer' < 2) (hu' : row' < 128)
    (h : outputRow m rank consumer row = outputRow m' rank' consumer' row') :
    m = m' ∧ rank = rank' ∧ consumer = consumer' ∧ row = row' := by
  unfold outputRow at h
  omega

theorem outputCol_injective {n slice col n' slice' col' : Nat}
    (hs : slice < 8) (hv : col < 32) (hs' : slice' < 8) (hv' : col' < 32)
    (h : outputCol n slice col = outputCol n' slice' col') :
    n = n' ∧ slice = slice' ∧ col = col' := by
  unfold outputCol at h
  omega

theorem outputRow_decompose (i : Nat) :
    outputRow (i / 512) (i % 512 / 256) (i % 256 / 128) (i % 128) = i := by
  unfold outputRow
  omega

theorem outputCol_decompose (j : Nat) :
    outputCol (j / 256) (j % 256 / 32) (j % 32) = j := by
  unfold outputCol
  omega

theorem outputRow_decomposition_bounds {i : Nat} (hi : i < 8192) :
    i / 512 < 16 ∧ i % 512 / 256 < 2 ∧ i % 256 / 128 < 2 ∧ i % 128 < 128 := by
  omega

theorem outputCol_decomposition_bounds {j : Nat} (hj : j < 8192) :
    j / 256 < 32 ∧ j % 256 / 32 < 8 ∧ j % 32 < 32 := by
  omega

/-- Every output element has a valid task/CTA/consumer/lane/slice decomposition. -/
theorem output_cover {i j : Nat} (hi : i < 8192) (hj : j < 8192) :
    ∃ task rank consumer row slice col : Nat,
      task < 512 ∧ rank < 2 ∧ consumer < 2 ∧ row < 128 ∧ slice < 8 ∧ col < 32 ∧
      outputRow (tileM task) rank consumer row = i ∧
      outputCol (tileN task) slice col = j := by
  obtain ⟨hm, hr, hg, hu⟩ := outputRow_decomposition_bounds hi
  obtain ⟨hn, hs, hv⟩ := outputCol_decomposition_bounds hj
  refine ⟨taskOfTile (i / 512) (j / 256), i % 512 / 256, i % 256 / 128,
    i % 128, j % 256 / 32, j % 32, taskOfTile_lt hm hn, hr, hg, hu, hs, hv, ?_, ?_⟩
  · rw [tileM_taskOfTile _ hn]
    exact outputRow_decompose i
  · rw [tileN_taskOfTile _ hn]
    exact outputCol_decompose j

end PTX.Kernels.Fp16Gemm8192
