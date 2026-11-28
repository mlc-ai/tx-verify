-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.InklingRelDecode.Proof.Lib.FoldPw

@[expose] public section

/-! # The sum of a round's block, by halves

The sum of the exponentials of a round's block of the lane's row (relative to the maximum the
round uses) is the sum of the two halves' words: the lane's 64 columns and the other half's. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX Finset SoftRow SoftFold Classical

/-- The sum of the round `i`'s block of the lane's row relative to the maximum the round uses. -/
noncomputable def laneSum (Q : Params) (L : Launch) (g i : Nat) : ℝ :=
  ((laneBlk Q L g i).map (pExp (Q.scale * log2eF32)
    (mUseOf (Q.scale * log2eF32) (laneBlk Q L g i) (laneSt Q L g i)))).sum

theorem laneSum_fold (Q : Params) (L : Launch) (g i : Nat) :
    laneSum Q L g i = ∑ κ ∈ range 128, foldPw Q L (g / L.block) i (softRow (g % L.block)) κ := by
  unfold laneSum laneBlk
  rw [kBlk_sum]
  rw [← sum_block Q ((L.ctaidOf (g / L.block)).get .z) ((L.ctaidOf (g / L.block)).get .x)
    (softRow (g % L.block) / 6) i]
  refine sum_congr rfl fun κ _ => ?_
  unfold foldPw laneHead laneSt
  rfl

/-- **The two halves' sums add up to the block's.** The partner `gp` is in the same CTA and row,
on the other half. -/
theorem laneSum_halves (Q : Params) (L : Launch) {g gp : Nat} (i : Nat) (hs : 0 < Q.splits)
    (hsc : 0 < Q.scale)
    (hi : i < Q.numIters ((L.ctaidOf (g / L.block)).get .z) ((L.ctaidOf (g / L.block)).get .x))
    (hc : gp / L.block = g / L.block) (hr : softRow (gp % L.block) = softRow (g % L.block))
    (hh : gp % L.block / 16 % 2 = 1 - g % L.block / 16 % 2) :
    (∑ c ∈ range 64, lanePw Q L g i c) + ∑ c ∈ range 64, lanePw Q L gp i c =
      laneSum Q L g i := by
  have hi' : i < Q.numIters ((L.ctaidOf (gp / L.block)).get .z)
      ((L.ctaidOf (gp / L.block)).get .x) := by rw [hc]; exact hi
  have e1 : ∑ c ∈ range 64, lanePw Q L g i c = ∑ c ∈ range 64,
      foldPw Q L (g / L.block) i (softRow (g % L.block)) (64 * (g % L.block / 16 % 2) + c) :=
    sum_congr rfl fun c hc' => lanePw_eq Q L g i c hs hsc hi (mem_range.mp hc')
  have e2 : ∑ c ∈ range 64, lanePw Q L gp i c = ∑ c ∈ range 64,
      foldPw Q L (g / L.block) i (softRow (g % L.block))
        (64 * (1 - g % L.block / 16 % 2) + c) := by
    refine sum_congr rfl fun c hc' => ?_
    rw [lanePw_eq Q L gp i c hs hsc hi' (mem_range.mp hc'), hc, hr, hh]
  rw [e1, e2, laneSum_fold, show (128 : Nat) = 64 + 64 from rfl, sum_range_add]
  rcases Nat.mod_two_eq_zero_or_one (g % L.block / 16) with h | h <;> rw [h]
  · simp
  · simp [add_comm]

end PTX.Kernels.InklingRelDecode.Proof.Lib
