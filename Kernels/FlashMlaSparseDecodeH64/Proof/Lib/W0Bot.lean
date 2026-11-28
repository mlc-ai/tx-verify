-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.W0Sum

@[expose] public section

/-! # No true maximum, no weight

A lane whose true maximum (`w0MxCarry`) is still `-inf` after some blocks has kept no column in
any of them: the maximum takes the larger of every block's own maximum, and a block's own maximum
is `-inf` only if every one of its scores is. So the weights of those blocks are all zero. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX

noncomputable section

theorem w0Loc_bot {sc : ℝ} (hsc : 0 < sc) {w : W0Words} (h : w0Loc sc w = ⊥) :
    ∀ i < 32, w0Score w i = ⊥ := by
  intro i hi
  have hs : (Finset.range 32).sup (w0Score w) = ⊥ := by
    unfold w0Loc at h
    generalize (Finset.range 32).sup (w0Score w) = S at h
    induction S using EReal.rec with
    | bot => rfl
    | top => rw [EReal.coe_mul_top_of_pos hsc] at h; exact absurd h (by simp)
    | coe x => rw [← EReal.coe_mul] at h; exact absurd h (EReal.coe_ne_bot _)
  have hle : w0Score w i ≤ (Finset.range 32).sup (w0Score w) :=
    Finset.le_sup (f := w0Score w) (Finset.mem_range.mpr hi)
  rw [hs] at hle
  exact le_bot_iff.mp hle

theorem w0MxCarry_bot {sc : ℝ} (hsc : 0 < sc) (bs : List (List Event))
    (h : w0MxCarry sc bs = ⊥) : w0SumWt sc bs = 0 := by
  induction bs using List.reverseRecOn with
  | nil => simp [w0SumWt]
  | append_singleton bs seg ih =>
    rw [w0MxCarry_snoc, max_eq_bot] at h
    have h0 := ih h.1
    have h1 := w0Loc_bot hsc (max_eq_bot.mp h.2).1
    have h2 : w0BlockWt sc seg = 0 :=
      Finset.sum_eq_zero fun i hi => by
        simp [w0Wt, h1 i (Finset.mem_range.mp hi)]
    simp [w0SumWt, h2] at h0 ⊢
    exact h0

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
