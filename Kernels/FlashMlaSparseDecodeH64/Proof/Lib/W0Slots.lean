-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.W0Sum
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Result.Run
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Reads

@[expose] public section

/-! # The lane's block weights are the reference's

The cache tag and the slot position of a block (`w0BlockExtra`, `w0BlockSlot`, in the lane's
terms) are the reference's (`Result.blockExtra`, `Result.blockSlot`). A column whose score and
mask word read as the reference's has the reference's weight (`w0Wt_eq_weight`), and the sum of a
list of blocks' weights is the sum over the block indices (`w0SumWt_eq`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX

noncomputable section

theorem w0OrigBlocks_eq (P : Params) (e : Nat) :
    w0OrigBlocks P e = Result.numOrigBlocks (P.topkLen e) := by
  unfold w0OrigBlocks Result.numOrigBlocks Result.origPadded Result.ceilToMultiple
    Result.topkBlock
  omega

theorem w0BlockExtra_eq (P : Params) (e t : Nat) :
    w0BlockExtra P e t = Result.blockExtra P e t := by
  unfold w0BlockExtra Result.blockExtra Result.isExtraBlock
  rw [w0OrigBlocks_eq]

theorem w0BlockSlot_eq (P : Params) (e t j : Nat) :
    w0BlockSlot P e t j = Result.blockSlot P e t j := by
  unfold w0BlockSlot Result.blockSlot
  rw [w0BlockExtra_eq]
  cases hc : Result.blockExtra P e t
  · simp [Result.topkBlock]
  · have ho : w0OrigBlocks P e = Result.origBlocks P e := w0OrigBlocks_eq P e
    simp [ho, Result.topkBlock]

/-- **A column that reads as the reference has the reference's weight.** -/
theorem w0Wt_eq_weight {sc : ℝ} {w : W0Words} {i : Nat} {P : Params} {e q h : Nat} {x : Bool}
    {j : Nat} (hsc : sc = P.scale)
    (hs : w0Bit w.mw i = true → w0F (w.hi.getD i (.pred false)) + w0PeerF w i =
      score P e q h x j)
    (hm : w0Bit w.mw i = true ↔ slotValid P e q x j) :
    w0Wt sc (w0Score w i) = weight P e q h x j := by
  unfold w0Wt w0Score weight
  by_cases hb : w0Bit w.mw i = true
  · have hv := hm.mp hb
    simp only [hb, ↓reduceIte, hv, EReal.coe_ne_bot, EReal.toReal_coe, hs hb, hsc]
  · have hv : ¬ slotValid P e q x j := fun h => hb (hm.mpr h)
    simp [hb, hv]

theorem w0SumWt_eq (sc : ℝ) (bs : List (List Event)) (g : Nat → ℝ)
    (hg : ∀ t seg, bs[t]? = some seg → w0BlockWt sc seg = g t) :
    w0SumWt sc bs = ∑ t ∈ Finset.range bs.length, g t := by
  induction bs using List.reverseRecOn with
  | nil => simp [w0SumWt]
  | append_singleton bs seg ih =>
    have h1 := ih (fun t s h => hg t s (by
      rw [List.getElem?_append_left (by
        have := (List.getElem?_eq_some_iff.mp h).1; exact this)]; exact h))
    have h2 := hg bs.length seg (by simp)
    simp only [w0SumWt, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero, List.length_append, List.length_singleton,
      Finset.sum_range_succ] at h1 ⊢
    rw [h1, h2]

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
