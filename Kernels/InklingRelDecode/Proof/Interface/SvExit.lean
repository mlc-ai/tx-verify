-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.SvRun

@[expose] public section

/-!
# The softmax region's last state

The loop leaves the region at one of four events (`DComp.leaves`): the barrier before the
preloads of a lane whose preloads are masked, the last preload, the barrier after the `P` store of
the last block (a thread other than thread 0) and the arrival on `p_ready`. At each the loop
counter has reached the split's `num_iters` (`d.e.r26 = d.i` before any update, `d.i + 1` after the
update of the last block), so `nDone d` is `num_iters` and `SvInv.corr` says the running maximum
and sum of the state are `Softmax.run` over all `num_iters` blocks (`SvInv.exit_corr`). The scale
of the state is the launch's (`EntFull.sc`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Sv
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX.Kernels.InklingRelDecode.Softmax

noncomputable section
open Classical

variable {Q : Params} {L : Launch} {g r s kvh : Nat} {B : Nat → List (ℝ × ℝ)}

/-- The sites at which the loop leaves the region. -/
def LeaveSite (d : D) : Prop :=
  (d.site = .bar0 ∧ d.e.r26 = d.i) ∨ (∃ j, d.site = .pre j ∧ d.e.r26 = d.i) ∨
  ((d.site = .bar21 ∨ d.site = .arrive) ∧ d.e.r26 = d.i + 1)

/-- At a site where the loop leaves, the number of blocks taken in is the loop bound. -/
theorem nDone_of_leave {d : D} (hl : LeaveSite d) :
    nDone d = d.e.r26 := by
  unfold LeaveSite at hl
  rcases hl with ⟨hs, he⟩ | ⟨j, hs, he⟩ | ⟨hs, he⟩
  · simp [nDone, hs, PostSite, he]
  · simp [nDone, hs, PostSite, he]
  · rcases hs with hs | hs <;> simp [nDone, hs, PostSite, he]

/-- **The region's last state holds the running maximum and sum of all the row's blocks.** -/
theorem SvInv.exit_corr {d : D} (hI : Inv L g d) (h : SvInv Q L g r s kvh B d)
    (hnI : Q.numIters r s < 2 ^ 31) (hl : LeaveSite d) :
    Corr (slQ Q) ((List.range (Q.numIters r s)).map B) d := by
  have hn := nDone_of_leave hl
  have hr26 : d.e.r26 = Q.numIters r s := by
    have h1 := hI.ok.r26
    rw [h.ent.r25] at h1
    rw [h1]
    simp only [hnI, ↓reduceIte]
  have := h.corr
  rwa [hn, hr26] at this

end
end PTX.Kernels.InklingRelDecode.Proof.Sv
