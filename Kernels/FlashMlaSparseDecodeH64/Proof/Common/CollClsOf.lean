-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.CollCls
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.CollDq
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.CollIdle
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.CollMmaLast
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.CollTmaLast
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.CollIxCls
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.CollW0Cls

@[expose] public section

/-! # Every lane's warp has a collective classification

`cls_of`: for a lane `g`, one of the six classes (`dqCls`, `idleCls`, `mmaCls`, `tmaCls`,
`ixCls`, `w0Cls`) classifies the lanes of its warp, all lanes of the warp are in it. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The lanes of a warp have its index. -/
theorem warpOf_sameWarp (hp : Pre P L m) {h : Nat} (hs : SameWarp L g h) :
    warpOf L g = warpOf L h := by
  simp only [warpOf, tidOf, tidOf_x_eq hp]
  have := hs.2
  rw [hp.block] at this
  exact this

/-- **A warp's lanes have a classification of their collectives.** -/
theorem cls_of (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hub : ¬ HasUb X) (hg : g < L.threads) :
    ∃ A : Nat → Prop, Nonempty (CollCls P L X A (collS P L)) ∧ A g ∧
      ∀ h, SameWarp L g h → A h := by
  have hw := warpOf_lt hp (g := g)
  have hsw : ∀ {h}, SameWarp L g h → warpOf L g = warpOf L h := fun hs => warpOf_sameWarp hp hs
  by_cases h4 : warpOf L g < 4
  · refine ⟨W0Lane L (warpOf L g) (g / L.block), ⟨w0Cls hp hX hFw hub _ _ h4⟩, ⟨hg, rfl, rfl⟩,
      fun h hs => ⟨hs.1.2.1, (hsw hs).symm, hs.1.2.2.symm⟩⟩
  by_cases h8 : 8 ≤ warpOf L g
  · exact ⟨DqLane L, ⟨dqCls hp hX hFw hub⟩, ⟨hg, h8, hw⟩, fun h hs =>
      ⟨hs.1.2.1, by rw [← hsw hs]; exact h8, by rw [← hsw hs]; exact hw⟩⟩
  have : warpOf L g = 4 ∨ warpOf L g = 5 ∨ warpOf L g = 6 ∨ warpOf L g = 7 := by omega
  rcases this with h | h | h | h
  · exact ⟨MmaLane L, ⟨mmaCls hp hX hFw hub⟩, ⟨hg, h⟩, fun h' hs =>
      ⟨hs.1.2.1, by rw [← hsw hs]; exact h⟩⟩
  · exact ⟨TmaLane L, ⟨tmaCls hp hX hFw hub⟩, ⟨hg, h⟩, fun h' hs =>
      ⟨hs.1.2.1, by rw [← hsw hs]; exact h⟩⟩
  · exact ⟨IdleLane L, ⟨idleCls hp hX hFw hub⟩, ⟨hg, h⟩, fun h' hs =>
      ⟨hs.1.2.1, by rw [← hsw hs]; exact h⟩⟩
  · exact ⟨IxLane L (g / L.block), ⟨ixCls hp hX hFw hub _⟩, ⟨hg, h, rfl⟩, fun h' hs =>
      ⟨hs.1.2.1, by rw [← hsw hs]; exact h, hs.1.2.2.symm⟩⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
