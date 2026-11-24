-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.LoaderBase

@[expose] public section

/-! # The end of a loader item

After an item's last V tile: the next item's register (`+ G`), its coordinates by the two
`FastDivmod` chains, and the branch back to the item loop's head (`setp.lt.s32`, decided under
`Pre` by `Work.loop_branch`) or into the drain. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow Work
open Prologue (sb)

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- From the end of item `d.i` to the head of the next item or the first drain poll. -/
theorem itemEnd (hpre : Pre P L mem0) (d : D) (hi : d.i < T L g) (hs : d.s < 6) :
    SegTo L g 450 (factsAt L g 450 d) (afterUse.itemEndOf L g d) := by
  have h1 : Seg kernel asms L g 16 450 (factsAt L g 450 d) 466
      (factsAt L g 466 { d with i := d.i + 1 }) := fun t h => by loader_seg h hpre
  have hv : valueOf L g { d with i := d.i + 1 } 91 = .pred (decide (d.i + 1 < T L g)) := by
    simp only [valueOf, table, PTX.Flow.lookupLit, Option.getD_some]
    rw [loop_branch hpre hi]
  obtain ⟨k, h2⟩ := segTo_bra (L := L) (g := g) (pc := 466)
    (d1 := { d with site := .head, i := d.i + 1, t := 0 }) (d2 := { d with site := .drain 0 })
    Flow.code_466 (tbl_mem (pc := 466) (by live_dec) hv)
    (fun _ => ⟨1, fun t h => by loader_seg h hpre⟩)
    (fun _ => ⟨4, fun t h => by loader_seg h hpre⟩)
  refine ⟨16 + k, ?_⟩
  unfold afterUse.itemEndOf
  by_cases hT : d.i + 1 < T L g
  · simp only [hT, decide_true, ↓reduceIte] at h2 ⊢
    exact Seg.comp h1 h2
  · simp only [hT, decide_false, Bool.false_eq_true, ↓reduceIte] at h2 ⊢
    exact Seg.comp h1 h2

/-- The bounds after an item's end. -/
theorem itemEnd_inv (d : D) (hs : d.s < 6) (hph : d.ph < 2) (hqp : d.qp < 2) :
    Inv L g (afterUse.itemEndOf L g d) := by
  unfold afterUse.itemEndOf
  split_ifs with hT
  · exact ⟨hs, hph, hqp, fun _ => hT, fun h => by simp [Site.inTrip] at h,
      fun h => by simp [Site.leadOnly] at h, fun u j h => by rcases h with h | h <;> cases h⟩
  · exact ⟨hs, hph, hqp, fun h => by simp [Site.inItem] at h, fun h => by simp [Site.inTrip] at h,
      fun h => by simp [Site.leadOnly] at h, fun u j h => by rcases h with h | h <;> cases h⟩

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Loader
