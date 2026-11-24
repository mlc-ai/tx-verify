-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsMmaNth
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsMmaUses
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsMmaRead

@[expose] public section

/-! # The MMAs of a released ring use

A commit to a ring empty barrier releases one use, at its commit site (`commit_state`): the
item's first K (commit 2), a trip's V (commit 4) or K (commit 6), the last V (commit 11), a Q
stage (commits 7, 8). A block of the item reads that use's region: block 0 for the first K,
block 3 for a trip's K, block 2 for a trip's V, block 6 for the last V, block 0 or 1 for Q
stage 0 or 1. Each of its eight steps comes before the commit (`mma_at_val`, from the commit
state's MMA count, `Counts.mmas`), with as many earlier commits to the empty barrier as the
commit (`MmaSt.kvEmpty`, `MmaSt.qEmpty` against `Counts.kvEmpty`, `Counts.qEmpty`;
`commit_use`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The MMAs of the use a commit releases.** -/
theorem commit_use (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) {g jc pc : Nat} {b : FBar} {sp : TcCommit.Spec}
    (he : X.get (g, jc) = some ⟨pc, .tc (.commit sp)⟩) (hb : b.isFull)
    (hm : sp.mbar = b.partner.loc L (ctaOf L g)) :
    ∃ (b' : Fin 8) (isB : Bool), (isB = false → Mma.isPv b' = false) ∧
      ∀ j : Fin 8, ∃ kR < jc, ∃ d', MmaSt L X g kR d' b' j ∧ Mma.readBar L d' b' isB = b ∧
        ((X.tr g).take kR).countP (commitsTo sp.mbar) =
          ((X.tr g).take jc).countP (commitsTo sp.mbar) := by
  obtain ⟨-, d, c, hJ, hi, hs, hsp, -, -⟩ := commit_state hpre hX ht he
  have hL := (lead_of_site hX hJ (by rw [hs]; rfl)).take jc
  have hbb := commit_bar hsp hm
  have hcnt := hJ.mmas hL
  have htr := hi.trip
  have hn := mma_trips_pos hpre
  obtain ⟨site, i, tt, base, pro⟩ := d
  simp only at hs hbb hcnt htr
  subst hs
  unfold Mma.TripOk at htr
  rw [hm]
  cases b <;> simp [FBar.isFull] at hb <;> simp only [FBar.partner] at hbb ⊢ <;>
    fin_cases c <;> simp [Mma.cBar] at hbb <;> simp [Mma.region] at htr
  · -- commit 7: Q stage 0, block 0 of the item
    subst hbb
    refine ⟨0, false, fun _ => rfl, fun j => ?_⟩
    obtain ⟨k, hk, d', h, hi', -⟩ := mma_at_val hpre hX ht (b := 0) (t := 0) (i := i)
      (by simp [Mma.TripAt]) j.isLt (by
        rw [hcnt]
        simp [Mma.cnt, Mma.mmaA, Mma.Site.after, Mma.Site.inTrip, Mma.Site.loop, Mma.Site.ord,
          Mma.elCOrd, Mma.blockPos, Mma.blk]
        omega)
    refine ⟨k, hk, d', h, by simp [Mma.readBar, Mma.mmaStage], ?_⟩
    have h1 := h.qEmpty rfl 0
    have h2 := hJ.qEmpty hL 0
    unfold ringCommits at h1
    change _ = ((X.tr g).take jc).countP (commitsTo (Mma.bar L g (.qEmpty 0)))
    rw [h1, h2, hi']
    simp [Mma.cnt, Mma.qeA, Mma.Site.after, Mma.Site.ord, Mma.elCOrd]
  · -- commit 8: Q stage 1, block 1 of the item
    subst hbb
    refine ⟨1, false, fun _ => rfl, fun j => ?_⟩
    obtain ⟨k, hk, d', h, hi', -⟩ := mma_at_val hpre hX ht (b := 1) (t := 0) (i := i)
      (by simp [Mma.TripAt]) j.isLt (by
        rw [hcnt]
        simp [Mma.cnt, Mma.mmaA, Mma.Site.after, Mma.Site.inTrip, Mma.Site.loop, Mma.Site.ord,
          Mma.elCOrd, Mma.blockPos, Mma.blk]
        omega)
    refine ⟨k, hk, d', h, by simp [Mma.readBar, Mma.mmaStage], ?_⟩
    have h1 := h.qEmpty rfl 1
    have h2 := hJ.qEmpty hL 1
    unfold ringCommits at h1
    change _ = ((X.tr g).take jc).countP (commitsTo (Mma.bar L g (.qEmpty 1)))
    rw [h1, h2, hi']
    simp [Mma.cnt, Mma.qeA, Mma.Site.after, Mma.Site.ord, Mma.elCOrd]
  · -- commit 2: block 0
    subst hbb
    refine ⟨0, true, fun h => absurd h (by decide), fun j => ?_⟩
    obtain ⟨k, hk, d', h, hi', ht'⟩ := mma_at_val hpre hX ht (b := 0) (t := 0) (i := i)
      (by simp [Mma.TripAt]) j.isLt (by
        rw [hcnt]
        simp [Mma.cnt, Mma.mmaA, Mma.Site.after, Mma.Site.inTrip, Mma.Site.loop, Mma.Site.ord,
          Mma.elCOrd, Mma.blockPos, Mma.blk]
        omega)
    refine ⟨k, hk, d', h, by simp [Mma.readBar, Mma.isPv, Mma.kSlot, hi'], ?_⟩
    have h1 := h.kvEmpty (Mma.slotOf L i 0)
    have h2 := hJ.kvEmpty hL (Mma.slotOf L i 0)
    unfold ringCommits at h1
    change _ = ((X.tr g).take jc).countP (commitsTo (Mma.bar L g (.kvEmpty (Mma.slotOf L i 0))))
    rw [h1, h2, hi', ht']
    simp only [Mma.cnt, Mma.relA, Mma.rv, Mma.Site.after, Mma.Site.inTrip, Mma.Site.loop,
      Mma.Site.ord, Mma.elCOrd]
    norm_num
    simp only [Mma.slots, Mma.slotOf, Mma.kvSlot, Mma.kvUse, Mma.kvBase]
    ring_nf
  · -- commit 4: block 2
    subst hbb
    refine ⟨2, true, fun h => absurd h (by decide), fun j => ?_⟩
    obtain ⟨k, hk, d', h, hi', ht'⟩ := mma_at_val hpre hX ht (b := 2) (t := tt) (i := i)
      (by simp [Mma.TripAt]; omega) j.isLt (by
        rw [hcnt]
        simp [Mma.cnt, Mma.mmaA, Mma.Site.after, Mma.Site.inTrip, Mma.Site.loop, Mma.Site.ord,
          Mma.elCOrd, Mma.blockPos, Mma.blk]
        omega)
    refine ⟨k, hk, d', h, by simp [Mma.readBar, Mma.isPv, Mma.vSlot, hi', ht'], ?_⟩
    have h1 := h.kvEmpty (Mma.slotOf L i (1 + 2 * tt))
    have h2 := hJ.kvEmpty hL (Mma.slotOf L i (1 + 2 * tt))
    unfold ringCommits at h1
    change _ = ((X.tr g).take jc).countP
      (commitsTo (Mma.bar L g (.kvEmpty (Mma.slotOf L i (1 + 2 * tt)))))
    rw [h1, h2, hi', ht']
    simp only [Mma.cnt, Mma.relA, Mma.rv, Mma.Site.after, Mma.Site.inTrip, Mma.Site.loop,
      Mma.Site.ord, Mma.elCOrd]
    norm_num
    simp only [Mma.slots, Mma.slotOf, Mma.kvSlot, Mma.kvUse, Mma.kvBase]
    ring_nf
  · -- commit 6: block 3
    subst hbb
    refine ⟨3, true, fun h => absurd h (by decide), fun j => ?_⟩
    obtain ⟨k, hk, d', h, hi', ht'⟩ := mma_at_val hpre hX ht (b := 3) (t := tt) (i := i)
      (by simp [Mma.TripAt]; omega) j.isLt (by
        rw [hcnt]
        simp [Mma.cnt, Mma.mmaA, Mma.Site.after, Mma.Site.inTrip, Mma.Site.loop, Mma.Site.ord,
          Mma.elCOrd, Mma.blockPos, Mma.blk]
        omega)
    refine ⟨k, hk, d', h, by simp [Mma.readBar, Mma.isPv, Mma.kSlot, hi', ht'], ?_⟩
    have h1 := h.kvEmpty (Mma.slotOf L i (2 + 2 * tt))
    have h2 := hJ.kvEmpty hL (Mma.slotOf L i (2 + 2 * tt))
    unfold ringCommits at h1
    change _ = ((X.tr g).take jc).countP
      (commitsTo (Mma.bar L g (.kvEmpty (Mma.slotOf L i (2 + 2 * tt)))))
    rw [h1, h2, hi', ht']
    simp only [Mma.cnt, Mma.relA, Mma.rv, Mma.Site.after, Mma.Site.inTrip, Mma.Site.loop,
      Mma.Site.ord, Mma.elCOrd]
    norm_num
    simp only [Mma.slots, Mma.slotOf, Mma.kvSlot, Mma.kvUse, Mma.kvBase]
    ring_nf
    omega
  · -- commit 11: block 6
    subst hbb
    refine ⟨6, true, fun h => absurd h (by decide), fun j => ?_⟩
    obtain ⟨k, hk, d', h, hi', ht'⟩ := mma_at_val hpre hX ht (b := 6) (t := tt) (i := i)
      (by simp [Mma.TripAt]; omega) j.isLt (by
        rw [hcnt]
        simp [Mma.cnt, Mma.mmaA, Mma.Site.after, Mma.Site.inTrip, Mma.Site.loop, Mma.Site.ord,
          Mma.elCOrd, Mma.blockPos, Mma.blk]
        omega)
    refine ⟨k, hk, d', h, by simp [Mma.readBar, Mma.isPv, Mma.vSlot, hi', ht'], ?_⟩
    have h1 := h.kvEmpty (Mma.slotOf L i (1 + 2 * tt))
    have h2 := hJ.kvEmpty hL (Mma.slotOf L i (1 + 2 * tt))
    unfold ringCommits at h1
    change _ = ((X.tr g).take jc).countP
      (commitsTo (Mma.bar L g (.kvEmpty (Mma.slotOf L i (1 + 2 * tt)))))
    rw [h1, h2, hi', ht']
    simp only [Mma.cnt, Mma.relA, Mma.rv, Mma.Site.after, Mma.Site.inTrip, Mma.Site.loop,
      Mma.Site.ord, Mma.elCOrd]
    norm_num
    simp only [Mma.slots, Mma.slotOf, Mma.kvSlot, Mma.kvUse, Mma.kvBase]
    ring_nf

end
end PTX.Kernels.FlashAttn4Fwd.Proof
