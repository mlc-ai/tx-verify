-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsMmaFootprint
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsMmaUses
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsMmaCommitCount

@[expose] public section

/-! # The MMA warp's operand reads of the rings

A byte an MMA reads lies in the region of the Q stage or KV slot its block's descriptor names,
in a CTA of the thread's pair (`mma_read_region`). The regions of the full barriers are
disjoint (`region_inj`), so a byte of full barrier `b`'s region is read by an MMA of a block
whose operand is `b`'s. At that MMA the thread has polled `b` for the use the block reads and
has not yet released that use (`Counts.qFull`, `Counts.kvFull`, `Counts.qEmpty`,
`Counts.kvEmpty`; `RingFacts.read`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The regions of two full barriers that share a byte are one. -/
theorem region_inj {c c' : Nat} {b b' : FBar} {l : Loc} (hb : b.isFull) (hb' : b'.isFull)
    (h : InRegion L c b l) (h' : InRegion L c' b' l) : b = b' := by
  obtain ⟨-, -, h1, h2⟩ := h
  obtain ⟨-, -, h1', h2'⟩ := h'
  cases b <;> simp [FBar.isFull] at hb <;> cases b' <;> simp [FBar.isFull] at hb' <;>
    simp only [FBar.regionOff, FBar.regionSize] at h1 h2 h1' h2' <;>
    rename_i x y <;> first
      | (congr 1; ext; omega)
      | omega

theorem slots_le_succ {R U N : Nat} (hR : R ≤ U) (hU : U < N) (s : Fin 6)
    (hs : U % 6 = s.val) : Mma.slots R s + 1 ≤ Mma.slots N s :=
  le_trans (Nat.add_le_add_right (slots_mono hR s) 1) (slots_succ_le hU s hs)

/-- An election of the full mask that returned the lane before an MMA state. -/
theorem MmaSt.leadAt {g k : Nat} {d : Mma.D} {b j : Fin 8} (h : MmaSt L X g k d b j) :
    LeadAt L X g k := by
  obtain ⟨e, he, inst, hk⟩ := h.counts.elected (by rw [h.site]; rfl)
  obtain ⟨j', hj, hget⟩ := mem_take_get he
  exact ⟨j', hj, e.pc, inst, by show (X.tr g)[j']? = _; rw [show (X.tr g)[j']? = some e from hget,
    ← show e.kind = _ from hk]⟩

/-- **The field `RingFacts.read`.** -/
theorem RingFacts_read (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) {g k c : Nat} {b : FBar} {isB : Bool} {idx : Nat} {l : Loc}
    (hc : AsyncCovers X (g, k) (.mmaRead isB idx) l) (hb : b.isFull) (hr : InRegion L c b l) :
    PairTc X (g, k) ∧ warpOf L g = 12 ∧ ctaOf L g = 2 * (c / 2) ∧ LeadAt L X g k ∧
      ((X.tr g).take k).countP (commitsTo (b.partner.loc L (ctaOf L g))) + 1 ≤
        okPolls (b.loc L (ctaOf L g)) ((X.tr g).take k) := by
  obtain ⟨d, b', j, h, hA, hcta, hreg⟩ := mma_read_region hpre hX ht hc
  have hfull : (Mma.readBar L d b' isB).isFull := by
    unfold Mma.readBar
    split_ifs <;> rfl
  obtain rfl := region_inj hb hfull hr hreg
  have hc' : c = l.cta := hr.2.1.symm
  have hr0 := h.item.2
  simp only [Mma.rank] at hr0
  refine ⟨.inl ⟨_, _, _, _, h.issue, by rw [Mma.mmaSpec_desc]; split <;> rfl⟩, h.warp, ?_,
    h.leadAt, ?_⟩
  · simp only [ctaOf, Mma.pairLo] at hcta ⊢
    omega
  have hJ := h.counts
  have hL := h.leadTake
  have htr := h.tripAt
  obtain ⟨site, i, tt, base, pro⟩ := d
  have hs := h.site
  simp only at hs htr hJ hA ⊢
  subst hs
  cases isB
  · have hp := hA rfl
    change ((X.tr g).take k).countP (commitsTo (Mma.bar L g (.qEmpty (Mma.mmaStage b')))) + 1 ≤
      okPolls (Mma.bar L g (.qFull (Mma.mmaStage b'))) _
    rw [hJ.qEmpty hL, hJ.qFull]
    fin_cases b' <;> simp [Mma.isPv] at hp <;> fin_cases j <;>
      simp [Mma.cnt, Mma.qeA, Mma.qA, Mma.mmaStage, Mma.Site.after, Mma.Site.ord, Mma.mmaOrd,
        Mma.isPv]
  · cases hpv : Mma.isPv b'
    · simp only [Mma.readBar, hpv, Bool.false_eq_true, ↓reduceIte]
      change ((X.tr g).take k).countP (commitsTo (Mma.bar L g (.kvEmpty (Mma.kSlot L _ b')))) +
        1 ≤ okPolls (Mma.bar L g (.kvFull (Mma.kSlot L _ b'))) _
      rw [hJ.kvEmpty hL, hJ.kvFull]
      apply slots_le_succ (U := Mma.kvUse L i (if b'.val < 2 then 0 else 2 + 2 * tt))
      · fin_cases b' <;> simp [Mma.isPv] at hpv <;> fin_cases j <;>
          simp [Mma.cnt, Mma.relA, Mma.Site.after, Mma.Site.inTrip, Mma.Site.loop, Mma.Site.ord,
            Mma.mmaOrd, Mma.isPv, Mma.kvUse, Mma.kvBase] <;> omega
      · fin_cases b' <;> simp [Mma.isPv] at hpv <;> fin_cases j <;>
          simp [Mma.cnt, Mma.kvA, Mma.Site.after, Mma.Site.inTrip, Mma.Site.loop, Mma.Site.ord,
            Mma.mmaOrd, Mma.isPv, Mma.kvUse, Mma.kvBase] <;> omega
      · simp only [Mma.kSlot, Mma.slotOf, Mma.kvSlot]
        split_ifs <;> rfl
    · simp only [Mma.readBar, hpv, ↓reduceIte]
      change ((X.tr g).take k).countP (commitsTo (Mma.bar L g (.kvEmpty (Mma.vSlot L _)))) +
        1 ≤ okPolls (Mma.bar L g (.kvFull (Mma.vSlot L _))) _
      rw [hJ.kvEmpty hL, hJ.kvFull]
      apply slots_le_succ (U := Mma.kvUse L i (1 + 2 * tt))
      · fin_cases b' <;> simp [Mma.isPv] at hpv <;> fin_cases j <;>
          simp [Mma.cnt, Mma.relA, Mma.Site.after, Mma.Site.inTrip, Mma.Site.loop, Mma.Site.ord,
            Mma.mmaOrd, Mma.isPv, Mma.kvUse, Mma.kvBase] <;> omega
      · fin_cases b' <;> simp [Mma.isPv] at hpv <;> fin_cases j <;>
          simp [Mma.cnt, Mma.kvA, Mma.Site.after, Mma.Site.inTrip, Mma.Site.loop, Mma.Site.ord,
            Mma.mmaOrd, Mma.isPv, Mma.kvUse, Mma.kvBase] <;> omega
      · rfl

end
end PTX.Kernels.FlashAttn4Fwd.Proof
