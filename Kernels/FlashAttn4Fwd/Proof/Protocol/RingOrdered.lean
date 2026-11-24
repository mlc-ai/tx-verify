-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Protocol.QRingSlotSources
public import Kernels.FlashAttn4Fwd.Proof.Protocol.OutputRegion
public import Kernels.FlashAttn4Fwd.Proof.Interface.Older
public import Lemmas.Protocol.RegionOrder

@[expose] public section

/-! # The ring regions' conflicts are ordered

A byte of a Q stage or a KV slot (`InRings`: the region of a full barrier in some CTA) is
accessed only by the ring's copies and MMA reads (`ring_access`): a thread's accesses lie below
the ring regions (`OlderFacts.access_low`), a tensor store reads a staging buffer
(`OutputFacts.store_tma`), and the kernel has no cancellation request or bulk copy
(`TmemFacts`). Of two conflicting accesses of the byte (`ring_ordered`):

* a copy and an MMA read are ordered by their uses (`modelCausality_ordered`);
* two copies of distinct uses are one loader's, ordered through an MMA read of the earlier use
  (`copies_ordered`); two copies of the same use writing the byte are the same copy writing the
  same element (`same_use_copy`: the byte's box and offset fix the copy and the slot), so they
  are one access and no conflict;
* two MMA reads do not conflict. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow PTX.Proof AsyncCopy MBarrier

noncomputable section

namespace Rings

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A byte of the region of a full barrier of the rings, in some CTA. -/
def InRings (L : Launch) (l : Loc) : Prop := ∃ c b, FBar.isFull b ∧ InRegion L c b l

/-- **An access of a ring byte** is a copy's write or an MMA read. -/
theorem ring_access (hX : Consistent L kernel asms mem0 X) (hout : OutputFacts L X)
    (htm : TmemFacts L X) (ho : OlderFacts P L X) {ref : Ref} {a : Acc} {w : Bool} {l : Loc}
    {c : Nat} {b : FBar} (h : X.Intent ref a w) (hc : a.Covers l) (hb : b.isFull)
    (hl : InRegion L c b l) :
    (∃ i x y z, ref = .async i (.write (.load x y z))) ∨
      ∃ i isB idx, ref = .async i (.mmaRead isB idx) := by
  have hpast := region_past hb hl
  rcases Execution.shared_intent h hc hl.1 with ⟨⟨g, k⟩, rfl, hae⟩ | ⟨i, isB, idx, rfl⟩ |
      ⟨i, x, y, k, rfl⟩ | ⟨i, x, y, z, rfl⟩ | ⟨i, c', s, tg, -, ⟨pc, hci⟩, -⟩ |
      ⟨i, q, s, -, ⟨pc, hbk⟩⟩ | ⟨i, -, ⟨pc, hbp⟩⟩
  · have := ho.access_low hae hc
    omega
  · exact .inr ⟨i, isB, idx, rfl⟩
  · exfalso
    obtain ⟨-, sp, addr, ⟨pc, hget⟩, hloc, hsz⟩ := h
    obtain ⟨-, st, hst, hsrc⟩ := hout.store_tma (event_thread_lt hX hget) hget
    have hl' := hsrc.2.1 x y k a.loc hloc
    rw [covers_one hc hsz] at hl'
    obtain ⟨-, -, -, h4⟩ := hl'
    omega
  · exact .inl ⟨i, x, y, z, rfl⟩
  · exact (htm.no_clc hci).elim
  · exact (htm.no_bulk hbk).elim
  · exact (htm.no_prefetch hbp).elim

/-- **Two copies of one ring byte in the same use are the same copy writing the same
element.** -/
theorem same_use_copy (hX : Consistent L kernel asms mem0 X) (ht : RingFacts L X)
    (hcp : RingCopies P L X) {b : FBar} (hb : b.isFull) {cta g1 k1 g2 k2 x y z x' y' z' : Nat}
    {l : Loc} (hl : InRegion L cta b l) (hw1 : AsyncCovers X (g1, k1) (.write (.load x y z)) l)
    (hw2 : AsyncCovers X (g2, k2) (.write (.load x' y' z')) l)
    (heq : copyUse L X (cta / 2) b (g1, k1) = copyUse L X (cta / 2) b (g2, k2)) :
    g1 = g2 ∧ k1 = k2 ∧ x = x' ∧ y = y' ∧ z = z' := by
  obtain ⟨pc0, al0, sp0, he0, hm0, -⟩ := write_slot ht hb hl hw1
  obtain ⟨pc0', al0', sp0', he0', hm0', -⟩ := write_slot ht hb hl hw2
  obtain ⟨a1, rfl, hca1, -, -⟩ := full_issue hX ht hb he0 hm0
  obtain ⟨a2, rfl, hca2, -, -⟩ := full_issue hX ht hb he0' hm0'
  obtain ⟨pc1, al1, he1, hc1, hwl1⟩ := copy_elem hcp ht hX hb hl hw1
  obtain ⟨pc2, al2, he2, hc2, hwl2⟩ := copy_elem hcp ht hX hb hl hw2
  have ha : a1 = a2 := Fin.ext (by omega)
  subst ha
  set S := slot L X (cta / 2) b
  set c1 := ((X.tr (S.prod a1)).take k1).countP (issuesTo (b.loc L (2 * (cta / 2)))) with hc1d
  set c2 := ((X.tr (S.prod a1)).take k2).countP (issuesTo (b.loc L (2 * (cta / 2)))) with hc2d
  obtain ⟨hx, hy, hz, hl1⟩ := copy_box hb hwl1
  obtain ⟨hx', hy', hz', hl2⟩ := copy_box hb hwl2
  rw [hl1] at hl2
  simp only [Loc.mk.injEq, true_and] at hl2
  obtain ⟨hjj, hoo⟩ := box_eq hb (Nat.mod_lt _ (copies_pos hb)) (Nat.mod_lt _ (copies_pos hb))
    (box_offset_lt' hb _ hx hy hz) (box_offset_lt' hb _ hx' hy' hz') hl2
  rw [← hjj] at hoo
  obtain ⟨rfl, rfl, rfl⟩ := TensorCopy.box_offset_inj (base := boxBase L b (c1 % b.copies)) hx hz
    hx' hz' hoo
  have hu : c1 / b.copies = c2 / b.copies := heq
  have hcc : c1 = c2 := by
    have e1 := Nat.div_add_mod c1 b.copies
    have e2 := Nat.div_add_mod c2 b.copies
    rw [hu, hjj] at e1
    omega
  have hmb : ∀ c, (copySpec P L (S.prod a1) b c).mbar = b.loc L (2 * (cta / 2)) := by
    intro c
    simp only [copySpec, pairBase, hc1]
  exact ⟨rfl, PairTmaRing.issue_index_unique he1 (hmb _) he2 (hmb _) hcc, rfl, rfl, rfl⟩

/-- **The ring regions' conflicts are ordered.** -/
theorem ring_ordered (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : RingFacts L X) (htm : TmemFacts L X) (hinit : RingInit L X) (hcp : RingCopies P L X)
    (hout : OutputFacts L X) (ho : OlderFacts P L X) : ConflictsOrdered L X (InRings L) := by
  intro e f a a' l hcon ha ha' ⟨c, b, hb, hl⟩
  obtain ⟨hne, we, wf, he, hf, hw, -⟩ := hcon
  rcases ring_access hX hout htm ho he ha hb hl with ⟨⟨g1, k1⟩, x, y, z, rfl⟩ |
      ⟨⟨g1, k1⟩, isB, idx, rfl⟩ <;>
    rcases ring_access hX hout htm ho hf ha' hb hl with ⟨⟨g2, k2⟩, x', y', z', rfl⟩ |
      ⟨⟨g2, k2⟩, isB', idx', rfl⟩
  · have hw1 : AsyncCovers X (g1, k1) (.write (.load x y z)) l := ⟨a, we, he, ha⟩
    have hw2 : AsyncCovers X (g2, k2) (.write (.load x' y' z')) l := ⟨a', wf, hf, ha'⟩
    obtain ⟨pc1, al1, sp1, he1, -, -⟩ := write_slot ht hb hl hw1
    have hg1 := Frame.lt_of_get hX he1
    rcases Nat.lt_trichotomy (copyUse L X (c / 2) b (g1, k1)) (copyUse L X (c / 2) b (g2, k2))
      with hlt | heq | hgt
    · obtain ⟨rfl, hch⟩ := copies_ordered hpre hX ht htm hinit hb hl hw1 hw2 hlt
      exact .inl ⟨.inl ⟨hg1, hg1, rfl⟩, hch⟩
    · obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := same_use_copy hX ht hcp hb hl hw1 hw2 heq
      exact (hne rfl).elim
    · obtain ⟨rfl, hch⟩ := copies_ordered hpre hX ht htm hinit hb hl hw2 hw1 hgt
      exact .inr ⟨.inl ⟨hg1, hg1, rfl⟩, hch⟩
  · exact modelCausality_ordered hpre hX ht htm hinit hb hl ⟨a, we, he, ha⟩ ⟨a', wf, hf, ha'⟩
  · exact (modelCausality_ordered hpre hX ht htm hinit hb hl ⟨a', wf, hf, ha'⟩ ⟨a, we, he, ha⟩).symm
  · exfalso
    obtain ⟨rfl, -⟩ := he
    obtain ⟨rfl, -⟩ := hf
    rcases hw with h | h <;> cases h

end Rings

end
end PTX.Kernels.FlashAttn4Fwd.Proof
