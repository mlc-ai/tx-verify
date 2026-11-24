-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.IndexRing
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingSourceSites

@[expose] public section

/-! # Origins of arrivals on the index ring -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.IndexRing

open PTX

private def ArrivalSite (P : Params) (L : Launch) (X : Execution) (g i : Nat) (m : Loc) : Prop :=
  (∃ d : Wg1Index.D, m = ready L (ctaOf L g) (indexSlot d.block) ∧
    (∃ extra, d.site = .ready extra) ∧
    Frame.stateAt (Machine.code P L) X g i = some (some (.index d))) ∨
  (∃ d : Wg0.D, m = free L (ctaOf L g) (indexSlot d.block) ∧ d.site = .validFree ∧
    Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d))) ∨
  (∃ d : Wg1Tma.D, m = free L (ctaOf L g) (indexSlot d.block) ∧ d.site = .coordFree ∧
    Frame.stateAt (Machine.code P L) X g i = some (some (.tma d)))

/-- Both index-ring objects lie in the same interval of shared addresses. -/
theorem ring_addr_range {L : Launch} {cta : Nat} {slot : Fin 4} {m : Loc}
    (hm : m = ready L cta slot ∨ m = free L cta slot) :
    L.sharedBase + 222840 ≤ m.addr ∧ m.addr ≤ L.sharedBase + 222896 := by
  have hslot := slot.isLt
  rcases hm with rfl | rfl
  · change _ ≤ L.sharedBase + (222840 + 8 * slot.val) ∧
      L.sharedBase + (222840 + 8 * slot.val) ≤ _
    omega
  · change _ ≤ L.sharedBase + (222872 + 8 * slot.val) ∧
      L.sharedBase + (222872 + 8 * slot.val) ≤ _
    omega

private theorem arrival_site {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g i cta tx count : Nat} {rel : Bool} {sc : MbarScope}
    {slot : Fin 4} {m : Loc} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound)
    (ht : Frame.stateAt (Machine.code P L) X g i ≠ some none)
    (hm : m = ready L cta slot ∨ m = free L cta slot)
    (he : X.get (g, i) = some e) (hk : e.kind = .arrive m tx count rel sc) :
    ArrivalSite P L X g i m ∧ tx = 0 ∧ count = 1 ∧ rel = true ∧ sc = .cta := by
  have haddr := ring_addr_range hm
  have hg := Frame.lt_of_get hX he
  obtain ⟨d, o, hstate, hf⟩ :
      ∃ d o, Frame.stateAt (Machine.code P L) X g i = some (some d) ∧
        (Machine.machine P L g).Fired (some d) e o := by
    rcases (hs.produces (hX.thr g hg)).fired he with ⟨σ, o, hst, hf⟩ | ⟨_, _, f, rfl⟩
    · cases σ with
      | none => exact (ht hst).elim
      | some d => exact ⟨d, o, hst, hf⟩
    · cases hk
  have hsite := RingSourceSites.arrive_site hf hk
  cases d
  case wg0 d =>
    rcases hsite with hd | hd | hd
    · have h := (Kind.arrive.inj (hk.symm.trans (RingEvents.lastStore_arrive hpre hd hf))).1
      rw [h] at haddr
      change L.sharedBase + 222840 ≤ L.sharedBase + 222768 ∧ _ at haddr
      omega
    · obtain ⟨h, htx, hn, hr, hsc⟩ :=
        Kind.arrive.inj (hk.symm.trans (RingEvents.maskFree_arrive hpre hd hf))
      exact ⟨.inr (.inl ⟨d, h, hd, hstate⟩), htx, hn, hr, hsc⟩
    · have h := (Kind.arrive.inj (hk.symm.trans (RingEvents.scores_arrive hpre hd hf))).1
      rw [h] at haddr
      change _ ∧ L.sharedBase + (222920 + 8 * (d.block % 2)) ≤ _ at haddr
      omega
  case mma d =>
    have h := (Kind.arrive.inj (hk.symm.trans (RingEvents.query_expectTx hpre hsite hf))).1
    rw [h] at haddr
    change L.sharedBase + 222840 ≤ L.sharedBase + 222776 ∧ _ at haddr
    omega
  case tma d =>
    rcases hsite with hd | hd
    · have h := (Kind.arrive.inj (hk.symm.trans (RingEvents.rawReady_expectTx hpre hd hf))).1
      rw [h] at haddr
      change L.sharedBase + 222840 ≤ L.sharedBase + (222808 + 8 * (d.block % 2)) ∧ _ at haddr
      omega
    · obtain ⟨h, htx, hn, hr, hsc⟩ :=
        Kind.arrive.inj (hk.symm.trans (RingEvents.validFree_arrive hpre hd hf))
      exact ⟨.inr (.inr ⟨d, h, hd, hstate⟩), htx, hn, hr, hsc⟩
  case index d =>
    obtain ⟨extra, hd⟩ := hsite
    obtain ⟨h, htx, hn, hr, hsc⟩ :=
      Kind.arrive.inj (hk.symm.trans (RingEvents.validReady_arrive hpre hd hf))
    exact ⟨.inl ⟨d, h, ⟨extra, hd⟩, hstate⟩, htx, hn, hr, hsc⟩
  case wg2 d =>
    rcases hsite with hd | hd
    · have h := (Kind.arrive.inj (hk.symm.trans (RingEvents.dequantReady_arrive hpre hd hf))).1
      rw [h] at haddr
      change L.sharedBase + 222840 ≤ L.sharedBase + (222792 + 8 * (d.block % 2)) ∧ _ at haddr
      omega
    · have h := (Kind.arrive.inj (hk.symm.trans (RingEvents.rawFree_arrive hpre hd hf))).1
      rw [h] at haddr
      change L.sharedBase + 222840 ≤ L.sharedBase + (222824 + 8 * (d.block % 2)) ∧ _ at haddr
      omega
  all_goals exact hsite.elim

/-- The ready address determines a CTA and index slot. -/
theorem ready_address {L : Launch} {c c' : Nat} {s s' : Fin 4}
    (h : ready L c s = ready L c' s') : c = c' ∧ s.val = s'.val := by
  have hc := congrArg Loc.cta h
  have ho := congrArg Loc.addr h
  change L.sharedBase + (222840 + 8 * s.val) =
    L.sharedBase + (222840 + 8 * s'.val) at ho
  exact ⟨hc, by omega⟩

/-- The free address determines a CTA and index slot. -/
theorem free_address {L : Launch} {c c' : Nat} {s s' : Fin 4}
    (h : free L c s = free L c' s') : c = c' ∧ s.val = s'.val := by
  have hc := congrArg Loc.cta h
  have ho := congrArg Loc.addr h
  change L.sharedBase + (222872 + 8 * s.val) =
    L.sharedBase + (222872 + 8 * s'.val) at ho
  exact ⟨hc, by omega⟩

/-- The publication and reuse addresses are disjoint. -/
theorem ready_ne_free {L : Launch} {c c' : Nat} {s s' : Fin 4} :
    ready L c s ≠ free L c' s' := by
  intro h
  have ho := congrArg Loc.addr h
  have hs := s.isLt
  change L.sharedBase + (222840 + 8 * s.val) =
    L.sharedBase + (222872 + 8 * s'.val) at ho
  omega

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g i cta tx count : Nat}
    {rel : Bool} {sc : MbarScope} {slot : Fin 4} {e : Event} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : (Machine.machine P L g).Sound)
include hpre hX hs

/-- Every publication on a ready slot comes from its index lane, given tracking at that event. -/
theorem publish_source_at_tracked_event (ht : Frame.stateAt (Machine.code P L) X g i ≠ some none)
    (he : X.get (g, i) = some e) (hk : e.kind = .arrive (ready L cta slot) tx count rel sc) :
    AtIndex P L X cta slot g i (fun s => ∃ extra, s = .ready extra) ∧
      tx = 0 ∧ count = 1 ∧ rel = true ∧ sc = .cta := by
  obtain ⟨h, hfields⟩ := arrival_site hpre hX hs ht (.inl rfl) he hk
  rcases h with ⟨d, hm, hd, hst⟩ | ⟨d, hm, hd, hst⟩ | ⟨d, hm, hd, hst⟩
  · obtain ⟨hc, hb⟩ := ready_address hm.symm
    exact ⟨⟨hc, d, hb, hd, hst⟩, hfields⟩
  · exact (ready_ne_free hm).elim
  · exact (ready_ne_free hm).elim

/-- Every publication on a ready slot comes from an index lane's release on that slot. -/
theorem publish_source (ht : Frame.Tracked (Machine.code P L) X) (he : X.get (g, i) = some e)
    (hk : e.kind = .arrive (ready L cta slot) tx count rel sc) :
    AtIndex P L X cta slot g i (fun s => ∃ extra, s = .ready extra) ∧
      tx = 0 ∧ count = 1 ∧ rel = true ∧ sc = .cta :=
  publish_source_at_tracked_event hpre hX hs (ht g i (Frame.lt_of_get hX he)) he hk

/-- A followed release on a free slot comes from a TMA or softmax consumer of that slot. -/
theorem release_source_at_tracked_event (ht : Frame.stateAt (Machine.code P L) X g i ≠ some none)
    (he : X.get (g, i) = some e) (hk : e.kind = .arrive (free L cta slot) tx count rel sc) :
    AtConsumer P L X cta slot g i .validFree .coordFree ∧
      tx = 0 ∧ count = 1 ∧ rel = true ∧ sc = .cta := by
  obtain ⟨h, hfields⟩ := arrival_site hpre hX hs ht (.inr rfl) he hk
  rcases h with ⟨d, hm, hd, hst⟩ | ⟨d, hm, hd, hst⟩ | ⟨d, hm, hd, hst⟩
  · exact (ready_ne_free hm.symm).elim
  · obtain ⟨hc, hb⟩ := free_address hm.symm
    exact ⟨⟨hc, .inl ⟨d, hb, hd, hst⟩⟩, hfields⟩
  · obtain ⟨hc, hb⟩ := free_address hm.symm
    exact ⟨⟨hc, .inr ⟨d, hb, hd, hst⟩⟩, hfields⟩

/-- Every release on a free slot comes from a TMA or softmax consumer on that slot. -/
theorem release_source (ht : Frame.Tracked (Machine.code P L) X) (he : X.get (g, i) = some e)
    (hk : e.kind = .arrive (free L cta slot) tx count rel sc) :
    AtConsumer P L X cta slot g i .validFree .coordFree ∧
      tx = 0 ∧ count = 1 ∧ rel = true ∧ sc = .cta :=
  release_source_at_tracked_event hpre hX hs (ht g i (Frame.lt_of_get hX he)) he hk

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.IndexRing
