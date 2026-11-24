-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.IndexRingArrivals

@[expose] public section

/-! # Origins of polls on the index ring -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.IndexRing

open PTX

private def WaitSite (P : Params) (L : Launch) (X : Execution) (g i : Nat) (m : Loc) : Prop :=
  (∃ d : Wg1Index.D, m = free L (ctaOf L g) (indexSlot d.block) ∧
    (∃ extra, d.site = .waitFree extra) ∧
    Frame.stateAt (Machine.code P L) X g i = some (some (.index d))) ∨
  (∃ d : Wg0.D, m = ready L (ctaOf L g) (indexSlot d.block) ∧ d.site = .maskReady ∧
    Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d))) ∨
  (∃ d : Wg1Tma.D, m = ready L (ctaOf L g) (indexSlot d.block) ∧ d.site = .waitCoord ∧
    Frame.stateAt (Machine.code P L) X g i = some (some (.tma d)))

private theorem wait_site {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g i cta parity : Nat} {ok acq : Bool} {sc : MbarScope}
    {slot : Fin 4} {m : Loc} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    (hm : m = ready L cta slot ∨ m = free L cta slot)
    (he : X.get (g, i) = some e) (hk : e.kind = .wait m parity ok acq sc) :
    WaitSite P L X g i m ∧ acq = true ∧ sc = .cta := by
  have haddr := ring_addr_range hm
  obtain ⟨d, o, hstate, hf⟩ :=
    RingSourceSites.fired_from_trace hX hs ht he (by intro f h; rw [hk] at h; cases h)
  have hsite := RingSourceSites.poll_site hf hk
  cases d
  case wg0 d =>
    rcases hsite with hd | hd
    · obtain ⟨_, h⟩ := RingEvents.maskReady_wait hpre hd hf
      obtain ⟨hloc, _, _, hacq, hsc⟩ := Kind.wait.inj (hk.symm.trans h)
      exact ⟨.inr (.inl ⟨d, hloc, hd, hstate⟩), hacq, hsc⟩
    · obtain ⟨off, _, _, _, hoff, h⟩ := RingEvents.gemmDone_wait hpre hd hf
      have hloc := (Kind.wait.inj (hk.symm.trans h)).1
      rw [hloc] at haddr
      change _ ∧ L.sharedBase + off ≤ _ at haddr
      rcases hoff with rfl | rfl <;> simp only [Wg0.qkDoneOff, Wg0.svDoneOff] at haddr <;> omega
  case mma d =>
    obtain ⟨off, _, _, hoff, h⟩ := RingEvents.mma_wait_object hpre hsite hf
    have hloc := (Kind.wait.inj (hk.symm.trans h)).1
    rw [hloc] at haddr
    change _ ≤ L.sharedBase + off ∧ L.sharedBase + off ≤ _ at haddr
    rcases hoff with rfl | rfl | rfl | rfl <;> omega
  case tma d =>
    have sites : (d.site = .waitQ ∨ d.site = .waitLast) ∨
        d.site = .waitCoord ∨ d.site = .waitFree := by
      change d.site = .waitQ ∨ d.site = .waitLast ∨
        d.site = .waitCoord ∨ d.site = .waitFree at hsite
      tauto
    rcases sites with hd | hd | hd
    · obtain ⟨off, _, hoff, h⟩ := RingEvents.tmaEntry_wait hpre hd hf
      have hloc := (Kind.wait.inj (hk.symm.trans h)).1
      rw [hloc] at haddr
      change _ ≤ L.sharedBase + off ∧ _ at haddr
      rcases hoff with rfl | rfl
      · unfold Wg1Tma.qUtccpOff at haddr
        omega
      · unfold Wg1Tma.lastStoreOff at haddr
        omega
    · obtain ⟨_, h⟩ := RingEvents.validReady_wait hpre hd hf
      obtain ⟨hloc, _, _, hacq, hsc⟩ := Kind.wait.inj (hk.symm.trans h)
      exact ⟨.inr (.inr ⟨d, hloc, hd, hstate⟩), hacq, hsc⟩
    · obtain ⟨_, h⟩ := RingEvents.rawFree_wait hpre hd hf
      have hloc := (Kind.wait.inj (hk.symm.trans h)).1
      rw [hloc] at haddr
      change _ ≤ L.sharedBase + (222824 + 8 * (d.block % 2)) ∧ _ at haddr
      omega
  case index d =>
    obtain ⟨extra, hd⟩ := hsite
    obtain ⟨_, h⟩ := RingEvents.validFree_wait hpre hd hf
    obtain ⟨hloc, _, _, hacq, hsc⟩ := Kind.wait.inj (hk.symm.trans h)
    exact ⟨.inl ⟨d, hloc, ⟨extra, hd⟩, hstate⟩, hacq, hsc⟩
  case wg2 d =>
    have sites : (d.site = .qUtccp ∨ d.site = .svDone) ∨ d.site = .rawReady := by
      change d.site = .qUtccp ∨ d.site = .rawReady ∨ d.site = .svDone at hsite
      tauto
    rcases sites with hd | hd
    · obtain ⟨off, _, _, hoff, h⟩ := RingEvents.dequant_wait_object hpre hd hf
      have hloc := (Kind.wait.inj (hk.symm.trans h)).1
      rw [hloc] at haddr
      change _ ≤ L.sharedBase + off ∧ L.sharedBase + off ≤ _ at haddr
      rcases hoff with rfl | rfl
      · unfold Wg2.qUtccpOff at haddr
        omega
      · unfold Wg2.svDoneOff at haddr
        omega
    · obtain ⟨_, h⟩ := RingEvents.rawReady_wait hpre hd hf
      have hloc := (Kind.wait.inj (hk.symm.trans h)).1
      rw [hloc] at haddr
      change _ ≤ L.sharedBase + (222808 + 8 * (d.block % 2)) ∧ _ at haddr
      omega
  all_goals exact hsite.elim

/-- Every poll of a free slot comes from an index lane waiting to reuse that slot. -/
theorem reuse_source {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g i cta parity : Nat} {ok acq : Bool} {sc : MbarScope} {slot : Fin 4} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    (he : X.get (g, i) = some e) (hk : e.kind = .wait (free L cta slot) parity ok acq sc) :
    AtIndex P L X cta slot g i (fun s => ∃ extra, s = .waitFree extra) ∧
      acq = true ∧ sc = .cta := by
  obtain ⟨h, hfields⟩ := wait_site hpre hX hs ht (.inr rfl) he hk
  rcases h with ⟨d, hm, hd, hst⟩ | ⟨d, hm, hd, hst⟩ | ⟨d, hm, hd, hst⟩
  · obtain ⟨hc, hb⟩ := free_address hm.symm
    exact ⟨⟨hc, d, hb, hd, hst⟩, hfields⟩
  · exact (ready_ne_free hm.symm).elim
  · exact (ready_ne_free hm.symm).elim

/-- Every poll of a ready slot comes from a TMA or softmax consumer of that slot. -/
theorem await_ready_source {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g i cta parity : Nat} {ok acq : Bool} {sc : MbarScope} {slot : Fin 4} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    (he : X.get (g, i) = some e) (hk : e.kind = .wait (ready L cta slot) parity ok acq sc) :
    AtConsumer P L X cta slot g i .maskReady .waitCoord ∧ acq = true ∧ sc = .cta := by
  obtain ⟨h, hfields⟩ := wait_site hpre hX hs ht (.inl rfl) he hk
  rcases h with ⟨d, hm, hd, hst⟩ | ⟨d, hm, hd, hst⟩ | ⟨d, hm, hd, hst⟩
  · exact (ready_ne_free hm).elim
  · obtain ⟨hc, hb⟩ := ready_address hm.symm
    exact ⟨⟨hc, .inl ⟨d, hb, hd, hst⟩⟩, hfields⟩
  · obtain ⟨hc, hb⟩ := ready_address hm.symm
    exact ⟨⟨hc, .inr ⟨d, hb, hd, hst⟩⟩, hfields⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.IndexRing
