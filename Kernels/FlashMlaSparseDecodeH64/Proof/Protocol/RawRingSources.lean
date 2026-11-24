-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.RingPhases
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingSourceSites

@[expose] public section

/-! # Sources of synchronization in the two-buffer raw ring -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.RawRing

open PTX

def ready (L : Launch) (cta : Nat) (slot : Fin 2) : Loc :=
  ⟨.shared, cta, L.sharedBase + Wg2.rawReadyOff slot.val⟩

def free (L : Launch) (cta : Nat) (slot : Fin 2) : Loc :=
  ⟨.shared, cta, L.sharedBase + Wg2.rawFreeOff slot.val⟩

theorem ready_loc (L : Launch) (cta : Nat) (slot : Fin 2) :
    ready L cta slot = (Mbar.rawReady slot).loc L cta := by
  fin_cases slot <;> rfl

theorem free_loc (L : Launch) (cta : Nat) (slot : Fin 2) :
    free L cta slot = (Mbar.rawFree slot).loc L cta := by
  fin_cases slot <;> rfl

private theorem ring_addr_range {L : Launch} {cta : Nat} {slot : Fin 2} {m : Loc}
    (hm : m = ready L cta slot ∨ m = free L cta slot) :
    L.sharedBase + 222808 ≤ m.addr ∧ m.addr ≤ L.sharedBase + 222832 := by
  have hs := slot.isLt
  rcases hm with rfl | rfl
  · change _ ≤ L.sharedBase + (222808 + 8 * slot.val) ∧
      L.sharedBase + (222808 + 8 * slot.val) ≤ _
    omega
  · change _ ≤ L.sharedBase + (222824 + 8 * slot.val) ∧
      L.sharedBase + (222824 + 8 * slot.val) ≤ _
    omega

private theorem ready_address {L : Launch} {c c' : Nat} {s s' : Fin 2}
    (h : ready L c s = ready L c' s') : c = c' ∧ s.val = s'.val := by
  have hc := congrArg Loc.cta h
  have ho := congrArg Loc.addr h
  change L.sharedBase + (222808 + 8 * s.val) =
    L.sharedBase + (222808 + 8 * s'.val) at ho
  exact ⟨hc, by omega⟩

private theorem free_address {L : Launch} {c c' : Nat} {s s' : Fin 2}
    (h : free L c s = free L c' s') : c = c' ∧ s.val = s'.val := by
  have hc := congrArg Loc.cta h
  have ho := congrArg Loc.addr h
  change L.sharedBase + (222824 + 8 * s.val) =
    L.sharedBase + (222824 + 8 * s'.val) at ho
  exact ⟨hc, by omega⟩

private theorem ready_ne_free {L : Launch} {c c' : Nat} {s s' : Fin 2} :
    ready L c s ≠ free L c' s' := by
  intro h
  have ho := congrArg Loc.addr h
  have hs := s.isLt
  change L.sharedBase + (222808 + 8 * s.val) =
    L.sharedBase + (222824 + 8 * s'.val) at ho
  omega

private def ArrivalSite (P : Params) (L : Launch) (X : Execution) (g i : Nat) (m : Loc)
    (tx : Nat) : Prop :=
  (∃ d : Wg1Tma.D, m = ready L (ctaOf L g) (rawSlot d.block) ∧
    d.site = .rawReady ∧ tx = 36864 ∧
    Frame.stateAt (Machine.code P L) X g i = some (some (.tma d))) ∨
  (∃ d : Wg2.D, m = free L (ctaOf L g) (rawSlot d.block) ∧ d.site = .free ∧ tx = 0 ∧
    Frame.stateAt (Machine.code P L) X g i = some (some (.wg2 d)))

private theorem arrival_site {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g i cta tx count : Nat} {rel : Bool} {sc : MbarScope} {slot : Fin 2} {m : Loc} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound)
    (ht : Frame.stateAt (Machine.code P L) X g i ≠ some none)
    (hm : m = ready L cta slot ∨ m = free L cta slot)
    (he : X.get (g, i) = some e) (hk : e.kind = .arrive m tx count rel sc) :
    ArrivalSite P L X g i m tx ∧ count = 1 ∧ rel = true ∧ sc = .cta := by
  have haddr := ring_addr_range hm
  obtain ⟨d, o, hstate, hf⟩ :
      ∃ d o, Frame.stateAt (Machine.code P L) X g i = some (some d) ∧
        (Machine.machine P L g).Fired (some d) e o := by
    rcases (hs.produces (hX.thr g (Frame.lt_of_get hX he))).fired he with
      ⟨d, o, hd, hf⟩ | ⟨_, _, _, rfl⟩
    · cases d with
      | none => exact (ht hd).elim
      | some d => exact ⟨d, o, hd, hf⟩
    · cases hk
  have hsite := RingSourceSites.arrive_site hf hk
  cases d
  case wg0 d =>
    rcases hsite with hd | hd | hd
    · have h := (Kind.arrive.inj (hk.symm.trans (RingEvents.lastStore_arrive hpre hd hf))).1
      rw [h] at haddr
      change L.sharedBase + 222808 ≤ L.sharedBase + 222768 ∧ _ at haddr
      omega
    · have h := (Kind.arrive.inj (hk.symm.trans (RingEvents.maskFree_arrive hpre hd hf))).1
      rw [h] at haddr
      change _ ∧ L.sharedBase + (222872 + 8 * (d.block % 4)) ≤ _ at haddr
      omega
    · have h := (Kind.arrive.inj (hk.symm.trans (RingEvents.scores_arrive hpre hd hf))).1
      rw [h] at haddr
      change _ ∧ L.sharedBase + (222920 + 8 * (d.block % 2)) ≤ _ at haddr
      omega
  case mma d =>
    have h := (Kind.arrive.inj (hk.symm.trans (RingEvents.query_expectTx hpre hsite hf))).1
    rw [h] at haddr
    change L.sharedBase + 222808 ≤ L.sharedBase + 222776 ∧ _ at haddr
    omega
  case tma d =>
    rcases hsite with hd | hd
    · obtain ⟨h, htx, hn, hr, hsc⟩ :=
        Kind.arrive.inj (hk.symm.trans (RingEvents.rawReady_expectTx hpre hd hf))
      exact ⟨.inl ⟨d, h, hd, htx, hstate⟩, hn, hr, hsc⟩
    · have h := (Kind.arrive.inj (hk.symm.trans (RingEvents.validFree_arrive hpre hd hf))).1
      rw [h] at haddr
      change _ ∧ L.sharedBase + (222872 + 8 * (d.block % 4)) ≤ _ at haddr
      omega
  case index d =>
    obtain ⟨extra, hd⟩ := hsite
    have h := (Kind.arrive.inj (hk.symm.trans (RingEvents.validReady_arrive hpre hd hf))).1
    rw [h] at haddr
    change _ ∧ L.sharedBase + (222840 + 8 * (d.block % 4)) ≤ _ at haddr
    omega
  case wg2 d =>
    rcases hsite with hd | hd
    · have h := (Kind.arrive.inj (hk.symm.trans (RingEvents.dequantReady_arrive hpre hd hf))).1
      rw [h] at haddr
      change L.sharedBase + 222808 ≤ L.sharedBase + (222792 + 8 * (d.block % 2)) ∧ _ at haddr
      omega
    · obtain ⟨h, htx, hn, hr, hsc⟩ :=
        Kind.arrive.inj (hk.symm.trans (RingEvents.rawFree_arrive hpre hd hf))
      exact ⟨.inr ⟨d, h, hd, htx, hstate⟩, hn, hr, hsc⟩
  all_goals exact hsite.elim

section
variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g i cta tx count : Nat}
    {rel : Bool} {sc : MbarScope} {slot : Fin 2} {e : Event} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : (Machine.machine P L g).Sound)
include hpre hX hs

/-- An actual raw-ready arrival is the TMA producer's expectation of this slot's bytes. -/
theorem publish_source_at_followed (ht : Frame.stateAt (Machine.code P L) X g i ≠ some none)
    (he : X.get (g, i) = some e) (hk : e.kind = .arrive (ready L cta slot) tx count rel sc) :
    tx = 36864 ∧ count = 1 ∧ rel = true ∧ sc = .cta ∧ ctaOf L g = cta ∧
      ∃ d : Wg1Tma.D, d.block % 2 = slot.val ∧ d.site = .rawReady ∧
        Frame.stateAt (Machine.code P L) X g i = some (some (.tma d)) := by
  obtain ⟨h, hn, hr, hsc⟩ := arrival_site hpre hX hs ht (.inl rfl) he hk
  rcases h with ⟨d, hm, hd, htx, hst⟩ | ⟨d, hm, hd, htx, hst⟩
  · obtain ⟨hc, hb⟩ := ready_address hm.symm
    exact ⟨htx, hn, hr, hsc, hc, d, hb, hd, hst⟩
  · exact (ready_ne_free hm).elim

/-- An actual raw-free arrival is a unit release from the dequantizer using this slot. -/
theorem release_source_at_followed (ht : Frame.stateAt (Machine.code P L) X g i ≠ some none)
    (he : X.get (g, i) = some e) (hk : e.kind = .arrive (free L cta slot) tx count rel sc) :
    tx = 0 ∧ count = 1 ∧ rel = true ∧ sc = .cta ∧ ctaOf L g = cta ∧
      ∃ d : Wg2.D, d.block % 2 = slot.val ∧ d.site = .free ∧
        Frame.stateAt (Machine.code P L) X g i = some (some (.wg2 d)) := by
  obtain ⟨h, hn, hr, hsc⟩ := arrival_site hpre hX hs ht (.inr rfl) he hk
  rcases h with ⟨d, hm, hd, htx, hst⟩ | ⟨d, hm, hd, htx, hst⟩
  · exact (ready_ne_free hm.symm).elim
  · obtain ⟨hc, hb⟩ := free_address hm.symm
    exact ⟨htx, hn, hr, hsc, hc, d, hb, hd, hst⟩


-- The globally followed execution supplies the local state witness.
theorem publish_source (ht : Frame.Tracked (Machine.code P L) X) (he : X.get (g, i) = some e)
    (hk : e.kind = .arrive (ready L cta slot) tx count rel sc) :
    tx = 36864 ∧ count = 1 ∧ rel = true ∧ sc = .cta ∧ ctaOf L g = cta ∧
      ∃ d : Wg1Tma.D, d.block % 2 = slot.val ∧ d.site = .rawReady ∧
        Frame.stateAt (Machine.code P L) X g i = some (some (.tma d)) :=
  publish_source_at_followed hpre hX hs (ht g i (Frame.lt_of_get hX he)) he hk

-- The globally followed execution supplies the local state witness.
theorem release_source (ht : Frame.Tracked (Machine.code P L) X) (he : X.get (g, i) = some e)
    (hk : e.kind = .arrive (free L cta slot) tx count rel sc) :
    tx = 0 ∧ count = 1 ∧ rel = true ∧ sc = .cta ∧ ctaOf L g = cta ∧
      ∃ d : Wg2.D, d.block % 2 = slot.val ∧ d.site = .free ∧
        Frame.stateAt (Machine.code P L) X g i = some (some (.wg2 d)) :=
  release_source_at_followed hpre hX hs (ht g i (Frame.lt_of_get hX he)) he hk
end

private def PollSite (P : Params) (L : Launch) (X : Execution) (g i : Nat) (m : Loc)
    (parity : Nat) : Prop :=
  (∃ d : Wg1Tma.D, m = free L (ctaOf L g) (rawSlot d.block) ∧
    d.site = .waitFree ∧ parity = 1 - d.block / 2 % 2 ∧
    Frame.stateAt (Machine.code P L) X g i = some (some (.tma d))) ∨
  (∃ d : Wg2.D, m = ready L (ctaOf L g) (rawSlot d.block) ∧ d.site = .rawReady ∧
    parity = d.block / 2 % 2 ∧
    Frame.stateAt (Machine.code P L) X g i = some (some (.wg2 d)))

private theorem poll_site {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g i cta parity : Nat} {ok acq : Bool} {sc : MbarScope} {slot : Fin 2} {m : Loc} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound)
    (hFollowed : Frame.stateAt (Machine.code P L) X g i ≠ some none)
    (hm : m = ready L cta slot ∨ m = free L cta slot)
    (he : X.get (g, i) = some e) (hk : e.kind = .wait m parity ok acq sc) :
    PollSite P L X g i m parity ∧ acq = true ∧ sc = .cta := by
  have haddr := ring_addr_range hm
  obtain ⟨d, o, hstate, hf⟩ :=
    RingSourceSites.fired_at_followed hX hs hFollowed he (by intro f h; rw [hk] at h; cases h)
  have hsite := RingSourceSites.poll_site hf hk
  cases d
  case wg0 d =>
    rcases hsite with hd | hd
    · obtain ⟨_, h⟩ := RingEvents.maskReady_wait hpre hd hf
      have hloc := (Kind.wait.inj (hk.symm.trans h)).1
      rw [hloc] at haddr
      change _ ∧ L.sharedBase + (222840 + 8 * (d.block % 4)) ≤ _ at haddr
      omega
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
      have hloc := (Kind.wait.inj (hk.symm.trans h)).1
      rw [hloc] at haddr
      change _ ∧ L.sharedBase + (222840 + 8 * (d.block % 4)) ≤ _ at haddr
      omega
    · obtain ⟨_, h⟩ := RingEvents.rawFree_wait hpre hd hf
      obtain ⟨hloc, hp, _, hacq, hsc⟩ := Kind.wait.inj (hk.symm.trans h)
      exact ⟨.inl ⟨d, hloc, hd, hp, hstate⟩, hacq, hsc⟩
  case index d =>
    obtain ⟨extra, hd⟩ := hsite
    obtain ⟨_, h⟩ := RingEvents.validFree_wait hpre hd hf
    have hloc := (Kind.wait.inj (hk.symm.trans h)).1
    rw [hloc] at haddr
    change _ ∧ L.sharedBase + (222872 + 8 * (d.block % 4)) ≤ _ at haddr
    omega
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
      obtain ⟨hloc, hp, _, hacq, hsc⟩ := Kind.wait.inj (hk.symm.trans h)
      exact ⟨.inr ⟨d, hloc, hd, hp, hstate⟩, hacq, hsc⟩
  all_goals exact hsite.elim

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g i cta parity : Nat}
    {ok acq : Bool} {sc : MbarScope} {slot : Fin 2} {e : Event} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : (Machine.machine P L g).Sound)
include hpre hX hs

/-- The TMA producer polls the free slot with the parity of its previous generation. -/
theorem reuse_source_at_followed (hFollowed : Frame.stateAt (Machine.code P L) X g i ≠ some none)
    (he : X.get (g, i) = some e) (hk : e.kind = .wait (free L cta slot) parity ok acq sc) :
    acq = true ∧ sc = .cta ∧ ctaOf L g = cta ∧
      ∃ d : Wg1Tma.D, d.block % 2 = slot.val ∧ d.site = .waitFree ∧ parity = 1 - d.block / 2 % 2 ∧
        Frame.stateAt (Machine.code P L) X g i = some (some (.tma d)) := by
  obtain ⟨h, ha, hs⟩ := poll_site hpre hX hs hFollowed (.inr rfl) he hk
  rcases h with ⟨d, hm, hd, hp, hst⟩ | ⟨d, hm, hd, hp, hst⟩
  · obtain ⟨hc, hb⟩ := free_address hm.symm
    exact ⟨ha, hs, hc, d, hb, hd, hp, hst⟩
  · exact (ready_ne_free hm.symm).elim

/-- Each dequantizer polls its raw-ready buffer with its current generation's parity. -/
theorem await_ready_source_at_followed
    (hFollowed : Frame.stateAt (Machine.code P L) X g i ≠ some none) (he : X.get (g, i) = some e)
    (hk : e.kind = .wait (ready L cta slot) parity ok acq sc) :
    acq = true ∧ sc = .cta ∧ ctaOf L g = cta ∧
      ∃ d : Wg2.D, d.block % 2 = slot.val ∧ d.site = .rawReady ∧ parity = d.block / 2 % 2 ∧
        Frame.stateAt (Machine.code P L) X g i = some (some (.wg2 d)) := by
  obtain ⟨h, ha, hs⟩ := poll_site hpre hX hs hFollowed (.inl rfl) he hk
  rcases h with ⟨d, hm, hd, hp, hst⟩ | ⟨d, hm, hd, hp, hst⟩
  · exact (ready_ne_free hm).elim
  · obtain ⟨hc, hb⟩ := ready_address hm.symm
    exact ⟨ha, hs, hc, d, hb, hd, hp, hst⟩

/-- A poll at a followed site of a fully tracked execution. -/
theorem reuse_source (ht : Frame.Tracked (Machine.code P L) X) (he : X.get (g, i) = some e)
    (hk : e.kind = .wait (free L cta slot) parity ok acq sc) :
    acq = true ∧ sc = .cta ∧ ctaOf L g = cta ∧
      ∃ d : Wg1Tma.D, d.block % 2 = slot.val ∧ d.site = .waitFree ∧ parity = 1 - d.block / 2 % 2 ∧
        Frame.stateAt (Machine.code P L) X g i = some (some (.tma d)) :=
  reuse_source_at_followed hpre hX hs (ht g i (Frame.lt_of_get hX he)) he hk

/-- A poll at a followed site of a fully tracked execution. -/
theorem await_ready_source (ht : Frame.Tracked (Machine.code P L) X) (he : X.get (g, i) = some e)
    (hk : e.kind = .wait (ready L cta slot) parity ok acq sc) :
    acq = true ∧ sc = .cta ∧ ctaOf L g = cta ∧
      ∃ d : Wg2.D, d.block % 2 = slot.val ∧ d.site = .rawReady ∧ parity = d.block / 2 % 2 ∧
        Frame.stateAt (Machine.code P L) X g i = some (some (.wg2 d)) :=
  await_ready_source_at_followed hpre hX hs (ht g i (Frame.lt_of_get hX he)) he hk

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.RawRing
