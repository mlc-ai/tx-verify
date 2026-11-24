-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.RawRingInitialized
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg1MmaLeader
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingCommitOrigins

@[expose] public section

/-! # Sources of the double-buffered GEMM synchronization records -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.GemmRing

open PTX AsyncCopy MBarrier PTX.Flow

/-- Four double-buffered objects along the dequantization, MMA and softmax pipeline. -/
inductive Object where
  | dequantReady
  | qkDone
  | soReady
  | svDone

/-- Offset of slot zero. The other slot is the next eight-byte object. -/
def Object.base : Object → Nat
  | .dequantReady => 222792
  | .qkDone => 222904
  | .soReady => 222920
  | .svDone => 222936

def Object.loc (obj : Object) (L : Launch) (cta : Nat) (slot : Fin 2) : Loc :=
  ⟨.shared, cta, L.sharedBase + (obj.base + 8 * slot.val)⟩

private theorem same_slot {obj : Object} {L : Launch} {cta cta' block : Nat} {slot : Fin 2}
    (h : obj.loc L cta slot = obj.loc L cta' (rawSlot block)) :
    cta' = cta ∧ block % 2 = slot.val := by
  exact ⟨(congrArg Loc.cta h).symm, by
    have ha := congrArg Loc.addr h
    change L.sharedBase + (obj.base + 8 * slot.val) =
      L.sharedBase + (obj.base + 8 * (block % 2)) at ha
    omega⟩

/-- An arrival originates at the selected slot's publication site with the matching block. -/
def Publisher (P : Params) (L : Launch) (X : Execution) (g i cta : Nat) (slot : Fin 2) :
    Object → Prop
  | .dequantReady => ctaOf L g = cta ∧ ∃ d : Wg2.D, d.block % 2 = slot.val ∧ d.site = .ready ∧
    Frame.stateAt (Machine.code P L) X g i = some (some (.wg2 d))
  | .soReady => ctaOf L g = cta ∧ ∃ d : Wg0.D, d.block % 2 = slot.val ∧ d.site = .soReady ∧
    Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d))
  | .qkDone | .svDone => False

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The only native arrivals on these objects are the dequant and probability publications. -/
theorem arrival_at_followed {g i cta tx count : Nat} {rel : Bool} {sc : MbarScope} {slot : Fin 2}
    {obj : Object} {e : Event} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : (Machine.machine P L g).Sound)
    (ht : Frame.stateAt (Machine.code P L) X g i ≠ some none) (he : X.get (g, i) = some e)
    (hk : e.kind = .arrive (obj.loc L cta slot) tx count rel sc) :
    Publisher P L X g i cta slot obj ∧ tx = 0 ∧ count = 1 ∧ rel = true ∧ sc = .cta := by
  obtain ⟨d, o, hstate, hf⟩ :=
    RingSourceSites.fired_at_followed hX hs ht he (by intro f h; rw [hk] at h; cases h)
  have hsite := RingSourceSites.arrive_site hf hk
  have hslot := slot.isLt
  cases d
  case wg0 d =>
    rcases hsite with hd | hd | hd
    · have h := congrArg Loc.addr
        (Kind.arrive.inj (hk.symm.trans (RingEvents.lastStore_arrive hpre hd hf))).1
      change L.sharedBase + (obj.base + 8 * slot.val) = L.sharedBase + 222768 at h
      cases obj <;> simp only [Object.base] at h <;> omega
    · have h := congrArg Loc.addr
        (Kind.arrive.inj (hk.symm.trans (RingEvents.maskFree_arrive hpre hd hf))).1
      change L.sharedBase + (obj.base + 8 * slot.val) =
        L.sharedBase + (222872 + 8 * (d.block % 4)) at h
      cases obj <;> simp only [Object.base] at h <;> omega
    · obtain ⟨h, htx, hn, hr, hsc⟩ :=
        Kind.arrive.inj (hk.symm.trans (RingEvents.scores_arrive hpre hd hf))
      have ha := congrArg Loc.addr h
      change L.sharedBase + (obj.base + 8 * slot.val) =
        L.sharedBase + (222920 + 8 * (d.block % 2)) at ha
      cases obj <;> simp only [Object.base] at ha <;> try omega
      obtain ⟨hc, hb⟩ := same_slot (obj := .soReady) h
      exact ⟨⟨hc, d, hb, hd, hstate⟩, htx, hn, hr, hsc⟩
  case mma d =>
    have h := congrArg Loc.addr
      (Kind.arrive.inj (hk.symm.trans (RingEvents.query_expectTx hpre hsite hf))).1
    change L.sharedBase + (obj.base + 8 * slot.val) = L.sharedBase + 222776 at h
    cases obj <;> simp only [Object.base] at h <;> omega
  case tma d =>
    rcases hsite with hd | hd
    · have h := congrArg Loc.addr
        (Kind.arrive.inj (hk.symm.trans (RingEvents.rawReady_expectTx hpre hd hf))).1
      change L.sharedBase + (obj.base + 8 * slot.val) =
        L.sharedBase + (222808 + 8 * (d.block % 2)) at h
      cases obj <;> simp only [Object.base] at h <;> omega
    · have h := congrArg Loc.addr
        (Kind.arrive.inj (hk.symm.trans (RingEvents.validFree_arrive hpre hd hf))).1
      change L.sharedBase + (obj.base + 8 * slot.val) =
        L.sharedBase + (222872 + 8 * (d.block % 4)) at h
      cases obj <;> simp only [Object.base] at h <;> omega
  case index d =>
    obtain ⟨extra, hd⟩ := hsite
    have h := congrArg Loc.addr
      (Kind.arrive.inj (hk.symm.trans (RingEvents.validReady_arrive hpre hd hf))).1
    change L.sharedBase + (obj.base + 8 * slot.val) =
      L.sharedBase + (222840 + 8 * (d.block % 4)) at h
    cases obj <;> simp only [Object.base] at h <;> omega
  case wg2 d =>
    rcases hsite with hd | hd
    · obtain ⟨h, htx, hn, hr, hsc⟩ :=
        Kind.arrive.inj (hk.symm.trans (RingEvents.dequantReady_arrive hpre hd hf))
      have ha := congrArg Loc.addr h
      change L.sharedBase + (obj.base + 8 * slot.val) =
        L.sharedBase + (222792 + 8 * (d.block % 2)) at ha
      cases obj <;> simp only [Object.base] at ha <;> try omega
      obtain ⟨hc, hb⟩ := same_slot (obj := .dequantReady) h
      exact ⟨⟨hc, d, hb, hd, hstate⟩, htx, hn, hr, hsc⟩
    · have h := congrArg Loc.addr
        (Kind.arrive.inj (hk.symm.trans (RingEvents.rawFree_arrive hpre hd hf))).1
      change L.sharedBase + (obj.base + 8 * slot.val) =
        L.sharedBase + (222824 + 8 * (d.block % 2)) at h
      cases obj <;> simp only [Object.base] at h <;> omega
  all_goals exact hsite.elim

/-- The only native arrivals on these objects are the dequant and probability publications. -/
theorem arrival {g i cta tx count : Nat} {rel : Bool} {sc : MbarScope} {slot : Fin 2} {obj : Object}
    {e : Event} (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    (he : X.get (g, i) = some e) (hk : e.kind = .arrive (obj.loc L cta slot) tx count rel sc) :
    Publisher P L X g i cta slot obj ∧ tx = 0 ∧ count = 1 ∧ rel = true ∧ sc = .cta :=
  arrival_at_followed hpre hX hs (ht g i (Frame.lt_of_get hX he)) he hk

private theorem notification_of_fired {g i cta : Nat} {slot : Fin 2} {obj : Object} {e : Event}
    {sp : TcCommit.Spec} {r : Fin 16} {d : Machine.ThreadD} {o : Option TState}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (he : X.get (g, i) = some e) (hk : e.kind = .tc (.commit sp))
    (ha : TcCommit.target sp r = some (obj.loc L cta slot))
    (hstate : Frame.stateAt (Machine.code P L) X g i = some (some d))
    (hf : (Machine.machine P L g).Fired (some d) e o) :
    sp.mbar = obj.loc L cta slot ∧ ctaOf L g = cta ∧
      ∃ d : Wg1Mma.D, d.i % 2 = slot.val ∧
        ((obj = .qkDone ∧ d.site = .qkCommit) ∨ (obj = .svDone ∧ d.site = .pvCommit)) ∧
        Frame.stateAt (Machine.code P L) X g i = some (some (.mma d)) := by
  have hg := Frame.lt_of_get hX he
  have hslot := slot.isLt
  obtain ⟨hmbar, q, rfl, ⟨hd, hl⟩ | ⟨hd, hl⟩ | ⟨hd, hl⟩⟩ :=
    RingCommitEvents.commit_source hpre hg hf hk ha
  · have ho := congrArg Loc.addr hl
    change L.sharedBase + (obj.base + 8 * slot.val) = L.sharedBase + 222784 at ho
    cases obj <;> simp only [Object.base] at ho <;> omega
  · have ho := congrArg Loc.addr hl
    change L.sharedBase + (obj.base + 8 * slot.val) =
      L.sharedBase + (222904 + 8 * (q.i % 2)) at ho
    cases obj <;> simp only [Object.base] at ho <;> try omega
    obtain ⟨hc, hb⟩ := same_slot (obj := .qkDone) hl
    exact ⟨hmbar.symm, hc, q, hb, .inl ⟨rfl, hd⟩, hstate⟩
  · have ho := congrArg Loc.addr hl
    change L.sharedBase + (obj.base + 8 * slot.val) =
      L.sharedBase + (222936 + 8 * (q.i % 2)) at ho
    cases obj <;> simp only [Object.base] at ho <;> try omega
    obtain ⟨hc, hb⟩ := same_slot (obj := .svDone) hl
    exact ⟨hmbar.symm, hc, q, hb, .inr ⟨rfl, hd⟩, hstate⟩

/-- QK and PV notifications come from the elected MMA lane and the matching block and slot. -/
theorem notification {g i cta : Nat} {slot : Fin 2} {obj : Object} {e : Event} {sp : TcCommit.Spec}
    {r : Fin 16} (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    (he : X.get (g, i) = some e) (hk : e.kind = .tc (.commit sp))
    (ha : TcCommit.target sp r = some (obj.loc L cta slot)) :
    sp.mbar = obj.loc L cta slot ∧ ctaOf L g = cta ∧
      ∃ d : Wg1Mma.D, d.i % 2 = slot.val ∧
        ((obj = .qkDone ∧ d.site = .qkCommit) ∨ (obj = .svDone ∧ d.site = .pvCommit)) ∧
        Frame.stateAt (Machine.code P L) X g i = some (some (.mma d)) := by
  obtain ⟨d, o, hstate, hf⟩ :=
    RingSourceSites.fired_from_trace hX hs ht he (by intro f h; rw [hk] at h; cases h)
  exact notification_of_fired hpre hX he hk ha hstate hf

/-- Actual notifications have identified issuers even after a consumer has been dismissed. -/
theorem actual_notification {g i cta : Nat} {slot : Fin 2} {obj : Object} {e : Event}
    {sp : TcCommit.Spec} {r : Fin 16} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (he : X.get (g, i) = some e)
    (hk : e.kind = .tc (.commit sp)) (ha : TcCommit.target sp r = some (obj.loc L cta slot)) :
    sp.mbar = obj.loc L cta slot ∧ ctaOf L g = cta ∧
      ∃ d : Wg1Mma.D, d.i % 2 = slot.val ∧
        ((obj = .qkDone ∧ d.site = .qkCommit) ∨ (obj = .svDone ∧ d.site = .pvCommit)) ∧
        Frame.stateAt (Machine.code P L) X g i = some (some (.mma d)) := by
  obtain ⟨_, _, hState, hFire⟩ := MachineTracking.actual_commit_fired hpre hX hs he hk
  exact notification_of_fired hpre hX he hk ha hState hFire

/-- A native poll at a GEMM object identifies the consumer and the block whose parity it uses. -/
def Poller (P : Params) (L : Launch) (X : Execution) (g i cta parity : Nat) (slot : Fin 2) :
    Object → Prop
  | .dequantReady => ctaOf L g = cta ∧ ∃ d : Wg1Mma.D, d.i % 2 = slot.val ∧
    parity = d.i / 2 % 2 ∧ d.site = .kvWait ∧
    Frame.stateAt (Machine.code P L) X g i = some (some (.mma d))
  | .soReady => ctaOf L g = cta ∧ ∃ d : Wg1Mma.D, d.i % 2 = slot.val ∧
    parity = d.i / 2 % 2 ∧ d.site = .soWait ∧
    Frame.stateAt (Machine.code P L) X g i = some (some (.mma d))
  | .qkDone => ctaOf L g = cta ∧ ∃ d : Wg0.D, d.block % 2 = slot.val ∧
    parity = d.block / 2 % 2 ∧ d.site = .qkDone ∧
    Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d))
  | .svDone => ctaOf L g = cta ∧
    ((∃ d : Wg2.D, d.block % 2 = slot.val ∧ parity = 1 - d.block / 2 % 2 ∧ d.site = .svDone ∧
      Frame.stateAt (Machine.code P L) X g i = some (some (.wg2 d))) ∨
     (∃ d : Wg0.D, d.block % 2 = slot.val ∧ parity = d.block / 2 % 2 ∧ d.site = .svDone ∧
      Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d))))

/-- The GEMM barriers' actual acquire polls use the dictated object and parity. -/
theorem poll_at_followed {g i cta parity : Nat} {ok acq : Bool} {sc : MbarScope} {slot : Fin 2}
    {obj : Object} {e : Event} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : (Machine.machine P L g).Sound)
    (ht : Frame.stateAt (Machine.code P L) X g i ≠ some none) (he : X.get (g, i) = some e)
    (hk : e.kind = .wait (obj.loc L cta slot) parity ok acq sc) :
    Poller P L X g i cta parity slot obj ∧ acq = true := by
  obtain ⟨d, o, hstate, hf⟩ :=
    RingSourceSites.fired_at_followed hX hs ht he (by intro f h; rw [hk] at h; cases h)
  have hsite := RingSourceSites.poll_site hf hk
  have hslot := slot.isLt
  cases d
  case wg0 d =>
    rcases hsite with hd | hd
    · obtain ⟨_, h⟩ := RingEvents.maskReady_wait hpre hd hf
      have ha := congrArg Loc.addr (Kind.wait.inj (hk.symm.trans h)).1
      change L.sharedBase + (obj.base + 8 * slot.val) =
        L.sharedBase + (222840 + 8 * (d.block % 4)) at ha
      cases obj <;> simp only [Object.base] at ha <;> omega
    · obtain ⟨_, _, h⟩ := RingEvents.gemmDone_wait_exact hpre hd hf
      rcases hd with hd | hd
      · rw [ite_eq_left hd] at h
        obtain ⟨hl, hp, _, hcq, _⟩ := Kind.wait.inj (hk.symm.trans h)
        have ha := congrArg Loc.addr hl
        change L.sharedBase + (obj.base + 8 * slot.val) =
          L.sharedBase + (222904 + 8 * (d.block % 2)) at ha
        cases obj <;> simp only [Object.base] at ha <;> try omega
        obtain ⟨hc, hb⟩ := same_slot (obj := .qkDone) hl
        exact ⟨⟨hc, d, hb, hp, hd, hstate⟩, hcq⟩
      · have hn : d.site ≠ .qkDone := by simp [hd]
        rw [ite_eq_right hn] at h
        obtain ⟨hl, hp, _, hcq, _⟩ := Kind.wait.inj (hk.symm.trans h)
        have ha := congrArg Loc.addr hl
        change L.sharedBase + (obj.base + 8 * slot.val) =
          L.sharedBase + (222936 + 8 * (d.block % 2)) at ha
        cases obj <;> simp only [Object.base] at ha <;> try omega
        obtain ⟨hc, hb⟩ := same_slot (obj := .svDone) hl
        exact ⟨⟨hc, .inr ⟨d, hb, hp, hd, hstate⟩⟩, hcq⟩
  case mma d =>
    obtain ⟨_, h⟩ := RingEvents.mma_wait_exact hpre hsite hf
    rcases hsite with hd | hd | hd | hd
    · simp only [hd, ↓reduceIte, true_or] at h
      have ha := congrArg Loc.addr (Kind.wait.inj (hk.symm.trans h)).1
      change L.sharedBase + (obj.base + 8 * slot.val) = L.sharedBase + 222776 at ha
      cases obj <;> simp only [Object.base] at ha <;> omega
    · simp [hd] at h
      have ha := congrArg Loc.addr (Kind.wait.inj (hk.symm.trans h)).1
      change L.sharedBase + (obj.base + 8 * slot.val) = L.sharedBase + 222784 at ha
      cases obj <;> simp only [Object.base] at ha <;> omega
    · simp [hd] at h
      obtain ⟨hl, hp, _, hcq, _⟩ := Kind.wait.inj (hk.symm.trans h)
      have ha := congrArg Loc.addr hl
      change L.sharedBase + (obj.base + 8 * slot.val) =
        L.sharedBase + (222792 + 8 * (d.i % 2)) at ha
      cases obj <;> simp only [Object.base] at ha <;> try omega
      obtain ⟨hc, hb⟩ := same_slot (obj := .dequantReady) hl
      exact ⟨⟨hc, d, hb, hp, hd, hstate⟩, hcq⟩
    · simp [hd] at h
      obtain ⟨hl, hp, _, hcq, _⟩ := Kind.wait.inj (hk.symm.trans h)
      have ha := congrArg Loc.addr hl
      change L.sharedBase + (obj.base + 8 * slot.val) =
        L.sharedBase + (222920 + 8 * (d.i % 2)) at ha
      cases obj <;> simp only [Object.base] at ha <;> try omega
      obtain ⟨hc, hb⟩ := same_slot (obj := .soReady) hl
      exact ⟨⟨hc, d, hb, hp, hd, hstate⟩, hcq⟩
  case tma d =>
    have sites : (d.site = .waitQ ∨ d.site = .waitLast) ∨
        d.site = .waitCoord ∨ d.site = .waitFree := by
      change d.site = .waitQ ∨ d.site = .waitLast ∨
        d.site = .waitCoord ∨ d.site = .waitFree at hsite
      tauto
    rcases sites with hd | hd | hd
    · obtain ⟨off, _, hoff, h⟩ := RingEvents.tmaEntry_wait hpre hd hf
      have ha := congrArg Loc.addr (Kind.wait.inj (hk.symm.trans h)).1
      change L.sharedBase + (obj.base + 8 * slot.val) = L.sharedBase + off at ha
      rcases hoff with rfl | rfl <;>
        cases obj <;>
        simp only [Object.base, Wg1Tma.qUtccpOff, Wg1Tma.lastStoreOff] at ha <;> omega
    · obtain ⟨_, h⟩ := RingEvents.validReady_wait hpre hd hf
      have ha := congrArg Loc.addr (Kind.wait.inj (hk.symm.trans h)).1
      change L.sharedBase + (obj.base + 8 * slot.val) =
        L.sharedBase + (222840 + 8 * (d.block % 4)) at ha
      cases obj <;> simp only [Object.base] at ha <;> omega
    · obtain ⟨_, h⟩ := RingEvents.rawFree_wait hpre hd hf
      have ha := congrArg Loc.addr (Kind.wait.inj (hk.symm.trans h)).1
      change L.sharedBase + (obj.base + 8 * slot.val) =
        L.sharedBase + (222824 + 8 * (d.block % 2)) at ha
      cases obj <;> simp only [Object.base] at ha <;> omega
  case index d =>
    obtain ⟨extra, hd⟩ := hsite
    obtain ⟨_, h⟩ := RingEvents.validFree_wait hpre hd hf
    have ha := congrArg Loc.addr (Kind.wait.inj (hk.symm.trans h)).1
    change L.sharedBase + (obj.base + 8 * slot.val) =
      L.sharedBase + (222872 + 8 * (d.block % 4)) at ha
    cases obj <;> simp only [Object.base] at ha <;> omega
  case wg2 d =>
    rcases hsite with hd | hd | hd
    · obtain ⟨_, h⟩ := RingEvents.dequant_wait_exact hpre (.inl hd) hf
      simp only [hd, ↓reduceIte] at h
      have ha := congrArg Loc.addr (Kind.wait.inj (hk.symm.trans h)).1
      change L.sharedBase + (obj.base + 8 * slot.val) = L.sharedBase + 222784 at ha
      cases obj <;> simp only [Object.base] at ha <;> omega
    · obtain ⟨_, h⟩ := RingEvents.rawReady_wait hpre hd hf
      have ha := congrArg Loc.addr (Kind.wait.inj (hk.symm.trans h)).1
      change L.sharedBase + (obj.base + 8 * slot.val) =
        L.sharedBase + (222808 + 8 * (d.block % 2)) at ha
      cases obj <;> simp only [Object.base] at ha <;> omega
    · obtain ⟨_, h⟩ := RingEvents.dequant_wait_exact hpre (.inr hd) hf
      simp [hd] at h
      obtain ⟨hl, hp, _, hcq, _⟩ := Kind.wait.inj (hk.symm.trans h)
      have ha := congrArg Loc.addr hl
      change L.sharedBase + (obj.base + 8 * slot.val) =
        L.sharedBase + (222936 + 8 * (d.block % 2)) at ha
      cases obj <;> simp only [Object.base] at ha <;> try omega
      obtain ⟨hc, hb⟩ := same_slot (obj := .svDone) hl
      exact ⟨⟨hc, .inl ⟨d, hb, hp, hd, hstate⟩⟩, hcq⟩
  all_goals exact hsite.elim
/-- The GEMM barriers' actual acquire polls use the dictated object and parity. -/
theorem poll {g i cta parity : Nat} {ok acq : Bool} {sc : MbarScope} {slot : Fin 2} {obj : Object}
    {e : Event} (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    (he : X.get (g, i) = some e) (hk : e.kind = .wait (obj.loc L cta slot) parity ok acq sc) :
    Poller P L X g i cta parity slot obj ∧ acq = true :=
  poll_at_followed hpre hX hs (ht g i (Frame.lt_of_get hX he)) he hk

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.GemmRing
