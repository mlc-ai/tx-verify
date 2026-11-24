-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingTmaCoordinate
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.RawRingSources
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxPublication
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingDequantBarrierAddress

@[expose] public section

/-! # The concrete sources of raw-ring arrivals -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow Protocol Protocol.RawRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private def dequantRegion (pc : Nat) : Prop := 2606 ≤ pc
private instance (pc : Nat) : Decidable (dequantRegion pc) :=
  inferInstanceAs (Decidable (2606 ≤ pc))

set_option maxRecDepth 100000 in
private theorem dequant_closed : controlRegionClosed dequantRegion = true := by decide +kernel

private theorem dequant_region (d : Wg2.D) : dequantRegion d.site.pc := by
  cases d.site <;> unfold dequantRegion <;> decide +revert

private theorem dequant_arrival_sites {pc : Nat}
    (hSite : pc ∈ Flow.mbarArrive.toList) (hRegion : dequantRegion pc) :
    pc = Wg2.Site.ready.pc ∨ pc = Wg2.Site.free.pc := by
  have h : Flow.mbarArrive.toList.all (fun t => decide
      (dequantRegion t → t = Wg2.Site.ready.pc ∨ t = Wg2.Site.free.pc)) = true :=
    by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h pc hSite) hRegion

private theorem raw_arrival_address {m : Loc} {cta : Nat} {slot : Fin 2}
    (hm : m = ready L cta slot ∨ m = free L cta slot) :
    L.sharedBase + 222808 ≤ m.addr ∧ m.addr ≤ L.sharedBase + 222832 := by
  have hb := slot.isLt
  rcases hm with rfl | rfl
  · change _ ≤ L.sharedBase + (222808 + 8 * slot.val) ∧
      L.sharedBase + (222808 + 8 * slot.val) ≤ _
    omega
  · change _ ≤ L.sharedBase + (222824 + 8 * slot.val) ∧
      L.sharedBase + (222824 + 8 * slot.val) ≤ _
    omega

private theorem dismissed_raw_arrival {g i cta tx count : Nat} {e : Event} {m : Loc}
    {slot : Fin 2} {rel : Bool} {scope : MbarScope}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (he : X.get (g, i) = some e) (hk : e.kind = .arrive m tx count rel scope)
    (hm : m = ready L cta slot ∨ m = free L cta slot)
    (hd : Frame.stateAt (Machine.code P L) X g i = some none) :
    ∃ b : Fin 2, wgOf L g = 2 ∧ e.pc = Wg2.Site.free.pc ∧ e.kind =
      .arrive (free L (ctaOf L g) b) 0 1 true .cta := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨j, hj, d, f, hf, hState, hn⟩ := prior_dismissal (PTX.len_of_get he).le hd
  have hSite := RingSourceSites.actual_arrive_pc hX he hk
  have hRole := RingRoleGeometry.of_trace hX hg (hs g hg).machine hState
  have hRange := raw_arrival_address hm
  cases dismissal_is_consumer hpre hX hs hf hState hn with
  | wg0 d =>
    change wgOf L g = 0 at hRole
    obtain ⟨hTags, start, hStart, hAnchor⟩ :=
      dismissed_softmax_arrival_site hpre hX hs he hf hj hState hn hSite
    rcases hTags with hFree | hPub
    · obtain ⟨b, _, _, hKind, _⟩ :=
        actual_softmax_return_ordinal hpre hX hs he hStart hAnchor hFree
      have hLoc := (Kind.arrive.inj (hk.symm.trans hKind)).1
      rw [hLoc] at hRange
      change _ ∧ L.sharedBase + (222872 + 8 * (b % 4)) ≤ _ at hRange
      omega
    · obtain ⟨b, hKind⟩ := actual_softmax_publication hpre hX hs he hRole hPub hk
      have hLoc := (Kind.arrive.inj (hk.symm.trans hKind)).1
      rw [hLoc] at hRange
      change _ ∧ L.sharedBase + (222920 + 8 * b.val) ≤ _ at hRange
      omega
  | wg2 d =>
    have hPc := Frame.event_pc hs hX hf hState
    change f.pc = d.site.pc at hPc
    have hReg : dequantRegion f.pc := hPc ▸ dequant_region d
    have hLater := later_event_in_control_region dequant_closed hX hg hf he hj hReg
    rcases actual_dequant_barrier_address hpre hX he (dequant_arrival_sites hSite hLater) hk with
      ⟨_, b, hKind⟩ | ⟨hFree, b, hKind⟩
    · have hLoc := (Kind.arrive.inj (hk.symm.trans hKind)).1
      rw [hLoc] at hRange
      change L.sharedBase + 222808 ≤ L.sharedBase + (222792 + 8 * b.val) ∧ _ at hRange
      have := b.isLt
      omega
    · exact ⟨b, hRole, hFree, hKind⟩

variable {g i cta tx count : Nat} {e : Event} {slot : Fin 2} {rel : Bool} {scope : MbarScope}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound) (he : X.get (g, i) = some e)
include hpre hX hs he

/-- The raw-ready arrival is issued by the followed TMA producer, with its byte expectation. -/
theorem actual_raw_ready_arrive (hk : e.kind = .arrive (ready L cta slot) tx count rel scope) :
    tx = 36864 ∧ count = 1 ∧ rel = true ∧ scope = .cta ∧ ctaOf L g = cta ∧
      ∃ d : Wg1Tma.D, d.block % 2 = slot.val ∧ d.site = .rawReady ∧
        Frame.stateAt (Machine.code P L) X g i = some (some (.tma d)) := by
  by_cases hFollow : Frame.stateAt (Machine.code P L) X g i = some none
  · obtain ⟨b, _, _, hKind⟩ := dismissed_raw_arrival hpre hX hs he hk (.inl rfl) hFollow
    have hAddr := congrArg Loc.addr (Kind.arrive.inj (hk.symm.trans hKind)).1
    change L.sharedBase + (222808 + 8 * slot.val) =
      L.sharedBase + (222824 + 8 * b.val) at hAddr
    have := slot.isLt
    omega
  · exact publish_source_at_followed hpre hX (hs g (Frame.lt_of_get hX he)).machine hFollow he hk

/-- Every actual raw-free arrival is a unit release from a dequantizer lane. -/
theorem actual_raw_free_arrive (hk : e.kind = .arrive (free L cta slot) tx count rel scope) :
    tx = 0 ∧ count = 1 ∧ rel = true ∧ scope = .cta ∧ ctaOf L g = cta ∧ wgOf L g = 2 ∧
      e.pc = Wg2.Site.free.pc := by
  have hg := Frame.lt_of_get hX he
  by_cases hFollow : Frame.stateAt (Machine.code P L) X g i = some none
  · obtain ⟨b, hRole, hTag, hKind⟩ := dismissed_raw_arrival hpre hX hs he hk (.inr rfl) hFollow
    obtain ⟨hm, hTx, hCount, hRel, hScope⟩ := Kind.arrive.inj (hk.symm.trans hKind)
    exact ⟨hTx, hCount, hRel, hScope, (congrArg Loc.cta hm).symm, hRole, hTag⟩
  · obtain ⟨hTx, hCount, hRel, hScope, hc, d, _, hSite, hState⟩ :=
      release_source_at_followed hpre hX (hs g hg).machine hFollow he hk
    refine ⟨hTx, hCount, hRel, hScope, hc,
      RingRoleGeometry.of_trace hX hg (hs g hg).machine hState, ?_⟩
    have hTag := Frame.event_pc hs hX he hState
    change e.pc = d.site.pc at hTag
    simpa only [hSite] using hTag

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
