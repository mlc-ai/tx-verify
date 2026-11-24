-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxActualUses
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.IndexRingArrivals
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxPublication
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingDequantBarrierAddress
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingRoleGeometry

@[expose] public section

/-! # Origins of actual arrivals on the index ring -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow PTX.Proof Protocol Protocol.IndexRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

private def softmaxArrivalRegion (pc : Nat) : Prop := (253 ≤ pc ∧ pc < 1842) ∨ 3611 ≤ pc
private def dequantArrivalRegion (pc : Nat) : Prop := 2606 ≤ pc

private instance (pc : Nat) : Decidable (softmaxArrivalRegion pc) := by
  unfold softmaxArrivalRegion
  infer_instance

private instance (pc : Nat) : Decidable (dequantArrivalRegion pc) :=
  inferInstanceAs (Decidable (2606 ≤ pc))

set_option maxRecDepth 100000 in
private theorem softmax_arrival_closed : controlRegionClosed softmaxArrivalRegion = true := by
  decide +kernel
set_option maxRecDepth 100000 in
private theorem dequant_arrival_closed : controlRegionClosed dequantArrivalRegion = true := by
  decide +kernel

private theorem wg2_region (d : Wg2.D) : dequantArrivalRegion d.site.pc := by
  cases d.site <;> unfold dequantArrivalRegion <;> decide +revert

private theorem softmax_arrival_site {pc : Nat}
    (hSite : pc ∈ Flow.mbarArrive.toList) (hRegion : softmaxArrivalRegion pc) :
    pc = Wg0.Site.validFree.pc ∨ pc = Wg0.Site.soReady.pc := by
  have h : Flow.mbarArrive.toList.all (fun t => decide
      (softmaxArrivalRegion t → t = Wg0.Site.validFree.pc ∨ t = Wg0.Site.soReady.pc)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h pc hSite) hRegion

private theorem dequant_arrival_site {pc : Nat}
    (hSite : pc ∈ Flow.mbarArrive.toList) (hRegion : dequantArrivalRegion pc) :
    pc = Wg2.Site.ready.pc ∨ pc = Wg2.Site.free.pc := by
  have h : Flow.mbarArrive.toList.all (fun t => decide
      (dequantArrivalRegion t → t = Wg2.Site.ready.pc ∨ t = Wg2.Site.free.pc)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h pc hSite) hRegion

/-- A late softmax arrival follows the first mask entry and is one of its two loop arrivals. -/
theorem dismissed_softmax_arrival_site {j i : Nat} {e f : Event} {d : Wg0.D}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (he : X.get (g, i) = some e) (hf : X.get (g, j) = some f) (hj : j < i)
    (hState : Frame.stateAt (Machine.code P L) X g j = some (some (.wg0 d)))
    (hn : Machine.next P L g (.wg0 d) f = some none)
    (hSite : e.pc ∈ Flow.mbarArrive.toList) :
    (e.pc = Wg0.Site.validFree.pc ∨ e.pc = Wg0.Site.soReady.pc) ∧
      ∃ start ≤ i, FirstMaskAnchor P L X g start := by
  obtain ⟨start, hBefore, first, hMask, hBlock, hAnchor⟩ :=
    dismissed_wg0_first_mask_ready hpre hX hs hf hState hn
  have hStartLen : start < (X.tr g).length := (hBefore.trans_lt hj).trans (PTX.len_of_get he)
  obtain ⟨a, ha⟩ : ∃ a, X.get (g, start) = some a :=
    ⟨_, List.getElem?_eq_getElem hStartLen⟩
  have hPc := Frame.event_pc hs hX ha hAnchor
  change a.pc = first.site.pc at hPc
  rw [hMask] at hPc
  have hReg : softmaxArrivalRegion a.pc := by rw [hPc]; exact .inl (by decide)
  have hLater := later_event_in_control_region softmax_arrival_closed hX (Frame.lt_of_get hX he)
    ha he (hBefore.trans_lt hj) hReg
  exact ⟨softmax_arrival_site hSite hLater, start, hBefore.trans hj.le,
    first, hMask, hBlock, hAnchor⟩

/-- The two consumers that actually release an index slot. -/
def ActualFreeIssuer (L : Launch) (g : Nat) (e : Event) : Prop :=
  (wgOf L g = 0 ∧ e.pc = Wg0.Site.validFree.pc) ∨
    (warpOf L g = 5 ∧ e.pc = Wg1Tma.Site.coordFree.pc)

private theorem dismissed_index_ring_arrive {i : Nat} {e : Event} {m : Loc}
    {cta tx count : Nat} {slot : Fin 4} {rel : Bool} {scope : MbarScope}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (he : X.get (g, i) = some e) (hk : e.kind = .arrive m tx count rel scope)
    (hm : m = ready L cta slot ∨ m = free L cta slot)
    (hd : Frame.stateAt (Machine.code P L) X g i = some none) :
    (∃ s : Fin 4, m = free L (ctaOf L g) s) ∧ ActualFreeIssuer L g e ∧
      tx = 0 ∧ count = 1 ∧ rel = true ∧ scope = .cta := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨j, hj, d, f, hf, hState, hn⟩ := prior_dismissal (PTX.len_of_get he).le hd
  have hSite := RingSourceSites.actual_arrive_pc hX he hk
  have hRole := RingRoleGeometry.of_trace hX hg (hs g hg).machine hState
  have hRange := ring_addr_range hm
  cases dismissal_is_consumer hpre hX hs hf hState hn with
  | wg0 d =>
    change wgOf L g = 0 at hRole
    obtain ⟨hSites, start, hStart, hAnchor⟩ :=
      dismissed_softmax_arrival_site hpre hX hs he hf hj hState hn hSite
    rcases hSites with hFree | hPub
    · obtain ⟨b, _, _, hKind, _⟩ :=
        actual_softmax_return_ordinal hpre hX hs he hStart hAnchor hFree
      obtain ⟨hLoc, hTx, hCount, hRel, hScope⟩ := Kind.arrive.inj (hk.symm.trans hKind)
      exact ⟨⟨indexSlot b, hLoc⟩, .inl ⟨hRole, hFree⟩, hTx, hCount, hRel, hScope⟩
    · obtain ⟨b, hKind⟩ := actual_softmax_publication hpre hX hs he hRole hPub hk
      have hLoc := (Kind.arrive.inj (hk.symm.trans hKind)).1
      rw [hLoc] at hRange
      change _ ∧ L.sharedBase + (222920 + 8 * b.val) ≤ _ at hRange
      omega
  | wg2 d =>
    have hPc := Frame.event_pc hs hX hf hState
    change f.pc = d.site.pc at hPc
    have hReg : dequantArrivalRegion f.pc := hPc ▸ wg2_region d
    have hLater := later_event_in_control_region dequant_arrival_closed hX hg hf he hj hReg
    rcases actual_dequant_barrier_address hpre hX he (dequant_arrival_site hSite hLater) hk with
      ⟨_, b, hKind⟩ | ⟨_, b, hKind⟩
    · have hLoc := (Kind.arrive.inj (hk.symm.trans hKind)).1
      rw [hLoc] at hRange
      change L.sharedBase + 222840 ≤ L.sharedBase + (222792 + 8 * b.val) ∧ _ at hRange
      have := b.isLt
      omega
    · have hLoc := (Kind.arrive.inj (hk.symm.trans hKind)).1
      rw [hLoc] at hRange
      change L.sharedBase + 222840 ≤ L.sharedBase + (222824 + 8 * b.val) ∧ _ at hRange
      have := b.isLt
      omega

variable {i cta tx count : Nat} {e : Event} {slot : Fin 4} {rel : Bool} {scope : MbarScope}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound) (he : X.get (g, i) = some e)
include hpre hX hs he

/-- Every actual ready notification comes from a followed index lane. -/
theorem actual_index_ready_arrive (hk : e.kind = .arrive (ready L cta slot) tx count rel scope) :
    AtIndex P L X cta slot g i (fun s => ∃ extra, s = .ready extra) ∧
      tx = 0 ∧ count = 1 ∧ rel = true ∧ scope = .cta := by
  by_cases hFollow : Frame.stateAt (Machine.code P L) X g i = some none
  · obtain ⟨⟨s, hEq⟩, _⟩ :=
      dismissed_index_ring_arrive hpre hX hs he hk (.inl rfl) hFollow
    exact (ready_ne_free hEq).elim
  · exact publish_source_at_tracked_event hpre hX (hs g (Frame.lt_of_get hX he)).machine
      hFollow he hk

/-- Every actual free notification is a unit release from the correct consumer warp. -/
theorem actual_index_free_arrive (hk : e.kind = .arrive (free L cta slot) tx count rel scope) :
    ctaOf L g = cta ∧ ActualFreeIssuer L g e ∧
      tx = 0 ∧ count = 1 ∧ rel = true ∧ scope = .cta := by
  have hg := Frame.lt_of_get hX he
  by_cases hFollow : Frame.stateAt (Machine.code P L) X g i = some none
  · obtain ⟨⟨s, hEq⟩, hOrigin, hFields⟩ :=
      dismissed_index_ring_arrive hpre hX hs he hk (.inr rfl) hFollow
    exact ⟨(free_address hEq).1.symm, hOrigin, hFields⟩
  · obtain ⟨⟨hc, hRole⟩, hFields⟩ :=
      release_source_at_tracked_event hpre hX (hs g hg).machine hFollow he hk
    refine ⟨hc, ?_, hFields⟩
    rcases hRole with ⟨d, _, hSite, hd⟩ | ⟨d, _, hSite, hd⟩
    · have hPc := Frame.event_pc hs hX he hd
      change e.pc = d.site.pc at hPc
      rw [hSite] at hPc
      exact .inl ⟨RingRoleGeometry.of_trace hX hg (hs g hg).machine hd, hPc⟩
    · have hPc := Frame.event_pc hs hX he hd
      change e.pc = d.site.pc at hPc
      rw [hSite] at hPc
      exact .inr ⟨RingRoleGeometry.of_trace hX hg (hs g hg).machine hd, hPc⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
