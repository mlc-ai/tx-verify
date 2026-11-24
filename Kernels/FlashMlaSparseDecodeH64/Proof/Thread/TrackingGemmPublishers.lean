-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.GemmRingSources
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingDequantInputs
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxPublication
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxReturnOrigin
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingIndexActualArrival
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingRoleGeometry

@[expose] public section

/-! # Actual arrivals on GEMM objects -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow Protocol.GemmRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- Only the actual dequantizers and softmax lanes publish to these four objects. -/
theorem actual_gemm_arrival {g i cta tx count : Nat} {rel : Bool} {sc : MbarScope}
    {slot : Fin 2} {obj : Object} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (he : X.get (g, i) = some e) (hk : e.kind = .arrive (obj.loc L cta slot) tx count rel sc) :
    ctaOf L g = cta ∧ tx = 0 ∧ count = 1 ∧ rel = true ∧ sc = .cta ∧
      ((obj = .dequantReady ∧ Publisher P L X g i cta slot .dequantReady) ∨
        (obj = .soReady ∧ wgOf L g = 0 ∧ e.pc = Wg0.Site.soReady.pc ∧
          ∃ start ≤ i, FirstMaskAnchor P L X g start)) := by
  have hg := Frame.lt_of_get hX he
  by_cases hFollow : Frame.stateAt (Machine.code P L) X g i = some none
  · have hWg : wgOf L g = 0 := by
      by_contra hn
      exact tracked_nonsoftmax_wg hpre hX hs hn i hFollow
    obtain ⟨j, hj, role, f, hf, hState, hNext⟩ := prior_dismissal (PTX.len_of_get he).le hFollow
    have hRole := RingRoleGeometry.of_trace hX hg (hs g hg).machine hState
    cases dismissal_is_consumer hpre hX hs hf hState hNext with
    | wg0 d =>
      obtain ⟨hSites, start, hStart, hAnchor⟩ :=
        dismissed_softmax_arrival_site hpre hX hs he hf hj hState hNext
          (RingSourceSites.actual_arrive_pc hX he hk)
      rcases hSites with hFree | hScore
      · obtain ⟨b, _, _, hKind, _⟩ :=
          actual_softmax_return_ordinal hpre hX hs he hStart hAnchor hFree
        have hAddr := congrArg Loc.addr (Kind.arrive.inj (hk.symm.trans hKind)).1
        have hLt := slot.isLt
        change L.sharedBase + (obj.base + 8 * slot.val) =
          L.sharedBase + (222872 + 8 * (b % 4)) at hAddr
        cases obj <;> simp only [Object.base] at hAddr <;> omega
      · obtain ⟨buf, hKind⟩ := actual_softmax_publication hpre hX hs he hWg hScore hk
        obtain ⟨hl, htx, hc, hr, hsc⟩ := Kind.arrive.inj (hk.symm.trans hKind)
        have hCta : ctaOf L g = cta := (congrArg Loc.cta hl).symm
        have hAddr := congrArg Loc.addr hl
        change L.sharedBase + (obj.base + 8 * slot.val) =
          L.sharedBase + (222920 + 8 * buf.val) at hAddr
        have hLt := slot.isLt
        have hB := buf.isLt
        cases obj <;> simp only [Object.base] at hAddr <;> try omega
        exact ⟨hCta, htx, hc, hr, hsc, .inr ⟨rfl, hWg, hScore, start, hStart, hAnchor⟩⟩
    | wg2 d =>
      change wgOf L g = 2 at hRole
      omega
  · obtain ⟨hSource, htx, hc, hr, hsc⟩ :=
      arrival_at_followed hpre hX (hs g hg).machine hFollow he hk
    cases obj with
    | dequantReady => exact ⟨hSource.1, htx, hc, hr, hsc, .inl ⟨rfl, hSource⟩⟩
    | soReady =>
      obtain ⟨hCta, d, _, hSite, hd⟩ := hSource
      have hWg := RingRoleGeometry.of_trace hX hg (hs g hg).machine hd
      have hPc := Frame.event_pc hs hX he hd
      change e.pc = d.site.pc at hPc
      rw [hSite] at hPc
      exact ⟨hCta, htx, hc, hr, hsc, .inr ⟨rfl, hWg, hPc,
        first_mask_of_probability_publication (PTX.len_of_get he).le hd hSite⟩⟩
    | qkDone | svDone => exact hSource.elim

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
