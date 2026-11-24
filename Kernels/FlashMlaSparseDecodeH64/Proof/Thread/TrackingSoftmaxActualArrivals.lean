-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingDequantInputs
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingIndexActualArrival
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxPublication

@[expose] public section

/-! # Actual arrival addresses after softmax dismissal -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow

/-- A dismissed lane only releases index slots and publishes score slots. -/
theorem dismissed_arrival_range {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g i tx count : Nat} {rel : Bool} {sc : MbarScope} {m : Loc} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (he : X.get (g, i) = some e) (hk : e.kind = .arrive m tx count rel sc)
    (hDismiss : Frame.stateAt (Machine.code P L) X g i = some none) :
    L.sharedBase + 222872 ≤ m.addr ∧ m.addr ≤ L.sharedBase + 222928 := by
  have hg := Frame.lt_of_get hX he
  have hWg : wgOf L g = 0 := by
    by_contra hn
    exact tracked_nonsoftmax_wg hpre hX hs hn i hDismiss
  obtain ⟨j, hj, d, f, hf, hState, hNext⟩ := prior_dismissal (PTX.len_of_get he).le hDismiss
  have hRole := RingRoleGeometry.of_trace hX hg (hs g hg).machine hState
  cases dismissal_is_consumer hpre hX hs hf hState hNext with
  | wg0 d =>
    obtain ⟨hSites, start, hLe, hAnchor⟩ :=
      dismissed_softmax_arrival_site hpre hX hs he hf hj hState hNext
        (RingSourceSites.actual_arrive_pc hX he hk)
    rcases hSites with hFree | hScore
    · obtain ⟨visit, _, _, hKind, _⟩ :=
        actual_softmax_return_ordinal hpre hX hs he hLe hAnchor hFree
      have hAddr := congrArg Loc.addr (Kind.arrive.inj (hk.symm.trans hKind)).1
      change m.addr = L.sharedBase + (222872 + 8 * (visit % 4)) at hAddr
      omega
    · obtain ⟨slot, hKind⟩ := actual_softmax_publication hpre hX hs he hWg hScore hk
      have hAddr := congrArg Loc.addr (Kind.arrive.inj (hk.symm.trans hKind)).1
      change m.addr = L.sharedBase + (222920 + 8 * slot.val) at hAddr
      have := slot.isLt
      omega
  | wg2 d => change wgOf L g = 2 at hRole; omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
