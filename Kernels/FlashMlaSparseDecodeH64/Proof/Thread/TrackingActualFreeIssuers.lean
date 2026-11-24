-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingActualReadyDescent
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg1TmaLeader

@[expose] public section

/-! # Identities of actual index-slot consumers -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow PTX.AsyncCopy PTX.MBarrier Protocol Protocol.IndexRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

private theorem actual_tma_return_has_body {i : Nat} {e : Event}
    {cta : Nat} {slot : Fin 4}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (he : X.get (g, i) = some e) (hWarp : warpOf L g = 5)
    (hk : e.kind = .arrive (free L cta slot) 0 1 true .cta) :
    ∃ j d, Frame.stateAt (Machine.code P L) X g j = some (some (.tma d)) ∧ d.site ≠ .elect := by
  have hg := Frame.lt_of_get hX he
  by_cases hFollow : Frame.stateAt (Machine.code P L) X g i = some none
  · obtain ⟨j, _, d, f, hf, hd, hn⟩ := prior_dismissal (PTX.len_of_get he).le hFollow
    have hRole := RingRoleGeometry.of_trace hX hg (hs g hg).machine hd
    cases dismissal_is_consumer hpre hX hs hf hd hn with
    | wg0 d => change wgOf L g = 0 at hRole; unfold wgOf warpOf at *; omega
    | wg2 d => change wgOf L g = 2 at hRole; unfold wgOf warpOf at *; omega
  · obtain ⟨⟨_, hOrigin⟩, _⟩ :=
      release_source_at_tracked_event hpre hX (hs g hg).machine hFollow he hk
    rcases hOrigin with ⟨d, _, _, hd⟩ | ⟨d, _, hSite, hd⟩
    · have hRole := RingRoleGeometry.of_trace hX hg (hs g hg).machine hd
      change wgOf L g = 0 at hRole
      unfold wgOf warpOf at *
      omega
    · exact ⟨i, d, hd, by simp [hSite]⟩

/-- The elected TMA issuer is shared by the followed coordinate reader and all actual
same-CTA TMA slot returns, even after a coordinate guard has dismissed them. -/
theorem actual_tma_return_same_lane {g i h j : Nat} {d : Wg1Tma.D} {e : Event}
    {slot : Fin 4}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ a < L.threads, (Machine.code P L a).Sound)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.tma d)))
    (hBody : d.site ≠ .elect)
    (he : X.get (h, j) = some e) (hWarp : warpOf L h = 5)
    (hk : e.kind = .arrive (free L (ctaOf L g) slot) 0 1 true .cta) : h = g := by
  obtain ⟨q, z, hz, hZ⟩ := actual_tma_return_has_body hpre hX hs he hWarp hk
  have hc := (actual_arrive_fields hX he hk).2.1.symm
  obtain ⟨leader, hLead⟩ := Wg1TmaLeader.cta_issuer (cta := ctaOf L g) hpre hX
    (fun a ha => (hs a ha).machine)
  exact (hLead h q z hc hz hZ).trans (hLead g i d rfl hd hBody).symm

/-- The earliest followed mask acquire gives a common origin for every release of a softmax lane. -/
noncomputable def firstMaskStart (P : Params) (L : Launch) (X : Execution) (g : Nat) : Nat := by
  classical
  exact if h : ∃ i, FirstMaskAnchor P L X g i then Nat.find h else 0

/-- This lane's earliest mask acquire can be used to replay any actual index-slot return. -/
theorem first_mask_start_of_release {i : Nat} {e : Event} {m : Loc}
    {tx count : Nat} {rel : Bool} {scope : MbarScope}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (he : X.get (g, i) = some e) (hWg : wgOf L g = 0)
    (hTag : e.pc = Wg0.Site.validFree.pc) (hk : e.kind = .arrive m tx count rel scope) :
    firstMaskStart P L X g ≤ i ∧ FirstMaskAnchor P L X g (firstMaskStart P L X g) := by
  obtain ⟨start, hLe, hAnchor⟩ := first_mask_anchor_of_release hpre hX hs he hWg hTag hk
  have hEx : ∃ t, FirstMaskAnchor P L X g t := ⟨start, hAnchor⟩
  classical
  rw [firstMaskStart, dite_eq_left hEx]
  exact ⟨(Nat.find_min' hEx hAnchor).trans hLe, Nat.find_spec hEx⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
