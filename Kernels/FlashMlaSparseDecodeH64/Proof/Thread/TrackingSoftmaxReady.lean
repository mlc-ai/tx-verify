-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingFreeDuplicate
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.FollowedPrefix

@[expose] public section

/-! # Earlier ready acquires of an actual WG0 release -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow PTX.MbarRing
open Protocol Protocol.IndexRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private theorem softmax_ready_site {g i q tag parity : Nat} {acq : Bool} {scope : MbarScope}
    {slot : Fin 4} {d : Wg0.D}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound) (hq : q < i)
    (hState : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (he : X.get (g, q) = some ⟨tag, .wait (ready L (ctaOf L g) slot) parity true acq scope⟩) :
    ∃ z, z.site = .maskReady ∧
      Frame.stateAt (Machine.code P L) X g q = some (some (.wg0 z)) := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨s, hst⟩ := FollowedPrefix.state_at hState hq.le
  obtain ⟨_, hFire⟩ := RingEvents.fired_of_trace hX hs he hst
  have hSite := RingSourceSites.poll_site hFire rfl
  have hGroup : wgOf L g = 0 := RingRoleGeometry.of_trace hX hg hs hState
  have hRole := RingRoleGeometry.of_trace hX hg hs hst
  have hWarp : warpOf L g < 4 := by unfold wgOf warpOf at *; omega
  have haddr := ring_addr_range (L := L) (cta := ctaOf L g) (slot := slot) (.inl rfl)
  cases s with
  | wg0 z =>
    rcases hSite with hz | hz | hz
    · exact ⟨z, hz, hst⟩
    · obtain ⟨off, _, _, _, hOff, hk⟩ := RingEvents.gemmDone_wait hpre (.inl hz) hFire
      rw [(Kind.wait.inj hk).1] at haddr
      change _ ∧ L.sharedBase + off ≤ _ at haddr
      rcases hOff with rfl | rfl <;>
        simp only [Wg0.qkDoneOff, Wg0.svDoneOff] at haddr <;> omega
    · obtain ⟨off, _, _, _, hOff, hk⟩ := RingEvents.gemmDone_wait hpre (.inr hz) hFire
      rw [(Kind.wait.inj hk).1] at haddr
      change _ ∧ L.sharedBase + off ≤ _ at haddr
      rcases hOff with rfl | rfl <;>
        simp only [Wg0.qkDoneOff, Wg0.svDoneOff] at haddr <;> omega
  | wg2 z => change wgOf L g = 2 at hRole; omega
  | index z => change warpOf L g = 7 at hRole; omega
  | tma z => change warpOf L g = 5 at hRole; omega
  | mma z => change warpOf L g = 4 at hRole; omega
  | prologue _ | head | idle _ | done => exact hSite.elim

/-- Every slot use through the WG0 mask read or release acquires at the matching ordinal. -/
theorem softmax_ready_acquire {g i n : Nat} {d : Wg0.D} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound) (he : X.get (g, i) = some e)
    (hState : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hSite : d.site = .validFree ∨ d.site = .maskRead) (hn : n ≤ d.block / 4) :
    let m := ready L (ctaOf L g) (indexSlot d.block)
    ∃ q tag z, q < i ∧ X.get (g, q) = some ⟨tag, .wait m (n % 2) true true .cta⟩ ∧
      okPolls m ((X.tr g).take q) = n ∧
      Frame.stateAt (Machine.code P L) X g q = some (some (.wg0 z)) := by
  let m := ready L (ctaOf L g) (indexSlot d.block)
  have hg := Frame.lt_of_get hX he
  have trace := hs.produces (hX.thr g hg)
  have hCount : okPolls m ((X.tr g).take i) = d.block / 4 + 1 := by
    rcases hSite with hRelease | hMask
    · exact (Wg0IndexTrace.composed_free_counts hpre trace hState hRelease).2
    · exact (Wg0IndexTrace.composed_mask_read_counts hpre trace hState hMask).2
  obtain ⟨q, tag, parity, acq, scope, hq, hWait, hOrd⟩ :=
    UnitHandoff.exists_poll (c := n) (show n + 1 ≤ okPolls m ((X.tr g).take i) by omega)
  obtain ⟨z, hz, hst⟩ := softmax_ready_site hpre hX hs hq hState hWait
  obtain ⟨_, hFire⟩ := RingEvents.fired_of_trace hX hs hWait hst
  obtain ⟨_, heq⟩ := RingEvents.maskReady_wait hpre hz hFire
  obtain ⟨hLoc, hParity, _, hAcq, hScope⟩ := Kind.wait.inj heq
  let m' := ready L (ctaOf L g) (indexSlot z.block)
  change m = m' at hLoc
  have hCount' := Wg0IndexTrace.composed_ready_counts hpre trace hst hz
  change okPolls m' ((X.tr g).take q) = z.block / 4 at hCount'
  rw [← hLoc, hOrd] at hCount'
  rw [← hCount'] at hParity
  exact ⟨q, tag, z, hq, by simpa only [hParity, hAcq, hScope] using hWait, hOrd, hst⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
