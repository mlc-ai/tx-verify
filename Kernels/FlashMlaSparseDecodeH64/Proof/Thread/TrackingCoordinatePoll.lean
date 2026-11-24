-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingIndexPublication
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.FollowedPrefix

@[expose] public section

/-! # Identifying the coordinate acquire without global tracking -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow PTX.MbarRing
open Protocol

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- An actual successful ready poll before a followed TMA coordinate read was itself a followed
TMA acquire of the same physical slot. -/
theorem coordinate_poll_at {g i q tag parity : Nat} {acq : Bool} {scope : MbarScope}
    {d : Wg1Tma.D}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound) (hq : q < i)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.tma d)))
    (he : X.get (g, q) = some ⟨tag, .wait (IndexRing.ready L (ctaOf L g) (indexSlot d.block))
      parity true acq scope⟩) :
    ∃ z, Frame.stateAt (Machine.code P L) X g q = some (some (.tma z)) ∧
      z.site = .waitCoord ∧ z.block % 4 = d.block % 4 ∧ acq = true ∧ scope = .cta := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨z, hz⟩ := FollowedPrefix.state_at hd hq.le
  have hcurrent : warpOf L g = 5 := RingRoleGeometry.of_trace hX hg hs hd
  have hprevious := RingRoleGeometry.of_trace hX hg hs hz
  obtain ⟨_, hfire⟩ := RingEvents.fired_of_trace hX hs he hz
  have hsite := RingSourceSites.poll_site hfire rfl
  have hgroup : wgOf L g = 1 := by unfold wgOf warpOf at *; omega
  have haddr := IndexRing.ring_addr_range
    (L := L) (cta := ctaOf L g) (slot := indexSlot d.block) (.inl rfl)
  cases z with
  | tma z =>
    change z.site = .waitQ ∨ z.site = .waitLast ∨ z.site = .waitCoord ∨
      z.site = .waitFree at hsite
    have hr : z.site = .waitCoord := by
      have hs' : (z.site = .waitQ ∨ z.site = .waitLast) ∨
          z.site = .waitCoord ∨ z.site = .waitFree := by tauto
      rcases hs' with h | h | h
      · obtain ⟨off, _, ho, hk⟩ := RingEvents.tmaEntry_wait hpre h hfire
        have hl := (Kind.wait.inj hk).1
        rw [hl] at haddr
        change L.sharedBase + 222840 ≤ L.sharedBase + off ∧ _ at haddr
        rcases ho with rfl | rfl
        · unfold Wg1Tma.qUtccpOff at haddr
          omega
        · unfold Wg1Tma.lastStoreOff at haddr
          omega
      · exact h
      · obtain ⟨_, hk⟩ := RingEvents.rawFree_wait hpre h hfire
        have hl := (Kind.wait.inj hk).1
        rw [hl] at haddr
        change L.sharedBase + 222840 ≤ L.sharedBase + (222824 + 8 * (z.block % 2)) ∧ _ at haddr
        omega
    obtain ⟨_, hk⟩ := RingEvents.validReady_wait hpre hr hfire
    obtain ⟨hl, _, _, ha, hs⟩ := Kind.wait.inj hk
    change IndexRing.ready L (ctaOf L g) (indexSlot d.block) =
      IndexRing.ready L (ctaOf L g) (indexSlot z.block) at hl
    exact ⟨z, hz, hr, (IndexRing.ready_address hl).2.symm, ha, hs⟩
  | wg0 z => change wgOf L g = 0 at hprevious; omega
  | wg2 z => change wgOf L g = 2 at hprevious; omega
  | mma z => change warpOf L g = 4 at hprevious; omega
  | index z => change warpOf L g = 7 at hprevious; omega
  | prologue _ | head | idle _ | done => exact hsite.elim

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
