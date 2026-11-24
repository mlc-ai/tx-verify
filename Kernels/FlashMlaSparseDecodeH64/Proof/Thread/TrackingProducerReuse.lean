-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingFirstFree
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.FollowedPrefix

@[expose] public section

/-! # The actual reuse wait required by a later index publication -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow PTX.MbarRing PTX.AsyncCopy PTX.MBarrier
open Protocol Protocol.IndexRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private theorem index_poll_site {g i q tag parity : Nat} {acq : Bool} {scope : MbarScope}
    {m : Loc} {d : Wg1Index.D}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound) (hq : q < i)
    (hState : Frame.stateAt (Machine.code P L) X g i = some (some (.index d)))
    (he : X.get (g, q) = some ⟨tag, .wait m parity true acq scope⟩) :
    ∃ z extra, z.site = .waitFree extra ∧
      Frame.stateAt (Machine.code P L) X g q = some (some (.index z)) := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨s, hs'⟩ := FollowedPrefix.state_at hState hq.le
  obtain ⟨_, hfire⟩ := RingEvents.fired_of_trace hX hs he hs'
  have hSite := RingSourceSites.poll_site hfire rfl
  have hWarp : warpOf L g = 7 := RingRoleGeometry.of_trace hX hg hs hState
  have hRole := RingRoleGeometry.of_trace hX hg hs hs'
  have hGroup : wgOf L g = 1 := by unfold wgOf warpOf at *; omega
  cases s with
  | index z =>
    obtain ⟨extra, hz⟩ := hSite
    exact ⟨z, extra, hz, hs'⟩
  | wg0 z => change wgOf L g = 0 at hRole; omega
  | wg2 z => change wgOf L g = 2 at hRole; omega
  | tma z => change warpOf L g = 5 at hRole; omega
  | mma z => change warpOf L g = 4 at hRole; omega
  | prologue _ | head | idle _ | done => exact hSite.elim

private theorem producer_free_acquire_of_count {g i use : Nat} {d : Wg1Index.D} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound) (he : X.get (g, i) = some e)
    (hState : Frame.stateAt (Machine.code P L) X g i = some (some (.index d)))
    (hCount : use + 1 ≤ okPolls (free L (ctaOf L g) (indexSlot d.block)) ((X.tr g).take i)) :
    let m := free L (ctaOf L g) (indexSlot d.block)
    ∃ q tag z ex, q < i ∧ X.get (g, q) = some ⟨tag, .wait m (1 - use % 2) true true .cta⟩ ∧
      Frame.stateAt (Machine.code P L) X g q = some (some (.index z)) ∧
      z.site = .waitFree ex ∧ z.block / 4 = use ∧ okPolls m ((X.tr g).take q) = use := by
  let m := free L (ctaOf L g) (indexSlot d.block)
  have hg := Frame.lt_of_get hX he
  have trace := hs.produces (hX.thr g hg)
  obtain ⟨q, tag, parity, acq, scope, hq, hWait, hUseCount⟩ :=
    UnitHandoff.exists_poll (c := use) hCount
  obtain ⟨z, ex, hz, hst⟩ := index_poll_site hX hs hq hState hWait
  obtain ⟨_, hFire⟩ := RingEvents.fired_of_trace hX hs hWait hst
  obtain ⟨_, hFields⟩ := RingEvents.validFree_wait hpre hz hFire
  obtain ⟨hLoc, hPar, _, hacq, hscope⟩ := Kind.wait.inj hFields
  let m' := free L (ctaOf L g) (indexSlot z.block)
  change m = m' at hLoc
  have hc := (IndexRingTrace.composed_free_counts hpre trace hst hz).1
  change okPolls m' ((X.tr g).take q) = z.block / 4 at hc
  rw [← hLoc, hUseCount] at hc
  rw [← hc] at hPar
  exact ⟨q, tag, z, ex, hq, by simpa only [hPar, hacq, hscope] using hWait,
    hst, hz, hc.symm, hUseCount⟩

/-- A producer release follows the real free-slot acquire of every use through its own. -/
theorem producer_free_acquire {g i use : Nat} {d : Wg1Index.D} {e : Event} {extra : Bool}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound) (he : X.get (g, i) = some e)
    (hState : Frame.stateAt (Machine.code P L) X g i = some (some (.index d)))
    (hReady : d.site = .ready extra) (hUse : use ≤ d.block / 4) :
    let m := free L (ctaOf L g) (indexSlot d.block)
    ∃ q tag z ex, q < i ∧ X.get (g, q) = some ⟨tag, .wait m (1 - use % 2) true true .cta⟩ ∧
      Frame.stateAt (Machine.code P L) X g q = some (some (.index z)) ∧
      z.site = .waitFree ex ∧ z.block / 4 = use ∧ okPolls m ((X.tr g).take q) = use := by
  have hCounts := (IndexRingTrace.composed_ready_counts hpre
    (hs.produces (hX.thr g (Frame.lt_of_get hX he))) hState hReady).2
  change okPolls (free L (ctaOf L g) (indexSlot d.block)) ((X.tr g).take i) = d.block / 4 + 1
    at hCounts
  exact producer_free_acquire_of_count hpre hX hs he hState (by omega)

/-- An index store already follows its reuse acquire, before the later ready publication. -/
theorem index_store_free_acquire {g i use : Nat} {d : Wg1Index.D} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound) (he : X.get (g, i) = some e)
    (hState : Frame.stateAt (Machine.code P L) X g i = some (some (.index d)))
    (hStore : (∃ extra high, d.site = .coord extra high) ∨ ∃ extra, d.site = .valid extra)
    (hUse : use ≤ d.block / 4) :
    let m := free L (ctaOf L g) (indexSlot d.block)
    ∃ q tag z ex, q < i ∧ X.get (g, q) = some ⟨tag, .wait m (1 - use % 2) true true .cta⟩ ∧
      Frame.stateAt (Machine.code P L) X g q = some (some (.index z)) ∧
      z.site = .waitFree ex ∧ z.block / 4 = use ∧ okPolls m ((X.tr g).take q) = use := by
  have hCounts := (IndexRingTrace.composed_write_counts hpre
    (hs.produces (hX.thr g (Frame.lt_of_get hX he))) hState hStore).2
  change okPolls (free L (ctaOf L g) (indexSlot d.block)) ((X.tr g).take i) = d.block / 4 + 1
    at hCounts
  exact producer_free_acquire_of_count hpre hX hs he hState (by omega)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
