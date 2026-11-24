-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingReadyCoverage
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingCoordinatePhase
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingActualIndexPhases

@[expose] public section

/-! # The selected coordinate writer from an aligned ready phase -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Proof PTX.Flow PTX.MbarRing PTX.AsyncCopy PTX.MBarrier
open Protocol Protocol.IndexRing IndexRingThreads

/-- To obtain the exact published coordinate bytes, it suffices to align the ordinary updates
of the observed ready phase with the reader's block. There is no full-ring premise. -/
theorem coordinate_writer_of_aligned_releases {P : Params} {L : Launch}
    {mem0 : Mem0} {X : Execution} {g i : Nat} {d : Wg1Tma.D} {e : Event}
    {k : Fin 16} {j : Fin 4}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.tma d)))
    (hsite : d.site = .coord k j)
    (hAligned : ∀ {q h t : Nat} {z : Wg1Index.D} {extra : Bool}, q < i →
      Flow.okPolls (ready L (ctaOf L g) (indexSlot d.block)) ((X.tr g).take q) = d.block / 4 →
      WaitObserves X (.thread (h, t)) (g, q) (ready L (ctaOf L g) (indexSlot d.block)) true .cta →
      Frame.stateAt (Machine.code P L) X h t = some (some (.index z)) →
      z.site = .ready extra → z.block / 4 = d.block / 4) :
    ∃ a bs w aw, e.kind = .rd a bs ∧ a.size = 4 ∧ a.loc = aw.loc ∧ aw.size = 4 ∧
      X.MemWrites (.thread w) aw (b32 (Wg1Tma.coordAt P L g d.block
        (Wg1Tma.coordPos k.val j.val))).toBytes ∧ baseCausality L X w (g, i) ∧
      ∃ (z : Wg1Index.D) (extra high : Bool),
        Frame.stateAt (Machine.code P L) X w.1 w.2 = some (some (.index z)) ∧
        z.site = .coord extra high ∧ z.block = d.block := by
  let cta := ctaOf L g
  let slot := indexSlot d.block
  let m := ready L cta slot
  let log := X.objects m
  obtain ⟨q, tag, idx, r, before, phase, hq, hWait, hCount, hi, hId, hBefore, hExp,
    _, hClean, hReply, hObs, hPhase, _, _⟩ :=
    coordinate_records_for_earlier_uses hpre hX hs he hd hsite (le_refl (d.block / 4))
  obtain ⟨positions, hCard, hRecords⟩ :=
    actual_ready_producers hpre hX hs hi hBefore hPhase hExp
  have observes (x : Nat) (hx : x ∈ positions) :
      ∃ (rec : Record Ref) (h t : Nat) (z : Wg1Index.D) (extra : Bool),
        log[x]? = some rec ∧ rec.id = .thread (h, t) ∧ ctaOf L h = cta ∧
        z.block = d.block ∧ z.site = .ready extra ∧
        Frame.stateAt (Machine.code P L) X h t = some (some (.index z)) ∧
        WaitObserves X (.thread (h, t)) (g, q) m true .cta := by
    obtain ⟨r', h, t, ht, get, rid, _, clean, hAt, hc, z, hSlot, ⟨extra, hSite⟩, hState⟩ :=
      hRecords x hx
    have hObserve : WaitObserves X (.thread (h, t)) (g, q) m true .cta :=
      ⟨⟨tag, d.block / 4 % 2, hWait⟩, x, idx, r', r, phase, get, rid, clean, hi, hId, hClean,
        hReply, ht, hAt, hObs, (objects_single_lifetime hX m).sameLifetime x idx⟩
    have hUse' := hAligned hq hCount hObserve hState hSite
    have hMod : z.block % 4 = d.block % 4 := hSlot
    exact ⟨r', h, t, z, extra, get, rid, hc, by omega, hSite, hState, hObserve⟩
  let pos := Wg1Tma.coordPos k.val j.val
  let lane : Fin 32 := ⟨pos / 2, by
    have hk := k.isLt
    have hj := j.isLt
    unfold pos Wg1Tma.coordPos
    omega⟩
  obtain ⟨x, hx, rec, t, z, extra, hRec, hRid, hBlock, hReady, hState⟩ :=
    ready_positions_cover_lanes hpre hX hs hCard
      (fun x hx => by
        obtain ⟨r, h, t, z, ex, hr, hid, hc, hb, hsite, hs, _⟩ := observes x hx
        exact ⟨r, h, t, z, ex, hr, hid, hc, hb, hsite, hs⟩) lane
  let h := producerThread L cta lane
  obtain ⟨rec', h', t', _, _, hr, hid, _, _, _, _, hObserve⟩ := observes x hx
  change log[x]? = some rec at hRec
  have hEq : rec' = rec := Option.some.inj (hr.symm.trans hRec)
  have hSource : (h', t') = (h, t) := Ref.thread.inj (hid.symm.trans (hEq ▸ hRid))
  have hObsHere : WaitObserves X (.thread (h, t)) (g, q) m true .cta := hSource ▸ hObserve
  obtain ⟨rel, hrel⟩ := hX.object_thread_record_present (List.mem_of_getElem? hRec) hRid
  have hh := Frame.lt_of_get hX hrel
  have hg := Frame.lt_of_get hX he
  have hCta : ctaOf L h = cta := (producerThread_facts hpre (NamedBar.cta_lt hg) lane).2.1
  obtain ⟨_, hFire⟩ := RingEvents.fired_of_trace hX (hs h hh).machine hrel hState
  have hReleaseKind := RingEvents.validReady_arrive hpre hReady hFire
  change h / L.block = cta at hCta
  rw [hCta, hBlock] at hReleaseKind
  change rel.kind = .arrive m 0 1 true .cta at hReleaseKind
  have hRelease : MbarRelease X (h, t) m .cta := by
    refine ⟨0, 1, rel.pc, ?_⟩
    rw [hrel, ← hReleaseKind]
  have hCounts := (IndexRingTrace.composed_ready_counts hpre
    ((hs h hh).machine.produces (hX.thr h hh)) hState hReady).1
  rw [hCta, hBlock] at hCounts
  exact coordinate_write_before_read hpre hX (fun g hg => (hs g hg).machine) he hd hsite
    lane rfl hq .cta .cta
    hRelease hCounts hObsHere (ScopesMeet.of_sameCta ⟨hh, hg, hCta⟩)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
