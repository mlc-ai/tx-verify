-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingTmaCoordinate
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingCoordinatePhase
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingReadyDescent

@[expose] public section

/-! # A later TMA return depends on a later index publication -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow PTX.AsyncCopy PTX.MBarrier Protocol Protocol.IndexRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

theorem tma_depends_on_later_producer {g i n : Nat} {d : Wg1Tma.D} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.tma d)))
    (hSite : d.site = .coordFree) (hLater : n < d.block / 4) :
    ∃ (h j : Nat) (f : Event) (z : Wg1Index.D) (extra : Bool),
      X.get (h, j) = some f ∧ Frame.stateAt (Machine.code P L) X h j = some (some (.index z)) ∧
      ctaOf L h = ctaOf L g ∧ z.block % 4 = d.block % 4 ∧ z.site = .ready extra ∧
      n < z.block / 4 ∧ baseCausality L X (h, j) (g, i) := by
  classical
  let slot := indexSlot d.block
  let m := ready L (ctaOf L g) slot
  have hg := Frame.lt_of_get hX he
  have hCount := (TmaIndexTrace.composed_free_counts hpre
    ((hs g hg).machine.produces (hX.thr g hg)) hd hSite).2
  change Flow.okPolls m ((X.tr g).take i) = d.block / 4 + 1 at hCount
  have existsPoll (a : Fin (n + 2)) :
      ∃ w : IndexPhaseWait X m g i 32, Flow.okPolls m ((X.tr g).take w.pos) = a.val ∧
        (w.before.phase - 1) % 2 = a.val % 2 := by
    have ha := a.isLt
    obtain ⟨q, tag, idx, r, t, ph, hq, hEvt, hOrd, hr, hid, hState, hExp, _, hClean,
      hWait, hObs, hNext, _, hParity⟩ :=
      tma_ready_record_at_use hpre hX hs he hd (show a.val + 1 ≤
        Flow.okPolls m ((X.tr g).take i) by omega)
    have hPh : t.phase - 1 = ph := by omega
    exact ⟨⟨q, tag, a.val % 2, hq, hEvt, idx, r, t, hr, hid, hClean, hWait, hState,
      hExp, by omega, by rwa [hPh]⟩, hOrd, hPh ▸ hParity⟩
  let waits (a : Fin (n + 2)) := (existsPoll a).choose
  have hOrdered : StrictMono (fun a => (waits a).before.phase) := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro a
    let w := waits a.castSucc
    let v := waits a.succ
    have hA := (existsPoll a.castSucc).choose_spec
    have hB := (existsPoll a.succ).choose_spec
    change Flow.okPolls m ((X.tr g).take w.pos) = a.val ∧ _ at hA
    change Flow.okPolls m ((X.tr g).take v.pos) = a.val + 1 ∧ _ at hB
    have hPos : w.pos < v.pos := by
      by_contra! hn
      have hh := PTX.MbarRing.Poll.okPolls_mono m (X.tr g) hn
      rw [hB.1, hA.1] at hh
      omega
    have hIdx := (hX.object_thread_index_iff w.get v.get w.source v.source).2 hPos
    obtain ⟨s, ht, hMon⟩ := (X.objects_checked hX m).phase_mono
      (objects_single_lifetime hX m) hIdx.le (List.getElem?_eq_some_iff.mp v.get).1.le w.state
    rw [v.state] at ht
    obtain rfl := Option.some.inj ht
    have hAP : (w.before.phase - 1) % 2 = a.val % 2 := hA.2
    have hBP : (v.before.phase - 1) % 2 = (a.val + 1) % 2 := hB.2
    change w.before.phase < v.before.phase
    omega
  obtain ⟨positions, hCard, hOrigins⟩ :=
    actual_index_phase_pool hpre hX hs (.inl rfl :
      m = ready L (ctaOf L g) slot ∨ m = free L (ctaOf L g) slot) he waits hOrdered
  apply later_producer_of_ready_pool hpre hX hs hCard
  intro p hp
  obtain ⟨r, h, j, tag, hr, hid, hGet, hOrder⟩ := hOrigins p hp
  obtain ⟨⟨hc, z, hSlot, ⟨extra, hSite⟩, hz⟩, _⟩ :=
    actual_index_ready_arrive hpre hX hs hGet rfl
  exact ⟨r, h, j, _, z, extra, hr, hid, hc, hSlot, hSite, hGet, hz, hOrder⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
