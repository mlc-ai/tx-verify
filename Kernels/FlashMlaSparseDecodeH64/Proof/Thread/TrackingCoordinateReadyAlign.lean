-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingCoordinateReadyBound
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingReadyCoverage

public section

set_option maxHeartbeats 800000

/-! # Each coordinate acquire observes exactly its own generation of index publishers -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow PTX.AsyncCopy PTX.MBarrier
open Protocol Protocol.IndexRing IndexRingThreads

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private structure CoordinatePoll (X : Execution) (m : Loc) (g i n : Nat) where
  pos : Nat
  tag : Nat
  idx : Nat
  record : Record Ref
  before : State
  phase : Nat
  lt : pos < i
  event : X.get (g, pos) = some ⟨tag, .wait m (n % 2) true true .cta⟩
  count : Flow.okPolls m ((X.tr g).take pos) = n
  get : (X.objects m)[idx]? = some record
  id : record.id = .thread (g, pos)
  state : stateBefore (X.objects m) idx = some before
  expected : before.expected = 32
  clean : record.fault = none
  waited : record.reply.waited = some true
  observed : observedAt (X.objects m) idx = some phase
  nextPhase : before.phase = phase + 1
  parity : phase % 2 = n % 2

private theorem CoordinatePoll.phase_lt_succ {g i n : Nat} {m : Loc}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (a : CoordinatePoll X m g i n) (b : CoordinatePoll X m g i (n + 1)) :
    a.phase < b.phase := by
  have hPos : a.pos < b.pos := by
    by_contra! hn
    have hp := PTX.MbarRing.Poll.okPolls_mono m (X.tr g) hn
    rw [a.count, b.count] at hp
    omega
  have hi := (hX.object_thread_index_iff a.get b.get a.id b.id).mpr hPos
  obtain ⟨v, hv, hMon⟩ := (X.objects_checked hX m).phase_mono (objects_single_lifetime hX m) hi.le
    (List.getElem?_eq_some_iff.mp b.get).1.le a.state
  rw [b.state] at hv
  obtain rfl := Option.some.inj hv
  have ha := a.parity
  have hb := b.parity
  rw [a.nextPhase, b.nextPhase] at hMon
  omega

/-- The ordinary releases observed by a successful coordinate poll come from the same
generation of its slot as counted in the consumer's own trace. -/
theorem coordinate_ready_sources_aligned {g i q : Nat} {d : Wg1Tma.D}
    {e : Event} {k : Fin 16} {j : Fin 4}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.tma d)))
    (hSite : d.site = .coord k j)
    (hCount : Flow.okPolls (ready L (ctaOf L g) (indexSlot d.block)) ((X.tr g).take q) =
      d.block / 4) :
    ∀ {h t : Nat} {z : Wg1Index.D} {extra : Bool},
      WaitObserves X (.thread (h, t)) (g, q) (ready L (ctaOf L g) (indexSlot d.block)) true .cta →
      Frame.stateAt (Machine.code P L) X h t = some (some (.index z)) →
      z.site = .ready extra → z.block / 4 = d.block / 4 := by
  classical
  let cta := ctaOf L g
  let slot := indexSlot d.block
  let m := ready L cta slot
  let N := d.block / 4
  have existsPoll (n : Fin (N + 1)) : Nonempty (CoordinatePoll X m g i n.val) := by
    obtain ⟨p, tag, idx, r, b, ph, hp, hEvt, hCount, hr, hid, hState, hExp,
      _, hClean, hWait, hObs, hNext, _, hParity⟩ :=
      coordinate_records_for_earlier_uses hpre hX hs he hd hSite (n := n.val)
        (by have := n.isLt; omega)
    exact ⟨⟨p, tag, idx, r, b, ph, hp, hEvt, hCount, hr, hid, hState, hExp, hClean,
      hWait, hObs, hNext, hParity⟩⟩
  let poll (n : Fin (N + 1)) := (existsPoll n).some
  have hStrict : StrictMono (fun n : Fin (N + 1) => (poll n).phase) := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro n
    exact (poll n.castSucc).phase_lt_succ hX (poll n.succ)
  have phase (n : Fin (N + 1)) {h t : Nat}
      (hObserve : WaitObserves X (.thread (h, t)) (g, (poll n).pos) m true .cta) :
      ∃ a r, (X.objects m)[a]? = some r ∧ r.id = .thread (h, t) ∧
        phaseAt (X.objects m) a = some (poll n).phase := by
    obtain ⟨a, b, r, w, ph, ha, hId, _, hb, hwId, _, _, _, hPh, hObs, _⟩ := hObserve.2
    have hbEq := hX.object_index_eq hb (poll n).get (hwId.trans (poll n).id.symm)
    rw [hbEq, (poll n).observed] at hObs
    obtain rfl := Option.some.inj hObs
    exact ⟨a, r, ha, hId, hPh⟩
  have aligned (u : Nat) (hu : u ≤ N) :
      ∀ {h t : Nat} {z : Wg1Index.D} {extra : Bool},
        WaitObserves X (.thread (h, t)) (g, (poll ⟨u, by omega⟩).pos) m true .cta →
        Frame.stateAt (Machine.code P L) X h t = some (some (.index z)) →
        z.site = .ready extra → z.block / 4 = u := by
    induction u using Nat.strong_induction_on with
    | h u ih =>
      intro h t z extra hObs hz hReady
      let p := poll ⟨u, by omega⟩
      have hUpper := coordinate_ready_source_bound hpre hX hs he hd p.lt p.event
        hObs hz hReady
      rw [p.count] at hUpper
      change z.block / 4 ≤ u at hUpper
      by_contra! hNe
      let v := z.block / 4
      have hv : v < u := by omega
      let n : Fin (N + 1) := ⟨v, by omega⟩
      let prev := poll n
      obtain ⟨pos, rec, hRec, hId, hAt⟩ := phase ⟨u, by omega⟩ hObs
      obtain ⟨f, hf⟩ := hX.object_thread_record_present (List.mem_of_getElem? hRec) hId
      have hh := Frame.lt_of_get hX hf
      have hWarp := RingRoleGeometry.of_trace hX hh (hs h hh).machine hz
      obtain ⟨_, hFire⟩ := RingEvents.fired_of_trace hX (hs h hh).machine hf hz
      have hKind := RingEvents.validReady_arrive hpre hReady hFire
      let m' := ready L (ctaOf L h) (indexSlot z.block)
      change f.kind = .arrive m' 0 1 true .cta at hKind
      have hf' : X.get (h, t) = some ⟨f.pc, .arrive m' 0 1 true .cta⟩ := by
        rw [hf, ← hKind]
      have hAction := ((hX.tma.2.2.1 m).2.1 rec (List.mem_of_getElem? hRec)).1
      rw [hId] at hAction
      simp only [objectAction, hf'] at hAction
      have hEq : m' = m := by
        by_contra hn
        have hEmpty : (if m' = m then some (Action.arrive 1 0) else none) =
            some rec.action := hAction
        rw [ite_eq_right hn] at hEmpty
        cases hEmpty
      obtain ⟨hCta, hZSlot⟩ := ready_address hEq
      obtain ⟨lane, hLane⟩ := producer_of_warp hpre hCta hWarp
      obtain ⟨ps, hCard, hPS⟩ :=
        actual_ready_producers hpre hX hs prev.get prev.state prev.nextPhase prev.expected
      have hSlotEq : indexSlot z.block = slot := Fin.ext hZSlot
      have counted (a : Nat) (ha : a ∈ ps) :
          ∃ (r : Record Ref) (b s : Nat) (w : Wg1Index.D) (ex : Bool),
            (X.objects (ready L cta (indexSlot z.block)))[a]? = some r ∧ r.id = .thread (b, s) ∧
            ctaOf L b = cta ∧ w.block = z.block ∧ w.site = .ready ex ∧
            Frame.stateAt (Machine.code P L) X b s = some (some (.index w)) := by
        obtain ⟨r, b, s, hEarlier, hr, hid, _, hClean, hPhase,
          hC, w, hSlot, ⟨ex, hSite⟩, hSt⟩ := hPS a ha
        have hObserve : WaitObserves X (.thread (b, s)) (g, prev.pos) m true .cta :=
          ⟨⟨prev.tag, n.val % 2, prev.event⟩, a, prev.idx, r, prev.record, prev.phase,
            hr, hid, hClean, prev.get, prev.id, prev.clean, prev.waited, hEarlier, hPhase,
            prev.observed, (objects_single_lifetime hX m).sameLifetime a prev.idx⟩
        have hUse := ih v hv (by omega) hObserve hSt hSite
        change w.block / 4 = z.block / 4 at hUse
        have hBlock : w.block = z.block := by
          change w.block % 4 = d.block % 4 at hSlot
          change z.block % 4 = d.block % 4 at hZSlot
          omega
        rw [hSlotEq]
        exact ⟨r, b, s, w, ex, hr, hid, hC, hBlock, hSite, hSt⟩
      obtain ⟨a, ha, r, s, w, ex, hr, hid, hBlock, hSite', hSt⟩ :=
        ready_positions_cover_lanes hpre hX hs hCard counted lane
      rw [hSlotEq] at hr
      rw [← hLane] at hid hSt
      obtain ⟨f', hf'⟩ := hX.object_thread_record_present (List.mem_of_getElem? hr) hid
      have hSame := ready_same_block_unique hpre hX (hs h hh).machine hf hf' hz hSt
        hReady hSite' hBlock.symm
      rw [hSame] at hId
      have hIndex := hX.object_index_eq hRec hr (hId.trans hid.symm)
      obtain ⟨_, _, _, _, _, _, _, _, hPrevPhase, _⟩ := hPS a ha
      rw [hIndex, hPrevPhase] at hAt
      have hPhaseOrder := hStrict (show n < (⟨u, by omega⟩ : Fin (N + 1)) from hv)
      have hPhaseSame := Option.some.inj hAt
      exact (Nat.ne_of_lt hPhaseOrder) hPhaseSame
  intro h t z extra hObserve hz hReady
  let last : Fin (N + 1) := ⟨N, by omega⟩
  obtain ⟨tag, p, hWait⟩ := hObserve.1
  have hQ := PTX.MbarRing.Poll.okPoll_index_unique hWait (poll last).event
    (hCount.trans (poll last).count.symm)
  rw [hQ] at hObserve
  exact aligned N (Nat.le_refl N) hObserve hz hReady

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
