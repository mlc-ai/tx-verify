-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingCoordinateFuture
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingCoordinatePhase
import Lemmas.Order.OrderWaits

public section

/-! # Every coordinate acquire bounds the generations of its observed publishers -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow PTX.AsyncCopy PTX.MBarrier
open Protocol Protocol.IndexRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- An observed index publication is no later than the coordinate acquire's slot use. -/
theorem coordinate_ready_source_bound
    {g i q tag p h t : Nat} {d : Wg1Tma.D} {z : Wg1Index.D} {e : Event} {extra : Bool}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ a < L.threads, (Machine.code P L a).Sound)
    (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.tma d)))
    (hq : q < i)
    (hWait : X.get (g, q) = some ⟨tag, .wait (ready L (ctaOf L g) (indexSlot d.block))
      p true true .cta⟩)
    (hObserved : WaitObserves X (.thread (h, t)) (g, q)
      (ready L (ctaOf L g) (indexSlot d.block)) true .cta)
    (hz : Frame.stateAt (Machine.code P L) X h t = some (some (.index z)))
    (hReady : z.site = .ready extra) :
    z.block / 4 ≤ Flow.okPolls (ready L (ctaOf L g) (indexSlot d.block)) ((X.tr g).take q) := by
  let m := ready L (ctaOf L g) (indexSlot d.block)
  have hg := Frame.lt_of_get hX he
  obtain ⟨cur, hCur, hSite, hSlot, _, _⟩ :=
    coordinate_poll_at hpre hX (hs g hg).machine hq hd hWait
  have hCurCount := TmaIndexTrace.composed_ready_counts hpre
    ((hs g hg).machine.produces (hX.thr g hg)) hCur hSite
  change Flow.okPolls (ready L (ctaOf L g) (indexSlot cur.block)) ((X.tr g).take q)
    = cur.block / 4 at hCurCount
  rw [show indexSlot cur.block = indexSlot d.block from Fin.ext hSlot] at hCurCount
  rw [hCurCount]
  let next : Wg1Tma.D := { cur with site := .waitFree }
  have hNext : Frame.stateAt (Machine.code P L) X g (q + 1) = some (some (.tma next)) := by
    rw [Frame.stateAt_succ hWait, hCur, Option.bind_some]
    change Machine.next P L g (.tma cur) ⟨tag, .wait m p true true .cta⟩ =
      some (some (.tma next))
    simp only [Machine.next, Wg1Tma.next, hSite, next, ite_true]
  have hNextLen : q + 1 < (X.tr g).length := (Nat.succ_le_of_lt hq).trans_lt (PTX.len_of_get he)
  let v := (X.tr g)[q + 1]'hNextLen
  have hv : X.get (g, q + 1) = some v := List.getElem?_eq_getElem hNextLen
  obtain ⟨u, _, r, _, _, hr, hId, _⟩ := hObserved.2
  have hObsAt : (X.objects m)[u]? = some r := hr
  obtain ⟨f, hf⟩ := hX.object_thread_record_present (List.mem_of_getElem? hObsAt) hId
  have hh := Frame.lt_of_get hX hf
  obtain ⟨_, hFire⟩ := RingEvents.fired_of_trace hX (hs h hh).machine hf hz
  let m' := ready L (ctaOf L h) (indexSlot z.block)
  have hKind := RingEvents.validReady_arrive hpre hReady hFire
  change f.kind = .arrive m' 0 1 true .cta at hKind
  have hf' : X.get (h, t) = some ⟨f.pc, .arrive m' 0 1 true .cta⟩ := by
    rw [hf, ← hKind]
  have hAction := ((hX.tma.2.2.1 m).2.1 r (List.mem_of_getElem? hObsAt)).1
  rw [hId] at hAction
  simp only [objectAction, hf'] at hAction
  have hEq : m' = m := by
    by_contra hn
    have hEmpty : (if m' = m then some (Action.arrive 1 0) else none) = some r.action := hAction
    rw [ite_eq_right hn] at hEmpty
    cases hEmpty
  obtain ⟨hCTA, hZSlot⟩ := ready_address hEq
  have hRel : MbarRelease X (h, t) m .cta := ⟨0, 1, f.pc, hEq ▸ hf'⟩
  have hOrder := Staging.baseCausality_of_handoff hRel hObserved
    (ScopesMeet.of_sameCta ⟨hh, hg, hCTA⟩)
    (e := (h, t)) (f := (g, q + 1)) ⟨rfl, le_rfl⟩ ⟨rfl, by omega, hNextLen⟩
  by_contra! hFuture
  have hCycle := tma_before_future_producer hpre hX hs hv hNext
    (by simp [next]) rfl hf hz (.inl ⟨extra, hReady⟩) hCTA (hZSlot.trans hSlot.symm) hFuture
  exact baseCausality_irrefl hX.object.cause (hCycle.trans hOrder)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
