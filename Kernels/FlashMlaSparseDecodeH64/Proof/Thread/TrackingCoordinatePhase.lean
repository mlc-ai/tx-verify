-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingCoordinateWait
import Lemmas.Order.CausalObjectWaitCount

public section

/-! # The sequence of TMA ready waits advances the checked barrier phases -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow PTX.AsyncCopy PTX.MBarrier
open Protocol Protocol.IndexRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private theorem ready_poll_record {g i q tag p : Nat} {d : Wg1Tma.D} {e : Event}
    {acq : Bool} {scope : MbarScope}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.tma d)))
    (hq : q < i)
    (hPoll : X.get (g, q) = some ⟨tag, .wait (ready L (ctaOf L g) (indexSlot d.block))
      p true acq scope⟩) :
    let m := ready L (ctaOf L g) (indexSlot d.block)
    ∃ idx r st, (X.objects m)[idx]? = some r ∧ r.id = .thread (g, q) ∧
      stateBefore (X.objects m) idx = some st ∧ st.expected = 32 ∧
      r.action = .pollParity p true ∧ r.fault = none ∧ r.reply.waited = some true ∧
      p = PTX.Flow.okPolls m ((X.tr g).take q) % 2 ∧ st.phase % 2 ≠ p % 2 ∧
      r.reply.completed = if 0 < st.phase then some (st.phase - 1) else none := by
  let m := ready L (ctaOf L g) (indexSlot d.block)
  have hg := Frame.lt_of_get hX he
  obtain ⟨z, hz, hSite, hSlot, rfl, rfl⟩ :=
    coordinate_poll_at hpre hX (hs g hg).machine hq hd hPoll
  let entry := readyEntry (indexSlot d.block)
  have hm : initTable.loc L (ctaOf L g) entry = m :=
    ready_entry_loc L (ctaOf L g) (indexSlot d.block)
  have hWait : X.get (g, q) = some
      ⟨tag, .wait (initTable.loc L (ctaOf L g) entry) p true true .cta⟩ := hm ▸ hPoll
  obtain ⟨idx, r, before, hi, hId, hBefore, hExp, hAct, hClean, hResponse⟩ :=
    wait_after_table_init hpre hX hs hz (by intro s hx; cases hx) entry hWait
  rw [hm] at hi hBefore
  change before.expected = initCount (readyEntry (indexSlot d.block)) at hExp
  rw [ready_entry_count] at hExp
  obtain ⟨_, parity, hState, hAct', hNe, hCompletion⟩ :=
    (X.objects_checked hX m).okPoll hi hResponse
  rw [hBefore] at hState
  obtain rfl := Option.some.inj hState
  rw [hAct] at hAct'
  obtain ⟨rfl, _⟩ := Action.pollParity.inj hAct'
  obtain ⟨_, hFire⟩ := RingEvents.fired_of_trace hX (hs g hg).machine hPoll hz
  obtain ⟨_, hKind⟩ := RingEvents.validReady_wait hpre hSite hFire
  have hParity : p = z.block / 4 % 2 := (Kind.wait.inj hKind).2.1
  have hCount := TmaIndexTrace.composed_ready_counts hpre
    ((hs g hg).machine.produces (hX.thr g hg)) hz hSite
  change PTX.Flow.okPolls (ready L (ctaOf L g) (indexSlot z.block)) ((X.tr g).take q) =
    z.block / 4 at hCount
  have hEq : indexSlot z.block = indexSlot d.block := Fin.ext hSlot
  rw [hEq] at hCount
  rw [← hCount] at hParity
  exact ⟨idx, r, before, hi, hId, hBefore, hExp, hAct, hClean, hResponse, hParity, hNe, hCompletion⟩

private theorem ready_wait_phase_lower {g i : Nat} {d : Wg1Tma.D} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.tma d))) :
    let m := ready L (ctaOf L g) (indexSlot d.block)
    ∀ n {q tag p : Nat} {acq : Bool} {scope : MbarScope},
      q < i → X.get (g, q) = some ⟨tag, .wait m p true acq scope⟩ →
      PTX.Flow.okPolls m ((X.tr g).take q) = n →
      ∃ idx r st, (X.objects m)[idx]? = some r ∧ r.id = .thread (g, q) ∧
        stateBefore (X.objects m) idx = some st ∧ n + 1 ≤ st.phase ∧ st.phase % 2 ≠ n % 2 := by
  let m := ready L (ctaOf L g) (indexSlot d.block)
  dsimp only
  intro n
  induction n with
  | zero =>
    intro q tag p acq scope hq hPoll hCount
    obtain ⟨idx, r, st, hi, hId, hState, _, _, _, _, hParity, hNe, _⟩ :=
      ready_poll_record hpre hX hs he hd hq hPoll
    rw [hCount] at hParity
    refine ⟨idx, r, st, hi, hId, hState, ?_, ?_⟩ <;> omega
  | succ n ih =>
    intro q tag p acq scope hq hPoll hCount
    obtain ⟨idx, r, st, hi, hId, hState, _, _, _, _, hParity, hNe, _⟩ :=
      ready_poll_record hpre hX hs he hd hq hPoll
    have hN : n + 1 ≤ PTX.Flow.okPolls m ((X.tr g).take q) := Nat.le_of_eq hCount.symm
    obtain ⟨q', tag', p', acq', scope', hq', hPoll', hCount'⟩ := PTX.MbarRing.Poll.exists_nth hN
    obtain ⟨idx', r', st', hi', hId', hState', hLower, hParity'⟩ :=
      ih (hq'.trans hq) hPoll' hCount'
    have hLt := (hX.object_thread_index_iff hi' hi hId' hId).2 hq'
    obtain ⟨st'', hState'', hMono⟩ := (X.objects_checked hX m).phase_mono
      (objects_single_lifetime hX m) hLt.le (List.getElem?_eq_some_iff.mp hi).1.le hState'
    rw [hState] at hState''
    obtain rfl := Option.some.inj hState''
    rw [hCount] at hParity
    refine ⟨idx, r, st, hi, hId, hState, ?_, ?_⟩ <;> omega

private theorem observed_ready_poll_record {g i q tag n : Nat} {d : Wg1Tma.D} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.tma d)))
    (hq : q < i)
    (hWait : X.get (g, q) = some ⟨tag, .wait (ready L (ctaOf L g) (indexSlot d.block))
      (n % 2) true true .cta⟩)
    (hCount : PTX.Flow.okPolls (ready L (ctaOf L g) (indexSlot d.block))
      ((X.tr g).take q) = n) :
    let m := ready L (ctaOf L g) (indexSlot d.block)
    ∃ idx r before phase,
      (X.objects m)[idx]? = some r ∧ r.id = .thread (g, q) ∧
      stateBefore (X.objects m) idx = some before ∧ before.expected = 32 ∧
      r.action = .pollParity (n % 2) true ∧ r.fault = none ∧ r.reply.waited = some true ∧
      observedAt (X.objects m) idx = some phase ∧
      before.phase = phase + 1 ∧ n ≤ phase ∧ phase % 2 = n % 2 := by
  let m := ready L (ctaOf L g) (indexSlot d.block)
  obtain ⟨idx, r, before, hi, hId, hBefore, hExp, hAct, hClean, hResponse,
    hParity, hNe, hCompleted⟩ :=
    ready_poll_record hpre hX hs he hd hq hWait
  obtain ⟨idx', r', st, hi', hId', hSt, hLower, _⟩ :=
    ready_wait_phase_lower hpre hX hs he hd n hq hWait hCount
  have hIdx := ObjectInit.checked_record_index_eq (X.objects_checked hX m) hi hi'
    (hId.trans hId'.symm)
  subst idx'
  rw [hi] at hi'
  obtain rfl := Option.some.inj hi'
  rw [hBefore] at hSt
  obtain rfl := Option.some.inj hSt
  have hPos : 0 < before.phase := by omega
  have hObs : observedAt (X.objects m) idx = some (before.phase - 1) := by
    change (X.objects m)[idx]? = some r at hi
    simp only [observedAt, hi, Option.bind_some, hCompleted, ite_eq_left hPos]
  exact ⟨idx, r, before, before.phase - 1, hi, hId, hBefore,
    hExp, hAct, hClean, hResponse, hObs, by omega, by omega, by omega⟩

variable {g i n : Nat}

/-- An earlier successful wait for this slot has an actual record and an observed phase. -/
theorem tma_ready_record_at_use {d : Wg1Tma.D} {e : Event} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound) (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.tma d)))
    (hUse : n + 1 ≤ PTX.Flow.okPolls (ready L (ctaOf L g) (indexSlot d.block)) ((X.tr g).take i)) :
    let m := ready L (ctaOf L g) (indexSlot d.block)
    ∃ q tag idx r before phase,
      q < i ∧ X.get (g, q) = some ⟨tag, .wait m (n % 2) true true .cta⟩ ∧
      PTX.Flow.okPolls m ((X.tr g).take q) = n ∧
      (X.objects m)[idx]? = some r ∧ r.id = .thread (g, q) ∧
      stateBefore (X.objects m) idx = some before ∧ before.expected = 32 ∧
      r.action = .pollParity (n % 2) true ∧ r.fault = none ∧ r.reply.waited = some true ∧
      observedAt (X.objects m) idx = some phase ∧
      before.phase = phase + 1 ∧ n ≤ phase ∧ phase % 2 = n % 2 := by
  let m := ready L (ctaOf L g) (indexSlot d.block)
  have hg := Frame.lt_of_get hX he
  let hSound := (hs g hg).machine
  obtain ⟨q, tag, p, acq, scope, hq, hPoll, hN⟩ := PTX.MbarRing.Poll.exists_nth hUse
  obtain ⟨_, _, _, _, rfl, rfl⟩ := coordinate_poll_at hpre hX hSound hq hd hPoll
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hParity, _, _⟩ :=
    ready_poll_record hpre hX hs he hd hq hPoll
  change p = PTX.Flow.okPolls m ((X.tr g).take q) % 2 at hParity
  rw [hN] at hParity
  subst p
  obtain ⟨idx, r, before, phase, hRec⟩ :=
    observed_ready_poll_record hpre hX hs he hd hq hPoll hN
  exact ⟨q, tag, idx, r, before, phase, hq, hPoll, hN, hRec⟩

/-- Each earlier use of a followed coordinate slot has a successful wait in the same
thread. The checked history supplies the actual record and the phase it acquired. -/
theorem coordinate_records_for_earlier_uses {d : Wg1Tma.D} {e : Event} {k : Fin 16} {j : Fin 4}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound) (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.tma d)))
    (hsite : d.site = .coord k j) (hUse : n ≤ d.block / 4) :
    let m := ready L (ctaOf L g) (indexSlot d.block)
    ∃ q tag idx r before phase,
      q < i ∧ X.get (g, q) = some ⟨tag, .wait m (n % 2) true true .cta⟩ ∧
      PTX.Flow.okPolls m ((X.tr g).take q) = n ∧
      (X.objects m)[idx]? = some r ∧ r.id = .thread (g, q) ∧
      stateBefore (X.objects m) idx = some before ∧ before.expected = 32 ∧
      r.action = .pollParity (n % 2) true ∧ r.fault = none ∧ r.reply.waited = some true ∧
      observedAt (X.objects m) idx = some phase ∧
      before.phase = phase + 1 ∧ n ≤ phase ∧ phase % 2 = n % 2 := by
  have hg := Frame.lt_of_get hX he
  have hCount := (TmaIndexTrace.composed_coord_counts hpre
    ((hs g hg).machine.produces (hX.thr g hg)) hd hsite).2
  apply tma_ready_record_at_use hpre hX hs he hd
  rw [show PTX.Flow.okPolls (ready L (ctaOf L g) (indexSlot d.block)) ((X.tr g).take i) =
      d.block / 4 + 1 from hCount]
  omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
