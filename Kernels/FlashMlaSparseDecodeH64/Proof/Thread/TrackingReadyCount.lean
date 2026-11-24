-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingReadyPhase
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingCoordinateWait
import Lemmas.Protocol.MbarInit

@[expose] public section

/-! # The actual arrival count of a completed ready phase -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow PTX.AsyncCopy PTX.MBarrier
open Protocol Protocol.IndexRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private theorem no_increment (hX : Consistent L kernel Assumptions.all mem0 X)
    {m : Loc} {r : Record Ref} (hr : r ∈ X.objects m) : r.action ≠ .increment := by
  intro hk
  cases record_source hX.tma.2.2.1 hr with
  | increment _ he _ => exact (no_async_arrive hX he rfl).elim
  | init _ _ ha | inval _ _ ha | wait _ _ ha | arrive _ _ ha | tensor _ _ _ ha
  | commit _ _ _ ha | bulk _ _ _ _ ha | arriveOn _ _ _ _ ha | clc _ _ _ _ ha =>
    rw [hk] at ha
    cases ha

/-- A completed phase of a live mbarrier in this kernel consumes exactly the object's actual
expected arrival count. The check allows fault records and transaction completions. -/
theorem completed_phase_unit_count (hX : Consistent L kernel Assumptions.all mem0 X)
    {m : Loc} {q phase : Nat}
    (hq : q < (X.objects m).length) (hcomp : Completes (X.objects m) q phase) :
    ∃ t, stateBefore (X.objects m) q = some t ∧ t.phase = phase ∧
      phaseUnits (X.objects m) (q + 1) phase = t.expected := by
  let log := X.objects m
  have hChecked := X.objects_checked hX m
  have hNI := objects_single_lifetime hX m
  obtain ⟨s, t, hs, hc, ht, htPhase⟩ := hcomp
  let r := log[q]'hq
  have hr : log[q]? = some r := List.getElem?_eq_getElem hq
  have hok := hChecked.at hr
  rw [hs] at hok
  rw [stateBefore_succ hr] at ht
  have hpe := hChecked.pending_eq hNI hq.le hs
  rw [hc, phaseIncrements_eq_zero (fun _ hu => no_increment hX hu)] at hpe
  change stateBefore log q = some s at hs
  change s.pending + phaseUnits log q phase = s.expected + 0 at hpe
  have hpq : phaseAt log q = some phase := by
    unfold phaseAt
    rw [hs, Option.map_some, hc]
  refine ⟨s, hs, hc, ?_⟩
  unfold RecordOk at hok
  split at hok
  · rename_i rep hp
    rw [hok.1] at ht
    obtain ⟨t', hSame, _, hcase⟩ := perform_some_pending hp (hNI r (List.mem_of_getElem? hr))
    rw [hSame] at ht
    obtain rfl := Option.some.inj ht
    rcases hcase with ⟨hSamePhase, _⟩ | ⟨_, _, hUnits, _⟩
    · omega
    · have hZero : r.action.increments = 0 := by
        cases hAct : r.action <;> simp [Action.increments]
        exact (no_increment hX (List.mem_of_getElem? hr) hAct).elim
      have hSum : phaseUnits log (q + 1) phase =
          phaseUnits log q phase + r.action.units := by
        simp [phaseUnits, Finset.sum_range_succ, unitsAt, hr, hpq, hok.2]
      rw [hZero] at hUnits
      rw [hSum]
      omega
  · rw [hok.1] at ht
    obtain rfl := Option.some.inj ht
    omega

/-- The completed ready phase consists of 32 distinct successful release records, each
from a followed index producer of the CTA. The conclusion counts records, not producer lanes. -/
theorem observed_ready_producers {g i q tag idx phase parity : Nat} {e : Event}
    {slot : Fin 4} {w : Record Ref} {before : State}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hRead : X.get (g, i) = some e) (hq : q < i)
    (hPrior : ∀ p, baseCausality L X p (g, i) → ¬ Dismisses P L X p)
    (hWait : X.get (g, q) = some ⟨tag, .wait (ready L (ctaOf L g) slot) parity true true .cta⟩)
    (hwId : w.id = .thread (g, q)) (hwClean : w.fault = none)
    (hwReply : w.reply.waited = some true)
    (hw : (X.objects (ready L (ctaOf L g) slot))[idx]? = some w)
    (hobs : observedAt (X.objects (ready L (ctaOf L g) slot)) idx = some phase)
    (hBefore : stateBefore (X.objects (ready L (ctaOf L g) slot)) idx = some before)
    (hBeforePhase : before.phase = phase + 1) (hExpected : before.expected = 32) :
    let log := X.objects (ready L (ctaOf L g) slot)
    ∃ positions : Finset Nat, positions.card = 32 ∧ ∀ t ∈ positions,
      ∃ (r : Record Ref) (h j : Nat), t < idx ∧ log[t]? = some r ∧ r.id = .thread (h, j) ∧
        r.action = .arrive 1 0 ∧ r.fault = none ∧ phaseAt log t = some phase ∧
        AtIndex P L X (ctaOf L g) slot h j (fun s => ∃ extra, s = .ready extra) := by
  classical
  let m := ready L (ctaOf L g) slot
  let log := X.objects m
  have hChecked := X.objects_checked hX m
  have hNI := objects_single_lifetime hX m
  have hIdxLen : idx < log.length := (List.getElem?_eq_some_iff.mp hw).1
  obtain ⟨finish, hLt, hFinish⟩ := hChecked.crossing hNI hIdxLen.le hBefore
    (show phase < before.phase by omega)
  have hFinLen : finish < log.length := hLt.trans hIdxLen
  obtain ⟨s, hFinishBefore, _, hCount⟩ := completed_phase_unit_count hX hFinLen hFinish
  obtain ⟨t, ht, hPreserved⟩ :=
    ObjectInit.checked_expected_after hChecked hNI hLt.le hIdxLen.le hFinishBefore
  have ht' : t = before := Option.some.inj (ht.symm.trans hBefore)
  change phaseUnits log (finish + 1) phase = s.expected at hCount
  have hCount32 : phaseUnits log (finish + 1) phase = 32 := by
    rw [hCount, ← hPreserved, ht', hExpected]
  let matching (t : Nat) := ∃ r, log[t]? = some r ∧ phaseAt log t = some phase ∧
    r.fault = none ∧ r.action = .arrive 1 0
  let positions := (Finset.range (finish + 1)).filter matching
  have hUnits (t : Nat) (ht : t ∈ Finset.range (finish + 1)) :
      (if matching t then 1 else 0) =
        (if phaseAt log t = some phase then unitsAt log t else 0) := by
    have hT := Finset.mem_range.mp ht
    have hTLen : t < log.length := by omega
    let r := log[t]'hTLen
    have hr : log[t]? = some r := List.getElem?_eq_getElem hTLen
    by_cases hPhase : phaseAt log t = some phase
    · by_cases hClean : r.fault = none
      · cases hAct : r.action
        case arrive n tx =>
          obtain ⟨_, _, _, _, hN, hTx⟩ := ready_phase_arrive hpre hX hs hRead hq hPrior hWait
            hwId hwClean hwReply (by omega : t < idx) hr hw hPhase hobs hClean hAct
          simp [matching, unitsAt, hr, hPhase, hClean, hAct, hN, hTx, Action.units]
        all_goals simp [matching, unitsAt, hr, hPhase, hClean, hAct, Action.units]
      · simp [matching, unitsAt, hr, hPhase, hClean]
    · simp [matching, hPhase]
  have hCard : positions.card = 32 := by
    unfold positions
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    exact (Finset.sum_congr rfl hUnits).trans hCount32
  refine ⟨positions, hCard, fun t ht => ?_⟩
  obtain ⟨hRange, r, hr, hPhase, hClean, hAct⟩ := Finset.mem_filter.mp ht
  have hT := Finset.mem_range.mp hRange
  have hEarlier : t < idx := by omega
  obtain ⟨h, j, hId, hState, _, _⟩ := ready_phase_arrive hpre hX hs hRead hq hPrior hWait
    hwId hwClean hwReply hEarlier hr hw hPhase hobs hClean hAct
  exact ⟨r, h, j, hEarlier, hr, hId, hAct, hClean, hPhase, hState⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
