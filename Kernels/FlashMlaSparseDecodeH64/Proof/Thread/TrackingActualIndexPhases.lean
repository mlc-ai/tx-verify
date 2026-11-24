-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingIndexActualArrival
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingReadyCount
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingCommitOrigins
import Lemmas.Protocol.MbarInit

@[expose] public section

/-! # Actual index-ring phase counts -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow PTX.AsyncCopy PTX.MBarrier Protocol Protocol.IndexRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- Every arrival record on an index object records a real unit release. -/
theorem actual_index_unit_arrive {m : Loc} {cta n tx : Nat} {slot : Fin 4} {r : Record Ref}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hm : m = ready L cta slot ∨ m = free L cta slot)
    (hr : r ∈ X.objects m) (hAct : r.action = .arrive n tx) :
    n = 1 ∧ tx = 0 ∧
      ∃ g i tag, r.id = .thread (g, i) ∧ X.get (g, i) = some ⟨tag, .arrive m 0 1 true .cta⟩ := by
  cases record_source hX.tma.2.2.1 hr with
  | @arrive g i tag bytes count release scope hid he ha =>
    have hCount : bytes = 0 ∧ count = 1 ∧ release = true ∧ scope = .cta := by
      rcases hm with rfl | rfl
      · exact (actual_index_ready_arrive hpre hX hs he rfl).2
      · exact (actual_index_free_arrive hpre hX hs he rfl).2.2
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hCount
    obtain ⟨rfl, rfl⟩ := Action.arrive.inj (hAct.symm.trans ha)
    exact ⟨rfl, rfl, g, i, tag, hid, he⟩
  | commit _ he hTarget _ =>
    rcases hm with rfl | rfl
    · exact (no_ready_commit hpre hX hs he rfl hTarget).elim
    · exact (no_free_commit hpre hX hs he rfl hTarget).elim
  | increment _ he _ | arriveOn _ he _ _ _ => exact (no_async_arrive hX he rfl).elim
  | init _ _ ha | inval _ _ ha | wait _ _ ha | tensor _ _ _ ha | bulk _ _ _ _ ha
  | clc _ _ _ _ ha =>
    rw [hAct] at ha
    cases ha

/-- The pending count of a completed index phase counts its distinct actual unit releases. -/
theorem actual_index_phase_units {m : Loc} {cta idx phase expected : Nat}
    {slot : Fin 4} {w : Record Ref} {before : State}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hm : m = ready L cta slot ∨ m = free L cta slot)
    (hw : (X.objects m)[idx]? = some w)
    (hBefore : stateBefore (X.objects m) idx = some before)
    (hPhase : before.phase = phase + 1) (hExpected : before.expected = expected) :
    ∃ positions : Finset Nat, positions.card = expected ∧ ∀ k ∈ positions,
      ∃ (r : Record Ref) (g i tag : Nat), k < idx ∧
        (X.objects m)[k]? = some r ∧ r.id = .thread (g, i) ∧
        r.fault = none ∧ phaseAt (X.objects m) k = some phase ∧
        X.get (g, i) = some ⟨tag, .arrive m 0 1 true .cta⟩ := by
  classical
  let log := X.objects m
  have hChecked := X.objects_checked hX m
  have hLife := objects_single_lifetime hX m
  have hIdxLen : idx < log.length := (List.getElem?_eq_some_iff.mp hw).1
  obtain ⟨finish, hFinish, hDone⟩ :=
    hChecked.crossing hLife hIdxLen.le hBefore (show phase < before.phase by omega)
  have hFinLen : finish < log.length := hFinish.trans hIdxLen
  obtain ⟨s, hSF, _, hCount⟩ := completed_phase_unit_count hX hFinLen hDone
  obtain ⟨t, ht, hPreserved⟩ :=
    ObjectInit.checked_expected_after hChecked hLife hFinish.le hIdxLen.le hSF
  have hEq : t = before := Option.some.inj (ht.symm.trans hBefore)
  have hTotal : phaseUnits log (finish + 1) phase = expected := by
    rw [hCount, ← hPreserved, hEq, hExpected]
  let matching (k : Nat) := ∃ r, log[k]? = some r ∧ phaseAt log k = some phase ∧
    r.fault = none ∧ r.action = .arrive 1 0
  let positions := (Finset.range (finish + 1)).filter matching
  have hUnits (k : Nat) (hk : k ∈ Finset.range (finish + 1)) :
      (if matching k then 1 else 0) =
        (if phaseAt log k = some phase then unitsAt log k else 0) := by
    have hLt := Finset.mem_range.mp hk
    have hLen : k < log.length := by omega
    let r := log[k]'hLen
    have hr : log[k]? = some r := List.getElem?_eq_getElem hLen
    by_cases hAt : phaseAt log k = some phase
    · by_cases hClean : r.fault = none
      · cases hAct : r.action
        case arrive n tx =>
          obtain ⟨rfl, rfl, _⟩ :=
            actual_index_unit_arrive hpre hX hs hm (List.mem_of_getElem? hr) hAct
          simp [matching, unitsAt, hr, hAt, hClean, hAct, Action.units]
        all_goals simp [matching, unitsAt, hr, hAt, hClean, hAct, Action.units]
      · simp [matching, unitsAt, hr, hAt, hClean]
    · simp [matching, hAt]
  refine ⟨positions, ?_, fun k hk => ?_⟩
  · unfold positions
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    exact (Finset.sum_congr rfl hUnits).trans hTotal
  · obtain ⟨hRange, r, hr, hAt, hClean, hAct⟩ := Finset.mem_filter.mp hk
    obtain ⟨_, _, g, i, tag, hId, hGet⟩ :=
      actual_index_unit_arrive hpre hX hs hm (List.mem_of_getElem? hr) hAct
    exact ⟨r, g, i, tag, (Finset.mem_range.mp hRange).trans_le hFinish, hr, hId, hClean, hAt, hGet⟩

/-- The ready records of the observed phase, classified using the actual write addresses. -/
theorem actual_ready_producers {g idx phase : Nat} {slot : Fin 4} {w : Record Ref}
    {before : State}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hw : (X.objects (ready L (ctaOf L g) slot))[idx]? = some w)
    (hBefore : stateBefore (X.objects (ready L (ctaOf L g) slot)) idx = some before)
    (hBeforePhase : before.phase = phase + 1) (hExpected : before.expected = 32) :
    let m := ready L (ctaOf L g) slot
    let log := X.objects m
    ∃ positions : Finset Nat, positions.card = 32 ∧ ∀ j ∈ positions,
      ∃ (r : Record Ref) (h t : Nat), j < idx ∧ log[j]? = some r ∧ r.id = .thread (h, t) ∧
        r.action = .arrive 1 0 ∧ r.fault = none ∧ phaseAt log j = some phase ∧
        AtIndex P L X (ctaOf L g) slot h t (fun s => ∃ extra, s = .ready extra) := by
  let m := ready L (ctaOf L g) slot
  obtain ⟨records, hCard, hEntries⟩ := actual_index_phase_units hpre hX hs
    (.inl rfl : m = ready L (ctaOf L g) slot ∨ m = free L (ctaOf L g) slot)
    hw hBefore hBeforePhase hExpected
  refine ⟨records, hCard, fun j hj => ?_⟩
  obtain ⟨r, h, t, tag, hLt, hr, hid, hClean, hPhase, hf⟩ := hEntries j hj
  have hAction := ((hX.tma.2.2.1 m).2.1 r (List.mem_of_getElem? hr)).1
  rw [hid] at hAction
  have ha : r.action = .arrive 1 0 :=
    Option.some.inj (by simpa [objectAction, hf] using hAction.symm)
  exact ⟨r, h, t, hLt, hr, hid, ha, hClean, hPhase, (actual_index_ready_arrive hpre hX hs hf rfl).1⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
