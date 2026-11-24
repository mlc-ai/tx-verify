-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.BiasCredits
public import Kernels.TmlFa4Fwd.Proof.Protocol.BiasGuardObservation
import Kernels.TmlFa4Fwd.Proof.MbarSafety
import Lemmas.Protocol.MbarRingRound
import Lemmas.Order.CausalThreadCount

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Bias
open PTX PTX.Flow PTX.AsyncCopy PTX.MBarrier Thread.Loader

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

private theorem biasReadyInitialized {cta : Nat} (stage : Fin 2) {r : Record Ref}
    (hr : r ∈ X.objects (biasReadyObject l cta stage)) :
    PairTmaRing.InitFirst X (biasReadyObject l cta stage) 1 := by
  fin_cases stage
  · exact (activeObjectHistory hp hX (30 : Fin 34) hr).1
  · exact (activeObjectHistory hp hX (31 : Fin 34) hr).1

private theorem biasUpdateShape {cta : Nat} (stage : Fin 2) {r : Record Ref}
    (hr : r ∈ X.objects (biasReadyObject l cta stage)) {units bytes : Nat}
    (ha : r.action = .arrive units bytes) :
    ∃ issue, r.id = .thread issue ∧
      X.Arrive issue (biasReadyObject l cta stage) 32768 1 true .cta ∧
      units = 1 ∧ bytes = 32768 := by
  cases biasReadyRecord hp hX stage hr with
  | init h => obtain ⟨_, h⟩ := h; rw [h] at ha; cases ha
  | poll h => obtain ⟨_, _, h⟩ := h; rw [h] at ha; cases ha
  | expect i hId hi hAct =>
    obtain ⟨rfl, rfl⟩ := Action.arrive.inj (ha.symm.trans hAct)
    exact ⟨i, hId, hi, rfl, rfl⟩
  | notify _ _ _ _ _ _ h => rw [h] at ha; cases ha

/-- The physical ready phase of an expectation never exceeds its local issuance ordinal,
even if the expectation faults. Every completed phase consumed one earlier expectation. -/
theorem biasExpectationPhaseLeOrdinal {cta i g j : Nat} (stage : Fin 2) {r : Record Ref}
    (hRecord : (X.objects (biasReadyObject l cta stage))[i]? = some r) (hId : r.id = .thread (g,j))
    (hIssue : X.Arrive (g,j) (biasReadyObject l cta stage) 32768 1 true .cta) {phase : Nat}
    (hPhase : phaseAt (X.objects (biasReadyObject l cta stage)) i = some phase) :
    phase ≤ arrivals (biasReadyObject l cta stage) ((X.tr g).take j) := by
  let loc := biasReadyObject l cta stage
  let log := X.objects loc
  have hInit := biasReadyInitialized hp hX stage (List.mem_of_getElem? hRecord)
  have hNo := objects_noInval hX.tma.2.2.1 (fun k _ => noMbarInval hX (i := k)) loc
  have hChecked := X.objects_checked hX loc
  have hLen := (List.getElem?_eq_some_iff.mp hRecord).1
  change phaseAt log i = some phase at hPhase
  cases hSt : stateBefore log i with
  | none => simp only [phaseAt, hSt, Option.map_none, reduceCtorEq] at hPhase
  | some st =>
    have hEq : st.phase = phase := by
      simpa only [phaseAt, hSt, Option.map_some, Option.some.injEq] using hPhase
    have hExp := PairTmaRing.expected_of_init hX hInit hNo hSt
    have hInc : incrementsBefore log i = 0 := by
      apply incrementsBefore_eq_zero log
      apply incrementsBefore_length_of
      intro q hq
      cases biasReadyRecord hp hX stage hq with
      | init h => obtain ⟨_, h⟩ := h; simp [h]
      | poll h => obtain ⟨_, _, h⟩ := h; simp [h]
      | expect _ _ _ h => simp [h]
      | notify _ _ _ _ _ _ h => simp [h]
    obtain ⟨hPending, hSum⟩ := (hChecked.accounted hNo hLen.le).2 st hSt
    rw [hExp, hInc] at hPending hSum
    rw [hEq] at hSum
    have hUnits (xs : List (Record Ref)) (hSub : ∀ q ∈ xs, q ∈ log) :
        arrivalUnits xs ≤ xs.countP (threadArrival g) := by
      induction xs with
      | nil => exact Nat.zero_le _
      | cons q tail ih =>
        have hTail := ih (fun f hf => hSub f (List.mem_cons_of_mem _ hf))
        cases hAct : q.action <;> try
          (simp only [arrivalUnits, hAct, List.countP_cons]; omega)
        case arrive units bytes =>
          obtain ⟨k, hK, hSource, rfl, _⟩ :=
            biasUpdateShape hp hX stage (hSub q List.mem_cons_self) hAct
          have hActor := PTX.Kernels.TmlFa4Fwd.Loader.biasExpectationSameIssuer hp hX
            hSource hIssue
          have hSelected : threadArrival g q = true :=
            threadArrival_iff.mpr ⟨objectThreadSelected_iff.mpr
              ⟨k.2, by rw [hK, ← hActor]⟩, _, _, hAct⟩
          cases hf : q.fault <;> simp_all [arrivalUnits] <;> omega
    have hU := hUnits (log.take i) (fun _ hq => List.mem_of_mem_take hq)
    change arrivalUnits (log.take i) ≤
      ((X.objects (biasReadyObject l cta stage)).take i).countP (threadArrival g) at hU
    rw [hX.object_thread_arrival_count_before hRecord hId] at hU
    change unitsBefore log i ≤ arrivals loc ((X.tr g).take j) at hU
    change unitsBefore log i + st.pending = 1 * (phase + 1) + 0 at hSum
    change phase ≤ arrivals loc ((X.tr g).take j)
    omega

/-- A successful ready observation names an actual expectation in the observed phase
whose loader ordinal is at least that phase. -/
theorem biasObservedExpectation {cta j phase : Nat} (stage : Fin 2) {poll : Record Ref}
    (hj : (X.objects (biasReadyObject l cta stage))[j]? = some poll)
    (hSuccess : poll.reply.waited = some true)
    (hPhase : observedAt (X.objects (biasReadyObject l cta stage)) j = some phase) :
    ∃ issue, X.Arrive issue (biasReadyObject l cta stage) 32768 1 true .cta ∧
      MbarObserved X (.thread issue) poll.id ∧
      phase ≤ arrivals (biasReadyObject l cta stage) ((X.tr issue.1).take issue.2) := by
  classical
  let loc := biasReadyObject l cta stage
  let log := X.objects loc
  obtain ⟨stop, _, hCount, _, _⟩ := biasReadyObservedCredits hp hX stage hj hSuccess hPhase
  have hPos : 0 < (pairTxPhaseRecords log stop phase (.arrive 1 32768)).card := by
    rw [hCount]
    decide
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hPos
  obtain ⟨_, hPh, r, hr, hf, ha⟩ := memPairTxPhaseRecords.mp hi
  obtain ⟨⟨g,k⟩, hId, hIssue, _, _⟩ := biasUpdateShape hp hX stage (List.mem_of_getElem? hr) ha
  have hNo := objects_noInval hX.tma.2.2.1 (fun i _ => noMbarInval hX (i := i)) loc
  have hObs := hX.observed_of_phase hNo hr hf (ha.symm ▸ trivial) hj hSuccess hPh hPhase
  rw [hId] at hObs
  exact ⟨(g,k), hIssue, hObs, biasExpectationPhaseLeOrdinal hp hX stage hr hId hIssue hPh⟩

end PTX.Kernels.TmlFa4Fwd.Protocol.Bias
