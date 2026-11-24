-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.SoftmaxProbabilityReuse
public import Kernels.TmlFa4Fwd.Proof.SoftmaxSingleVisitScoreOrdinal
import Kernels.TmlFa4Fwd.Proof.MbarSafety

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Scores
open PTX PTX.Proof PTX.AsyncCopy PTX.MBarrier PTX.MbarRing Prologue Epilogue Thread.Scores

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hDone : Complete l X)
    (hFrame : OutputFootprint p X) {batch cta : Nat} (hb : batch < p.batch)
    (hLo : tilePrefix p batch * p.heads ≤ cta) (hHi : cta < tilePrefix p (batch+1) * p.heads)
    (hTrip : Mma.trips p batch (assignedCoordinates p batch cta).1 = 1)
include hp hX hDone hFrame hb hLo hHi hTrip

/-- A softmax producer cannot publish a second probability packet in a one-visit CTA. -/
theorem singleVisitSoftmaxCreditOrdinalZero {i : EvId} (stage packet : Fin 2)
    (hw : warpIndex l i.1 < 8) (hCredit : ProbabilityCredit l X i cta stage packet) :
    probabilityOrdinal l X cta stage packet i = 0 := by
  obtain ⟨_,_,observed,_,hRecord,_,hSuccess,_,hPhase,hBefore⟩ :=
    scoreObservedBeforeSoftmaxCredit hp hX stage packet hw hCredit
  obtain ⟨_,_,_,hScore,hGeneration,_⟩ :=
    scoreCommitOfObservation hp hX stage hRecord hSuccess hPhase
  have hZero := Softmax.singleVisitScoreCommitOrdinalZero hp hX hDone hFrame hb hLo hHi hTrip
    hScore
  omega

/-- In a one-visit CTA, every actual elected tail-packet arrival belongs to phase zero. -/
theorem singleVisitTailCreditPhaseZero (stage : Fin 2) {k : Nat} {r : Record AsyncCopy.Ref}
    (hRecord : (X.objects (probabilityObject l cta stage 1))[k]? = some r)
    (hUpdate : CounterUpdate r.action) :
    r.fault = none ∧ phaseAt (X.objects (probabilityObject l cta stage 1)) k = some 0 := by
  obtain ⟨i,hId,hCredit,_,_⟩ := probabilityUpdate hp hX stage 1
    (List.mem_of_getElem? hRecord) hUpdate
  have hRole : warpIndex l i.1 < 8 := by
    rcases (probabilityCreditRole hp hX stage 1 hCredit).2 with h | h
    · exact h.1
    · have hn : (1 : Fin 2).val ≠ 0 := by decide
      exact (hn h.1).elim
  have hZero := singleVisitSoftmaxCreditOrdinalZero hp hX hDone hFrame
    hb hLo hHi hTrip stage 1 hRole hCredit
  simpa only [hZero] using tailProbabilityCreditPhaseExact hp hX stage hRecord hUpdate hId

/-- A successful parity-zero wait on a single-visit tail packet observes its initial phase. -/
theorem singleVisitTailObservedPhaseZero (stage : Fin 2) {k : Nat} {r : Record AsyncCopy.Ref}
    (hRecord : (X.objects (probabilityObject l cta stage 1))[k]? = some r)
    (hAction : r.action = .pollParity 0 true) (hSuccess : r.reply.waited = some true) :
    observedAt (X.objects (probabilityObject l cta stage 1)) k = some 0 := by
  classical
  let loc := probabilityObject l cta stage 1
  let log := X.objects loc
  have hChecked := X.objects_checked hX loc
  have hInit := probabilityInitialized hp hX stage 1 (List.mem_of_getElem? hRecord)
  have hNo := objects_noInval hX.tma.2.2.1 (fun _ _ => noMbarInval hX) loc
  have hUnit {r : Record AsyncCopy.Ref} (hr : r ∈ log) (hu : CounterUpdate r.action) :
      r.action = .arrive 1 0 := by
    obtain ⟨_,_,_,_,ha⟩ := probabilityUpdate hp hX stage 1 hr hu
    exact ha
  have hIncr : incrementsBefore log log.length = 0 := by
    apply incrementsBefore_length_of
    intro r hr hInc
    have h := hUnit hr (by rw [hInc]; trivial)
    rw [hInc] at h
    cases h
  obtain ⟨st,parity,hState,hAct,hOpposite,hReply⟩ := hChecked.okPoll hRecord hSuccess
  have hParity : parity = 0 := (Action.pollParity.inj (hAct.symm.trans hAction)).1
  have hPositive : 0 < st.phase := by rw [hParity] at hOpposite; omega
  have hObserve : observedAt log k = some (st.phase-1) := by
    change (log[k]?).bind (·.reply.completed) = some (st.phase-1)
    rw [hRecord, Option.bind_some, hReply, ite_eq_left hPositive]
  have hCard := hChecked.card_unit_arrivals_phase hNo (q := st.phase-1)
    (fun _ rec count tx hr _ ha =>
      (Action.arrive.inj (ha.symm.trans (hUnit (List.mem_of_getElem? hr)
        (by rw [ha]; trivial)))).1)
    (fun _ _ _ h => PairTmaRing.expected_of_init hX hInit hNo h) hIncr
    (List.getElem?_eq_some_iff.mp hRecord).1.le hState (by omega)
  have hCount : 0 < probabilityCredits 1 := by decide
  obtain ⟨_,hk⟩ := Finset.card_pos.mp (show 0 < _ from hCard.symm ▸ hCount)
  obtain ⟨_,credit,count,hCredit,hArrive,_,hPhase⟩ := Finset.mem_filter.mp hk
  have hUpdate : CounterUpdate credit.action := by rw [hArrive]; trivial
  have hZero := (singleVisitTailCreditPhaseZero hp hX hDone hFrame hb hLo hHi hTrip stage
    hCredit hUpdate).2
  rw [hZero] at hPhase
  exact hPhase ▸ hObserve

end PTX.Kernels.TmlFa4Fwd.Protocol.Scores
