-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.JointProbabilityGate
import Kernels.TmlFa4Fwd.Proof.Protocol.SingleVisitProbabilityPhase

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Scores
open PTX PTX.MBarrier PTX.AsyncCopy Prologue Thread.Scores

/-- If both opening scores are the only generations, every softmax probability
credit belongs to its first generation. -/
theorem probabilityOrdinalZeroOfOnlyInitialScores {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {cta : Nat} (stage packet : Fin 2)
    (hInitial : ∀ {i spec rank}, ScoreCommit l X i cta stage spec rank →
      scoreCommitOrdinal l X cta stage i = 0)
    {i : EvId} (hw : warpIndex l i.1 < 8)
    (hCredit : ProbabilityCredit l X i cta stage packet) :
    probabilityOrdinal l X cta stage packet i = 0 := by
  obtain ⟨_,_,_,_,hRecord,_,hSuccess,_,hPhase,hBefore⟩ :=
    scoreObservedBeforeSoftmaxCredit hp hX stage packet hw hCredit
  obtain ⟨_,_,_,hScore,hGeneration,_⟩ :=
    scoreCommitOfObservation hp hX stage hRecord hSuccess hPhase
  have hZero := hInitial hScore
  omega

/-- A complete second joint phase would require a second credit from each
softmax lane, even in an execution with no returning MMA probability wait. -/
theorem jointPhaseAtMostOneOfOnlyInitialScores {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hGuard : CorrectionJointGuards l X) {cta : Nat} (stage : Fin 2)
    (hInitial : ∀ {i spec rank}, ScoreCommit l X i cta stage spec rank →
      scoreCommitOrdinal l X cta stage i = 0)
    {state : State} (hFinal : let log := X.objects (probabilityObject l cta stage 0)
      stateBefore log log.length = some state) :
    state.phase ≤ 1 := by
  let log := X.objects (probabilityObject l cta stage 0)
  change stateBefore log log.length = some state at hFinal
  by_contra! hLater
  have hNonempty : log ≠ [] := by
    intro h
    rw [h] at hFinal
    cases hFinal
  obtain ⟨sample,hSample⟩ := List.exists_mem_of_ne_nil log hNonempty
  let lane := cta*l.block+128*stage.val
  have hBlock : 0 < l.block := by rw [hp.block]; decide
  have hBound : 128*stage.val < l.block := by rw [hp.block]; have := stage.isLt; omega
  obtain ⟨hOwner,hLocal⟩ := NamedBar.lane_cta (c := cta) hBlock hBound
  have hRole : warpIndex l lane < 8 ∧ warpIndex l lane/4 = stage.val := by
    unfold warpIndex
    rw [show lane%l.block = 128*stage.val from hLocal]
    have := stage.isLt
    omega
  obtain ⟨_,_,credit,_,_,_,_,_,hCredit,hLane,hOrdinal⟩ :=
    jointPhaseProducerRecord hp hX hGuard stage (g := lane) (phase := 1)
      hOwner (.inl hRole) hSample le_rfl hFinal hLater
  have hWarp : warpIndex l credit.1 < 8 := hLane.symm ▸ hRole.1
  have hZero := probabilityOrdinalZeroOfOnlyInitialScores hp hX stage 0 hInitial hWarp hCredit
  omega


/-- Every tail contribution of a one-visit score history belongs to phase zero.
The tail object cannot complete a phase without any contributing records. -/
theorem tailPhaseAtMostOneOfOnlyInitialScores {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {cta : Nat} (stage : Fin 2)
    (hInitial : ∀ {i spec rank}, ScoreCommit l X i cta stage spec rank →
      scoreCommitOrdinal l X cta stage i = 0)
    {state : State} (hFinal : let log := X.objects (probabilityObject l cta stage 1)
      stateBefore log log.length = some state) :
    state.phase ≤ 1 := by
  classical
  let loc := probabilityObject l cta stage 1
  let log := X.objects loc
  change stateBefore log log.length = some state at hFinal
  by_contra! hLater
  have hNonempty : log ≠ [] := by
    intro h
    rw [h] at hFinal
    cases hFinal
  obtain ⟨sample,hSample⟩ := List.exists_mem_of_ne_nil log hNonempty
  have hNo := objects_noInval hX.tma.2.2.1 (fun _ _ => noMbarInval hX) loc
  have hInit := probabilityInitialized hp hX stage 1 hSample
  have hUnit {r : Record Ref} (hr : r ∈ log) (ha : CounterUpdate r.action) :
      r.action = .arrive 1 0 := by
    obtain ⟨_,_,_,_,hAction⟩ := probabilityUpdate hp hX stage 1 hr ha
    exact hAction
  have hIncr : incrementsBefore log log.length = 0 := by
    apply incrementsBefore_length_of
    intro r hr hi
    have h := hUnit hr (by rw [hi]; trivial)
    rw [hi] at h
    cases h
  have hCard := (X.objects_checked hX loc).card_unit_arrivals_phase hNo (n := 4) (q := 1)
    (fun _ _ _ _ hr _ ha =>
      (Action.arrive.inj (ha.symm.trans (hUnit (List.mem_of_getElem? hr)
        (by rw [ha]; trivial)))).1)
    (fun _ _ _ hs => by
      simpa [probabilityCredits] using PairTmaRing.expected_of_init hX hInit hNo hs)
    hIncr le_rfl hFinal hLater
  have hSome : ((Finset.range log.length).filter (UnitArrivalIn log 1)).Nonempty :=
    Finset.card_pos.mp (by rw [hCard]; decide)
  obtain ⟨k,hk⟩ := hSome
  obtain ⟨_,r,_,hr,hArrive,_,hAt⟩ := Finset.mem_filter.mp hk
  have hUpdate : CounterUpdate r.action := by rw [hArrive]; trivial
  obtain ⟨credit,hId,hCredit,_,_⟩ :=
    probabilityUpdate hp hX stage 1 (List.mem_of_getElem? hr) hUpdate
  have hWarp : warpIndex l credit.1 < 8 := by
    rcases (probabilityCreditRole hp hX stage 1 hCredit).2 with h | h
    · exact h.1
    · exact (of_decide_eq_true rfl : (1 : Fin 2).val ≠ 0) h.1 |>.elim
  have hZero := probabilityOrdinalZeroOfOnlyInitialScores hp hX stage 1 hInitial hWarp hCredit
  have hExact := (tailProbabilityCreditPhaseExact hp hX stage hr hUpdate hId).2
  rw [hZero,hAt] at hExact
  cases hExact

end PTX.Kernels.TmlFa4Fwd.Protocol.Scores
