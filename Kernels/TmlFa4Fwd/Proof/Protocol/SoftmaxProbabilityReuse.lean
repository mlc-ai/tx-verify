-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.RecurringScoreGate
import Kernels.TmlFa4Fwd.Proof.MbarSafety
import Lemmas.Protocol.GatedFaults
import Lemmas.Protocol.MbarRingRound

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Scores
open PTX PTX.AsyncCopy PTX.MBarrier Thread.Scores
open PTX.Kernels.TmlFa4Fwd.Prologue (warpIndex)

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

/-- A successful score observation witnesses the actual MMA notification of that generation. -/
theorem scoreCommitOfObservation {cta i phase : Nat} (stage : Fin 2) {w : Record Ref}
    (hi : (X.objects (scoreReadyObject l cta stage))[i]? = some w)
    (hPoll : w.reply.waited = some true)
    (hPhase : observedAt (X.objects (scoreReadyObject l cta stage)) i = some phase) :
    ∃ e spec rank, ScoreCommit l X e cta stage spec rank ∧
      scoreCommitOrdinal l X cta stage e = phase ∧
      MbarObserved X (.async e (.tcNotify rank)) w.id := by
  classical
  let loc := scoreReadyObject l cta stage
  let log := X.objects loc
  have hChecked := X.objects_checked hX loc
  have hInit := scoreReadyInitialized hp hX stage (List.mem_of_getElem? hi)
  have hNo := objects_noInval hX.tma.2.2.1 (fun _ _ => noMbarInval hX) loc
  have hUnit {r : Record Ref} (hr : r ∈ log) (h : CounterUpdate r.action) :
      r.action = .arrive 1 0 := by
    obtain ⟨_,_,_,_,_,_,_,ha⟩ := scoreReadyUpdate hp hX stage hr h
    exact ha
  have hIncr : incrementsBefore log log.length = 0 := by
    apply incrementsBefore_length_of
    intro r hr hInc
    have h := hUnit hr (by rw [hInc]; trivial)
    rw [hInc] at h
    cases h
  obtain ⟨st,hState,hObserve⟩ := hChecked.observed_phase hi hPoll hPhase
  have hCard := hChecked.card_unit_arrivals_phase hNo (q := phase)
    (fun _ r count tx hr _ ha =>
      (Action.arrive.inj (ha.symm.trans (hUnit (List.mem_of_getElem? hr)
        (by rw [ha]; trivial)))).1)
    (fun _ _ _ h => PairTmaRing.expected_of_init hX hInit hNo h) hIncr
    (List.getElem?_eq_some_iff.mp hi).1.le hState (by omega)
  obtain ⟨_,hk⟩ := Finset.card_pos.mp (show 0 < _ from hCard.symm ▸ Nat.zero_lt_one)
  obtain ⟨_, r, tx, hr, ha, hClean, hPhaseR⟩ := Finset.mem_filter.mp hk
  have hUpdate : CounterUpdate r.action := by rw [ha]; trivial
  obtain ⟨e,s,rank,hId,hCommit,hTarget,_,_⟩ :=
    scoreReadyUpdate hp hX stage (List.mem_of_getElem? hr) hUpdate
  have hExact := (scoreNotificationPhaseExact hp hX stage hr hUpdate hId).2
  have hObserved := hX.observed_of_phase hNo hr hClean hUpdate hi hPoll hPhaseR hPhase
  rw [hId] at hObserved
  exact ⟨e,s,rank,⟨hCommit,hTarget⟩,Option.some.inj (hExact.symm.trans hPhaseR),hObserved⟩

/-- A positive softmax credit has a successful acquire on its own probability object
before the credit's record, with completed phase at least the preceding local generation. -/
theorem softmaxCreditProbabilityGuard {g : EvId} {cta atCredit : Nat} (stage packet : Fin 2)
    {r : Record Ref} (hr : (X.objects (probabilityObject l cta stage packet))[atCredit]? = some r)
    (hId : r.id = .thread g) (hCredit : ProbabilityCredit l X g cta stage packet)
    (hw : warpIndex l g.1 < 8) (hPos : 0 < probabilityOrdinal l X cta stage packet g) :
    let loc := probabilityObject l cta stage packet
    ∃ k w st, k < atCredit ∧ (X.objects loc)[k]? = some w ∧ w.reply.waited = some true ∧
      stateBefore (X.objects loc) k = some st ∧ probabilityOrdinal l X cta stage packet g ≤
        st.phase := by
  let loc := probabilityObject l cta stage packet
  let n := probabilityOrdinal l X cta stage packet g
  obtain ⟨j,i,phase,poll,hPoll,hPollId,hSuccess,hGuard,hObserve,hLower⟩ :=
    scoreObservedBeforeSoftmaxCredit hp hX stage packet hw hCredit
  obtain ⟨mma,spec,rank,hCommit,hOrdinal,hNotified⟩ :=
    scoreCommitOfObservation hp hX stage hPoll hSuccess hObserve
  have hN : n - 1 < scoreCommitOrdinal l X cta stage mma := by
    change n ≤ phase at hLower
    omega
  obtain ⟨a,k,past,w,hW,hWId,hOk,hWResume,hSeen,hBound,_,_⟩ :=
    probabilityObservedBeforeScoreOrdinal hp hX hCommit packet hN
  have hPresent : X.RefPresent (.async mma (.tcNotify rank)) := hNotified.1
  obtain ⟨_,hGet⟩ := hCommit.1
  have hIssue : DepStep l kernel X (.thread mma,false) (.async mma (.tcNotify rank),false) :=
    DepStep.issue ⟨_,hGet⟩ hPresent (by intro t h; cases h)
      (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)
  rw [hPollId] at hNotified
  have hChain := (((Relation.TransGen.single (DepStep.of_resumes l hWResume)).tail hIssue).tail
    (DepStep.of_witness l (Witness.of_mbarObserved hNotified))).tail (DepStep.of_resumes l hGuard)
  rw [← hWId, ← hId] at hChain
  have hNot := MbarRing.Round.Slot.not_before_of_reach (m := loc) hX hChain
  have hOrder : k < atCredit := by
    rcases Nat.lt_trichotomy k atCredit with h | rfl | h
    · exact h
    · obtain rfl := Option.some.inj (hW.symm.trans hr)
      have hSame := Ref.thread.inj (hWId.symm.trans hId)
      have hLane : mma.1 = g.1 := congrArg (a₁ := (mma.1,a)) (a₂ := g) Prod.fst hSame
      have hMma := (scoreCommitActor hp hX hCommit).2.1
      rw [hLane] at hMma
      omega
    · exact (hNot ⟨atCredit,k,r,w,hr,rfl,hW,rfl,h⟩).elim
  obtain ⟨st,hState,hPhase⟩ := (X.objects_checked hX loc).observed_phase hW hOk hSeen
  exact ⟨k,w,st,hOrder,hW,hOk,hState,by omega⟩

private theorem tailUpdateAligned {cta i c tx : Nat} (stage : Fin 2) {r : Record Ref}
    (hi : (X.objects (probabilityObject l cta stage 1))[i]? = some r) (ha : r.action = .arrive c tx)
    :
    r.fault = none ∧ phaseAt (X.objects (probabilityObject l cta stage 1)) i =
      some (tailLabel l X cta stage r.id).2 := by
  let loc := probabilityObject l cta stage 1
  let log := X.objects loc
  let labels := tailLabel l X cta stage
  have hInit := probabilityInitialized hp hX stage 1 (List.mem_of_getElem? hi)
  have hNo := objects_noInval hX.tma.2.2.1 (fun _ _ => noMbarInval hX) loc
  have unit {d : Record Ref} (hd : d ∈ log) (h : CounterUpdate d.action) :
      d.action = .arrive 1 0 := by
    obtain ⟨_,_,_,_,ha⟩ := probabilityUpdate hp hX stage 1 hd h
    exact ha
  have source {i c tx : Nat} {d : Record Ref} (hd : log[i]? = some d)
      (ha : d.action = .arrive c tx) :
      ∃ issue, d.id = .thread issue ∧ ProbabilityCredit l X issue cta stage 1 ∧
        (labels d.id).2 = probabilityOrdinal l X cta stage 1 issue := by
    obtain ⟨e,hId,hCredit,_,_⟩ :=
      probabilityUpdate hp hX stage 1 (List.mem_of_getElem? hd) (by rw [ha]; trivial)
    exact ⟨e,hId,hCredit,by rw [hId]; rfl⟩
  have hInc : incrementsBefore log log.length = 0 := by
    apply incrementsBefore_length_of
    intro d hd h
    have ha := unit hd (by rw [h]; trivial)
    rw [h] at ha
    cases ha
  have hCh := X.objects_checked hX loc
  apply hCh.gated_arrive hNo (Finset.univ : Finset (Fin 4)) labels _ _ _ _ _ hInc i r c tx hi ha
  · intro k s hk hs
    have hExpected := PairTmaRing.expected_of_init hX hInit hNo hs
    have hZero := MbarRing.tx_zero_of hX hNo
      (fun d hd c tx h => (Action.arrive.inj (h.symm.trans (unit hd (by rw [h]; trivial)))).2)
      (fun d hd n h => by
        have ha := unit hd (by rw [h]; trivial)
        rw [h] at ha
        cases ha) hk hs
    exact ⟨by simpa [probabilityCredits] using hExpected,hZero⟩
  · intro index d c tx hd hArrive
    obtain ⟨_,st,hState,_⟩ := PairTmaRing.state_of_init hX hInit hNo hd
      (by intro n; rw [hArrive]; simp)
    exact ⟨st,hState⟩
  · intro index d c tx hd hArrive
    have h := Action.arrive.inj
      (hArrive.symm.trans (unit (List.mem_of_getElem? hd) (by rw [hArrive]; trivial)))
    exact ⟨h.1,h.2,Finset.mem_univ _⟩
  · intro j k d f cd td cf tf hd hf had haf heq
    obtain ⟨ed,hId,hD,_⟩ := source hd had
    obtain ⟨ef,hIF,hF,_⟩ := source hf haf
    rw [hId,hIF] at heq
    obtain rfl := tailLabelInj hp hX hD hF heq
    exact ObjectInit.checked_record_index_eq hCh hd hf (hId.trans hIF.symm)
  · intro j d c tx hd hArrive hPos
    obtain ⟨e,hId,hCredit,hOrd⟩ := source hd hArrive
    rw [hOrd] at hPos ⊢
    have hw : warpIndex l e.1 < 8 := by
      rcases (probabilityCreditRole hp hX stage 1 hCredit).2 with h | h
      · exact h.1
      · have hn : (1 : Fin 2).val ≠ 0 := by decide
        exact (hn h.1).elim
    exact softmaxCreditProbabilityGuard hp hX stage 1 hd hId hCredit hw hPos

/-- Every actual tail probability notification is clean and has its local generation. -/
theorem tailProbabilityCreditPhaseExact {cta i : Nat} (stage : Fin 2) {e : EvId} {r : Record Ref}
    (hi : (X.objects (probabilityObject l cta stage 1))[i]? = some r) (ha : CounterUpdate r.action)
    (hId : r.id = .thread e) :
    r.fault = none ∧ phaseAt (X.objects (probabilityObject l cta stage 1)) i =
      some (probabilityOrdinal l X cta stage 1 e) := by
  obtain ⟨_,_,_,_,hAct⟩ := probabilityUpdate hp hX stage 1 (List.mem_of_getElem? hi) ha
  have h := tailUpdateAligned hp hX stage hi hAct
  rw [hId] at h
  exact h

/-- Both tail probability histories are fault-free in every consistent prefix. -/
theorem tailProbabilityHistoryNoFault {cta : Nat} (stage : Fin 2) {r : Record Ref}
    (hr : r ∈ X.objects (probabilityObject l cta stage 1)) : r.fault = none := by
  have hNo := objects_noInval hX.tma.2.2.1 (fun _ _ => noMbarInval hX)
    (probabilityObject l cta stage 1)
  cases ha : r.action with
  | init n => exact actualInitOrPollClean hp hX hr (.inl ⟨n,ha⟩)
  | pollParity q ok => exact actualInitOrPollClean hp hX hr (.inr ⟨q,ok,ha⟩)
  | inval => exact (hNo _ hr ha).elim
  | arrive | completeTx | increment =>
    have hUpdate : CounterUpdate r.action := by rw [ha]; trivial
    obtain ⟨_,hId,_,_,_⟩ := probabilityUpdate hp hX stage 1 hr hUpdate
    obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp hr
    exact (tailProbabilityCreditPhaseExact hp hX stage hi hUpdate hId).1

end PTX.Kernels.TmlFa4Fwd.Protocol.Scores
