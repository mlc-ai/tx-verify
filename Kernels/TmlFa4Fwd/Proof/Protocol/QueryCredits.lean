-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.QueryCredits
public import Kernels.TmlFa4Fwd.Proof.Protocol.QueryInput
import Lemmas.Protocol.PollPhase
import Lemmas.Protocol.PairTxCredits

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol
open PTX PTX.AsyncCopy PTX.MBarrier
open Thread.Output (queryObject)
open Thread.Loader (QuerySubbox QueryRecord queryRecord queryPollRecord)

noncomputable section

private theorem noInvalidation {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) (loc : Loc) :
    NoInval (X.objects loc) :=
  objects_noInval hX.tma.2.2.1 (fun i _ => noMbarInval hX (i := i)) loc

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

/-- An actual successful parity-zero query acquire observes an even completed phase. -/
theorem queryAcquirePhaseOfZero (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {wait : EvId} {stage : Fin 2}
    (h : ∃ e, X.get wait = some e ∧
      e.kind = .wait (queryObject l (wait.1 / l.block) stage) 0 true true .cta) :
    QueryAcquire l X wait stage ∧
      ∃ phase, phase % 2 = 0 ∧ QueryAcquirePhase l X wait stage phase := by
  obtain ⟨e, he, hk⟩ := h
  refine ⟨⟨e, 0, he, hk⟩, ?_⟩
  obtain ⟨j, r, hr, hid, ha, _, hWait⟩ := queryPollRecord hp hX he hk
  let loc := queryObject l (wait.1 / l.block) stage
  obtain ⟨s, n, _, ha', hParity, hCompleted⟩ := (X.objects_checked hX loc).okPoll hr hWait
  obtain rfl : n = 0 := (Action.pollParity.inj (ha'.symm.trans ha)).1
  have hPos : 0 < s.phase := by omega
  refine ⟨s.phase - 1, by omega, j, r, hr, hid, ?_⟩
  simp [observedAt, hr, hCompleted, hPos]

private theorem queryInitialHistory (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {cta : Nat} (stage : Fin 2) {r : Record Ref} (hr : r ∈ X.objects (queryObject l cta stage)) :
    PairTmaRing.InitFirst X (queryObject l cta stage) 1 := by
  fin_cases stage
  · exact (activeObjectHistory hp hX (0 : Fin 34) hr).1
  · exact (activeObjectHistory hp hX (1 : Fin 34) hr).1

/-- The observed generation has one live 32768-byte expectation and exactly two live
16384-byte tensor notifications in its completed prefix. -/
private theorem queryCompletedCounts (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {cta j phase : Nat} {stage : Fin 2} {poll : Record Ref}
    (hj : (X.objects (queryObject l cta stage))[j]? = some poll)
    (hSuccess : poll.reply.waited = some true)
    (hPhase : observedAt (X.objects (queryObject l cta stage)) j = some phase) :
    let log := X.objects (queryObject l cta stage)
    ∃ stop ≤ j, (pairTxPhaseRecords log stop phase (.arrive 1 32768)).card = 1 ∧
      (pairTxPhaseRecords log stop phase (.completeTx 16384)).card = 2 ∧
      ∀ i r, log[i]? = some r → phaseAt log i = some phase → i < stop := by
  let loc := queryObject l cta stage
  have hLog := X.objects_checked hX loc
  have hNo := noInvalidation hX loc
  have hInit := queryInitialHistory hp hX stage (List.mem_of_getElem? hj)
  apply completedPairTxCounts hLog hNo _ _ hj hSuccess hPhase
  · intro record hr
    cases queryRecord hp hX stage hr with
    | init h => exact .init h
    | poll h => exact .poll h
    | expect _ _ _ h => exact .expect h
    | notify _ _ _ _ _ _ h => exact .notify h
  · intro _ _ hs
    exact PairTmaRing.expected_of_init hX hInit hNo hs

/-- A successful query poll requires at least one actual tensor subbox in its CTA. -/
theorem successfulQueryPollHasSubbox (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {cta j : Nat} {stage : Fin 2} {poll : Record Ref}
    (hj : (X.objects (queryObject l cta stage))[j]? = some poll)
    (hAction : poll.action = .pollParity 0 true) (hSuccess : poll.reply.waited = some true) :
    ∃ issue plane spec, issue.1/l.block = cta ∧ QuerySubbox p l X issue stage plane spec := by
  let log := X.objects (queryObject l cta stage)
  obtain ⟨s,q,_,ha,hParity,hState⟩ :=
    (X.objects_checked hX (queryObject l cta stage)).okPoll hj hSuccess
  obtain rfl : q = 0 := (Action.pollParity.inj (ha.symm.trans hAction)).1
  have hPos : 0 < s.phase := by omega
  have hObs : observedAt log j = some (s.phase-1) := by
    simp [observedAt,log,hj,hState,hPos]
  obtain ⟨stop,_,_,hCount,_⟩ := queryCompletedCounts hp hX hj hSuccess hObs
  have hSome : 0 < (pairTxPhaseRecords log stop (s.phase-1) (.completeTx 16384)).card := by
    rw [hCount]
    decide
  obtain ⟨i,hi⟩ := Finset.card_pos.mp hSome
  obtain ⟨_,_,r,hr,_,hAct⟩ := memPairTxPhaseRecords.mp hi
  cases queryRecord hp hX stage (List.mem_of_getElem? hr) with
  | notify issue plane spec _ hc hb _ => exact ⟨issue,plane,spec,hc,hb⟩
  | init hi => obtain ⟨_, hi⟩ := hi; rw [hi] at hAct; cases hAct
  | poll hi => obtain ⟨_, _, hi⟩ := hi; rw [hi] at hAct; cases hAct
  | expect _ _ _ hi => rw [hi] at hAct; cases hAct

/-- The actual expect-transaction issue credited for one completed query phase. -/
def QueryExpected (l : Launch) (X : Execution) (cta : Nat) (stage : Fin 2) (phase : Nat) : Prop :=
  let loc := queryObject l cta stage
  ∃ issue index record, X.Arrive issue loc 32768 1 true .cta ∧
    (X.objects loc)[index]? = some record ∧ record.id = .thread issue ∧
    record.fault = none ∧ phaseAt (X.objects loc) index = some phase

/-- One of the actual clean query completion notifications observed by a successful acquire. -/
def QueryPhaseBox (p : Params) (l : Launch) (X : Execution) (wait : EvId)
    (stage : Fin 2) (phase : Nat) (tensor : EvId) : Prop :=
  tensor.1 / l.block = wait.1 / l.block ∧
    (∃ plane spec, QuerySubbox p l X tensor stage plane spec) ∧
    QueryNotifyPhase l X tensor stage phase ∧
    AsyncObserved X tensor (.notify .load) wait true .cta

/-- The observed query generation retires two distinct actual tensor subboxes and a
single live expectation. The two issue identities exhaust the phase's notifications. -/
theorem QueryAcquire.hasTransactionPair (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {wait : EvId} {stage : Fin 2} {phase : Nat}
    (hWait : QueryAcquire l X wait stage) (hPhase : QueryAcquirePhase l X wait stage phase) :
    QueryExpected l X (wait.1 / l.block) stage phase ∧
      ∃ a b, a ≠ b ∧ QueryPhaseBox p l X wait stage phase a ∧
        QueryPhaseBox p l X wait stage phase b ∧
        ∀ tensor, tensor.1 / l.block = wait.1 / l.block →
          QueryNotifyPhase l X tensor stage phase → tensor = a ∨ tensor = b := by
  let loc := queryObject l (wait.1 / l.block) stage
  let log := X.objects loc
  obtain ⟨e, parity, he, hk⟩ := hWait
  have hWait : QueryAcquire l X wait stage := ⟨e, parity, he, hk⟩
  obtain ⟨j, r, hj, hid, hObserved⟩ := hPhase
  have hPhase : QueryAcquirePhase l X wait stage phase := ⟨j, r, hj, hid, hObserved⟩
  obtain ⟨k, r', hk', hid', _, _, hSuccess⟩ := queryPollRecord hp hX he hk
  have hLog := X.objects_checked hX loc
  have hEq : k = j := ObjectInit.checked_record_index_eq hLog hk' hj (hid'.trans hid.symm)
  subst k
  obtain rfl := Option.some.inj (hk'.symm.trans hj)
  obtain ⟨stop, _, hCredit, hTensors, hBefore⟩ := queryCompletedCounts hp hX hj hSuccess hObserved
  obtain ⟨credit, hCredit⟩ := Finset.card_eq_one.mp hCredit
  have hCreditMem : credit ∈ pairTxPhaseRecords log stop phase (.arrive 1 32768) := by
    rw [hCredit]
    exact Finset.mem_singleton_self _
  obtain ⟨_, hCreditPhase, rec, hRec, hClean, hAct⟩ := memPairTxPhaseRecords.mp hCreditMem
  have hExpected : QueryExpected l X (wait.1 / l.block) stage phase := by
    cases queryRecord hp hX stage (List.mem_of_getElem? hRec) with
    | expect issue hId hCredit _ =>
      exact ⟨issue, credit, rec, hCredit, hRec, hId, hClean, hCreditPhase⟩
    | init hi => obtain ⟨_, hi⟩ := hi; rw [hi] at hAct; cases hAct
    | poll hi => obtain ⟨_, _, hi⟩ := hi; rw [hi] at hAct; cases hAct
    | notify _ _ _ _ _ _ hi => rw [hi] at hAct; cases hAct
  have box {n : Nat} (hn : n ∈ pairTxPhaseRecords log stop phase (.completeTx 16384)) :
      ∃ i rec, log[n]? = some rec ∧ rec.id = .async i (.notify .load) ∧
        QueryPhaseBox p l X wait stage phase i := by
    obtain ⟨_, hNPhase, rec, hRec, hClean, hAct⟩ := memPairTxPhaseRecords.mp hn
    cases queryRecord hp hX stage (List.mem_of_getElem? hRec) with
    | notify i plane spec hId hCta hBox _ =>
      have hNotify : QueryNotifyPhase l X i stage phase := by
        unfold QueryNotifyPhase
        rw [hCta]
        exact ⟨n, rec, hRec, hId, hClean, hNPhase⟩
      exact ⟨i, rec, hRec, hId, hCta, ⟨plane, spec, hBox⟩, hNotify,
        hWait.observesTensor hp hX hCta hPhase hNotify⟩
    | init hi => obtain ⟨_, hi⟩ := hi; rw [hi] at hAct; cases hAct
    | poll hi => obtain ⟨_, _, hi⟩ := hi; rw [hi] at hAct; cases hAct
    | expect _ _ _ hi => rw [hi] at hAct; cases hAct
  obtain ⟨u, v, huv, hPair⟩ := Finset.card_eq_two.mp hTensors
  have huMem : u ∈ pairTxPhaseRecords log stop phase (.completeTx 16384) := by
    rw [hPair]
    exact Finset.mem_insert_self _ _
  have hvMem : v ∈ pairTxPhaseRecords log stop phase (.completeTx 16384) := by
    rw [hPair]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  obtain ⟨a, ra, hu, hA, hABox⟩ := box huMem
  obtain ⟨b, rb, hv, hB, hBBox⟩ := box hvMem
  refine ⟨hExpected, a, b, ?_, hABox, hBBox, ?_⟩
  · intro hab
    rw [hab] at hA
    exact huv (ObjectInit.checked_record_index_eq hLog hu hv (hA.trans hB.symm))
  · intro tensor hCta hNotify
    unfold QueryNotifyPhase at hNotify
    rw [hCta] at hNotify
    obtain ⟨n, rec, hRec, hId, hClean, hPhaseN⟩ := hNotify
    have hAct : rec.action = .completeTx 16384 := by
      have hMem := List.mem_of_getElem? hRec
      have hSource := record_source hX.tma.2.2.1 hMem
      have hAction : ∃ n, rec.action = .completeTx n := by
        cases hSource <;> first
          | exact ⟨_, ‹rec.action = .completeTx _›⟩
          | grind
      obtain ⟨n, hn⟩ := hAction
      exact hn.trans (congrArg Action.completeTx (completedInputBytes hp hX hMem hn))
    have hN : n ∈ pairTxPhaseRecords log stop phase (.completeTx 16384) :=
      memPairTxPhaseRecords.mpr ⟨hBefore n rec hRec hPhaseN, hPhaseN, rec, hRec, hClean, hAct⟩
    rw [hPair] at hN
    simp only [Finset.mem_insert, Finset.mem_singleton] at hN
    rcases hN with rfl | rfl
    · obtain rfl := Option.some.inj (hRec.symm.trans hu)
      exact .inl (Ref.async.inj (hId.symm.trans hA)).1
    · obtain rfl := Option.some.inj (hRec.symm.trans hv)
      exact .inr (Ref.async.inj (hId.symm.trans hB)).1

end
end PTX.Kernels.TmlFa4Fwd.Protocol
