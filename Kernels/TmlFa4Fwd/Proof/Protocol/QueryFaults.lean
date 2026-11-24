-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.QueryCredits
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderQueryUniqueness
import Kernels.TmlFa4Fwd.Proof.Thread.QueryDrainRelease
import Lemmas.Protocol.MbarRingRound
import Lemmas.Order.DependencyWitness
import Kernels.TmlFa4Fwd.Proof.MbarSafety
import Lemmas.Protocol.MbarUnitTx
import Lemmas.Protocol.PairTmaRing.Faults

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Query
open PTX PTX.AsyncCopy PTX.MBarrier Thread.Loader Thread.Output

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

private theorem notificationUnique {cta : Nat} {stage : Fin 2} {r q : Record Ref} {a b : EvId}
    {plane : Fin 2} {s t : TensorCopy.Spec} (hR : r ∈ X.objects (queryObject l cta stage))
    (hQ : q ∈ X.objects (queryObject l cta stage)) (hRid : r.id = .async a (.notify .load))
    (hQid : q.id = .async b (.notify .load)) (hA : a.1 / l.block = cta) (hB : b.1 / l.block = cta)
    (hBoxA : QuerySubbox p l X a stage plane s) (hBoxB : QuerySubbox p l X b stage plane t) :
    r = q := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hR
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hQ
  have hId := querySubboxUnique hp hX (hA.trans hB.symm) hBoxA hBoxB
  have hIndex := ObjectInit.checked_record_index_eq (X.objects_checked hX _) hi hj
    (by rw [hRid, hQid, hId])
  exact Option.some.inj ((hIndex ▸ hi).symm.trans hj)

/-- The completed transaction credits of a query object are bounded by its two actual boxes. -/
private theorem completedQueryCount (cta : Nat) (stage : Fin 2) (j : Nat) :
    completedTxCount ((X.objects (queryObject l cta stage)).take j) ≤ 2 := by
  classical
  let log := X.objects (queryObject l cta stage)
  let entries := (log.take j).filter (fun r => match r.action, r.fault with
    | .completeTx _, none => true
    | _, _ => false)
  let comesFrom (r : Record Ref) (plane : Fin 2) : Prop :=
    ∃ issue s, r.id = .async issue (.notify .load) ∧ issue.1 / l.block = cta ∧
      QuerySubbox p l X issue stage plane s
  have hSource (r : Record Ref) (hr : r ∈ entries) : ∃ plane, comesFrom r plane := by
    obtain ⟨hTake, hCheck⟩ := List.mem_filter.mp hr
    have hShape := queryRecord hp hX stage (List.mem_of_mem_take hTake)
    cases hShape with
    | init ha => obtain ⟨_, ha⟩ := ha; simp [ha] at hCheck
    | poll ha => obtain ⟨_, _, ha⟩ := ha; simp [ha] at hCheck
    | expect _ _ _ ha => simp [ha] at hCheck
    | notify issue plane s hId hCta hBox _ =>
      exact ⟨plane, issue, s, hId, hCta, hBox⟩
  let planeOf (r : Record Ref) := if h : ∃ plane, comesFrom r plane then
    Classical.choose h else (0 : Fin 2)
  have hPlane (r : Record Ref) (hr : r ∈ entries) : comesFrom r (planeOf r) := by
    simp only [planeOf, dite_eq_left (hSource r hr)]
    exact Classical.choose_spec (hSource r hr)
  have hNodup : entries.Nodup := List.Nodup.of_map Record.id
    ((X.objects_checked hX (queryObject l cta stage)).1.sublist
      ((List.filter_sublist.trans (List.take_sublist j log)).map Record.id))
  have hMapped : (entries.map planeOf).Nodup := hNodup.map_on fun a ha b hb hEq => by
    obtain ⟨i, s, hId, hOwner, hBox⟩ := hPlane a ha
    obtain ⟨k, t, hId', hOwner', hBox'⟩ := hPlane b hb
    rw [hEq] at hBox
    exact notificationUnique hp hX (List.mem_of_mem_take (List.mem_filter.mp ha).1)
      (List.mem_of_mem_take (List.mem_filter.mp hb).1) hId hId' hOwner hOwner' hBox hBox'
  have hCard : (entries.map planeOf).toFinset.card ≤ 2 := by
    simpa using (Finset.card_le_univ (entries.map planeOf).toFinset)
  rw [List.toFinset_card_of_nodup hMapped, List.length_map] at hCard
  rw [completedTxCount, List.countP_eq_length_filter]
  exact hCard

private theorem noQueryIncr (cta : Nat) (stage : Fin 2) :
    incrementsBefore (X.objects (queryObject l cta stage))
      (X.objects (queryObject l cta stage)).length = 0 := by
  apply incrementsBefore_length_of
  intro r hr hIncr
  cases queryRecord hp hX stage hr with
  | init h => obtain ⟨_, h⟩ := h; rw [h] at hIncr; cases hIncr
  | poll h => obtain ⟨_, _, h⟩ := h; rw [h] at hIncr; cases hIncr
  | expect _ _ _ h | notify _ _ _ _ _ _ h => rw [h] at hIncr; cases hIncr

private theorem queryExpectedBytes (cta : Nat) (stage : Fin 2) (j : Nat) :
    expectedTxBytes ((X.objects (queryObject l cta stage)).take j) =
      32768 * unitsBefore (X.objects (queryObject l cta stage)) j := by
  apply expectedTxBytes_unit
  intro r hr _ c tx ha
  cases queryRecord hp hX stage (List.mem_of_mem_take hr) with
  | init h => obtain ⟨_, h⟩ := h; rw [h] at ha; cases ha
  | poll h => obtain ⟨_, _, h⟩ := h; rw [h] at ha; cases ha
  | expect _ _ _ h => exact Action.arrive.inj (ha.symm.trans h)
  | notify _ _ _ _ _ _ h => rw [h] at ha; cases ha

private theorem queryCompletedBytes (cta : Nat) (stage : Fin 2) (j : Nat) :
    completedTxBytes ((X.objects (queryObject l cta stage)).take j) =
      16384 * completedTxCount ((X.objects (queryObject l cta stage)).take j) := by
  apply completedTxBytes_eq_unit_mul_count
  intro r hr _ n ha
  cases queryRecord hp hX stage (List.mem_of_mem_take hr) with
  | init h => obtain ⟨_, h⟩ := h; rw [h] at ha; cases ha
  | poll h => obtain ⟨_, _, h⟩ := h; rw [h] at ha; cases ha
  | expect _ _ _ h => rw [h] at ha; cases ha
  | notify _ _ _ _ _ _ h => exact Action.completeTx.inj (ha.symm.trans h)

private theorem queryInitialized {cta : Nat} (stage : Fin 2) {record : Record Ref}
    (hr : record ∈ X.objects (queryObject l cta stage)) :
    PairTmaRing.InitFirst X (queryObject l cta stage) 1 := by
  fin_cases stage
  · exact (activeObjectHistory hp hX (0 : Fin 34) hr).1
  · exact (activeObjectHistory hp hX (1 : Fin 34) hr).1

/-- A query object's history has at most one completed phase and its transaction counter
remains in range even if a credit is recorded as a fault. -/
theorem queryHistoryRange {cta j : Nat} (stage : Fin 2) {record : Record Ref} {s : State}
    (hr : record ∈ X.objects (queryObject l cta stage))
    (hj : j ≤ (X.objects (queryObject l cta stage)).length)
    (hs : stateBefore (X.objects (queryObject l cta stage)) j = some s) :
    s.phase ≤ 1 ∧ -32768 ≤ s.tx ∧ s.tx ≤ 65536 := by
  let loc := queryObject l cta stage
  let log := X.objects loc
  change j ≤ log.length at hj
  have hInit := queryInitialized hp hX stage hr
  have hNoInval := objects_noInval hX.tma.2.2.1 (fun _ _ => noMbarInval hX) loc
  have hChecked := X.objects_checked hX loc
  have hExp j st (h : stateBefore log j = some st) :=
    PairTmaRing.expected_of_init hX hInit hNoInval h
  have hIncr j : incrementsBefore log j = 0 :=
    incrementsBefore_eq_zero log (noQueryIncr hp hX cta stage) j
  have hUnits {j st} (hj : j ≤ log.length) (h : stateBefore log j = some st) :
      st.phase ≤ unitsBefore log j ∧ unitsBefore log j ≤ st.phase + 1 := by
    obtain ⟨hPending, hAccount⟩ := (hChecked.accounted hNoInval hj).2 st h
    change st.pending ≤ st.expected + incrementsBefore log j at hPending
    change unitsBefore log j + st.pending =
      st.expected * (st.phase + 1) + incrementsBefore log j at hAccount
    rw [hExp j st h, hIncr j, Nat.add_zero] at hPending hAccount
    omega
  have hPhase : s.phase ≤ 1 := by
    by_contra! hLate
    obtain ⟨k, hk, before, after, hBefore, hP, hAfter, hP'⟩ :=
      hChecked.crossing hNoInval hj hs (c := s.phase - 1) (by omega)
    have hkL : k < log.length := by omega
    obtain ⟨r, hkGet⟩ : ∃ r, log[k]? = some r := ⟨_, List.getElem?_eq_getElem hkL⟩
    have hBalanced := hChecked.phase_advance_transaction_bytes hNoInval hkGet
      hBefore hAfter (by omega)
    change expectedTxBytes (log.take (k+1)) = completedTxBytes (log.take (k+1)) at hBalanced
    have hE := queryExpectedBytes hp hX cta stage (k+1)
    have hC := queryCompletedBytes hp hX cta stage (k+1)
    change expectedTxBytes (log.take (k+1)) = 32768 * unitsBefore log (k+1) at hE
    change completedTxBytes (log.take (k+1)) =
      16384 * completedTxCount (log.take (k+1)) at hC
    rw [hE, hC] at hBalanced
    have hMax := completedQueryCount hp hX cta stage (k+1)
    change completedTxCount (log.take (k+1)) ≤ 2 at hMax
    have hMin := (hUnits (show k+1 ≤ log.length by omega) hAfter).1
    omega
  have hSum := hChecked.tx_balance hNoInval hj hs
  have hE := queryExpectedBytes hp hX cta stage j
  have hC := queryCompletedBytes hp hX cta stage j
  have hMax := completedQueryCount hp hX cta stage j
  have hCount := (hUnits hj hs).2
  change s.tx = (expectedTxBytes (log.take j) : Int) - completedTxBytes (log.take j) at hSum
  change expectedTxBytes (log.take j) = 32768 * unitsBefore log j at hE
  change completedTxBytes (log.take j) =
    16384 * completedTxCount (log.take j) at hC
  change completedTxCount (log.take j) ≤ 2 at hMax
  rw [hE, hC] at hSum
  push_cast at hSum
  omega

/-- Query notification records are fault free in both stages. A query expectation can only
fault through an unobserved preceding phase or a duplicate arrival in the current phase. -/
theorem queryHistoryFaults {cta : Nat} (stage : Fin 2) {r : Record Ref}
    (hr : r ∈ X.objects (queryObject l cta stage)) :
    r.fault = none ∨
      r.action = .arrive 1 32768 ∧
        (r.fault = some .precedingPhaseNotObserved ∨ r.fault = some .arrivalUnderflow) := by
  let loc := queryObject l cta stage
  obtain ⟨_, hInit⟩ := actualObjectInitialized hp hX hr
  have hNo := objects_noInval hX.tma.2.2.1 (fun _ _ => noMbarInval hX) loc
  have hChecked := X.objects_checked hX loc
  have update {a : Action} (ha : r.action = a) (hn : ∀ n, a ≠ .init n) :
      ∃ st, RecordOk (some st) r ∧ -32768 ≤ st.tx ∧ st.tx ≤ 65536 := by
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hr
    obtain ⟨_, st, hState, _⟩ := PairTmaRing.state_of_init hX hInit hNo hi
      (by intro n; rw [ha]; exact hn n)
    have hRange := queryHistoryRange hp hX stage hr (List.getElem?_eq_some_iff.mp hi).1.le hState
    have hOk := hChecked.at hi
    rw [hState] at hOk
    exact ⟨st, hOk, hRange.2⟩
  cases queryRecord hp hX stage hr with
  | init ha => exact .inl (actualInitOrPollClean hp hX hr (.inl ha))
  | poll ha => exact .inl (actualInitOrPollClean hp hX hr (.inr ha))
  | expect _ _ _ ha =>
    obtain ⟨st, hOk, hLo, hHi⟩ := update ha (by simp)
    have hTx : validTx (st.tx + 32768) := by simp only [validTx, limit]; norm_num; omega
    rcases PairTmaRing.arrive_fault_cases hOk ha (by decide) (by decide) hTx with h | h | h
    · exact .inl h
    · exact .inr ⟨ha, .inl h⟩
    · exact .inr ⟨ha, .inr h⟩
  | notify _ _ _ _ _ _ ha =>
    obtain ⟨st, hOk, hLo, hHi⟩ := update ha (by simp)
    have hTx : validTx (st.tx - 16384) := by simp only [validTx, limit]; norm_num; omega
    exact .inl (hOk.complete_fault_none ha (by decide) hTx)

/-- A query object's first recorded expectation succeeds, even when the corresponding
notifications appear earlier in the object history. -/
theorem firstQueryExpectationClean {cta i : Nat} (stage : Fin 2) {r : Record Ref}
    (hr : (X.objects (queryObject l cta stage))[i]? = some r) (ha : r.action = .arrive 1 32768)
    (hFirst : ∀ j < i, ∀ q, (X.objects (queryObject l cta stage))[j]? = some q →
      q.action ≠ .arrive 1 32768) : r.fault = none := by
  let loc := queryObject l cta stage
  let log := X.objects loc
  have hInit := queryInitialized hp hX stage (List.mem_of_getElem? hr)
  have hNo := objects_noInval hX.tma.2.2.1 (fun _ _ => noMbarInval hX) loc
  have hChecked := X.objects_checked hX loc
  have hUnits : unitsBefore log i = 0 := by
    classical
    apply Nat.eq_zero_of_le_zero
    apply (arrivalUnits_le_countP (fun q => decide (q.action = .arrive 1 32768)) ?_).trans
    · apply le_of_eq
      apply List.countP_eq_zero.mpr
      intro q hq hAction
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hq
      have hLen := (List.getElem?_eq_some_iff.mp hj).1
      simp only [List.length_take] at hLen
      rw [List.getElem?_take_of_lt (by omega)] at hj
      exact hFirst j (by omega) q hj (of_decide_eq_true hAction)
    · intro q hq _ c tx hAction
      cases queryRecord hp hX stage (List.mem_of_mem_take hq) with
      | init h => obtain ⟨_, h⟩ := h; rw [h] at hAction; cases hAction
      | poll h => obtain ⟨_, _, h⟩ := h; rw [h] at hAction; cases hAction
      | expect _ _ _ h =>
        obtain ⟨rfl, _⟩ := Action.arrive.inj (hAction.symm.trans h)
        exact ⟨rfl, decide_eq_true h⟩
      | notify _ _ _ _ _ _ h => rw [h] at hAction; cases hAction
  have hOut := hChecked.arrive_fault_free hNo hr ha (s := 0) (fun st hs => by
    have hExpected := PairTmaRing.expected_of_init hX hInit hNo hs
    change unitsBefore log i < st.expected * (0+1)
    rw [hUnits, hExpected]
    decide) (by intro q hLo hHi; omega)
  rcases queryHistoryFaults hp hX stage (List.mem_of_getElem? hr) with hf | ⟨_, hf | hf⟩
  · exact hf
  · exact (hOut.2 hf).elim
  · exact (hOut.1 hf).elim

private theorem queryExpectationSource {cta : Nat} (stage : Fin 2) {r : Record Ref}
    (hr : r ∈ X.objects (queryObject l cta stage)) (ha : r.action = .arrive 1 32768) :
    ∃ i, r.id = .thread i ∧ X.Arrive i (queryObject l cta stage) 32768 1 true .cta := by
  cases queryRecord hp hX stage hr with
  | init h => obtain ⟨_, h⟩ := h; rw [h] at ha; cases ha
  | poll h => obtain ⟨_, _, h⟩ := h; rw [h] at ha; cases ha
  | expect i hId hCredit _ => exact ⟨i, hId, hCredit⟩
  | notify _ _ _ _ _ _ h => rw [h] at ha; cases ha

/-- The first query object's whole actual history is fault free. -/
theorem queryStageZeroHistoryClean {cta : Nat} {r : Record Ref}
    (hr : r ∈ X.objects (queryObject l cta 0)) :
    r.fault = none := by
  rcases queryHistoryFaults hp hX (0 : Fin 2) hr with h | ⟨ha, _⟩
  · exact h
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hr
  apply firstQueryExpectationClean hp hX (0 : Fin 2) hi ha
  intro j hj q hq hqa
  obtain ⟨issue, hId, hCredit⟩ := queryExpectationSource hp hX (0 : Fin 2) hr ha
  obtain ⟨other, hOtherId, hOtherCredit⟩ :=
    queryExpectationSource hp hX (0 : Fin 2) (List.mem_of_getElem? hq) hqa
  have hSame := queryStageZeroExpectationUnique hp hX hCredit hOtherCredit
  have hIndex := ObjectInit.checked_record_index_eq (X.objects_checked hX _) hi hq
    (by rw [hId, hOtherId, hSame])
  omega

private theorem queryPhaseOfCleanCredits {cta : Nat} (stage : Fin 2)
    (hClean : ∀ r ∈ X.objects (queryObject l cta stage), r.fault = none)
    {credit left right : Record Ref} (hCredit : credit ∈ X.objects (queryObject l cta stage))
    (hExpected : credit.action = .arrive 1 32768)
    (hLeft : left ∈ X.objects (queryObject l cta stage))
    (hRight : right ∈ X.objects (queryObject l cta stage)) (hDifferent : left ≠ right)
    (hLeftTx : left.action = .completeTx 16384) (hRightTx : right.action = .completeTx 16384) :
    let log := X.objects (queryObject l cta stage)
    ∃ s, stateBefore log log.length = some s ∧ s.phase = 1 := by
  classical
  let loc := queryObject l cta stage
  let log := X.objects loc
  have hLog := X.objects_checked hX loc
  have hNo := objects_noInval hX.tma.2.2.1 (fun _ _ => noMbarInval hX) loc
  have hFirst := queryInitialized hp hX stage hCredit
  obtain ⟨initial,hInitial,hInitAct,hInitClean,_⟩ := hFirst credit hCredit
  have hLength : 0 < log.length := (List.getElem?_eq_some_iff.mp hInitial).1
  obtain ⟨s,hState,hCount⟩ := ObjectInit.checked_expected_after_init hLog hNo
    hInitial hInitAct hInitClean hLength (Nat.le_refl _)
  have hPhase := (queryHistoryRange hp hX stage hCredit (Nat.le_refl _) hState).1
  refine ⟨s,hState,Nat.le_antisymm hPhase ?_⟩
  by_contra! hZero
  have hz : s.phase = 0 := by omega
  have hUnits : 1 ≤ unitsBefore log log.length := by
    unfold unitsBefore
    rw [List.take_length,arrivalUnits_eq_length]
    · have hc : credit ∈ log.filter countedArrive :=
        List.mem_filter.mpr
          ⟨hCredit,countedArrive_iff.mpr
            ⟨hClean credit hCredit,1,32768,hExpected⟩⟩
      exact List.length_pos_of_mem hc
    · intro r hr c tx _ ha
      cases queryRecord hp hX stage hr with
      | init h => obtain ⟨_, h⟩ := h; rw [h] at ha; cases ha
      | poll h => obtain ⟨_, _, h⟩ := h; rw [h] at ha; cases ha
      | expect _ _ _ h => exact (Action.arrive.inj (ha.symm.trans h)).1
      | notify _ _ _ _ _ _ h => rw [h] at ha; cases ha
  have hBefore := ((hLog.accounted hNo (Nat.le_refl _)).2 s hState).2
  change unitsBefore log log.length + s.pending = s.expected*(s.phase+1) +
    incrementsBefore log log.length at hBefore
  rw [hCount,hz,noQueryIncr hp hX cta stage] at hBefore
  have hOne : unitsBefore log log.length = 1 := by omega
  have hPending : s.pending = 0 := by omega
  let note (r : Record Ref) : Bool :=
    match r.action,r.fault with | .completeTx _,none => true | _,_ => false
  have hL : left ∈ log.filter note := List.mem_filter.mpr
    ⟨hLeft,by simp [note,hLeftTx,hClean left hLeft]⟩
  have hR : right ∈ log.filter note := List.mem_filter.mpr
    ⟨hRight,by simp [note,hRightTx,hClean right hRight]⟩
  have hSubset : ({left,right} : Finset (Record Ref)) ⊆ (log.filter note).toFinset := by
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl | hr
    · exact List.mem_toFinset.mpr hL
    · obtain rfl := Finset.mem_singleton.mp hr
      exact List.mem_toFinset.mpr hR
  have hLower := (Finset.card_le_card hSubset).trans (List.toFinset_card_le _)
  have hTwo : ({left,right} : Finset (Record Ref)).card = 2 := by simp [hDifferent]
  rw [hTwo,← List.countP_eq_length_filter] at hLower
  have hUpper := completedQueryCount hp hX cta stage log.length
  change completedTxCount (log.take log.length) ≤ 2 at hUpper
  rw [List.take_length] at hUpper
  have hNotes : completedTxCount log = 2 := Nat.le_antisymm hUpper hLower
  have hExpBytes := queryExpectedBytes hp hX cta stage log.length
  have hDoneBytes := queryCompletedBytes hp hX cta stage log.length
  have hBalance := hLog.tx_balance hNo (Nat.le_refl _) hState
  change s.tx = (expectedTxBytes (log.take log.length) : Int) -
    completedTxBytes (log.take log.length) at hBalance
  rw [hExpBytes,hDoneBytes,hOne,List.take_length,hNotes] at hBalance
  have hPos := stateBefore_pending_pos hLog hState (by omega : s.tx = 0)
  omega

/-- The first query phase completes after its expectation and its two distinct actual notes. -/
theorem queryStageZeroPhaseOfCredits {cta : Nat} {credit left right : Record Ref}
    (hCredit : credit ∈ X.objects (queryObject l cta 0))
    (hExpected : credit.action = .arrive 1 32768) (hLeft : left ∈ X.objects (queryObject l cta 0))
    (hRight : right ∈ X.objects (queryObject l cta 0)) (hDifferent : left ≠ right)
    (hLeftTx : left.action = .completeTx 16384) (hRightTx : right.action = .completeTx 16384) :
    let log := X.objects (queryObject l cta 0)
    ∃ s, stateBefore log log.length = some s ∧ s.phase = 1 :=
  queryPhaseOfCleanCredits hp hX 0 (fun _ => queryStageZeroHistoryClean hp hX)
    hCredit hExpected hLeft hRight hDifferent hLeftTx hRightTx

private theorem stageOneDrainRecordGate {cta k : Nat} {initial draining : EvId} {r : Record Ref}
    (hInitial : StageOneExpectation l X cta initial false)
    (hDraining : StageOneExpectation l X cta draining true)
    (hr : (X.objects (queryObject l cta 1))[k]? = some r) (hId : r.id = .thread draining)
    (hAction : r.action = .arrive 1 32768) :
    let log := X.objects (queryObject l cta 1)
    (∃ j poll st, j < k ∧ log[j]? = some poll ∧ poll.reply.waited = some true ∧
      stateBefore log j = some st ∧ st.phase = 1) ∧
    ∃ (i : Nat) (first : Record Ref),
      log[i]? = some first ∧ first.id = .thread initial ∧ first.fault = none := by
  let loc := queryObject l cta 1
  let log := X.objects loc
  have hChecked := X.objects_checked hX loc
  have hNo := objects_noInval hX.tma.2.2.1 (fun _ _ => noMbarInval hX) loc
  obtain ⟨emptyWait, e, he, hk, hResumes⟩ :=
    stageOneDrainingExpectationAfterEmptyWait hp hX hInitial hDraining
  have hOwner : cta = emptyWait.1 / l.block := by
    rw [hResumes.1.1]
    exact stageOneExpectationOwner hp hX hDraining
  rw [hOwner] at hk
  obtain ⟨acquire, f, hCta, hf, hfKind, hPath⟩ := secondQueryAcquireBeforeEmptyWait hp hX he hk
  have hLocal : acquire.1 / l.block = cta := hCta.trans hOwner.symm
  rw [← hCta] at hfKind
  obtain ⟨j, poll, hPoll, hPollId, hPollAct, _, hSuccess⟩ := queryPollRecord hp hX hf hfKind
  rw [hLocal] at hPoll
  have hOrder := hPath.tail (DepStep.of_resumes (L := l) hResumes)
  have hBefore : j < k := by
    rcases Nat.lt_trichotomy j k with hLt | hEq | hGt
    · exact hLt
    · rw [hEq, hr] at hPoll
      have hSame := Option.some.inj hPoll
      rw [← hSame, hAction] at hPollAct
      cases hPollAct
    · exact (MbarRing.Round.Slot.not_before_of_reach hX hOrder
        ⟨k, j, r, poll, hr, hId, hPoll, hPollId, hGt⟩).elim
  obtain ⟨st, q, hState, hStepAct, hParity, hSeen⟩ := hChecked.okPoll hPoll hSuccess
  have hQ := (Action.pollParity.inj (hStepAct.symm.trans hPollAct)).1
  subst q
  have hRange := queryHistoryRange hp hX (1 : Fin 2) (List.mem_of_getElem? hPoll)
    (List.getElem?_eq_some_iff.mp hPoll).1.le hState
  have hPhase : st.phase = 1 := by omega
  have hObserved : observedAt log j = some 0 := by
    change log[j]? = some poll at hPoll
    simp [observedAt, hPoll, hSeen, hPhase]
  have hAcquire : QueryAcquire l X acquire 1 := ⟨f, 0, hf, hfKind⟩
  have hObs : QueryAcquirePhase l X acquire 1 0 := by
    rw [QueryAcquirePhase, hLocal]
    exact ⟨j, poll, hPoll, hPollId, hObserved⟩
  obtain ⟨expected, _⟩ := hAcquire.hasTransactionPair hp hX hObs
  unfold QueryExpected at expected
  rw [hLocal] at expected
  obtain ⟨issue, i, first, hArrival, hRec, hRecId, hClean, hRecPhase⟩ := expected
  obtain ⟨tag, hTag⟩ := stageOneExpectationOfArrival hp hX hArrival
  have hEarlier : i < j := by
    by_contra! hLate
    obtain ⟨after, hAfter, hMono⟩ := hChecked.phase_mono hNo hLate
      (List.getElem?_eq_some_iff.mp hRec).1.le hState
    change phaseAt log i = some 0 at hRecPhase
    change stateBefore log i = some after at hAfter
    simp [phaseAt, hAfter] at hRecPhase
    omega
  refine ⟨⟨j, poll, st, hBefore, hPoll, hSuccess, hState, hPhase⟩, ?_⟩
  cases tag
  · have hi := stageOneExpectationUnique hp hX hTag hInitial
    exact ⟨i, first, hRec, hi ▸ hRecId, hClean⟩
  · have hi := stageOneExpectationUnique hp hX hTag hDraining
    have hIndex := ObjectInit.checked_record_index_eq hChecked hRec hr
      (by rw [hRecId, hId, hi])
    omega

/-- The second query object's entire history is clean, including the draining expectation
if the active path issued its initial expectation. -/
theorem queryStageOneHistoryClean {cta : Nat} {r : Record Ref}
    (hr : r ∈ X.objects (queryObject l cta 1)) :
    r.fault = none := by
  rcases queryHistoryFaults hp hX (1 : Fin 2) hr with hClean | ⟨ha, hFault⟩
  · exact hClean
  let loc := queryObject l cta 1
  let log := X.objects loc
  have hChecked := X.objects_checked hX loc
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hr
  classical
  by_cases hEarlier : ∃ j < i, ∃ q, log[j]? = some q ∧ q.action = .arrive 1 32768
  · obtain ⟨j, hj, earlier, hEarlier, hEarlierAction⟩ := hEarlier
    obtain ⟨issue, hId, hCredit⟩ := queryExpectationSource hp hX (1 : Fin 2) hr ha
    obtain ⟨other, hOtherId, hOtherCredit⟩ :=
      queryExpectationSource hp hX (1 : Fin 2) (List.mem_of_getElem? hEarlier) hEarlierAction
    obtain ⟨tag, hTag⟩ := stageOneExpectationOfArrival hp hX hCredit
    obtain ⟨otherTag, hOtherTag⟩ := stageOneExpectationOfArrival hp hX hOtherCredit
    have hDist : tag ≠ otherTag := by
      intro h
      subst otherTag
      have hIssue := stageOneExpectationUnique hp hX hTag hOtherTag
      have hIndex := ObjectInit.checked_record_index_eq hChecked hi hEarlier
        (by rw [hId, hOtherId, hIssue])
      omega
    cases tag
    · have hOther : otherTag = true := by cases otherTag <;> simp_all
      subst otherTag
      obtain ⟨_, k, first, hRecord, hFId, hFClean⟩ :=
        stageOneDrainRecordGate hp hX hTag hOtherTag hEarlier hOtherId hEarlierAction
      have hk := ObjectInit.checked_record_index_eq hChecked hi hRecord (hId.trans hFId.symm)
      rw [hk, hRecord] at hi
      exact Option.some.inj hi ▸ hFClean
    · have hOther : otherTag = false := by cases otherTag <;> simp_all
      subst otherTag
      obtain ⟨⟨pos, poll, st, hLt, hPoll, hSuccess, hState, hPhase⟩, _⟩ :=
        stageOneDrainRecordGate hp hX hOtherTag hTag hi hId ha
      have hNo := objects_noInval hX.tma.2.2.1 (fun _ _ => noMbarInval hX) loc
      let selected (r : Record Ref) := decide (r.action = .arrive 1 32768)
      have hTotal : unitsBefore log i ≤ 1 := by
        apply (arrivalUnits_le_countP selected ?_).trans
        · exact countP_take_le_card hChecked.1 selected {Ref.thread other} (i := i)
            (fun k hk entry hEntry hSelected => by
              have hAction : entry.action = .arrive 1 32768 := of_decide_eq_true hSelected
              obtain ⟨actual, hActual, hSource⟩ :=
                queryExpectationSource hp hX (1 : Fin 2) (List.mem_of_getElem? hEntry) hAction
              obtain ⟨label, hLabel⟩ := stageOneExpectationOfArrival hp hX hSource
              cases label
              · rw [hActual, stageOneExpectationUnique hp hX hLabel hOtherTag]
                exact Finset.mem_singleton_self _
              · have hSame := stageOneExpectationUnique hp hX hLabel hTag
                have hk' := ObjectInit.checked_record_index_eq hChecked hEntry hi
                  (by rw [hActual, hId, hSame])
                omega)
        · intro entry hMem _ count tx hEntry
          cases queryRecord hp hX (1 : Fin 2) (List.mem_of_mem_take hMem) with
          | init h => obtain ⟨_, h⟩ := h; rw [h] at hEntry; cases hEntry
          | poll h => obtain ⟨_, _, h⟩ := h; rw [h] at hEntry; cases hEntry
          | expect _ _ _ h =>
            exact ⟨(Action.arrive.inj (hEntry.symm.trans h)).1, decide_eq_true h⟩
          | notify _ _ _ _ _ _ h => rw [h] at hEntry; cases hEntry
      have hInit := queryInitialized hp hX (1 : Fin 2) hr
      have hOk := hChecked.arrive_fault_free hNo hi ha (s := 1)
        (fun state hs => by
          have hExpected := PairTmaRing.expected_of_init hX hInit hNo hs
          change unitsBefore log i < state.expected * (1 + 1)
          rw [hExpected]
          omega)
        (fun q hlo hhi => ⟨pos, poll, st, hLt, hPoll, hSuccess, hState, by omega⟩)
      exact hFault.elim (fun hf => (hOk.2 hf).elim) (fun hf => (hOk.1 hf).elim)
  · exact firstQueryExpectationClean hp hX (1 : Fin 2) hi ha
      (fun j hj q hRec hAction => hEarlier ⟨j, hj, q, hRec, hAction⟩)

/-- The initial second-query expectation and two notes establish its exact ready phase. -/
theorem queryStageOnePhaseOfCredits {cta : Nat} {credit left right : Record Ref}
    (hCredit : credit ∈ X.objects (queryObject l cta 1))
    (hExpected : credit.action = .arrive 1 32768) (hLeft : left ∈ X.objects (queryObject l cta 1))
    (hRight : right ∈ X.objects (queryObject l cta 1)) (hDifferent : left ≠ right)
    (hLeftTx : left.action = .completeTx 16384) (hRightTx : right.action = .completeTx 16384) :
    let log := X.objects (queryObject l cta 1)
    ∃ s, stateBefore log log.length = some s ∧ s.phase = 1 :=
  queryPhaseOfCleanCredits hp hX 1 (fun _ => queryStageOneHistoryClean hp hX)
    hCredit hExpected hLeft hRight hDifferent hLeftTx hRightTx

end PTX.Kernels.TmlFa4Fwd.Protocol.Query
