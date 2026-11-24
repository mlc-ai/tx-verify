-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaOperandReady
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaSharedFootprint
public import Kernels.TmlFa4Fwd.Proof.MmaRecurringKeyPack
import Kernels.TmlFa4Fwd.Proof.Thread.MmaIssueElection

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Mma
open PTX PTX.Kernels.TmlFa4Fwd.Mma

private theorem otherReadyGate :
    ∀ gate : Fin 4, (2 : Fin 4) ≠ gate →
      2145 ≤ readyHead gate ∧ readyHead gate < 2768 ∧
      readyHead gate ≠ (slotWait 2).pc + 1 ∧
      ¬ ((slotWait 2).pc + 2 < readyHead gate ∧ readyHead gate ≤ (slotElect 2).pc) := by decide

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (stage : Fin 2) {g index d : Nat} {step : Fin 8}
include hp hX stage

/-- Every actual recurring QK fragment follows its own key-ready acquire.
No other successful cache-ready acquire intervenes. -/
theorem recurringKeyLatestReady {op : TcMma.OperandSpec} {accum : Bool} {mask : List Nat}
    (hMma : QkInstruction X (g,index) (recurringKeyBlock stage) step d op accum mask) :
    ∃ (wait : Nat) (slot : Fin 3) (parity : Nat),
      ReleaseReadyObservation X g wait .loopKey (Observation.readyObject l g slot) parity ∧
      ReadyPoll l X g wait slot parity true .cta ∧ TraceBefore X (g,wait) (g,index) ∧
      readyOccurrence X g wait .loopKey = releaseElections X g index .loopKey ∧
      ∀ {j slot' parity' acquire scope}, wait < j → j < index →
        ¬ ReadyPoll l X g j slot' parity' acquire scope := by
  let i : Fin 4 := 2
  have hWindow : (slotWait i).pc + 3 ≤ qkPc (recurringKeyBlock stage) + step.val ∧
      qkPc (recurringKeyBlock stage) + step.val ≤ (slotElect i).pc := by
    fin_cases stage <;> fin_cases step <;> decide
  have hIssue : X.MmaIssue (g,index) d op accum mask := ⟨_,hMma.decoded⟩
  have hWarp := (mmaIssueElection hp hX hIssue).1
  obtain ⟨wait,hBefore,loc,parity,acquire,scope,hObs,hOrdinal⟩ :=
    pendingReadyOrdinal hp hX i hMma.decoded hWindow
  obtain ⟨rfl,rfl⟩ := readyGateAcquireFlags hX i hObs
  have hMark : readyEvent ⟨(slotWait i).pc,.wait loc parity true true .cta⟩ =
      some (loc,parity) := by
    simp only [readyEvent,show (List.finRange 4).any
      (fun gate => readyHead gate == (slotWait i).pc) = true by decide,↓reduceIte]
  obtain ⟨slot,rfl⟩ := readySlotOfProjection hp hX hWarp hObs hMark
  have hBalance := pendingReadyBalance hp hX i hMma.decoded hWindow
  refine ⟨wait,slot,parity,hObs,⟨_,hObs,rfl⟩,
    ⟨rfl,hBefore,len_of_get hMma.decoded⟩,hOrdinal,?_⟩
  intro j slot' parity' acquire scope hAfter hLaterBefore hLater
  obtain ⟨gate,hGet⟩ := hLater.atGate hp hX hWarp
  let selected := readyAtSite i
  have hMark : selected ⟨(slotWait i).pc,
      .wait (Observation.readyObject l g slot) parity true true .cta⟩ = true := by
    simp [selected,readyAtSite]
  have hWait : (X.tr g)[wait]? = some ⟨(slotWait i).pc,
      .wait (Observation.readyObject l g slot) parity true true .cta⟩ := hObs
  have hStep : ((X.tr g).take (wait+1)).countP selected =
      ((X.tr g).take wait).countP selected + 1 := by
    rw [List.take_add_one,hWait]
    simp [List.countP_append,hMark]
  have hLower := (List.take_sublist_take_left (l := X.tr g)
    (show wait + 1 ≤ j by omega)).countP_le (p := selected)
  change ((X.tr g).take wait).countP selected =
    releaseElections X g index .loopKey at hOrdinal
  have hTotal : ((X.tr g).take index).countP selected =
      releaseElections X g index .loopKey + 1 := by
    exact hBalance.trans (Nat.add_comm _ _)
  by_cases hSame : i = gate
  · have hLaterMark : selected ⟨readyHead gate,
        .wait (Observation.readyObject l g slot') parity' true acquire scope⟩ = true := by
      have hHead : readyHead gate = (slotWait gate).pc := by fin_cases gate <;> rfl
      simp [selected,readyAtSite,hSame,hHead]
    change (X.tr g)[j]? = _ at hGet
    have hLaterStep : ((X.tr g).take (j+1)).countP selected =
        ((X.tr g).take j).countP selected + 1 := by
      rw [List.take_add_one,hGet]
      simp [List.countP_append,hLaterMark]
    have hUpper := (List.take_sublist_take_left (l := X.tr g)
      (show j + 1 ≤ index by omega)).countP_le (p := selected)
    omega
  · have hSites := otherReadyGate gate hSame
    have hLaterBalance := readyBalanceAtEvent hp hX i hGet hSites.1 hSites.2.1 hSites.2.2.1
    change ((X.tr g).take j).countP selected =
      (if (slotWait i).pc + 2 < readyHead gate ∧ readyHead gate ≤ (slotElect i).pc
        then 1 else 0) + ElectOrd.siteOrdinal (· == (slotElect i).pc) X g j at hLaterBalance
    have hOff : ¬ ((slotWait i).pc + 2 < readyHead gate ∧
        readyHead gate ≤ (slotElect i).pc) := hSites.2.2.2
    simp only [hOff,↓reduceIte,Nat.zero_add] at hLaterBalance
    have hElection := (List.take_sublist_take_left (l := X.tr g) hLaterBefore.le).countP_le
      (p := ElectOrd.atSites (· == (slotElect i).pc))
    change ElectOrd.siteOrdinal (· == (slotElect i).pc) X g j ≤
      releaseElections X g index .loopKey at hElection
    omega

/-- The ready event paired with a recurring QK is at the last logical use
counted in the fragment's prefix. -/
theorem recurringKeyLatestReadyOccurrence {op : TcMma.OperandSpec} {accum : Bool} {mask : List Nat}
    (hKey : QkInstruction X (g,index) (recurringKeyBlock stage) step d op accum mask) :
    ∃ (wait : Nat) (slot : Fin 3) (parity : Nat),
      ReleaseReadyObservation X g wait .loopKey (Observation.readyObject l g slot) parity ∧
      ReadyPoll l X g wait slot parity true .cta ∧ TraceBefore X (g,wait) (g,index) ∧
      readyOccurrence X g wait .loopKey = releaseElections X g index .loopKey ∧
      (((X.tr g).take wait).filterMap readyEvent).length + 1 =
        (((X.tr g).take index).filterMap readyEvent).length ∧
      ∀ {j slot' parity' acquire scope}, wait < j → j < index →
        ¬ ReadyPoll l X g j slot' parity' acquire scope := by
  obtain ⟨wait,slot,parity,hObs,hPoll,hBefore,hOrdinal,hNoLater⟩ :=
    recurringKeyLatestReady hp hX stage hKey
  have hMark : readyEvent ⟨(slotWait 2).pc,
      .wait (Observation.readyObject l g slot) parity true true .cta⟩ =
        some (Observation.readyObject l g slot,parity) := by
    simp only [readyEvent,show (List.finRange 4).any
      (fun gate => readyHead gate == (slotWait 2).pc) = true by decide,↓reduceIte]
  have hGet : (X.tr g)[wait]? = some ⟨(slotWait 2).pc,
      .wait (Observation.readyObject l g slot) parity true true .cta⟩ := hObs
  let rank := (((X.tr g).take wait).filterMap readyEvent).length + 1
  let total := (((X.tr g).take index).filterMap readyEvent).length
  have hStep : (((X.tr g).take (wait+1)).filterMap readyEvent).length = rank := by
    rw [List.take_add_one,hGet]
    simp [rank,hMark]
  have hMonotone {a b : Nat} (hab : a ≤ b) :
      (((X.tr g).take a).filterMap readyEvent).length ≤
        (((X.tr g).take b).filterMap readyEvent).length :=
    ((List.take_sublist_take_left hab).filterMap _).length_le
  have hLe : rank ≤ total := hStep ▸ hMonotone (Nat.succ_le_of_lt hBefore.2.1)
  refine ⟨wait,slot,parity,hObs,hPoll,hBefore,hOrdinal,le_antisymm hLe ?_,hNoLater⟩
  by_contra! hLt
  have hIssue : X.MmaIssue (g,index) d op accum mask := ⟨_,hKey.decoded⟩
  have hWarp := (mmaIssueElection hp hX hIssue).1
  obtain ⟨j,hj,hReady,hRank⟩ := readyPollAtOrdinalBefore hp hX
    (stop := index) (use := rank) (PTX.Proof.event_thread_lt hX hKey.decoded) hWarp hLt
  change (((X.tr g).take j).filterMap readyEvent).length = rank at hRank
  have hAfter : wait < j := by
    by_contra! hBefore
    have hm := hMonotone hBefore
    unfold rank at hRank
    omega
  exact hNoLater hAfter hj hReady

/-- A recurring QK precedes a delivered release of the same or a later logical
cache use, even in an unfinished execution. -/
theorem recurringKeyBeforeRelease {op : TcMma.OperandSpec} {accum : Bool} {mask : List Nat}
    {owner position : Nat} {slot : Fin 3}
    (hKey : QkInstruction X (g,index) (recurringKeyBlock stage) step d op accum mask)
    (release : EmptyReleaseAt l X (Observation.emptyObject l owner slot) g position)
    (hUse : (atPrefix l X g index).kvAcquires 0 + (atPrefix l X g index).kvAcquires 1 +
      (atPrefix l X g index).kvAcquires 2 - 1 ≤ 3 * release.ordinal + slot.val) :
    TraceBefore X (g,index) (g,release.index) := by
  obtain ⟨wait,selected,parity,hObs,hPoll,_,hOrdinal,hCount,hNoLater⟩ :=
    recurringKeyLatestReadyOccurrence hp hX stage hKey
  have hMma : X.MmaIssue (g,index) d op accum mask := ⟨_,hKey.decoded⟩
  have hWarp := (mmaIssueElection hp hX hMma).1
  have hg : g < l.threads := PTX.Proof.event_thread_lt hX hKey.decoded
  let total := fun n => (atPrefix l X g n).kvAcquires 0 +
    (atPrefix l X g n).kvAcquires 1 + (atPrefix l X g n).kvAcquires 2
  have hTotal (n : Nat) : (((X.tr g).take n).filterMap readyEvent).length = total n :=
    readyUsesAtPrefix hp hX hg hWarp n
  rw [hTotal,hTotal] at hCount
  change total wait + 1 = total index at hCount
  have hSelected := hPoll.exactOccurrence hp hX hWarp
  have hRelease := release.matched.ready.exactOccurrence hp hX hWarp
  change selected.val = total wait % 3 ∧
    (atPrefix l X g wait).kvAcquires selected = total wait / 3 ∧ _ at hSelected
  change release.matched.slot.val = total release.matched.wait % 3 ∧
    release.ordinal = total release.matched.wait / 3 ∧ _ at hRelease
  rw [release.matchedSlot] at hRelease
  have hReleaseUse : total release.matched.wait = 3 * release.ordinal + slot.val := by
    omega
  change total index - 1 ≤ 3 * release.ordinal + slot.val at hUse
  have hCmp : total wait ≤ total release.matched.wait := by omega
  rcases hCmp.lt_or_eq with hLt | hEq
  · have hAfter : wait < release.matched.wait := by
      by_contra! h
      have hm := ((List.take_sublist_take_left (l := X.tr g) h).filterMap
        readyEvent).length_le
      rw [hTotal,hTotal] at hm
      change total release.matched.wait ≤ total wait at hm
      omega
    have hBefore : index ≤ release.matched.wait := by
      by_contra! h
      exact hNoLater hAfter h release.matched.ready
    exact ⟨rfl,hBefore.trans_lt release.matched.earlier,release.matched.resumes.1.2.2⟩
  · have hSlot : selected = slot := Fin.ext (by rw [hSelected.1,hRelease.1,hEq])
    subst selected
    have hPhase : (atPrefix l X g wait).kvAcquires slot = release.ordinal := by
      rw [hSelected.2.1,hEq, hRelease.2.1]
    exact (release.afterFragmentOfReady hp hX hMma hObs hOrdinal hPhase).2

end PTX.Kernels.TmlFa4Fwd.Thread.Mma
