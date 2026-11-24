-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaOperandReady
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaFinalCacheUseOrder
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaValueUseRelease
import Kernels.TmlFa4Fwd.Proof.Thread.MmaRecurringKeyRelease
import Kernels.TmlFa4Fwd.Proof.Thread.OutputCommitOrder
import Lemmas.Flow.NthEv
import Kernels.TmlFa4Fwd.Proof.Thread.MmaShuffleOrdinal

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Mma
open PTX PTX.Flow PTX.Proof
open PTX.Kernels.TmlFa4Fwd.Mma
open Observation (readyObject)

private def releaseOfGate : Fin 4 → ReleaseForm
  | 0 => .firstKey
  | 1 => .loopValue
  | 2 => .loopKey
  | _ => .tailValue

private theorem releaseOfGateIndex (i : Fin 4) : releaseIndex (releaseOfGate i) = i := by
  fin_cases i <;> rfl

/-- Every actual ready before O1 on the elected lane has a matching release
issue before O1. The asynchronous notification need not have arrived. -/
theorem readyReleaseIssueBeforeFinal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g wait final : Nat} {output : TcCommit.Spec} {slot : Fin 3} {parity : Nat}
    (hFinal : SecondOutputCommit X (g,final) output)
    (hReady : ReadyPoll l X g wait slot parity true .cta)
    (hBefore : TraceBefore X (g,wait) (g,final)) :
    ∃ index form spec, ReleaseIssue X g index form spec ∧
      ReleaseReadyObservation X g wait form (readyObject l g slot) parity ∧
      readyOccurrence X g wait form = releaseOccurrence X g index form ∧
      TraceBefore X (g,wait) (g,index) ∧ TraceBefore X (g,index) (g,final) := by
  have hw : Prologue.warpIndex l g = 12 := hFinal.issuerWarp hp hX
  obtain ⟨gate, hGet⟩ := hReady.atGate hp hX hw
  let r := readyAtSite gate
  let e := releaseAtSite gate
  let form := releaseOfGate gate
  have hHead : readyHead gate = (slotWait gate).pc := by fin_cases gate <;> rfl
  have hPoll : X.get (g,wait) = some ⟨(slotWait gate).pc,
      .wait (readyObject l g slot) parity true true .cta⟩ := by simpa only [hHead] using hGet
  have hReadyOn : r ⟨(slotWait gate).pc, .wait (readyObject l g slot) parity true true .cta⟩ =
      true := by simp [r, readyAtSite]
  have hStep : ((X.tr g).take (wait+1)).countP r = ((X.tr g).take wait).countP r+1 := by
    rw [List.take_add_one, show (X.tr g)[wait]? = _ from hPoll]
    simp [List.countP_append,hReadyOn]
  have hCount := (List.take_sublist_take_left (l := X.tr g) hBefore.2.1).countP_le (p := r)
  have he := hFinal.decoded
  have hb := readyBalanceAtEvent hp hX gate he
    (by change 2145 ≤ 2646; decide) (by change 2646 < 2768; decide)
    (by change 2646 ≠ (slotWait gate).pc + 1; fin_cases gate <;> decide)
  have hQuiet : ¬ ((slotWait gate).pc + 2 < 2646 ∧ 2646 ≤ (slotElect gate).pc) := by
    fin_cases gate <;> decide
  change ((X.tr g).take final).countP r =
    (if (slotWait gate).pc + 2 < 2646 ∧ 2646 ≤ (slotElect gate).pc then 1 else 0) +
      ((X.tr g).take final).countP e at hb
  rw [ite_eq_right hQuiet, Nat.zero_add] at hb
  have hWithin : ((X.tr g).take wait).countP r < ((X.tr g).take final).countP e := by
    change ((X.tr g).take (wait+1)).countP r ≤ ((X.tr g).take final).countP r at hCount
    omega
  obtain ⟨j, hj, ⟨pc,k⟩, hElect, hMarked, hOrdinal⟩ := exists_nth e (X.tr g) hWithin
  obtain ⟨_, inst', lead', hFinalVote, hFinalLane⟩ := secondOutputCommitLeader hp hX he
  cases k <;> simp [e, releaseAtSite, ElectOrd.atSites, isElectEv] at hMarked
  case elect mask inst lead =>
    subst pc
    have hElect' : X.Elect (g,j) (slotElect gate).pc mask inst lead := hElect
    have hFull := actualFullElectionMask hX hElect'
    subst mask
    have hg : g < l.threads := event_thread_lt hX he
    have hSame : SameWarp l g g := ⟨⟨hg,hg,rfl⟩,rfl⟩
    have hLead := hFinalLane.trans (sameLeader hX hSame hFinalVote hElect')
    have hRoom : j+1 < final := by
      by_contra! hLast
      have hjLast : j = final-1 := by omega
      have hEvent := Option.some.inj (hElect'.symm.trans (hjLast.symm ▸ hFinalVote))
      have hPc := congrArg Event.pc hEvent
      have hNe : (slotElect gate).pc ≠ 2643 := by fin_cases gate <;> decide
      exact hNe hPc
    obtain ⟨spec, hCommit⟩ :=
      electedCommitOccurs hp hX (releaseCommitSite gate) hElect' hLead
        (by have hLen : final < (X.tr g).length := len_of_get he; omega)
    have hForm := releaseOfGateIndex gate
    have hIssue : ReleaseIssue X g (j+1) form spec := by
      unfold ReleaseIssue
      exact (show releaseIndex form = gate from hForm).symm ▸ hCommit
    have hObserved : ReleaseReadyObservation X g wait form (readyObject l g slot) parity := by
      unfold ReleaseReadyObservation
      exact (show releaseIndex form = gate from hForm).symm ▸ hPoll
    obtain ⟨k,hK,loc,q,acq,scope,hOther,hOtherOrdinal⟩ :=
      releaseElectionWaitOrdinal hp hX gate hElect'
    have hOtherOn : r ⟨(slotWait gate).pc, .wait loc q true acq scope⟩ = true := by
      simp [r, readyAtSite]
    have hEq : wait = k := eq_of_count_eq r (X.tr g) hPoll hReadyOn hOther hOtherOn
      (hOrdinal.symm.trans hOtherOrdinal.symm)
    have hRank : readyOccurrence X g wait form = releaseOccurrence X g (j+1) form := by
      unfold readyOccurrence releaseOccurrence
      rw [show releaseIndex form = gate from hForm, Nat.add_sub_cancel]
      exact hOrdinal.symm
    exact ⟨j+1,form,spec,hIssue,hObserved,hRank,
      ⟨rfl,by omega,len_of_get hCommit⟩, ⟨rfl,hRoom,len_of_get he⟩⟩

/-- An odd logical ready use before O1 belongs to one of the two V
release forms, and that release issue precedes O1. -/
theorem valueReadyReleaseIssueBeforeFinal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g wait final use : Nat} {output : TcCommit.Spec} {slot : Fin 3} {parity : Nat}
    (hFinal : SecondOutputCommit X (g,final) output)
    (hReady : ReadyPoll l X g wait slot parity true .cta)
    (hUse : readyCount X g wait = use) (hOdd : use % 2 = 1)
    (hBefore : TraceBefore X (g,wait) (g,final)) :
    ∃ (steady : Bool) (index : Nat) (spec : TcCommit.Spec),
      ReleaseIssue X g index (valueReleaseForm steady) spec ∧
      ReleaseReadyObservation X g wait (valueReleaseForm steady) (readyObject l g slot) parity ∧
      readyOccurrence X g wait (valueReleaseForm steady) =
        releaseOccurrence X g index (valueReleaseForm steady) ∧
      TraceBefore X (g,wait) (g,index) ∧ TraceBefore X (g,index) (g,final) := by
  obtain ⟨index,form,spec,hRelease,hObs,hOrdinal,hAfter,hEarlier⟩ :=
    readyReleaseIssueBeforeFinal hp hX hFinal hReady hBefore
  obtain ⟨pc,hGet,hGate⟩ := hReady.useSite hp hX (hFinal.issuerWarp hp hX)
  change ReadyUseSite (readyCount X g wait) pc at hGate
  rw [hUse] at hGate
  have hSite : (slotWait (releaseIndex form)).pc = pc :=
    congrArg Event.pc (Option.some.inj (hObs.symm.trans hGet))
  have hValue : pc = readyHead 1 ∨ pc = readyHead 3 := by
    rcases hGate with ⟨_, hz⟩ | ⟨_, _, hz⟩ | ⟨h, _⟩
    · omega
    · omega
    · exact h
  have hCheck (f : ReleaseForm) :
      ((slotWait (releaseIndex f)).pc = readyHead 1 ∨
        (slotWait (releaseIndex f)).pc = readyHead 3) →
      f = valueReleaseForm true ∨ f = valueReleaseForm false := by cases f <;> decide
  rw [← hSite] at hValue
  rcases hCheck form hValue with h | h
  · subst form
    exact ⟨true,index,spec,hRelease,hObs,hOrdinal,hAfter,hEarlier⟩
  · subst form
    exact ⟨false,index,spec,hRelease,hObs,hOrdinal,hAfter,hEarlier⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Mma
