-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaOpeningSteadyRoots
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaSteadyCohortIteration
import Kernels.TmlFa4Fwd.Proof.Thread.MmaOpeningProbabilityCount
import all Kernels.TmlFa4Fwd.Proof.Thread.MmaReadyTraversal
import all Kernels.TmlFa4Fwd.Proof.Thread.MmaSteadyCursor
import all Kernels.TmlFa4Fwd.Proof.Thread.MmaTailValueProgress
import Kernels.TmlFa4Fwd.Proof.MmaReadyRelease
import Lemmas.Flow.ReturningPrefix

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Proof PTX.Flow Prologue Epilogue
open Thread.Mma (readyValueCountAtPrefix readyCountsAtPrefix readySequenceSlotCount rawReadySequence
  atPrefix kvAcquireCount)

noncomputable section

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X)
include hp hMax

private theorem openingReadySlotCounts {g n shuffles votes : Nat} (hg : g < l.threads)
    (hw : warpIndex l g = 12) {ends : Nat → Option TState}
    (c : OpeningKeyReturnedWithTrip l X g n shuffles votes ends) {lane : Nat} (hl : lane < 32)
    (slot : Fin 3) :
    okPolls (cacheLoc l (g/l.block) slot)
      ((X.tr (warpLane l g lane)).take (c.pos lane)) = (1+(2-slot.val))/3 := by
  let peer := warpLane l g lane
  let pos := c.pos lane
  let before := (X.tr peer).take pos
  have hSame : SameWarp l g peer := (Step.sameWarp_lane (by rw [hp.block]) hg hl).1
  have hwPeer : warpIndex l peer = 12 := hSame.2.symm.trans hw
  have hCta : peer/l.block = g/l.block := hSame.1.2.2.symm
  have hTrace := (c.recorded lane hl).returning_reach.append
    (TraceReach.of_local (c.localSteps lane hl))
  rw [List.append_nil] at hTrace
  have hNoLate (e : Event) (hm : e ∈ before) : e.pc < 2285 := by
    by_contra! hHigh
    have hh := eventReachesFloor (by decide : 2285 ∈ [2285,2534]) hTrace ⟨e,hm,hHigh⟩
    have hPc := (c.checkpoint lane hl).1
    omega
  have hEmpty (gate : Fin 4) (hFloor : 2285 ≤ (slotWait gate).pc) :
      before.countP (readyAtSite gate) = 0 := by
    apply List.countP_eq_zero.mpr
    intro e hm hMark
    have hSite : e.pc = (slotWait gate).pc := by
      obtain ⟨_,kind⟩ := e
      cases kind <;> simp only [readyAtSite,Bool.false_eq_true] at hMark
      case wait loc parity ok acquire scope =>
        cases ok <;> simp only [Bool.false_eq_true,beq_iff_eq] at hMark
        exact hMark
    exact (Nat.not_lt_of_ge (hSite ▸ hFloor)) (hNoLate e hm)
  have hValue := readyValueCountAtPrefix hp hMax.1 hSame.1.2.1 hwPeer pos
  change before.countP (readyAtSite 1) + before.countP (readyAtSite 3) =
    (before.filterMap readyEvent).length/2 at hValue
  rw [hEmpty 1 (by decide),hEmpty 3 (by decide)] at hValue
  obtain ⟨idx,inst,leader,hEarlier,hElect⟩ :=
    (c.steadyRootsAndElections hp hMax hg hw lane hl).2 0
  obtain ⟨j,hJ,loc,parity,hReady,_⟩ :=
    readyWaitBeforeGate hp hMax.1 0
      (show X.get (peer,idx) = some ⟨2153,.elect (2^32-1) inst leader⟩ from hElect)
      (by change (waitSite (releaseWaitSite 0)).pc+3 ≤ 2153 ∧
            2153 ≤ (commitSite (releaseCommitSite 0)).pc; decide)
  have hMem : ⟨(waitSite (releaseWaitSite 0)).pc,.wait loc parity true true .cta⟩ ∈ before :=
    List.mem_of_getElem? (by
      change ((X.tr peer).take pos)[j]? = _
      rwa [List.getElem?_take_of_lt (hJ.trans hEarlier)])
  have hMark : readyEvent ⟨(waitSite (releaseWaitSite 0)).pc,.wait loc parity true true .cta⟩ =
      some (loc,parity) := by
    have hSite : ((List.finRange 4).any
        (fun i => readyHead i == (waitSite (releaseWaitSite 0)).pc)) = true := by decide
    simp only [readyEvent,hSite,ite_true]
  have hSome := List.mem_filterMap.mpr ⟨_,hMem,hMark⟩
  have hLen : (before.filterMap readyEvent).length = 1 := by
    have hh : 0 < (before.filterMap readyEvent).length := List.length_pos_of_mem hSome
    omega
  let tail := ((X.tr peer).drop pos).filterMap readyEvent
  have hSequence : ReadySequence l peer 0 (before.filterMap readyEvent ++ tail) := by
    dsimp only [before,tail]
    rw [← List.filterMap_append,List.take_append_drop]
    exact rawReadySequence hp hMax.1 hSame.1.2.1 hwPeer
  have hCounts := readySequenceSlotCount hSequence
    (n := (before.filterMap readyEvent).length) (by simp) slot
  rw [List.take_left,Nat.zero_add,Nat.zero_add,hLen] at hCounts
  have hSmall : (2-slot.val)/3 = 0 := by omega
  rw [hSmall,Nat.zero_add] at hCounts
  have hState := readyCountsAtPrefix hp hMax.1 (g := peer) (index := pos) hwPeer slot
  change (before.filterMap readyEvent).countP _ = _ at hState
  rw [hState,atPrefix,kvAcquireCount] at hCounts
  change okPolls (initObject l (peer/l.block) (Loader.readySlot slot)) before = _ at hCounts
  rw [Loader.readySlot_address,hCta] at hCounts
  simpa only [cacheLoc,Nat.add_assoc] using hCounts

/-- The actual opening run establishes the initial consumer ledger. It records
the priming K acquire, while every recurring P generation is still unconsumed. -/
theorem openingSteadyIterationWithLedger {g n shuffles votes : Nat} (hg : g < l.threads)
    (hw : warpIndex l g = 12) {ends : Nat → Option TState} (hn : 2 ≤ n) (hSigned : n < 2^31)
    (c : OpeningKeyReturnedWithTrip l X g n shuffles votes ends) :
    ∃ next : SteadyIterationCursor l X g 0 n shuffles votes ends,
      SteadyVisitLedger l X g 0 next.pos := by
  obtain ⟨next,hNext⟩ := openingSteadyIterationReachedWithPosition hp hMax hg hw hn hSigned c
  refine ⟨next,⟨?_,?_⟩⟩ <;> rw [hNext]
  · intro lane hl slot
    exact openingReadySlotCounts hp hMax hg hw c hl slot
  · intro lane hl stage packet
    have hCta : (warpLane l g lane)/l.block = g/l.block :=
      (Step.sameWarp_lane (by rw [hp.block]) hg hl).1.1.2.2.symm
    have hCount := openingProbabilityCountsAtKeyReturn hp hMax.1 c hl stage packet
    rwa [hCta] at hCount

/-- Every visited recurring body runs from its published cohorts and propagates
the exact consumer ledger through the final steady backedge. -/
theorem steadyIterationsOfCohorts (hGuard : Protocol.Scores.CorrectionJointGuards l X) {g : Nat}
    (hg : g < l.threads) (hWarp : warpIndex l g = 12) (visit remaining shuffles votes : Nat)
    {ends : Nat → Option TState} (hRemaining : 2 ≤ remaining) (hBound : remaining < 2^32)
    (cur : SteadyIterationCursor l X g visit remaining shuffles votes ends)
    (hLedger : SteadyVisitLedger l X g visit cur.pos)
    (hCohorts : ∀ j < remaining-1, SteadyVisitCohorts l X g (visit+j)) :
    ∃ finalShuffles finalEnds,
    ∃ last : SchedulerWarpReached l X g 2534
      (fun _ => steadyFrame l (visit+remaining-1) 1 ++ steadyIterationRoots l)
      finalShuffles votes finalEnds,
      SteadyVisitLedger l X g (visit+remaining-1) last.pos ∧
      ∀ j < remaining-1, SteadyIterationIssues l X g (visit+j) := by
  induction remaining using Nat.strong_induction_on generalizing visit shuffles ends with
  | h remaining ih =>
    have hStep := steadyIterationOfCohorts hp hMax hGuard hg hWarp
      hRemaining hBound cur hLedger (by simpa using hCohorts 0 (by omega))
    by_cases hLater : 2 < remaining
    · rw [ite_eq_left hLater] at hStep
      obtain ⟨nextEnds,next,hNext,hIssue,_⟩ := hStep
      obtain ⟨lastSh,lastEnds,last,hLast,hIssues⟩ :=
        ih (remaining-1) (by omega) (visit+1) (shuffles+3+1+2)
          (by omega) (by omega) next hNext (by
            intro j hj
            have h := hCohorts (j+1) (by omega)
            have he : visit+1+j = visit+(j+1) := by omega
            rwa [he])
      have hv : visit+1+(remaining-1)-1 = visit+remaining-1 := by omega
      have hReached : ∃ d : SchedulerWarpReached l X g 2534
          (fun _ => steadyFrame l (visit+1+(remaining-1)-1) 1 ++ steadyIterationRoots l)
          lastSh votes lastEnds, SteadyVisitLedger l X g (visit+1+(remaining-1)-1) d.pos :=
        ⟨last,hLast⟩
      rw [hv] at hReached
      obtain ⟨last',hLast'⟩ := hReached
      refine ⟨lastSh,lastEnds,last',?_,fun j hj => ?_⟩
      · exact hLast'
      · rcases j with _ | j
        · simpa using hIssue
        · have h := hIssues j (by omega)
          have he : visit+1+j = visit+(j+1) := by omega
          rwa [he] at h
    · have hTwo : remaining = 2 := by omega
      subst remaining
      have hVisit : visit+2-1 = visit+1 := by omega
      rw [hVisit]
      rw [ite_eq_right (by decide : ¬ 2 < 2)] at hStep
      obtain ⟨nextEnds,next,hNext,hIssue,_⟩ := hStep
      refine ⟨_,nextEnds,next,hNext,fun j hj => ?_⟩
      have hz : j = 0 := by omega
      simpa [hz] using hIssue

/-- From the actual opening key return, all published recurring cohorts take
the MMA warp through exactly the recurring visits before its final PV route. -/
theorem steadyIterationsFromOpeningCohorts (hGuard : Protocol.Scores.CorrectionJointGuards l X)
    {g n shuffles votes : Nat} (hg : g < l.threads) (hw : warpIndex l g = 12)
    {ends : Nat → Option TState} (hn : 2 ≤ n) (hSigned : n < 2^31)
    (c : OpeningKeyReturnedWithTrip l X g n shuffles votes ends)
    (hCohorts : ∀ j < n-1, SteadyVisitCohorts l X g j) :
    ∃ finalShuffles finalEnds,
    ∃ last : SchedulerWarpReached l X g 2534
      (fun _ => steadyFrame l (n-1) 1 ++ steadyIterationRoots l) finalShuffles votes finalEnds,
      SteadyVisitLedger l X g (n-1) last.pos ∧
      ∀ j < n-1, SteadyIterationIssues l X g j := by
  obtain ⟨start,hLedger⟩ := openingSteadyIterationWithLedger hp hMax hg hw hn hSigned c
  have h := steadyIterationsOfCohorts hp hMax hGuard hg hw 0 n shuffles votes hn (by omega)
    start hLedger (by simpa only [Nat.zero_add] using hCohorts)
  rw [Nat.zero_add] at h
  simpa only [Nat.zero_add] using h

end
end PTX.Kernels.TmlFa4Fwd.Mma
