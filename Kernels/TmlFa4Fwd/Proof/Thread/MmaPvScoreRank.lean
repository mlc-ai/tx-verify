-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaValueUseRelease
import Kernels.TmlFa4Fwd.Proof.Thread.MmaReadyTraversal
import Kernels.TmlFa4Fwd.Proof.MmaReadyReleaseElection
import Kernels.TmlFa4Fwd.Proof.EpilogueWarpReady
import Kernels.TmlFa4Fwd.Proof.OutputAssignedBox
import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixStartup
import Kernels.TmlFa4Fwd.Proof.EpilogueCuts
import Kernels.TmlFa4Fwd.Proof.OutputFrame
import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
import Lemmas.Flow.NotClc
import Lemmas.Step.CtaBar
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopEvents
import Kernels.TmlFa4Fwd.Proof.RoleDispatch
import Kernels.TmlFa4Fwd.Proof.PrologueDispatchTrace
import Kernels.TmlFa4Fwd.Proof.PrologueWarp0Prefix
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
import Kernels.TmlFa4Fwd.Proof.LoaderCountExit
import Kernels.TmlFa4Fwd.Proof.Thread.DecodedEventFrame
import Kernels.TmlFa4Fwd.Proof.Thread.TraceFloor
import Kernels.TmlFa4Fwd.Proof.Thread.MmaIssueElection
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaScoreRounds
import Kernels.TmlFa4Fwd.Proof.Thread.MmaRecurringKeyRelease
import Kernels.TmlFa4Fwd.Proof.Thread.ScoreProbabilityGate
import Kernels.TmlFa4Fwd.Proof.Thread.TmemProbabilityReuseTrace
import Kernels.TmlFa4Fwd.Proof.MmaReleaseOrdinals
import Lemmas.Order.ElectOrdinal

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Proof PTX.Flow PTX.TcMma PTX.Assumption Scores
open _root_.PTX.Kernels.TmlFa4Fwd.Mma

private theorem readyCountMonotone (X : Execution) (g : Nat) {a b : Nat}
    (h : a ≤ b) : Mma.readyCount X g a ≤ Mma.readyCount X g b := by
  exact ((List.take_sublist_take_left (l := X.tr g) h).filterMap readyEvent).length_le

private theorem PvInstruction.valueReadyCountOfLatest {p : Params} {l : Launch}
    {m : Mem0} {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index use d : Nat} {block : Fin 4} {step : Fin 8} {op : OperandSpec}
    {acc : Bool} {mask : List Nat} (hPv : PvInstruction X (g,index) block step d op acc mask)
    (hLatest : Mma.LatestValueReadyUse l X g index use) :
    let before := (X.tr g).take index
    before.countP (readyAtSite 1) + before.countP (readyAtSite 3) = use/2+1 := by
  have hIssue : X.MmaIssue (g,index) d op acc mask := ⟨_,hPv.decoded⟩
  have hw := (mmaIssueElection hp hX hIssue).1
  have hg := event_thread_lt hX hPv.decoded
  obtain ⟨wait,hPoll,hUse,hOdd,hBefore,hOnly⟩ := hLatest
  obtain ⟨pc,hGet,hSite⟩ := hPoll.useSite hp hX hw
  have hPC : ∃ gate : Fin 4, pc = readyHead gate := by
    rcases hSite with ⟨h,_⟩ | ⟨h,_,_⟩ | ⟨h,_⟩
    · exact ⟨0,h⟩
    · exact ⟨2,h⟩
    · exact h.elim (fun h => ⟨1,h⟩) (fun h => ⟨3,h⟩)
  obtain ⟨gate,rfl⟩ := hPC
  have hStep : Mma.readyCount X g (wait+1) = use+1 := by
    have hSeen : (X.tr g)[wait]? = _ := hGet
    unfold Mma.readyCount at hUse ⊢
    rw [List.take_add_one,hSeen,Option.toList_some,List.filterMap_append,List.length_append,hUse]
    fin_cases gate <;> rfl
  have hLower := readyCountMonotone X g (show wait+1 ≤ index from hBefore.2.1)
  have hUpper : Mma.readyCount X g index ≤ use+2 := by
    by_contra! hTooMany
    obtain ⟨j,hJ,hAnother,hRank⟩ :=
      Mma.readyPollAtOrdinalBefore hp hX hg hw (stop := index) (use := use+2) hTooMany
    have hLater : wait < j := by
      by_contra! hNot
      have hMono := readyCountMonotone X g hNot
      change Mma.readyCount X g j = use+2 at hRank
      omega
    have hEven := hOnly j _ _ hLater hJ hAnother
    change Mma.readyCount X g j = use+2 at hRank
    omega
  have hValues := Mma.readyValueCountAtPrefix hp hX hg hw index
  dsimp only at hValues
  change _ = Mma.readyCount X g index/2 at hValues
  omega

private theorem tailReleaseFloor :
    (kernel.code.drop (slotElect 3).pc).all (fun i => staysPastEvent (slotElect 3).pc i.op) =
      true := by
  set_option maxRecDepth 100000 in kernel_rfl

private theorem tailReleaseSegmentFloor :
    Assumptions.swExp2Sites.all (fun site => match cuteExp2.matchAt kernel site with
      | some seg => decide ((slotElect 3).pc ≤ seg.stop)
      | none => false) = true := by
  set_option maxRecDepth 100000 in kernel_rfl

set_option maxRecDepth 100000 in
private theorem noTailReleaseElectionBeforePv {l : Launch} {m : Mem0}
    {X : Execution} (hX : Consistent l kernel Assumptions.all m X) {g index d : Nat}
    {block : Fin 4} {step : Fin 8} {op : OperandSpec} {acc : Bool} {mask : List Nat}
    (hPv : PvInstruction X (g,index) block step d op acc mask) :
    ElectOrd.siteOrdinal (· == (slotElect 3).pc) X g index = 0 := by
  apply List.countP_eq_zero.mpr
  intro e hMem
  obtain ⟨j,hJ,rfl⟩ := List.getElem_of_mem hMem
  have hLen := hJ
  rw [List.length_take] at hLen
  have hBefore : j < index := by omega
  have hJ' : j < (X.tr g).length := by omega
  rw [List.getElem_take]
  have hGet : X.get (g,j) = some (X.tr g)[j] := List.getElem?_eq_getElem hJ'
  by_contra hVote
  have hMarked : ElectOrd.atSites (· == (slotElect 3).pc) (X.tr g)[j] = true := by
    simpa only [Bool.not_eq_false] using hVote
  have hPC : (X.tr g)[j].pc = (slotElect 3).pc := by
    unfold ElectOrd.atSites at hMarked
    exact beq_iff_eq.mp (Bool.and_eq_true_iff.mp hMarked).2
  have hBound : pvPc block step < (slotElect 3).pc := by
    fin_cases block <;> fin_cases step <;> decide
  have hOrder := traceOrderOfPcFloor hX tailReleaseFloor tailReleaseSegmentFloor
    hPv.decoded hGet hBound hPC.ge
  omega

/-- The V use of an actual PV fragment is indexed by the prior recurring score
elections of that stage, including the terminal visit. -/
theorem PvInstruction.valueUseOfScoreElections {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index use d : Nat} {block : Fin 4} {step : Fin 8} {op : OperandSpec}
    {acc : Bool} {mask : List Nat} (hPv : PvInstruction X (g,index) block step d op acc mask)
    (hLatest : Mma.LatestValueReadyUse l X g index use) :
    let stage := (pvSite block).stage
    let election := (electSite (commitElection
      (qkCommitSite (if stage = 0 then 2 else 3)))).pc
    ElectOrd.siteOrdinal (· == election) X g index = use/2 := by
  dsimp only
  let stage := (pvSite block).stage
  let election := (electSite (commitElection (qkCommitSite (if stage = 0 then 2 else 3)))).pc
  have hValues := hPv.valueReadyCountOfLatest hp hX hLatest
  have hBounds : 2145 ≤ pvPc block step ∧ pvPc block step < 2768 ∧
      ∀ gate : Fin 4, pvPc block step ≠ (slotWait gate).pc+1 := by
    fin_cases block <;> fin_cases step <;> decide
  have hSteady := valueReadyBalanceAtEvent hp hX hPv.decoded hBounds.1 hBounds.2.1
    (hBounds.2.2 1)
  have hTail := readyBalanceAtEvent hp hX 3 hPv.decoded hBounds.1 hBounds.2.1
    (hBounds.2.2 3)
  have hKey := readyBalanceAtEvent hp hX 2 hPv.decoded hBounds.1 hBounds.2.1
    (hBounds.2.2 2)
  have hScore := keyScoreBalanceAtEvent hp hX stage hPv.decoded hBounds.1 hBounds.2.1
    (hBounds.2.2 2)
  have hNoTail := noTailReleaseElectionBeforePv hX hPv
  rw [hNoTail,Nat.add_zero] at hTail
  have hK : (if (slotWait 2).pc+2 < pvPc block step ∧ pvPc block step ≤ (slotElect 2).pc
      then 1 else 0 : Nat) =
      (if (slotWait 2).pc+2 < pvPc block step ∧ pvPc block step ≤ election then 1 else 0) := by
    fin_cases block <;> fin_cases step <;> rfl
  have hV : (if (slotWait 1).pc+2 < pvPc block step ∧ pvPc block step ≤ (slotElect 2).pc
      then 1 else 0 : Nat) +
      (if (slotWait 3).pc+2 < pvPc block step ∧ pvPc block step ≤ (slotElect 3).pc
      then 1 else 0) = 1 := by
    fin_cases block <;> fin_cases step <;> rfl
  change ElectOrd.siteOrdinal (· == election) X g index = use/2
  change ((X.tr g).take index).countP (readyAtSite 2) =
    (if (slotWait 2).pc+2 < pvPc block step ∧ pvPc block step ≤ election then 1 else 0) +
      ElectOrd.siteOrdinal (· == election) X g index at hScore
  rw [hK] at hKey
  dsimp only at hSteady hKey hTail hValues
  omega

/-- The last same-stage score committed before a PV fragment has the same
logical visit as the V operands of that fragment. -/
theorem PvInstruction.valueUseOfLatestScoreCommit {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index use d : Nat} {block : Fin 4} {step : Fin 8} {op : OperandSpec}
    {acc : Bool} {mask : List Nat} (hPv : PvInstruction X (g,index) block step d op acc mask)
    (hLatest : Mma.LatestValueReadyUse l X g index use)
    {commit : EvId} {spec : TcCommit.Spec} {rank : Fin 16} :
    let stage := (pvSite block).stage
    ScoreCommit l X commit (g/l.block) stage spec rank →
    scoreCommitOrdinal l X (g/l.block) stage (g,index) =
      scoreCommitOrdinal l X (g/l.block) stage commit+1 →
    scoreCommitOrdinal l X (g/l.block) stage commit = use/2 := by
  dsimp only
  intro hCommit hCount
  let stage := (pvSite block).stage
  let keyBlock := recurringKeyBlock stage
  let election := (electSite (commitElection (qkCommitSite keyBlock))).pc
  let mark := ElectOrd.atSites (· == election)
  let n := scoreCommitOrdinal l X (g/l.block) stage commit
  change scoreCommitOrdinal l X (g/l.block) stage (g,index) = n+1 at hCount
  let votes := ((X.tr g).take index).countP mark
  have hSameBlock : keyBlock = if stage = 0 then 2 else 3 := by
    have audit : ∀ stage : Fin 2, recurringKeyBlock stage = if stage=0 then 2 else 3 :=
      by decide
    exact audit stage
  have hValue : votes = use/2 := by
    dsimp [votes,mark,election]
    rw [hSameBlock]
    exact hPv.valueUseOfScoreElections hp hX hLatest
  suffices n = votes by exact this.trans hValue
  have hIssue : X.MmaIssue (g,index) d op acc mask := ⟨_,hPv.decoded⟩
  have hLen := len_of_get hPv.decoded
  change index < (X.tr g).length at hLen
  have hG := event_thread_lt hX hPv.decoded
  have hLane := mmaAndScoreCommitSameThread hp hX hIssue hCommit rfl
  apply Nat.le_antisymm
  · by_contra! hFew
    have hPos : 0 < n := by omega
    obtain ⟨b,hStage,hRepeat,hGet⟩ := positiveScoreCommitRepeats hp hX hCommit hPos
    have hBlock : b = keyBlock := by
      have audit : ∀ (b : Fin 4) (s : Fin 2), b.val%2=s.val → 2 ≤ b.val →
          b = recurringKeyBlock s := by decide
      exact audit b stage hStage hRepeat
    subst b
    have hId : commit = (g,commit.2) := Prod.ext hLane.symm rfl
    rw [hId] at hGet
    obtain ⟨hI,inst,leader,hVote,_⟩ := scoreCommitLeader hp hX keyBlock hGet
    have hRank := recurringScoreExactOrdinal hp hX stage hGet
    have hRecorded : commit.2 ≤ index := by
      by_contra! hFuture
      have hMono := (List.take_sublist_take_left (l := X.tr g) hFuture.le).countP_le
        (p := scoreCommitOn (scoreReadyObject l (g/l.block) stage))
      change scoreCommitOrdinal l X (g/l.block) stage (g,index) ≤
        scoreCommitOrdinal l X (g/l.block) stage (g,commit.2) at hMono
      rw [← hId] at hMono
      omega
    have hVoteMark : mark ⟨election,.elect (2^32-1) inst leader⟩ = true := by
      simp [mark,ElectOrd.atSites,isElectEv]
    have hV : (X.tr g)[commit.2-1]? = some ⟨election,.elect (2^32-1) inst leader⟩ := hVote
    have hMono := countP_take_mono mark (X.tr g)
      (show commit.2-1+1 ≤ index by omega)
    rw [List.take_add_one,hV,Option.toList_some,List.countP_append,List.countP_singleton,
      ite_eq_left hVoteMark] at hMono
    change _ ≤ votes at hMono
    rw [← hId] at hRank
    change n = 1+((X.tr g).take (commit.2-1)).countP mark at hRank
    omega
  · by_contra! hMany
    obtain ⟨j,hJ,event,hEvent,hMarked,hLocal⟩ := Flow.exists_nth mark (X.tr g)
      (k := index) (n := n) hMany
    obtain ⟨pc,kind⟩ := event
    cases kind <;> simp [mark,ElectOrd.atSites,isElectEv] at hMarked
    case elect mask' inst leader =>
      subst pc
      have hVote : X.Elect (g,j) election mask' inst leader := hEvent
      have hMask := actualFullElectionMask hX hVote
      subst mask'
      obtain ⟨_,q,site,inst',lead,hV,hOwn⟩ := mmaIssueElection hp hX hIssue
      have hWarp : SameWarp l g g := ⟨⟨hG,hG,rfl⟩,rfl⟩
      have hSame := sameLeader hX hWarp hV hVote
      obtain ⟨next,hGet⟩ | ⟨hCut,fault,hGet⟩ :=
        Mma.electedCommitOccursOrFault hp hX (qkCommitSite keyBlock) hVote
          (hOwn.trans hSame) (by omega)
      swap
      · have hAt : j+1 = index := by omega
        rw [hAt] at hGet
        cases congrArg Event.kind (Option.some.inj (hPv.decoded.symm.trans hGet))
      have hEarlier : j+1 < index := by
        rcases Nat.eq_or_lt_of_le (show j+1 ≤ index from hJ) with h | h
        · rw [h] at hGet
          cases congrArg Event.kind (Option.some.inj (hPv.decoded.symm.trans hGet))
        · exact h
      have hStage : keyBlock.val%2 = stage.val := by
        have audit : ∀ stage : Fin 2, (recurringKeyBlock stage).val%2 = stage.val :=
          by decide
        exact audit stage
      have hScore := scoreCommitAtBlock hp hX stage keyBlock hStage hGet
      have hOrdinal := recurringScoreExactOrdinal hp hX stage hGet
      have hBudget := scoreCommitCountBeforeMma hp hX hIssue hScore rfl hEarlier.le
      change scoreCommitOrdinal l X (g/l.block) stage (g,j+1) =
        1+((X.tr g).take (j+1-1)).countP mark at hOrdinal
      rw [Nat.add_sub_cancel] at hOrdinal
      omega


end PTX.Kernels.TmlFa4Fwd.Thread
