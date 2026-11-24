-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.QueryOutputCommit
public import Kernels.TmlFa4Fwd.Proof.Thread.ScoreProbabilityGate
import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasReadyOrder
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
import Kernels.TmlFa4Fwd.Proof.MmaMbarAddress
import Kernels.TmlFa4Fwd.Proof.RegisterHintBody
import Kernels.TmlFa4Fwd.Proof.PollSafety
import Kernels.TmlFa4Fwd.Proof.Thread.ProbabilityIssuers
import Lemmas.Order.GuardOrder

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Scores
open PTX PTX.Flow PTX.Proof PTX.Assumption PTX.AsyncCopy Prologue
open PTX.Kernels.TmlFa4Fwd.Mma

/-- The MMA commit completing the selected output stage. -/
def TerminalOutputCommit (X : Execution) (stage : Fin 2) (issue : EvId)
    (s : TcCommit.Spec) : Prop :=
  if stage = 0 then FirstOutputCommit X issue s else SecondOutputCommit X issue s

private theorem terminalOutputDecoded {X : Execution} {stage : Fin 2}
    {issue : EvId} {s : TcCommit.Spec} (hIssue : TerminalOutputCommit X stage issue s) :
    X.get issue = some ⟨if stage = 0 then 2642 else 2646, .tc (.commit s)⟩ := by
  fin_cases stage
  · exact hIssue
  · exact SecondOutputCommit.decoded hIssue

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

private theorem terminalOutputActor (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {stage : Fin 2} {issue : EvId} {s : TcCommit.Spec}
    (hIssue : TerminalOutputCommit X stage issue s) :
    warpIndex l issue.1 = 12 ∧
      ∃ k source inst, X.Elect (issue.1,k) source (2 ^ 32 - 1) inst (laneOf l issue.1) := by
  obtain ⟨g,i⟩ := issue
  have he := terminalOutputDecoded hIssue
  let site := if stage = 0 then 2642 else 2646
  have hLo : 173 < site := by fin_cases stage <;> decide
  have hHi : site < 2768 := by fin_cases stage <;> decide
  have hHint : site ∉ registerHintSites := by fin_cases stage <;> decide
  have hw : warpIndex l g = 12 := by
    obtain h | h := roleBodyPcOfEvent hp hX he hLo hHint
    · change site = 9205 at h
      omega
    · rw [show (⟨site, .tc (.commit s)⟩ : Event).pc = site from rfl] at h
      have hMma : 1908 ≤ site := by fin_cases stage <;> decide
      split_ifs at h <;> omega
  refine ⟨hw, ?_⟩
  fin_cases stage
  · obtain ⟨_, inst, leader, hElect, hLane⟩ := firstOutputCommitLeader hp hX he
    exact ⟨i-1, _, inst, hLane.symm ▸ hElect⟩
  · obtain ⟨_, inst, leader, hElect, hLane⟩ := secondOutputCommitLeader hp hX he
    exact ⟨i-1, _, inst, hLane.symm ▸ hElect⟩

private def terminalWaitSite (stage : Fin 2) : Nat := if stage = 0 then 2548 else 2595

/-- Decoded terminal acquire of either probability packet. -/
def terminalProbabilityHead (stage packet : Fin 2) : Nat :=
  if packet = 0 then (if stage = 0 then 2548 else 2595)
  else if stage = 0 then 2586 else 2626

private theorem terminalWaitFloor (stage packet : Fin 2) :
    (kernel.code.drop (terminalProbabilityHead stage packet)).all
      (fun i => staysPastEvent (terminalProbabilityHead stage packet) i.op) = true := by
  set_option maxRecDepth 100000 in
    fin_cases stage <;> fin_cases packet <;> kernel_rfl

private theorem terminalWaitSegments (stage packet : Fin 2) :
    Assumptions.swExp2Sites.all (fun site =>
      match cuteExp2.matchAt kernel site with
      | some seg => decide (terminalProbabilityHead stage packet ≤ seg.stop)
      | none => false) = true := by
  set_option maxRecDepth 100000 in
    fin_cases stage <;> fin_cases packet <;> kernel_rfl

/-- An actual terminal probability poll occurs after every earlier same-lane score commit
and covers that commit's probability ordinal. -/
theorem terminalProbabilityPollCoversScore (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g j k cta : Nat} {stage : Fin 2}
    {spec : TcCommit.Spec} {rank : Fin 16} (packet : Fin 2) {q : Nat} {acq : Bool}
    {scope : MbarScope} (hScore : ScoreCommit l X (g,j) cta stage spec rank)
    (hPoll : X.get (g,k) = some
      ⟨terminalProbabilityHead stage packet,
        .wait (probabilityObject l cta stage packet) q true acq scope⟩) :
    scoreCommitOrdinal l X cta stage (g,j) ≤
      okPolls (probabilityObject l cta stage packet) ((X.tr g).take k) := by
  let loc := probabilityObject l cta stage packet
  obtain ⟨b,_,hScoreEvent⟩ := scoreCommitSite hp hX hScore
  have hLower : (commitSite (qkCommitSite b)).pc < terminalProbabilityHead stage packet := by
    fin_cases stage <;> fin_cases packet <;> fin_cases b <;> decide
  have hOrder := traceOrderOfPcFloor hX (terminalWaitFloor stage packet)
    (terminalWaitSegments stage packet)
    hScoreEvent hPoll hLower (Nat.le_refl _)
  let n := scoreCommitOrdinal l X cta stage (g,j)
  have hCount : n ≤ okPolls loc ((X.tr g).take k) := by
    by_cases hz : n = 0
    · omega
    have hN : n-1 < scoreCommitOrdinal l X cta stage (g,j) := by
      change n-1 < n
      omega
    obtain ⟨a,e,_,_,_,hE,hKind,hOrdinal,hResume⟩ :=
      scoreCommitProbabilityOfOrdinal hp hX hScore packet hN
    have hLt := hResume.1.2.1
    change a < j at hLt
    have hMono := countP_take_mono (okPoll loc) (X.tr g) (i := a+1) (j := k) (by omega)
    have hMark : okPoll loc e = true := by simp [okPoll, sourceWaitSuccess, hKind, loc]
    change (X.tr g)[a]? = some e at hE
    rw [List.take_add_one, hE, Option.toList_some, List.countP_append,
      List.countP_singleton, ite_eq_left hMark] at hMono
    change okPolls loc ((X.tr g).take a) + 1 ≤ okPolls loc ((X.tr g).take k) at hMono
    change okPolls loc ((X.tr g).take a) = n-1 at hOrdinal
    omega
  exact hCount

/-- The terminal joint packet poll covers an earlier same-lane score commit. -/
theorem terminalJointPollCoversScore (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j k cta : Nat} {stage : Fin 2} {spec : TcCommit.Spec} {rank : Fin 16} {q : Nat} {acq : Bool}
    {scope : MbarScope} (hScore : ScoreCommit l X (g,j) cta stage spec rank)
    (hPoll : X.get (g,k) = some
      ⟨if stage = 0 then 2548 else 2595,.wait (probabilityObject l cta stage 0) q true acq scope⟩) :
    scoreCommitOrdinal l X cta stage (g,j) ≤
      okPolls (probabilityObject l cta stage 0) ((X.tr g).take k) :=
  terminalProbabilityPollCoversScore hp hX 0 hScore hPoll

/-- The terminal output commit follows a successful joint probability wait whose local
ordinal is at least that of any actual score commit in the selected stage and CTA. -/
theorem terminalOutputProbabilityAfterScore (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {out score : EvId} {cta : Nat} {stage : Fin 2}
    {s spec : TcCommit.Spec} {rank : Fin 16} (hOut : TerminalOutputCommit X stage out s)
    (hCta : out.1 / l.block = cta) (hScore : ScoreCommit l X score cta stage spec rank) :
    let loc := probabilityObject l cta stage 0
    ∃ k e q acq scope, X.get (out.1,k) = some e ∧ e.kind = .wait loc q true acq scope ∧
      scoreCommitOrdinal l X cta stage score ≤ okPolls loc ((X.tr out.1).take k) ∧
      Resumes kernel X (out.1,k) out := by
  obtain ⟨g,i⟩ := out
  obtain ⟨h,j⟩ := score
  have hCommit := terminalOutputDecoded hOut
  obtain ⟨k,hK,q,target,acq,scope,hPoll⟩ :=
    Softmax.terminalMmaProbabilityWaitSource hX stage hCommit rfl
  change X.get (g,k) = some ⟨terminalWaitSite stage, .wait target q true acq scope⟩ at hPoll
  have hSite : terminalWaitSite stage ∈
      [2141, 2145, 2210, 2297, 2335, 2419, 2450, 2548, 2586, 2595, 2626] := by
    fin_cases stage <;> decide
  have hTarget := mmaFixedWaitAddress hp hX hPoll hSite
  let loc := probabilityObject l cta stage 0
  have hLoc : target = loc := by
    rw [hTarget]
    change g / l.block = cta at hCta
    rw [hCta]
    fin_cases stage <;> rfl
  rw [hLoc] at hPoll
  obtain ⟨hOwner, hWarp, _, _, _, hE⟩ := scoreCommitActor hp hX hScore
  obtain ⟨hWarp', _, _, _, hE'⟩ := terminalOutputActor hp hX hOut
  obtain ⟨_, _, hScoreEvent⟩ := scoreCommitSite hp hX hScore
  change h / l.block = cta at hOwner
  have hSame : SameWarp l h g :=
    ⟨⟨event_thread_lt hX hScoreEvent,event_thread_lt hX hCommit,hOwner.trans hCta.symm⟩,
      hWarp.trans hWarp'.symm⟩
  have hh : h = g := sameWarp_eq_of_lane_eq hSame (sameLeader hX hSame hE hE')
  subst h
  have hCount := terminalJointPollCoversScore hp hX hScore hPoll
  obtain ⟨exit, hSpin⟩ := actualCanonicalPoll hX hPoll
  have ht : TraceBefore X (g,k) (g,i) := ⟨rfl,hK,(List.getElem?_eq_some_iff.mp hCommit).1⟩
  refine ⟨k,_,q,acq,scope,hPoll,rfl,hCount,ht,?_⟩
  simp only [hPoll, Option.map_some, Kind.resume]
  exact ⟨_,exit,loc,q,acq,scope,hPoll,hSpin,ht⟩

/-- The final joint credit makes the correction lane's last rescaled accumulator available. -/
@[no_expose] def TerminalProbabilityCredit (l : Launch) (X : Execution) (credit : EvId)
    (cta : Nat) (stage : Fin 2) : Prop :=
  X.get credit = some ⟨if stage = 0 then 8759 else 9055,
    .arrive (probabilityObject l cta stage 0) 0 1 true .cta⟩

/-- The checked terminal arrival identifies the final correction credit. -/
theorem terminalProbabilityCreditOfDecoded {l : Launch} {X : Execution} {credit : EvId}
    {cta : Nat} {stage : Fin 2}
    (h : X.get credit = some ⟨if stage = 0 then 8759 else 9055,
      .arrive (probabilityObject l cta stage 0) 0 1 true .cta⟩) :
    TerminalProbabilityCredit l X credit cta stage := h

/-- A terminal correction credit follows the terminal MMA notification that it acquired. -/
theorem terminalCreditDependsOnMmaOutput (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {credit : EvId} {cta : Nat} {stage : Fin 2}
    (hCredit : TerminalProbabilityCredit l X credit cta stage) :
    ∃ out s, TerminalOutputCommit X stage out s ∧ out.1 / l.block = cta ∧
      Relation.TransGen (DepStep l kernel X) (.thread out,false) (.thread credit,false) := by
  obtain ⟨g,i⟩ := credit
  let loc := probabilityObject l cta stage 0
  have hCredit' : ProbabilityCredit l X (g,i) cta stage 0 := ⟨_, hCredit⟩
  have hCta := (probabilityCreditRole hp hX stage 0 hCredit').1
  have hOut : ∃ out s rank wait object scope, TerminalOutputCommit X stage out s ∧
      SameCta l out.1 wait.1 ∧ rank ∈ X.tcNotified out ∧
      WaitObserves X (.async out (.tcNotify rank)) wait object true scope ∧
      po X wait (g,i) := by
    fin_cases stage
    · have hSite : X.get (g,i) = some ⟨8759,.arrive loc 0 1 true .cta⟩ := hCredit
      obtain ⟨k,hWait,hBefore⟩ := Correction.firstOutputAcquireBeforeTerminalCredit hp hX hSite rfl
      obtain ⟨out,s,rank,scope,hCommit,hCta,_,hReady,hObs⟩ :=
        firstOutputAcquireCommit hp hX hWait
      exact ⟨out,s,rank,(g,k),_,scope,hCommit,hCta,hReady,hObs,hBefore⟩
    · have hSite : X.get (g,i) = some ⟨9055,.arrive loc 0 1 true .cta⟩ := hCredit
      obtain ⟨w,hWait,hBefore⟩ := Correction.secondOutputAcquireBeforeTerminalCredit hp hX hSite rfl
      obtain ⟨out,s,rank,scope,hCommit,hCta,_,hReady,hObs⟩ :=
        secondOutputAcquireCommit hp hX hWait
      exact ⟨out,s,rank,w,_,scope,hCommit,hCta,hReady,hObs,hBefore⟩
  obtain ⟨out,s,rank,wait,object,scope,hCommit,hSame,hReady,hObs,hBefore⟩ := hOut
  have hThread : wait.1 = g := hBefore.1
  have hOwner : out.1 / l.block = cta := hSame.2.2.trans (hThread ▸ hCta)
  have hPresent : X.AsyncPresent out (.tcNotify rank) := hReady
  have hIssue : DepStep l kernel X (.thread out,false) (.async out (.tcNotify rank),false) :=
    DepStep.issue ⟨_,terminalOutputDecoded hCommit⟩ hPresent (by intro x h; cases h)
      (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)
  have hObserve := mbarObserved_of_waitObserves hX.tma.2.2.1 hPresent hObs
  obtain ⟨site,phase,hWait⟩ := hObs.1
  obtain ⟨exit,hSpin⟩ := actualCanonicalPoll hX hWait
  have hTrace := hBefore.trace
  have hResume : Resumes kernel X wait (g,i) := by
    refine ⟨hTrace,?_⟩
    simp only [hWait, Option.map_some, Kind.resume]
    exact ⟨site,exit,object,phase,true,scope,hWait,hSpin,hTrace⟩
  exact ⟨out,s,hCommit,hOwner,((Relation.TransGen.single hIssue).tail
    (DepStep.of_witness l (Witness.of_mbarObserved hObserve))).tail
    (DepStep.of_resumes l hResume)⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Scores
