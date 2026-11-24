-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.TmemProbabilityReuseTrace
public import Kernels.TmlFa4Fwd.Proof.Thread.TmemProbabilityReadGeometry
import Kernels.TmlFa4Fwd.Proof.Thread.TmemInitialScoreStore
import Kernels.TmlFa4Fwd.Proof.Thread.MmaPvPipeline
import Kernels.TmlFa4Fwd.Proof.MmaReadyRelease
import Kernels.TmlFa4Fwd.Proof.MmaMbarAddress
import Lemmas.Protocol.MbarRingRound

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow PTX.Proof PTX.AsyncCopy PTX.TcMma Scores
open _root_.PTX.Kernels.TmlFa4Fwd.Mma

/-- A PV acquire after an overlapping QK issue. Every score commit whose ordinal
covers this poll was issued after the QK fragment. -/
structure ScoreToPvGuard (l : Launch) (X : Execution) (writer wait reader : EvId)
    (stage : Fin 2) : Prop where
  acquire : ScoreAcquire X wait (probabilityObject l (reader.1/l.block) stage 0)
  afterIssue : TraceBefore X writer wait
  returns : Resumes kernel X wait reader
  beforeCommit : ∀ {commit spec rank},
    ScoreCommit l X commit (reader.1/l.block) stage spec rank →
    okPolls (probabilityObject l (reader.1/l.block) stage 0)
      ((X.tr wait.1).take wait.2) ≤ scoreCommitOrdinal l X (reader.1/l.block) stage commit →
    writer.2 < commit.2

private theorem qkOutsidePvGate (block : Fin 4) (frag : Fin 8) (terminal : Bool) :
    qkPc block+frag.val < earlyProbabilityHead (qkStage block) terminal ∨
      earlyProbabilityEnd (qkStage block) terminal < qkPc block+frag.val := by
  fin_cases block <;> cases terminal <;> fin_cases frag <;> decide

private theorem pvInsideGate (block : Fin 4) (frag : Fin 8) :
    let terminal := decide (2 ≤ block.val)
    earlyProbabilityHead (pvSite block).stage terminal+3 ≤ pvPc block frag ∧
      pvPc block frag ≤ earlyProbabilityEnd (pvSite block).stage terminal := by
  fin_cases block <;> fin_cases frag <;> decide

private theorem pollCountStrictlyLater {X : Execution} {first second : EvId} {object : Loc}
    (hGet : ScoreAcquire X first object) (hOrder : TraceBefore X first second) :
    okPolls object ((X.tr first.1).take first.2)+1 ≤
      okPolls object ((X.tr second.1).take second.2) := by
  obtain ⟨⟨tag,kind⟩,parity,hGet,hKind⟩ := hGet
  change kind = _ at hKind
  subst kind
  obtain ⟨g,i⟩ := first
  obtain ⟨g',j⟩ := second
  have hg : g = g' := hOrder.1
  subst g'
  have h := MbarRing.Poll.okPoll_get hGet
  rw [← h]
  exact MbarRing.Poll.okPolls_mono object (X.tr g) hOrder.2.1

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

private theorem qkBeforeCoveredCommit {writer wait commit : EvId} {block : Fin 4} {frag : Fin 8}
    {d cta : Nat} {op : OperandSpec} {acc : Bool} {mask : List Nat} {spec : TcCommit.Spec}
    {rank : Fin 16} (hIssue : QkInstruction X writer block frag d op acc mask)
    (hWait : TraceBefore X writer wait)
    (hScore : ScoreCommit l X commit cta (qkStage block) spec rank) (hCta : writer.1/l.block = cta)
    (hCover : okPolls (probabilityObject l cta (qkStage block) 0)
      ((X.tr wait.1).take wait.2) ≤ scoreCommitOrdinal l X cta (qkStage block) commit) :
    writer.2 < commit.2 := by
  by_cases hInitial : block.val < 2
  · have hBlock : block = initialQkBlock (qkStage block) := by
      revert hInitial
      fin_cases block <;> decide
    exact initialScoreIssueBeforeCommit hp hX (qkStage block) (hBlock ▸ hIssue) hScore hCta
  by_contra! hLater
  obtain ⟨prior,hPrior⟩ := hIssue.recurringProbabilityAcquire hp hX (by omega) 0
  have hEarlierScore := scoreCommitCountBeforeMma hp hX ⟨_,hIssue.decoded⟩ hScore hCta hLater
  have hPriorCount := hPrior.coversScores
  rw [hCta] at hPriorCount
  have hTrace : TraceBefore X prior wait :=
    ⟨hPrior.resume.1.1.trans hWait.1,hPrior.resume.1.2.1.trans hWait.2.1,hWait.2.2⟩
  have hEvent := hPrior.event
  rw [hCta] at hEvent
  have hCount := pollCountStrictlyLater hEvent hTrace
  omega

/-- An actual PV fragment after a same-stage QK fragment returns from an
intervening early-packet poll, in steady state and in the tail. -/
theorem scoreToPvGuard (stage : Fin 2) {writer reader : EvId} {cell : Cell}
    (hWrite : X.MmaCell writer cell) (hQk : MmaAccumulatorOn X writer cell (.probability stage))
    (hPv : MmaAOnProbabilityStage X reader cell stage) (hBefore : writer.2 < reader.2) :
    ∃ wait, ScoreToPvGuard l X writer wait reader stage := by
  obtain ⟨b,k,d,op,acc,mask,_,_,hBank,hw,_⟩ := hQk
  obtain ⟨b',k',d',op',acc',mask',index,byte,hBank',hr,hCell⟩ := hPv
  have hRead : X.MmaACell reader cell :=
    ⟨d',op',acc',mask',index,byte,⟨_,hr.decoded⟩,hCell⟩
  have hSame := (mmaWrittenCellCta hp hX hWrite).symm.trans (mmaAOperandCta hp hX hRead)
  have hLane := mmaIssueSameThread hp hX ⟨_,hw.decoded⟩ ⟨_,hr.decoded⟩ hSame
  obtain ⟨g,i⟩ := writer
  obtain ⟨g',j⟩ := reader
  change g = g' at hLane
  subst g'
  let terminal := decide (2 ≤ b'.val)
  have hIn := pvInsideGate b' k'
  change earlyProbabilityHead (pvSite b').stage terminal+3 ≤ pvPc b' k' ∧
    pvPc b' k' ≤ earlyProbabilityEnd (pvSite b').stage terminal at hIn
  rw [hBank'] at hIn
  have hOut := qkOutsidePvGate b k terminal
  rw [hBank] at hOut
  have hEntry : 2145 ≤ qkPc b+k.val ∧ qkPc b+k.val < 2768 := by
    fin_cases b <;> fin_cases k <;> decide
  obtain ⟨wait,hLo,_,loc,q,hGet,hResume⟩ :=
    earlyProbabilityWaitBetween hp hX stage terminal hw.decoded hr.decoded
      hBefore hEntry hOut hIn
  change X.get (g,wait) =
    some ⟨earlyProbabilityHead stage terminal,.wait loc q true true .cta⟩ at hGet
  have audit : ∀ (s : Fin 2) tail, earlyProbabilityHead s tail ∈
        [2141,2145,2210,2297,2335,2419,2450,2548,2586,2595,2626] ∧
      fixedMmaWaitOffset (earlyProbabilityHead s tail) = 96+8*s.val := by
    intro s tail
    fin_cases s <;> cases tail <;> decide
  obtain ⟨hSite,hOffset⟩ := audit stage terminal
  have hLocation := mmaFixedWaitAddress hp hX hGet hSite
  rw [hOffset] at hLocation
  change loc = probabilityObject l (g/l.block) stage 0 at hLocation
  subst loc
  have hBefore : TraceBefore X (g,i) (g,wait) := ⟨rfl,hLo,len_of_get hGet⟩
  refine ⟨(g,wait),⟨_,q,hGet,rfl⟩,hBefore,hResume,?_⟩
  intro commit spec rank hScore hCover
  exact qkBeforeCoveredCommit hp hX hw hBefore (hBank.symm ▸ hScore) rfl
    (hBank.symm ▸ hCover)

/-- A successful record of a softmax lane gives its CTA-acquire observation. -/
theorem scoreAcquireOfRecord {wait : EvId} {cta index : Nat} (stage : Fin 2)
    {poll : MBarrier.Record Ref} (hWarp : Prologue.warpIndex l wait.1 < 8)
    (hPoll : (X.objects (scoreReadyObject l cta stage))[index]? = some poll)
    (hId : poll.id = .thread wait) (hSuccess : poll.reply.waited = some true) :
    ScoreAcquire X wait (scoreReadyObject l cta stage) := by
  obtain ⟨other,_,q,_,_,hOther,hGet⟩ := hX.wait_of_record hPoll hSuccess
  have hSame := Ref.thread.inj (hId.symm.trans hOther)
  subst other
  obtain ⟨rfl,rfl⟩ := successfulScoreWaitIsAcquire hp hX stage hWarp hGet
  exact ⟨_,q,hGet,rfl⟩

end PTX.Kernels.TmlFa4Fwd.Thread
