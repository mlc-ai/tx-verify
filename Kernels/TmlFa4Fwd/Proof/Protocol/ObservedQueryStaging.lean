-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.QueryOperandOutputOrder
public import Kernels.TmlFa4Fwd.Proof.Thread.InitialQueryStagingRoute

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol
open PTX PTX.AsyncCopy Thread
open Epilogue (DrainCuQProtected)

/-- An actual initial QK operand read precedes the actual stage-zero staging store, using
the paired softmax statistics rendezvous for the operand's physical Q stage. -/
theorem initialQueryReadBeforeStagingInPrefix {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {writer : EvId} {a : Acc} {data : List Byte}
    (hStage : StageStagingWrite X writer 0 a data)
    (hWork : writer.1 / l.block < tilePrefix p p.batch * p.heads)
    (hCuQ : DrainCuQProtected p X) (hUsedK : UsedKProtected p X)
    {stage : Fin 2} {producer consumer commit scoreWait issue d index : Nat}
    {op : TcMma.OperandSpec} {accum : Bool} {mask : List Nat} {loc : Loc}
    (hPhase : Softmax.FirstQkPhase l X stage producer consumer commit scoreWait)
    (hInit : Thread.Mma.InitialQueryFragment X stage (producer, issue))
    (hMma : X.MmaIssue (producer, issue) d op accum mask)
    (hLoc : op.byteLoc .a index = some loc) (hShared : loc.space = .shared)
    (hOwner : loc.cta = writer.1 / l.block) (hCta : producer / l.block = writer.1 / l.block) :
    (∃ value, X.MmaRead (producer, issue) false index loc value) ∧
      modelCausality l X loc (.async (producer, issue) (.mmaRead false index))
        (.thread writer) := by
  obtain ⟨g, store⟩ := writer
  obtain ⟨out, hOutput, hAfterOutput⟩ := stageZeroStagingAcquire hp hX hStage
  obtain ⟨final, spec, _, hFinal, hFinalCta, hRead⟩ := firstOutputAcquireReads hp hX hOutput
  have hOut : out.1 = g := hAfterOutput.1
  have hCommitCta : final.1 / l.block = g / l.block := by
    rw [← hOut]
    exact hFinalCta.2.2
  have hSameActor := firstQkOutputIssuer hp hX hPhase hFinal (hCta.trans hCommitCta.symm)
  have hBeforeFinal := initialQueryFragmentBeforeOutputCommit hX hInit hFinal hSameActor
  obtain ⟨_, _, value, hValue⟩ := hRead (isB := false) hMma hSameActor hBeforeFinal hLoc
  obtain ⟨stats, hStatsBefore, hStats⟩ :=
    stageZeroStagingInitialStats hp hX hStage hWork hUsedK stage
  have hPass : stats+1 < (X.tr g).length := by
    obtain ⟨_,hStore⟩ := hStage.writes
    have hExtent : store < (X.tr g).length := len_of_get hStore
    omega
  obtain ⟨score, wait, fence, notice, hSame, hPair, hPoll, hFence, hPub, hAfter, hBefore⟩ :=
    firstScoreRouteToCorrectionOfWait hp hX hStats hPass hWork hCuQ hUsedK
  have hPaired : Statistics.Paired l score g stage := hPair
  obtain ⟨hPubOrdinal, hStatsOrdinal⟩ := Statistics.firstOrdinals hp hX
    (producer := (score, notice)) (consumer := (g, stats)) hPaired hPub hStats
  obtain ⟨hObserved, hMmaCta⟩ :=
    hPoll.observesInitialQuery hp hX hFinal hInit hSameActor (hCommitCta.trans hSame.2.2.symm)
  have hOwner' : loc.cta = score / l.block := hOwner.trans hSame.2.2.symm
  exact ⟨⟨value, hValue⟩, queryOperandBeforeStagingOfStatistics hp hX hObserved hMmaCta hValue
    hShared hOwner' hFence hAfter hSame hPaired hPub hStats (hPubOrdinal.trans hStatsOrdinal.symm)
    hBefore hStatsBefore hAfterOutput.2.2.1⟩

/-- An actual initial QK operand read precedes the actual stage-zero staging store, using
the paired softmax statistics rendezvous for the operand's physical Q stage. -/
theorem initialQueryReadBeforeStaging {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (_hDone : Complete l X) {writer : EvId} {a : Acc} {data : List Byte}
    (hStage : StageStagingWrite X writer 0 a data)
    (hWork : writer.1 / l.block < tilePrefix p p.batch * p.heads)
    (hCuQ : DrainCuQProtected p X) (hUsedK : UsedKProtected p X)
    {stage : Fin 2} {producer consumer commit scoreWait issue d index : Nat}
    {op : TcMma.OperandSpec} {accum : Bool} {mask : List Nat} {loc : Loc}
    (hPhase : Softmax.FirstQkPhase l X stage producer consumer commit scoreWait)
    (hInit : Thread.Mma.InitialQueryFragment X stage (producer, issue))
    (hMma : X.MmaIssue (producer, issue) d op accum mask)
    (hLoc : op.byteLoc .a index = some loc) (hShared : loc.space = .shared)
    (hOwner : loc.cta = writer.1 / l.block) (hCta : producer / l.block = writer.1 / l.block) :
    (∃ value, X.MmaRead (producer, issue) false index loc value) ∧
      modelCausality l X loc (.async (producer, issue) (.mmaRead false index))
        (.thread writer) :=
  initialQueryReadBeforeStagingInPrefix hp hX hStage hWork hCuQ hUsedK
    hPhase hInit hMma hLoc hShared hOwner hCta

end PTX.Kernels.TmlFa4Fwd.Protocol
