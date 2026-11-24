-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Statistics
public import Kernels.TmlFa4Fwd.Proof.Thread.FirstQueryStatisticsTrace
public import Kernels.TmlFa4Fwd.Proof.Thread.FirstScoreCommitObservation
public import Kernels.TmlFa4Fwd.Proof.Thread.QueryOperandOutputOrder
public import Kernels.TmlFa4Fwd.Proof.Thread.QueryOutputCommit
public import Kernels.TmlFa4Fwd.Proof.SoftmaxMbarAddress
public import Kernels.TmlFa4Fwd.Proof.MmaFirstQueryOperand
public import Kernels.TmlFa4Fwd.Proof.TerminalSite
public import Kernels.TmlFa4Fwd.Proof.NoCancellation
import Lemmas.Protocol.UnitGate

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol
open PTX PTX.AsyncCopy Thread

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
include hp

/-- A score wait and a subsequent shared proxy fence can order an MMA's operand read before
correction's store. The named statistics barrier carries the fence to the destination lane. -/
theorem queryOperandBeforeStagingOfStatistics (hX : Consistent l kernel Assumptions.all m X)
    {mma : EvId} {score wait fence notice correction rendezvous store index : Nat} {stage : Fin 2}
    {producerRound : Scores.Round} {consumerRound : CorrectionRound} {loc : Loc}
    {value : Option Byte} (hObserved : AsyncObserved X mma .mmaDone (score, wait) true .cta)
    (hMmaCta : SameCta l mma.1 score) (hRead : X.MmaRead mma false index loc value)
    (hSpace : loc.space = .shared) (hOwner : loc.cta = score / l.block)
    (hFence : X.IsProxyFence (score, fence) (.async (some (.shared .cta))) none)
    (hAfterWait : wait < fence) (hSame : SameCta l score correction)
    (hPair : Protocol.Statistics.Paired l score correction stage)
    (hPub : Scores.Publishes X (score, notice) producerRound)
    (hWait : CorrectionWaits X (correction, rendezvous) consumerRound stage)
    (hOrdinal : (Scores.before X (score, notice)).barrier (3 + Prologue.warpIndex l score) =
      (correctionBefore X (correction, rendezvous)).barrier (3 + Prologue.warpIndex l score))
    (hBeforeNotice : fence < notice) (hAfterRendezvous : rendezvous < store)
    (hInTrace : store < (X.tr correction).length) :
    modelCausality l X loc (.async mma (.mmaRead false index)) (.thread (correction, store)) := by
  have hBefore := scoreWaitBeforeProxyFence hFence hAfterWait
  have hAfter := Protocol.Statistics.handoff hp hX hSame hPair hPub hWait hOrdinal
    hBeforeNotice hAfterRendezvous hInTrace
  have hReach : SameCluster l score correction :=
    ⟨hSame.1, hSame.2.1, congrArg l.clusterOfCta hSame.2.2⟩
  have hCover : ({loc, size := 1} : Acc).Covers loc := ⟨rfl, rfl, le_rfl, Nat.lt_succ_self _⟩
  exact ⟨⟨{loc, size := 1}, false, ⟨rfl, rfl, hRead.1⟩, hCover⟩,
    (score, wait), .inr ⟨.cta, hObserved,
      PTX.MbarRing.Unit.Gate.scopesMeet hMmaCta .cluster .cta⟩,
    .inl ⟨(score, fence), some (.shared .cta), none, hFence, hSame.1, ⟨hSpace, hOwner⟩,
      hReach, .single (.inl hBefore), hAfter⟩⟩

end PTX.Kernels.TmlFa4Fwd.Protocol
