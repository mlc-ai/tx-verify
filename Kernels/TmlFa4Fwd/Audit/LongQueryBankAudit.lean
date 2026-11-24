-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Audit.LongQueryBankLaunch
public import Kernels.TmlFa4Fwd.Audit.QueryOutputCounterexample
public import Kernels.TmlFa4Fwd.Proof.SoftmaxExitPublications
public import Kernels.TmlFa4Fwd.Proof.Protocol.ScorePollOrdinals
public import Kernels.TmlFa4Fwd.Proof.Protocol.PlainProbabilityFenceOrder
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaQueryRounds
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaQueryBank
public import Kernels.TmlFa4Fwd.Proof.Safety.StagingOperandOrder
import Kernels.TmlFa4Fwd.Proof.Protocol.CorrectionProbabilityReuse

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Audit
open PTX PTX.Flow Epilogue Thread Thread.Scores Protocol.Scores
open Prologue (warpIndex)
open _root_.PTX.Kernels.TmlFa4Fwd.Mma (qkStage recurringKeyBlock)

theorem longCuQProtected {m : Mem0} {X : Execution}
    (hp : Pre longParams longLaunch m) (hX : Consistent longLaunch kernel Assumptions.all m X) :
    DrainCuQProtected longParams X :=
  cuQProtectedOfHighOutputBases hp hX (by decide +kernel) rfl rfl (by decide +kernel)

/-- The complete sixteen-block launch issues a concrete score commit for each of its rounds. -/
theorem longScoreCommitOfComplete {m : Mem0} {X : Execution}
    (hp : Pre longParams longLaunch m) (hX : Consistent longLaunch kernel Assumptions.all m X)
    (hDone : Complete longLaunch X) (stage : Fin 2) {round : Nat} (hRound : round < 16) :
    ∃ commit spec rank, ScoreCommit longLaunch X commit 0 stage spec rank ∧
      scoreCommitOrdinal longLaunch X 0 stage commit = round := by
  let g := 128*stage.val
  have hg : g < longLaunch.threads := by fin_cases stage <;> decide
  have hCta : g/longLaunch.block = 0 := by fin_cases stage <;> decide
  have hWarp : Prologue.warpIndex longLaunch g < 8 := by fin_cases stage <;> decide
  have hStage : Prologue.warpIndex longLaunch g/4 = stage.val := by fin_cases stage <;> decide
  have hWork : g/longLaunch.block < tilePrefix longParams longParams.batch*longParams.heads := by
    rw [hCta]
    decide +kernel
  have hCuQ := longCuQProtected hp hX
  have hUsedK := usedKProtected hp hX
  obtain ⟨batch, hb, _, _, hCount⟩ :=
    Softmax.exitedActiveScorePollExtent hp hX hg hWarp hWork hCuQ hUsedK
      (exitedOfComplete hX hDone hg)
  have hBatch : batch = 0 := by change batch < 1 at hb; omega
  subst batch
  have hTile : (assignedCoordinates longParams 0 0).1 = 0 := by decide +kernel
  rw [hCta,hTile,longExampleTrips] at hCount
  have hStageEq : (⟨Prologue.warpIndex longLaunch g/4, by omega⟩ : Fin 2) = stage := Fin.ext hStage
  rw [hStageEq] at hCount
  obtain ⟨commit,spec,rank,hCommit,hOrd,_⟩ := scorePollObservesExactCommit hp hX
    (correctionJointGuardsOfCuQ hp hX hCuQ) stage hCta hWarp hStage (hRound.trans_le hCount)
  exact ⟨commit,spec,rank,hCommit,hOrd⟩

/-- The audit CTA's correction warp stages the first output tile before completing. -/
theorem longFirstStagingOfComplete {m : Mem0} {X : Execution}
    (hp : Pre longParams longLaunch m) (hX : Consistent longLaunch kernel Assumptions.all m X)
    (hDone : Complete longLaunch X) :
    ∃ writer a data, StageStagingWrite X writer 0 a data ∧ writer.1/longLaunch.block = 0 := by
  obtain ⟨index,a,data,hs⟩ := firstStagingObservationOfComplete hp hX hDone (g := 256)
    (by decide +kernel) (by decide) (by decide) (by decide +kernel)
  exact ⟨(256,index),a,data,hs,by change 256 / longLaunch.block = 0; decide⟩

/-- Each last query bank follows all Bias fences through both preceding plain packets. -/
theorem longFinalQueryBanksAfterBias {m : Mem0} {X : Execution}
    (hp : Pre longParams longLaunch m) (hX : Consistent longLaunch kernel Assumptions.all m X)
    (hDone : Complete longLaunch X) (stage : Fin 2) (step : Fin 8) :
    ∃ mma d op accum mask, X.MmaIssue mma d op accum mask ∧
      mma.1/longLaunch.block = 0 ∧ Mma.QueryOperandFragment longLaunch mma.1 stage step op ∧
      ∀ fence repeated, BiasOperandFence X fence repeated →
        fence.1/longLaunch.block = 0 → baseCausality longLaunch X fence mma := by
  have hCuQ := longCuQProtected hp hX
  obtain ⟨commit,spec,rank,hCommit,hRound⟩ :=
    longScoreCommitOfComplete hp hX hDone stage (round := 15) (by decide)
  obtain ⟨g,index⟩ := commit
  obtain ⟨start,hStart,hBank⟩ := scoreCommitRecurringQueryBank hp hX hCommit (by omega)
  obtain ⟨d,op,accum,mask,hFragment,_,_⟩ := hBank step
  let mma := (g,start+step.val)
  have hCta : mma.1/longLaunch.block = 0 := (scoreCommitActor hp hX hCommit).1
  have hStageOf (s : Fin 2) : qkStage (recurringKeyBlock s) = s := by fin_cases s <;> decide
  have hMma := hFragment.mmaIssue
  refine ⟨mma,d,op,accum,mask,hMma,hCta,hStageOf stage ▸ hFragment.queryOperand hp hX,?_⟩
  intro fence repeated hFence hSame
  have hWarp := hFence.role hp hX
  let producingStage : Fin 2 := ⟨warpIndex longLaunch fence.1 / 4, by omega⟩
  obtain ⟨prev,s,r,hPrev,hPrevRound⟩ :=
    longScoreCommitOfComplete hp hX hDone producingStage (round := 14) (by decide)
  obtain ⟨previousLane,previousIndex⟩ := prev
  obtain ⟨priorStart,_,hPrevBank⟩ := scoreCommitRecurringQueryBank hp hX hPrev (by omega)
  obtain ⟨_,_,_,_,hPrevFrag,hPrevBefore,hPrevCount⟩ := hPrevBank 0
  let prior := (previousLane,priorStart+(0 : Fin 8).val)
  have hPriorCta : prior.1/longLaunch.block = 0 := (scoreCommitActor hp hX hPrev).1
  obtain ⟨laterStart,hLaterStart,hLaterBank⟩ :=
    hPrev.beforeLaterRecurringCacheBank hp hX hCommit (by omega) (by omega)
  obtain ⟨_,_,_,_,_,hLater⟩ := hLaterBank step
  rw [show laterStart = start by omega] at hLater
  have hPriorCausal := hFragment.baseCausalityOfTrace (l := longLaunch) (hPrevBefore.trans hLater)
  have hRepeated := (by decide : ∀ s : Fin 2, 2 ≤ (recurringKeyBlock s).val) producingStage
  obtain ⟨wait,hWait⟩ := hPrevFrag.recurringProbabilityAcquire hp hX hRepeated 0
  rw [hStageOf producingStage] at hWait
  have hWork : prior.1/longLaunch.block <
      tilePrefix longParams longParams.batch*longParams.heads := by
    rw [hPriorCta]
    decide +kernel
  have hEnough : 12 ≤ scoreCommitOrdinal longLaunch X (prior.1/longLaunch.block)
      producingStage prior := by
    rw [hPriorCta]
    change 12 ≤ scoreCommitOrdinal longLaunch X 0 producingStage
      (previousLane,priorStart+(0 : Fin 8).val)
    rw [hPrevCount,hPrevRound]
    decide
  exact (biasFencesBeforeMmaOfComplete hp hX hDone (correctionJointGuardsOfCuQ hp hX hCuQ)
    hCuQ hWait hWork hEnough hFence (hSame.trans hPriorCta.symm) rfl).trans hPriorCausal

/-- With the original proxy-only order the first staging write and a late QK read
would conflict. The actual Core relation orders the same pair by source reuse. -/
theorem longQueryOperandLegacyConflictOfComplete {m : Mem0} {X : Execution}
    (hp : Pre longParams longLaunch m) (hX : Consistent longLaunch kernel Assumptions.all m X)
    (hDone : Complete longLaunch X) : Safety.LegacyStagingOperandConflict longLaunch X := by
  obtain ⟨writer, a, data, hWriter, hCta⟩ := longFirstStagingOfComplete hp hX hDone
  apply Safety.legacyConflictOfQueryBanksAfterBias hp hX (longCuQProtected hp hX) hWriter
  simpa only [hCta] using longFinalQueryBanksAfterBias hp hX hDone

end PTX.Kernels.TmlFa4Fwd.Audit
