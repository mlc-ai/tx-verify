-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.ProbabilityOperandSources
public import Kernels.TmlFa4Fwd.Proof.Thread.PlainProbabilityCredit

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Scores
open PTX PTX.AsyncCopy Thread Thread.Scores
open Prologue (warpIndex)

/-- A real MMA acquire of a plain packet brings every Bias fence of its producing
stage before the MMA issue. Every softmax lane publishes an early packet credit. -/
theorem biasFencesBeforeMmaOfPlainAcquire {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hGuard : CorrectionJointGuards l X) {mma wait : EvId} {stage : Fin 2} {round : Nat}
    (hAcquire : MmaProbabilityAcquire l X mma stage 0 wait)
    (hRound : round + 1 ≤ scoreCommitOrdinal l X (mma.1/l.block) stage mma)
    (hPlain : ∀ credit, ProbabilityCredit l X credit (mma.1/l.block) stage 0 →
      warpIndex l credit.1 < 8 → round ≤ probabilityOrdinal l X (mma.1/l.block) stage 0 credit →
      PlainProbabilityCredit l X credit (mma.1/l.block) stage)
    {fence : EvId} {repeated : Bool} (hFence : BiasOperandFence X fence repeated)
    (hCta : fence.1/l.block = mma.1/l.block) (hStage : warpIndex l fence.1/4 = stage.val) :
    baseCausality l X fence mma := by
  obtain ⟨_,phase,poll,hRecord,hId,hOk,hPhase,hBound⟩ := hAcquire.record hp hX
  have hw := hFence.role hp hX
  obtain ⟨credit,hCredit,hLane,hOrdinal,hObserved⟩ :=
    jointPollObservesLane hp hX hGuard stage hCta hw hStage hRecord hOk hPhase
  have hCreditWarp : warpIndex l credit.1 < 8 := hLane.symm ▸ hw
  have hCreditPlain := hPlain credit hCredit hCreditWarp (by omega)
  exact (hCreditPlain.afterBiasFence hX hFence hLane.symm).trans
    (probabilityCreditBeforeMma hp hX hCredit hAcquire (hId ▸ hObserved))

/-- In a complete active CTA, a probability acquire past the biased rounds orders
all Bias fences of its source stage before the MMA that resumes from the acquire. -/
theorem biasFencesBeforeMmaOfComplete {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (hDone : Complete l X)
    (hGuard : CorrectionJointGuards l X) (hCuQ : Epilogue.DrainCuQProtected p X)
    {mma wait : EvId} {stage : Fin 2}
    (hAcquire : MmaProbabilityAcquire l X mma stage 0 wait)
    (hWork : mma.1/l.block < tilePrefix p p.batch*p.heads)
    (hRound : 12 ≤ scoreCommitOrdinal l X (mma.1/l.block) stage mma)
    {fence : EvId} {repeated : Bool} (hFence : BiasOperandFence X fence repeated)
    (hCta : fence.1/l.block = mma.1/l.block) (hStage : warpIndex l fence.1/4 = stage.val) :
    baseCausality l X fence mma := by
  refine biasFencesBeforeMmaOfPlainAcquire hp hX hGuard hAcquire (round := 11)
    hRound ?_ hFence hCta hStage
  intro credit hCredit hw hOrdinal
  have hSource := hCredit
  obtain ⟨_,he⟩ := hSource
  have hg := PTX.Proof.event_thread_lt hX he
  exact PlainProbabilityCredit.ofOrdinalAtExit hp hX hCredit hw hWork hCuQ
    (exitedOfComplete hX hDone hg) hOrdinal

end PTX.Kernels.TmlFa4Fwd.Protocol.Scores
