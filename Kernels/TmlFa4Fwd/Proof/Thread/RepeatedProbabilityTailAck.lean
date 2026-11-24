-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionTripReads
public import Kernels.TmlFa4Fwd.Proof.SoftmaxRepeatedTail
import all Kernels.TmlFa4Fwd.Proof.SoftmaxRepeatedTail
public import Kernels.TmlFa4Fwd.Proof.SoftmaxWaits
public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxOpeningScore

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof Correction

/-- A reached repeated P join advances to its actual denominator entry when the
matching correction credit supplies an available phase. -/
theorem repeatedProbabilityTailAckOfMaximal
    {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (r : Repeated) (warp : Fin 8)
    (phase : Nat) (hPhaseBound : phase < 2) (values : Nat → Value)
    (hPhase : values 7258 = b32 phase) (keep : Bool)
    (c : OpeningTripCursor l X g ((signalSite r.tailSignal).pc+1)
      (tailCarryWith l warp r.round (some values) keep))
    (hReady : OpeningPollReady X (waitLoc l g (stageOf warp) r.correctionSite) phase) :
    ∃ index, ∃ u : OpeningTripCursor l X g r.sumStart
        (tailCarryWith l warp r.round (some values) keep),
      X.get (g,index) = some ⟨(waitSite r.correctionSite).pc,
        .wait (waitLoc l g (stageOf warp) r.correctionSite) phase true true .cta⟩ ∧
      c.pos ≤ index ∧ u.pos = index+1 ∧ u.ending = c.ending := by
  let stage := stageOf warp
  let offset := 8*stage.val
  have hLocal := ((ackStage r l g warp values keep).comp
    (ackAddress hp r g warp offset (by have := stage.isLt; omega) values keep))
  obtain ⟨t,hPath,ht⟩ := hLocal.rtg c.checkpoint
  have hBase : ((waitSite r.correctionSite).base,b32 (waitLoc l g stage r.correctionSite).addr) ∈
      ackFacts r l warp offset values keep := by
    cases r <;> exact List.Mem.head _
  have hReg : (waitSite r.correctionSite).phase = 7258 := by cases r <;> rfl
  have hPar : ((waitSite r.correctionSite).phase,b32 phase) ∈
      ackFacts r l warp offset values keep := by
    rw [hReg,← hPhase]
    exact .tail _ (.tail _ (.tail _ (mem_factsFrom (phaseLive r keep))))
  obtain ⟨n,after,ready,he,hPast,hTail,hResume,hAt⟩ :=
    waitOfMaximal hp hMax hg stage r.correctionSite hPhaseBound (ackFactsFresh r)
      hBase hPar (fun _ _ _ => hReady) c.positive c.bounded c.released ht
      c.recorded c.remaining (c.localSteps.trans hPath)
  have hPc : (waitSite r.correctionSite).pc+3 = r.sumStart := by cases r <;> rfl
  exact ⟨c.pos+n,⟨c.pos+n+1,after,ready,c.ending,Nat.succ_pos _,len_of_get he,
    Prologue.releasedIfLast he (by simp [Kind.resume]),hPc ▸ hAt.mono hAt.2.2.2.2.2,
    hPast,hTail,hResume⟩,he,Nat.le_add_right _ _,rfl,rfl⟩

/-- The reached correction acknowledgement leaves a runnable repeated denominator
reduction. The actual cursor retains its position while the local instructions run. -/
theorem repeatedDenominatorOfCursor {l : Launch} {X : Execution} {g : Nat}
    (r : Repeated) (weights : Nat → ℝ) (old alpha : ℝ)
    {F : List (Nat × Value)} (c : OpeningTripCursor l X g r.sumStart F)
    (hOld : c.ready.regs 7257 = some (fl old))
    {word : Value} (hAlpha : c.ready.regs r.alphaReg = some word)
    (hAlphaValue : valFloat .f32 word = .ok alpha)
    (hWeights : RepeatedWeights r c.ready weights) :
    let mass := old*alpha + ∑ i ∈ Finset.range 128, weights i
    ∃ u : OpeningTripCursor l X g r.sumEnd [(7257,fl mass)],
      u.pos = c.pos ∧ u.ending = c.ending ∧
      ∀ n ∈ sumContinuationRegs, u.ready.regs n = c.ready.regs n := by
  obtain ⟨u,hu,hLocal,hKeeps⟩ := repeatedRowSumLocalOfWordWithFrame (l := l) (g := g)
    r weights old alpha (c.checkpoint.mono trivial) hOld hAlpha hAlphaValue hWeights
  exact ⟨⟨c.pos,c.before,u,c.ending,c.positive,c.bounded,c.released,hu,
    c.recorded,c.remaining,c.localSteps.trans hLocal⟩,rfl,rfl,hKeeps⟩

end PTX.Kernels.TmlFa4Fwd.Softmax
