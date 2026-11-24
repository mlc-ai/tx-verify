-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedProbabilityDenominatorProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedDenominatorBackedge
public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxBiasedLoopHead
import all Kernels.TmlFa4Fwd.Proof.SoftmaxRepeatedTail
import all Kernels.TmlFa4Fwd.Proof.Thread.RepeatedProbabilityDenominatorProgress

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof Correction

variable {p : Params}

/-- A reached repeated P join acquires its correction credit when the credit is available
whenever the lane has made no further statistics credit acquire. The window consists of the
failed and the successful polls. -/
theorem repeatedProbabilityTailAckOfPending {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g : Nat} (hg : g < l.threads) (r : Repeated)
    (warp : Fin 8) (phase : Nat) (hPhaseBound : phase < 2) (values : Nat → Value)
    (hPhase : values 7258 = b32 phase) (keep : Bool)
    (c : OpeningTripCursor l X g ((signalSite r.tailSignal).pc+1)
      (tailCarryWith l warp r.round (some values) keep)) (credits : Nat)
    (hCount : ((X.tr g).take c.pos).countP Thread.Scores.creditAcquired = credits)
    (hReady : (X.tr g).countP Thread.Scores.creditAcquired = credits →
      OpeningPollReady X (waitLoc l g (stageOf warp) r.correctionSite) phase) :
    ∃ index, ∃ u : OpeningTripCursor l X g r.sumStart
        (tailCarryWith l warp r.round (some values) keep),
      X.get (g,index) = some ⟨(waitSite r.correctionSite).pc,
        .wait (waitLoc l g (stageOf warp) r.correctionSite) phase true true .cta⟩ ∧
      c.pos ≤ index ∧ u.pos = index+1 ∧ u.ending = c.ending ∧
      (X.tr g).drop c.pos = List.replicate (index-c.pos)
        ⟨(waitSite r.correctionSite).pc,
          .wait (waitLoc l g (stageOf warp) r.correctionSite) phase false true .cta⟩ ++
        ⟨(waitSite r.correctionSite).pc,
          .wait (waitLoc l g (stageOf warp) r.correctionSite) phase true true .cta⟩ ::
          (X.tr g).drop u.pos := by
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
  have hFail : Thread.Scores.creditAcquired ⟨(waitSite r.correctionSite).pc,
      .wait (waitLoc l g stage r.correctionSite) phase false true .cta⟩ = false := rfl
  obtain ⟨n,after,ready,he,hPast,hTail,hResume,hAt,trace⟩ :=
    waitAtCountOfMaximalWithTrace hp hMax hg stage r.correctionSite hPhaseBound
      (ackFactsFresh r) hBase hPar Thread.Scores.creditAcquired hFail credits
      (fun h {_ _} _ _ _ => by
        obtain ⟨s,hs,hp'⟩ := hReady h
        exact ⟨s,hs,hp'⟩)
      hCount c.positive c.bounded c.released ht c.recorded c.remaining (c.localSteps.trans hPath)
  have hPc : (waitSite r.correctionSite).pc+3 = r.sumStart := by cases r <;> rfl
  refine ⟨c.pos+n,⟨c.pos+n+1,after,ready,c.ending,Nat.succ_pos _,len_of_get he,
    Prologue.releasedIfLast he (by simp [Kind.resume]),hPc ▸ hAt.mono hAt.2.2.2.2.2,
    hPast,hTail,hResume⟩,he,Nat.le_add_right _ _,rfl,rfl,?_⟩
  simpa only [Nat.add_sub_cancel_left] using trace

/-- `RepeatedProbabilityJoinCursor.denominatorWithPhaseOfMaximal` for a lane whose
acknowledgement is needed only while it is pending. It also reports the poll window. -/
theorem RepeatedProbabilityJoinCursor.denominatorOfPending {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X) {g : Nat} (hg : g < l.threads)
    {mode : Repeated} {warp : Fin 8} {weights : Nat → ℝ} {old alpha : ℝ} {phase : Nat}
    (j : RepeatedProbabilityJoinCursor l X g mode warp weights old alpha phase) (credits : Nat)
    (hCount : ((X.tr g).take j.cursor.pos).countP Thread.Scores.creditAcquired = credits)
    (hReady : (X.tr g).countP Thread.Scores.creditAcquired = credits →
      OpeningPollReady X (waitLoc l g (stageOf warp) mode.correctionSite) phase) :
    let mass := old*alpha + ∑ i ∈ Finset.range 128, weights i
    ∃ index,
      ∃ u : OpeningTripCursor l X g mode.sumEnd [(7257,fl mass)],
        X.get (g,index) = some ⟨(waitSite mode.correctionSite).pc,
          .wait (waitLoc l g (stageOf warp) mode.correctionSite) phase true true .cta⟩ ∧
        u.pos = index+1 ∧ u.ending = j.cursor.ending ∧
        u.ready.regs 7258 = some (b32 phase) ∧
        (∀ n ∈ mode.continuationRegs, u.ready.regs n = some (j.values n)) ∧
        j.cursor.pos ≤ index ∧
        (X.tr g).drop j.cursor.pos = List.replicate (index-j.cursor.pos)
          ⟨(waitSite mode.correctionSite).pc,
            .wait (waitLoc l g (stageOf warp) mode.correctionSite) phase false true .cta⟩ ++
          ⟨(waitSite mode.correctionSite).pc,
            .wait (waitLoc l g (stageOf warp) mode.correctionSite) phase true true .cta⟩ ::
            (X.tr g).drop u.pos := by
  obtain ⟨index,entered,he,hLe,hPos,hEnding,trace⟩ :=
    repeatedProbabilityTailAckOfPending hp hMax hg mode warp phase j.phaseBound j.values
      j.phaseWord true j.cursor credits hCount hReady
  have hField (n : Nat) (hn : n ∈ mode.sumLive) :
      entered.ready.regs n = some (j.values n) := tailFrameReg entered.checkpoint.2.2.2.2 hn
  have hOld : entered.ready.regs 7257 = some (fl old) :=
    (hField _ (by simp [Repeated.sumLive])).trans (congrArg some j.oldMass)
  have hAlpha := hField mode.alphaReg (by simp [Repeated.sumLive])
  have hWeights : RepeatedWeights mode entered.ready weights := by
    constructor
    · intro n hn
      exact (hField n (List.mem_append_left _ (List.mem_append_left _ hn))).trans
        (congrArg some (j.scalar n hn))
    · intro n hn
      exact (hField n (List.mem_append_left _ (List.mem_append_right _ hn))).trans
        (congrArg some (j.packed n hn))
  obtain ⟨u,hUPos,hUEnd,hKeep⟩ :=
    repeatedDenominatorOfCursor mode weights old alpha entered hOld hAlpha j.alphaValue hWeights
  have hPhase : u.ready.regs 7258 = some (b32 phase) :=
    ((hKeep 7258 (by simp [sumContinuationRegs])).trans
      (hField 7258 (by simp [Repeated.sumLive]))).trans (congrArg some j.phaseWord)
  refine ⟨index,u,he,hUPos.trans hPos,hUEnd.trans hEnding,hPhase,?_,hLe,?_⟩
  · intro n hn
    have hLive : n ∈ tailLiveWith mode.round true := by
      have h : n ∈ mode.sumLive ++ mode.continuationRegs := List.mem_append_right _ hn
      cases mode <;> exact h
    have hContinuation : n ∈ sumContinuationRegs := by
      have hm := Repeated.continuationRegs_mem hn
      simp only [roundContinuationRegs,sumContinuationRegs,List.mem_cons,List.not_mem_nil,
        or_false] at hm ⊢
      tauto
    exact (hKeep n hContinuation).trans (holds_mem entered.checkpoint.2.2.2.2
      (.tail _ (.tail _ (mem_factsFrom hLive))))
  · rw [hUPos.trans hPos,← hPos]
    exact trace

end PTX.Kernels.TmlFa4Fwd.Softmax
