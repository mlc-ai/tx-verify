-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasedScoreWait
public import Kernels.TmlFa4Fwd.Proof.SoftmaxLaterBiasVectorTrace
public import Kernels.TmlFa4Fwd.Proof.SoftmaxLaterBiasFma
import Lemmas.Step.ExitLast

import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxRecordedEntry

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption Prologue Epilogue Thread Thread.Scores

noncomputable section

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
    (hCuQ : DrainCuQProtected p X) {g start last pc batch : Nat} {addr : Nat} {words : List Value}
    {shape : TcShape} (he : X.get (g,start) = some ⟨scorePc .biased 0,.tc (.ld addr words shape)⟩)
    (hExit : X.get (g,last) = some ⟨pc,.exit⟩) (hLast : start < last) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hBytes : ∀ (stage : Fin 2) (q : Fin 4) (xs : List Value),
      X.get (g,start+q.val) =
        some ⟨scorePc .biased q,.tc (.ld (scoreAddress l g stage q) xs .s32x32b)⟩ →
      ∀ k < 32, (xs.getD k (b32 0)).bytes = 4)
include hp hX hFrame hCuQ he hExit hLast hb hLo hHi hBytes

/-- The observed biased loads and Bias input reads supply the affine-score entry
on one execution. The packed QK words survive the actual retries and rendezvous. -/
theorem observedBiasedAffineInputsWithPath :
    ∃ warp : Fin 8, warp.val = warpIndex l g ∧
      let stage := stageOf warp
      let co := assignedCoordinates p batch (g/l.block)
      let row := 256*co.1+128*stage.val+(g%l.block)%128
      ∃ wait phase u, ∃ values : Fin 4 → List Value,
        let visit := observedBarrierOrdinal X (g,wait) (11+stage.val)
        let pos := if laneOf l g = 0 then wait+1+64+3 else wait+1+64+2
        start+4 ≤ wait ∧
        X.get (g,wait) = some ⟨5181,.wait (waitLoc l g stage 5) phase true true .cta⟩ ∧
        0 < visit ∧ visit < Mma.trips p batch co.1 ∧
        visit < Mma.trips p batch co.1-stageGeometryBlocks p batch co.1 stage+10 ∧
        At u (biasBodyStart true) [] ∧
        readERealPair l g u (.reg 7896) =
          some (.ok ((abiFloat p.invScaleBits : EReal),(abiFloat p.invScaleBits : EReal))) ∧
        (∀ i, BiasUnpacked true i u (laterBiasWord p batch co.1 row co.2 visit i)) ∧
        (∀ q : Fin 4, (values q).length = 32 ∧
          X.get (g,start+q.val) =
            some ⟨scorePc .biased q,.tc (.ld (scoreAddress l g stage q) (values q) .s32x32b)⟩) ∧
        (∀ (q : Fin 4) (k : Fin 16), u.regs (repeatedScorePairReg .biased q k.val) =
          some (joinValue ((values q).getD (2*k.val) (b32 0))
            ((values q).getD (2*k.val+1) (b32 0)))) ∧
        Run kernel Assumptions.all l g u ((X.tr g).drop pos) none ∧
        (∀ q : Fin 4, ((X.tr g).take wait).countP earlyProbabilityMark =
          ((X.tr g).take (start+q.val)).countP earlyProbabilityMark) ∧
        (∀ k e, start ≤ k → k < wait → X.get (g,k) = some e → e.pc < 5189) ∧
        ∃ pre, pre.pc = 5181 ∧ Stops kernel Assumptions.all l g pre ∧
          TraceReach kernel Assumptions.all l g {} ((X.tr g).take wait) pre ∧
          TraceReach kernel Assumptions.all l g pre (((X.tr g).drop wait).take (pos-wait)) u ∧
          ∀ r, r ∉ [9755,4166,4167,4168,4169,4170] →
            (∀ i, biasVectorKeeps true i r) → r ∉ biasFenceWritten true →
            u.regs r = pre.regs r := by
  obtain ⟨other,hOther,_⟩ :=
    softmaxBodySuffix hp hX he (show 3420 ≤ 5112 by decide) (show 5112 < 7742 by decide)
  obtain ⟨warp,hWarp,entry,s,ending,hStart,hEntry,hOrigin,hEntryRun⟩ :=
    softmaxRoleEntryRecorded hp hX he (by change 173 < 5112; decide)
      (by change 5112 ≠ 3102; decide) (hOther ▸ other.isLt)
  have hEnds : ending = none := by
    cases ending with
    | none => rfl
    | some u =>
      have he' : ((X.tr g).drop entry)[last-entry]? = some ⟨pc,.exit⟩ := by
        rw [List.getElem?_drop,Nat.add_sub_of_le (by omega : entry ≤ last)]
        exact hExit
      exact (hEntryRun.no_exit he').elim
  subst ending
  obtain ⟨wait,phase,pre,values,hWait,hObserved,hReads,hPairs,hReach,hStop,hEarly,hOrder⟩ :=
    biasedScoreWaitPackedInPrefix hp warp hEntry hEntryRun he hStart (hBytes (stageOf warp))
      (.inl rfl)
  have hBefore : wait < last := by
    have hLen := X.exit_last hX (event_thread_lt hX hExit) hExit
    have hValid := len_of_get hObserved
    change wait < (X.tr g).length at hValid
    change last+1 = (X.tr g).length at hLen
    have hNe : wait ≠ last := by
      intro h
      subst wait
      exact Kind.noConfusion (congrArg Event.kind (Option.some.inj (hObserved.symm.trans hExit)))
    omega
  obtain ⟨hVisit,hTrips,hBudget,pre',u,hPC,_,hDots,hu,hScale,hBias,hTail,_,hBiasPath,
      hBiasStop,hReadyPath,hKeep⟩ :=
    laterBiasThroughAcquireFromEntryWithPath hp hX hFrame hCuQ warp hWarp hEntry hEntryRun
      (by omega : entry ≤ wait) hObserved hExit hBefore hb hLo hHi
  have hSame := reachedEventSourceUnique hReach hBiasPath hStop hBiasStop
  subst pre'
  refine ⟨warp,hWarp,wait,phase,u,values,hWait,hObserved,hVisit,hTrips,hBudget,
    hu.mono trivial,hScale,(fun i => (hBias i).2),hReads,?_,hTail,hEarly,?_,?_⟩
  · intro q k
    have hSize := q.isLt
    have hPair := k.isLt
    have hReg : repeatedScorePairReg .biased q k.val = 7367+(16*q.val+k.val) := by
      simp only [repeatedScorePairReg,Nat.add_assoc]
    rw [hReg,hDots _ (by omega),← hReg]
    exact hPairs q k
  · intro k e hA hB hE
    by_cases hAfter : start+4 ≤ k
    · have hPc : e.pc = 5181 := by
        by_contra hDifferent
        exact Nat.not_lt_of_ge hB.le (hOrder k e hAfter hE hDifferent)
      omega
    · let q : Fin 4 := ⟨k-start,by omega⟩
      have hGet := (hReads q).2
      have hI : start+q.val = k := Nat.add_sub_of_le hA
      rw [hI] at hGet
      obtain rfl := Option.some.inj (hE.symm.trans hGet)
      exact (by decide : ∀ q : Fin 4, scorePc .biased q < 5189) q
  · refine ⟨pre,hPC,hStop,?_,hReadyPath,hKeep⟩
    rw [show wait = entry+(wait-entry) by omega,List.take_add]
    exact hOrigin.append hReach

end

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
    (hCuQ : DrainCuQProtected p X) {g start last pc batch : Nat} {addr : Nat} {words : List Value}
    {shape : TcShape} (he : X.get (g,start) = some ⟨scorePc .biased 0,.tc (.ld addr words shape)⟩)
    (hExit : X.get (g,last) = some ⟨pc,.exit⟩) (hLast : start < last) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hRow : let co := assignedCoordinates p batch (g/l.block)
      256*co.1+128*(warpIndex l g/4)+(g%l.block)%128 < p.qLength batch)
    (hBytes : ∀ (stage : Fin 2) (q : Fin 4) (xs : List Value),
      X.get (g,start+q.val) =
        some ⟨scorePc .biased q,.tc (.ld (scoreAddress l g stage q) xs .s32x32b)⟩ →
      ∀ k < 32, (xs.getD k (b32 0)).bytes = 4)
    (hDot : ∀ (stage : Fin 2) (wait phase : Nat) (values : Fin 4 → List Value),
      X.get (g,wait) = some ⟨5181,.wait (waitLoc l g stage 5) phase true true .cta⟩ →
      (∀ q : Fin 4, X.get (g,start+q.val) =
        some ⟨scorePc .biased q,.tc (.ld (scoreAddress l g stage q) (values q) .s32x32b)⟩) →
      (∀ q : Fin 4, ((X.tr g).take wait).countP earlyProbabilityMark =
        ((X.tr g).take (start+q.val)).countP earlyProbabilityMark) →
      let co := assignedCoordinates p batch (g/l.block)
      let visit := observedBarrierOrdinal X (g,wait) (11+stage.val)
      ∀ (q : Fin 4) (k : Fin 32), (values q)[k.val]? = some (.float .f32
        (firstScoreDot p l g batch co.2 (p.qOffset batch+256*co.1+128*stage.val)
          (128*(Mma.trips p batch co.1-1-visit)) q k)))
include hp hX hFrame hCuQ he hExit hLast hb hLo hHi hRow hBytes hDot

/-- The actual Bias path reaches its masked affine logits from the score dot
products of that visit on the same lane trace. -/
theorem observedBiasedAffineScoresOfDotsWithPath :
    ∃ stage : Fin 2, stage.val = warpIndex l g/4 ∧ ∃ wait phase u,
      let co := assignedCoordinates p batch (g/l.block)
      let row := 256*co.1+128*stage.val+(g%l.block)%128
      let visit := observedBarrierOrdinal X (g,wait) (11+stage.val)
      let pos := if laneOf l g = 0 then wait+1+64+3 else wait+1+64+2
      let logit := fun col => maskedLogit p batch co.2 row
        (visitKey (Mma.trips p batch co.1) visit col)
      X.get (g,wait) = some ⟨5181,.wait (waitLoc l g stage 5) phase true true .cta⟩ ∧
      0 < visit ∧ visit < Mma.trips p batch co.1 ∧
      At u (biasBodyStart true+4*biasBodyPairs true) [] ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop pos) none ∧
      (∀ i ∈ biasBodyItems true,
        u.regs i.result = some (.pair
          (scoreValue (logit (2*(i.qk-7367))))
          (scoreValue (logit (2*(i.qk-7367)+1))))) ∧
      start+4 ≤ wait ∧
      ((X.tr g).take wait).countP earlyProbabilityMark =
        ((X.tr g).take start).countP earlyProbabilityMark ∧
      (∀ k e, start ≤ k → k < wait → X.get (g,k) = some e → e.pc < 5189) ∧
      ∃ pre, pre.pc = 5181 ∧ Stops kernel Assumptions.all l g pre ∧
        TraceReach kernel Assumptions.all l g {} ((X.tr g).take wait) pre ∧
        TraceReach kernel Assumptions.all l g pre (((X.tr g).drop wait).take (pos-wait)) u ∧
        ∀ r, r ∉ [9755,4166,4167,4168,4169,4170] →
          (∀ i, biasVectorKeeps true i r) → r ∉ biasFenceWritten true →
          r ∉ (biasBodyItems true).flatMap BiasAffineItem.writes →
          u.regs r = pre.regs r := by
  obtain ⟨w,hw,wait,phase,t,values,hwBefore,hWait,hVisit,hTrips,hBudget,ht,hScale,hBias,
      hLoads,hPacked,hRun,hEarly,hRegion,pre,hPc,hStop,hRoot,hPath,hKeep⟩ :=
    observedBiasedAffineInputsWithPath hp hX hFrame hCuQ he hExit hLast hb hLo hHi hBytes
  let stage := stageOf w
  have hStage : stage.val = warpIndex l g/4 := by rw [← hw]; rfl
  let co := assignedCoordinates p batch (g/l.block)
  have hLive : 256*co.1+128*stage.val+(g%l.block)%128 < p.qLength batch := by
    rw [hStage]
    exact hRow
  obtain ⟨u,hu,hLocal,hFrame,hLogits⟩ :=
    laterBiasBodyLocalFromObservedWords hp stage hb (assignedCoordinates_valid hp hLo hHi).2
      hLive hVisit hTrips hBudget ht hScale hBias values hPacked
      (hDot stage wait phase values hWait (fun q => (hLoads q).2) hEarly)
  refine ⟨stage,hStage,wait,phase,u,hWait,hVisit,hTrips,hu,hRun.after_local hLocal,
    hLogits,hwBefore,by simpa only [Fin.val_zero,Nat.add_zero] using hEarly 0,
    hRegion,pre,hPc,hStop,hRoot,?_,?_⟩
  · simpa only [List.append_nil] using hPath.append (TraceReach.of_local hLocal)
  · intro r hBefore hVector hFence hBody
    exact (hFrame r hBody).trans (hKeep r hBefore hVector hFence)

end
end PTX.Kernels.TmlFa4Fwd.Softmax
