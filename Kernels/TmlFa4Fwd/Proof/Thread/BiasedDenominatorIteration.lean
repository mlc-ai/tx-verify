-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.BiasedDenominatorEntry
public import Kernels.TmlFa4Fwd.Proof.Thread.BiasedDenominatorVisit
public import Kernels.TmlFa4Fwd.Proof.Thread.DenominatorVisitRank

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof PTX.Numeric Prologue Epilogue Thread.Scores

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hFrame : OutputFootprint p X) (warp : Fin 8)
    {g j last pc batch visited : Nat} {t : TState} (hWarp : warp.val = warpIndex l g)
    (old : Option ℝ) (phase biasPhase scorePhase : Bool) (word block floor : Nat)
    (hWord : word < 2^32) (hBlock : block < 2^32) (refs : Nat → Option ℝ) (sums : Nat → ℝ)
    (hPrefix : let co := assignedCoordinates p batch (g/l.block)
      let row := 256*co.1+128*(stageOf warp).val+(g%l.block)%128
      SoftmaxSumPrefix p batch co.2 row (Mma.trips p batch co.1) visited refs sums)
    (hReference : refs (visited-1) = old.map (abiFloat p.scaleLog2Bits * ·))
    (hCount : probabilityOrdinal l X (g/l.block) (stageOf warp) 0 (g,j) = visited)
    (ht : At t 5032
      [(7249,b32 block),(7251,scoreValue old),(7257,fl (sums (visited-1))),
        (1361,b32 floor),(7258,b32 phase.toNat),(1062,b32 warp.val),(2535,b32 l.sharedBase),
        (5127,b32 (3+warp.val)),(1230,fl (-abiFloat p.scaleLog2Bits)),(7132,b32 p.scaleLog2Bits),
        (7250,b32 biasPhase.toNat),(7253,b32 scorePhase.toNat),(7248,b32 word)])
    (hReach : TraceReach kernel Assumptions.all l g {} ((X.tr g).take j) t)
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) none)
    (hExit : X.get (g,last) = some ⟨pc,.exit⟩) (hLast : j ≤ last) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hRow : let co := assignedCoordinates p batch (g/l.block)
      256*co.1+128*(warpIndex l g/4)+(g%l.block)%128 < p.qLength batch)
include hp hX hFrame warp hWarp old phase biasPhase scorePhase word block floor hWord hBlock refs
    sums hPrefix hReference hCount ht hReach hRun hExit hLast hb hLo hHi hRow

/-- One recorded biased loop iteration updates the running denominator and
writes both the coefficient and the probabilities for the matching score visit. -/
theorem biasedDenominatorVisitOfHeadWithPath :
    let stage := stageOf warp
    let co := assignedCoordinates p batch (g/l.block)
    let row := 256*co.1+128*stage.val+(g%l.block)%128
    let blocks := Mma.trips p batch co.1
    let scale := abiFloat p.scaleLog2Bits
    ∃ u endPos storePos candidate mass bar,
      let chosen := chosenReference scale old candidate
      let ref := chosen.map (scale * ·)
      let weights := fun col => shiftedWeight p batch co.2 row (visitKey blocks visited col)
        (ref.getD 0)
      let events := Repeated.probabilityEvents .biased l g stage weights
      let site := scoreLoopSite .biased
      let nextWord := (word+1)%2^32
      j < storePos ∧ storePos+2+events.length < endPos ∧
      SoftmaxSumPrefix p batch co.2 row blocks (visited+1)
        (Function.update refs visited ref) (Function.update sums visited mass) ∧
      StatisticsStore X (g,storePos) (rescaleStore true) (statsAcc l g warp 0)
        (alphaWord scale old candidate).toBytes ∧
      (∀ k : Fin events.length, X.get (g,storePos+2+k.val) = events[k.val]?) ∧
      At u (if nextWord ≠ site.sentinel then site.head else site.increment+4)
        ([(site.word,b32 nextWord),(roundPriorMaxReg .biased,scoreValue chosen),
          (7256,scoreValue chosen),(7257,fl mass),(7258,b32 (!phase).toNat)] ++
          tailPhaseWords (!biasPhase) (!scorePhase) .biased) ∧
      X.get (g,storePos+2+events.length+1) =
        some ⟨probabilityWaitPc .biased true+1,.warpBar (2^32-1) bar⟩ ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop endPos) none ∧
      TraceReach kernel Assumptions.all l g {} ((X.tr g).take endPos) u ∧
      ((X.tr g).take endPos).countP earlyProbabilityMark =
        ((X.tr g).take storePos).countP earlyProbabilityMark + 1 ∧
      probabilityOrdinal l X (g/l.block) stage 0 (g,storePos) = visited ∧
      probabilityOrdinal l X (g/l.block) stage 0 (g,endPos) = visited+1 ∧
      u.regs 7249 = some (b32 ((block+(2^32-1))%2^32)) := by
  obtain ⟨stage,hStage,pos,cursor,hPos,hVisit,hTrips,hAt,hPath,hTail,hLogits,hKeep,hDecrement,
    hOrdinal⟩ :=
    biasedDenominatorEntryOfHeadWithOrdinal hp hX hFrame (ht.mono trivial) hReach hRun hExit hLast
      hb hLo hHi hRow
  have hs : stage = stageOf warp := Fin.ext (by rw [hStage,← hWarp]; rfl)
  subst stage
  simp only [hCount] at hVisit hLogits
  obtain ⟨hB,hOld,hMass,hFloor,hPhase,hWarpReg,hBase,hStats,hNeg,hScale,
    hBias,hScore,hCounter,_⟩ := ht.2.2.2.2
  let nextBlock := (block+(2^32-1))%2^32
  have hBlockReg : cursor.regs 7249 = some (b32 nextBlock) := hDecrement block hBlock hB
  obtain ⟨u,endPos,candidate,mass,bar,hEnd,hNext,hCoeff,hProbability,hState,hBar,hRun,hAfter,
    hEarly,hBlockOut⟩ :=
    biasedDenominatorVisitOfLogitsWithPath hp warp hWarp old nextBlock floor phase biasPhase
      scorePhase
      refs sums hPrefix hVisit hReference hAt hLogits
      ⟨(hKeep 7251 (by decide)).trans hOld,(hKeep 7257 (by decide)).trans hMass,
        hBlockReg,(hKeep 1361 (by decide)).trans hFloor,(hKeep 7258 (by decide)).trans hPhase,
        (hKeep 1062 (by decide)).trans hWarpReg,(hKeep 2535 (by decide)).trans hBase,
        (hKeep 5127 (by decide)).trans hStats,(hKeep 1230 (by decide)).trans hNeg,
        (hKeep 7132 (by decide)).trans hScale,trivial⟩
      word hWord ⟨(hKeep 7250 (by decide)).trans hBias,(hKeep 7253 (by decide)).trans hScore,
        (hKeep 7248 (by decide)).trans hCounter,trivial⟩ hTail
  have hOrder : pos ≤ endPos := by omega
  have hJoin := hPath.append hAfter
  rw [← List.take_add,Nat.add_sub_of_le hOrder] at hJoin
  refine ⟨u,endPos,pos,candidate,mass,bar,hPos,hEnd,hNext,hCoeff,hProbability,hState,hBar,hRun,
    hJoin,hEarly,hOrdinal.trans hCount,?_,hBlockOut⟩
  have hS : warpIndex l g/4 = (stageOf warp).val := by rw [← hWarp]; rfl
  exact (probabilityRankOfRepeatedVisit hp hX _ (hWarp ▸ warp.isLt) hS
    (len_of_get hCoeff) hRun hEarly).trans (congrArg (·+1) (hOrdinal.trans hCount))

end PTX.Kernels.TmlFa4Fwd.Softmax
