-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxPlainIteration
public import Kernels.TmlFa4Fwd.Proof.SoftmaxTerminalNumerics
public import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedProbabilityPublication
public import Kernels.TmlFa4Fwd.Proof.Thread.DenominatorVisitRank

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof PTX.Numeric Epilogue Prologue Thread Thread.Scores

noncomputable section

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hFrame : OutputFootprint p X) (warp : Fin 8)
    {g j last pc batch visited : Nat} {t : TState} (hWarp : warp.val = warpIndex l g)
    (old : Option ℝ) (phase scorePhase : Bool) (word : Nat) (hWord : word < 2^32)
    (refs : Nat → Option ℝ) (sums : Nat → ℝ)
    (hPrefix : let co := assignedCoordinates p batch (g/l.block)
      let row := 256*co.1+128*(stageOf warp).val+(g%l.block)%128
      SoftmaxSumPrefix p batch co.2 row (Mma.trips p batch co.1) visited refs sums)
    (hVisited : 0 < visited)
    (hReference : refs (visited-1) = old.map (abiFloat p.scaleLog2Bits * ·))
    (hCount : probabilityOrdinal l X (g/l.block) (stageOf warp) 0 (g,j) = visited)
    (ht : At t 6661 ((1062,b32 warp.val)::(2535,b32 l.sharedBase)::
      (7253,b32 scorePhase.toNat)::
        plainIterationInputs p warp old (sums (visited-1)) phase word))
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) none)
    (hExit : X.get (g,last) = some ⟨pc,.exit⟩) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hRow : let tile := (assignedCoordinates p batch (g/l.block)).1
      256*tile+128*(warpIndex l g/4)+(g%l.block)%128 < p.qLength batch)
include hp hX hFrame warp hWarp old phase scorePhase word hWord refs sums hPrefix hVisited
    hReference hCount ht hRun hExit hb hLo hHi hRow

/-- An actual plain iteration extends the denominator recurrence and exposes the
coefficient and probabilities for the same descending visit. -/
theorem plainDenominatorVisitOfHeadWithPath :
    let stage := stageOf warp
    let co := assignedCoordinates p batch (g/l.block)
    let row := 256*co.1+128*stage.val+(g%l.block)%128
    let blocks := Mma.trips p batch co.1
    let scale := abiFloat p.scaleLog2Bits
    ∃ u endPos storePos candidate mass,
      let chosen := chosenReference scale old candidate
      let ref := chosen.map (scale * ·)
      let weights := fun col => shiftedWeight p batch co.2 row (visitKey blocks visited col)
        (ref.getD 0)
      let events := Repeated.probabilityEvents .unbiased l g stage weights
      let site := scoreLoopSite .plain
      let nextWord := (word+1)%2^32
      j ≤ storePos ∧ storePos+2+events.length < endPos ∧
      SoftmaxSumPrefix p batch co.2 row blocks (visited+1)
        (Function.update refs visited ref) (Function.update sums visited mass) ∧
      X.get (g,storePos) =
        some ⟨6890,.wr (statsAcc l g warp 1) (alphaWord scale old candidate).toBytes⟩ ∧
      (∀ k : Fin events.length, X.get (g,storePos+2+k.val) = events[k.val]?) ∧
      ObservedProbabilityTile l X g stage visited weights ∧
      At u (if nextWord ≠ site.sentinel then site.head else site.increment+4)
        ([(site.word,b32 nextWord),(roundPriorMaxReg .plain,scoreValue chosen),
          (7256,scoreValue chosen),(7257,fl mass),(7258,b32 (!phase).toNat)] ++
          tailPhaseWords true (!scorePhase) .plain) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop endPos) none ∧
      TraceReach kernel Assumptions.all l g t (((X.tr g).drop j).take (endPos-j)) u ∧
      ((X.tr g).take endPos).countP earlyProbabilityMark =
        ((X.tr g).take storePos).countP earlyProbabilityMark + 1 ∧
      probabilityOrdinal l X (g/l.block) stage 0 (g,storePos) = visited ∧
      probabilityOrdinal l X (g/l.block) stage 0 (g,endPos) = visited+1 := by
  obtain ⟨failed,candidate,u,endPos,bar,hVisit,hCandidate,hStore,_,hEvents,hBar,_,_,hPolls,
      hBefore,hAt,hTail,hPath,hEarly,hOrdinal⟩ :=
    plainRoundFromHeadOfFootprintWithPath hp hX hFrame (hFrame.metadataProtected hp).1 warp hWarp
      old (sums (visited-1)) phase scorePhase word hWord ht hRun hExit hb hLo hHi hRow
  have hActual := hVisit.trans hCount
  change probabilityOrdinal l X (g/l.block) (stageOf warp) 0 (g,j+failed+1) = visited at hActual
  simp only [hActual] at hCandidate hBar hPolls hBefore hAt
  have hCandidateZero :=
    ((hCandidate (scoreReal candidate)).mp le_rfl).2 0 (by decide)
  let co := assignedCoordinates p batch (g/l.block)
  let row := 256*co.1+128*(stageOf warp).val+(g%l.block)%128
  let blocks := Mma.trips p batch co.1
  let scale := abiFloat p.scaleLog2Bits
  let ref := (chosenReference scale old candidate).map (scale * ·)
  let mass := sums (visited-1)*maskedRescale (old.map (scale * ·)) ref +
    (2 : ℝ)^(-ref.getD 0)*maskedBlockSum (p.keyCount batch row) blocks visited
      (weight p batch co.2 row)
  let weights := fun col => shiftedWeight p batch co.2 row (visitKey blocks visited col)
    (ref.getD 0)
  have hEq : Repeated.unbiased.probabilityEvents l g (stageOf warp)
      (fun col => shiftedWeight p batch co.2 row
        (visitKey blocks (probabilityOrdinal l X (g/l.block) (stageOf warp) 0
          (g,j+failed+1)) col) (ref.getD 0)) =
      Repeated.unbiased.probabilityEvents l g (stageOf warp) weights := by
    rw [hActual]
  change (∀ k : Fin _, X.get (g,j+failed+1+8+2+k.val) = _[k.val]?) at hEvents
  rw [hEq] at hEvents
  have hR : u.regs 7257 = some (fl mass) := by
    exact holds_mem hAt.2.2.2.2 (by simp [mass,ref,scale,co,row,blocks])
  have hNext := appendRepeatedSum hPrefix hVisited old candidate hCandidateZero mass
    (by simp only [mass, hReference]; rfl) hR
  have hStage : warpIndex l g/4 = (stageOf warp).val := by rw [← hWarp]; rfl
  have hTile := Repeated.observedProbabilityTile (inst := bar) hp hX .unbiased (stageOf warp)
    hStage (weights := weights) hEvents hBar hPolls
  refine ⟨u,endPos,j+failed+1+8,candidate,mass,by omega,hBefore,hNext.1,hStore,hEvents,
    hTile,hAt,hTail,hPath,hEarly,hOrdinal.trans hActual,?_⟩
  exact (probabilityRankOfRepeatedVisit hp hX _ (hWarp ▸ warp.isLt) hStage
    (len_of_get hStore) hTail hEarly).trans (congrArg (·+1) (hOrdinal.trans hActual))

end

end PTX.Kernels.TmlFa4Fwd.Softmax
