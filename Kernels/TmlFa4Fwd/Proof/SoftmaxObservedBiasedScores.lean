-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasedScoreBank
import Kernels.TmlFa4Fwd.Proof.SoftmaxObservedBiasedInputs
public import Kernels.TmlFa4Fwd.Proof.SoftmaxRecurringScoreValue
import Kernels.TmlFa4Fwd.Proof.Protocol.CompetingCacheWrites
import Kernels.TmlFa4Fwd.Proof.Thread.AllScoreLoadWords
import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxProbabilityGate

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow PTX.TcMma PTX.AsyncCopy
open Prologue Epilogue Thread Thread.Scores Thread.Loader Protocol.LoaderReady

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
    {g start last pc batch : Nat} {addr : Nat} {words : List Value} {shape : TcShape}
    (he : X.get (g,start) = some ⟨scorePc .biased 0,.tc (.ld addr words shape)⟩)
    (hExit : X.get (g,last) = some ⟨pc,.exit⟩) (hLast : start < last) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hRow : let co := assignedCoordinates p batch (g/l.block)
      256*co.1+128*(warpIndex l g/4)+(g%l.block)%128 < p.qLength batch)
include hp hX hFrame he hExit hLast hb hLo hHi hRow

/-- A live lane's actual biased scores are the masked launch-input logits of
the visit identified by its observed Bias wait. -/
theorem observedBiasedAffineScoresOfFootprintWithPath :
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
      probabilityOrdinal l X (g/l.block) stage 0 (g,start) = visit ∧
      (∀ k e, start ≤ k → k < wait → X.get (g,k) = some e → e.pc < 5189) ∧
      ∃ pre, pre.pc = 5181 ∧ Stops kernel Assumptions.all l g pre ∧
        TraceReach kernel Assumptions.all l g {} ((X.tr g).take wait) pre ∧
        TraceReach kernel Assumptions.all l g pre (((X.tr g).drop wait).take (pos-wait)) u ∧
        ∀ r, r ∉ [9755,4166,4167,4168,4169,4170] →
          (∀ i, biasVectorKeeps true i r) → r ∉ biasFenceWritten true →
          r ∉ (biasBodyItems true).flatMap BiasAffineItem.writes →
          u.regs r = pre.regs r := by
  let hCuQ := (hFrame.metadataProtected hp).1
  have hWord (stage : Fin 2) (q : Fin 4) (k : Fin 32) {xs : List Value}
      (hLoad : X.get (g,start+q.val) =
        some ⟨scorePc .biased q,.tc (.ld (scoreAddress l g stage q) xs .s32x32b)⟩) :
      warpIndex l g < 8 ∧ warpIndex l g/4 = stage.val ∧
      let co := assignedCoordinates p batch (g/l.block)
      let visit := probabilityOrdinal l X (g/l.block) stage 0 (g,start+q.val)
      xs[k.val]? = some (.float .f32
        (firstScoreDot p l g batch co.2 (p.qOffset batch+256*co.1+128*stage.val)
          (128*(Mma.trips p batch co.1-1-visit)) q k)) := by
    obtain ⟨hWarp,hStage,_,_⟩ := observedBiasedScoreBank hp hX hCuQ stage q k hLoad
    obtain ⟨other, b',hOther,hB',hLo',hHi',hValue⟩ :=
      scoreLoadWordsOfLaunch hp hX hFrame .biased q hLoad
    have hStageEq : other = stage := Fin.ext (hOther.symm.trans hStage)
    subst other
    have hBatch : b' = batch := by
      obtain ⟨chosen,_,hUnique⟩ := tileBatch_existsUnique p
        (hHi.trans_le (Nat.mul_le_mul_right _ (tilePrefix_mono p (by omega))))
      exact (hUnique b' ⟨hB',hLo',hHi'⟩).trans (hUnique batch ⟨hb,hLo,hHi⟩).symm
    subst b'
    exact ⟨hWarp,hStage,hValue k⟩
  have hBytes (stage : Fin 2) (q : Fin 4) (xs : List Value)
      (hLoad : X.get (g,start+q.val) =
        some ⟨scorePc .biased q,.tc (.ld (scoreAddress l g stage q) xs .s32x32b)⟩)
      (k : Nat) (hK : k < 32) : (xs.getD k (b32 0)).bytes = 4 := by
    obtain ⟨_,_,hVal⟩ := hWord stage q ⟨k,hK⟩ hLoad
    dsimp only at hVal
    simp [List.getD,hVal,Value.bytes,FloatFmt.bytes]
  have hDots (stage : Fin 2) (wait phase : Nat) (values : Fin 4 → List Value)
      (hWait : X.get (g,wait) =
        some ⟨5181,.wait (waitLoc l g stage 5) phase true true .cta⟩)
      (hLoads : ∀ q : Fin 4, X.get (g,start+q.val) =
        some ⟨scorePc .biased q,.tc (.ld (scoreAddress l g stage q) (values q) .s32x32b)⟩)
      (hSame : ∀ q : Fin 4, ((X.tr g).take wait).countP earlyProbabilityMark =
        ((X.tr g).take (start+q.val)).countP earlyProbabilityMark)
      (q : Fin 4) (k : Fin 32) :
      let co := assignedCoordinates p batch (g/l.block)
      let visit := observedBarrierOrdinal X (g,wait) (11+stage.val)
      (values q)[k.val]? = some (.float .f32
        (firstScoreDot p l g batch co.2 (p.qOffset batch+256*co.1+128*stage.val)
          (128*(Mma.trips p batch co.1-1-visit)) q k)) := by
    obtain ⟨hWarp,hStage,hValue⟩ := hWord stage q k (hLoads q)
    have hRank := biasedVisitEqualsProbabilityOrdinal hp hX stage hWarp hStage hWait
    have hCountLoad := earlyProbabilityCount hp hX stage hWarp hStage (len_of_get (hLoads q))
    have hCountWait := earlyProbabilityCount hp hX stage hWarp hStage (len_of_get hWait)
    have hSameRank := hCountLoad.symm.trans ((hSame q).symm.trans hCountWait)
    dsimp only at hValue
    rw [hSameRank,← hRank] at hValue
    exact hValue
  obtain ⟨stage,hStage,wait,phase,u,hWait,hVisit,hTrips,hu,hTail,hLogits,
      hBefore,hLedger,hRegion,hPath⟩ :=
    observedBiasedAffineScoresOfDotsWithPath hp hX hFrame hCuQ he hExit hLast hb hLo hHi hRow
      hBytes hDots
  have hWarp : warpIndex l g < 8 := by have := stage.isLt; omega
  have hRank := biasedVisitEqualsProbabilityOrdinal hp hX stage hWarp hStage.symm hWait
  have hOpen := earlyProbabilityCount hp hX stage hWarp hStage.symm (len_of_get he)
  have hBias := earlyProbabilityCount hp hX stage hWarp hStage.symm (len_of_get hWait)
  have hCount := hOpen.symm.trans (hLedger.symm.trans (hBias.trans hRank.symm))
  exact ⟨stage,hStage,wait,phase,u,hWait,hVisit,hTrips,hu,hTail,hLogits,
    hBefore,hCount,hRegion,hPath⟩

end

end PTX.Kernels.TmlFa4Fwd.Softmax
