-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.RepeatedRowHistory
public import Kernels.TmlFa4Fwd.Proof.Protocol.PvDirectCarryValues

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol
open PTX PTX.Numeric PTX.TcMma Thread Thread.Correction Thread.Scores Thread.Mma Softmax
open Scores (probabilityProducer)
open Epilogue (assignedCoordinates stageRow)
open _root_.PTX.Kernels.TmlFa4Fwd.Mma

noncomputable section

/-- The exact probabilities, coefficients and denominator from one softmax history
determine the row of a completed work item. Both physical carry paths are derived. -/
theorem repeatedRowHistoryOfCompletedSoftmax {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hDone : Complete l X)
    (hFrame : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y)
    (hOperands : Safety.CompletedMmaOperandsAreBf16 X)
    (hStats : Statistics.RescaleStoreValuesAreF32 X)
    {g batch : Nat} (stage : Fin 2) (hg : g < l.threads)
    (hWarp : 8 ≤ Prologue.warpIndex l g ∧ Prologue.warpIndex l g < 12)
    (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (ref : Nat → Option ℝ) (sums : Nat → ℝ) :
    let coords := assignedCoordinates p batch (g/l.block)
    let row : Fin 128 := ⟨TmlFa4Fwd.Correction.rowOf l g,Nat.mod_lt _ (by decide)⟩
    let qrow := stageRow coords.1 stage+row.val
    let blocks := trips p batch coords.1
    let producer := probabilityProducer l (g/l.block) stage row.val
    0 < blocks →
    SoftmaxSumRun p batch coords.2 qrow blocks ref sums →
    (∀ n < blocks, ObservedProbabilityTile l X producer stage n
      (fun k => shiftedWeight p batch coords.2 qrow (visitKey blocks n k) ((ref n).getD 0))) →
    (∀ pos, CorrectionWaits X (g,pos) .terminal stage → pos+1 < (X.tr g).length →
      ∃ pub maximum,
        TerminalPublishedWords l X g stage pub (.float .f32 (sums (blocks-1)))
          (.float .f32 maximum) ∧ TerminalGeneration l X g stage (pub-2) pos) →
    (∀ {writer : EvId} {pos : Nat} {biased : Bool} {a : Acc} {data : List Byte}
        {word : Value} {α : ℝ} {n : Nat},
      0 < n → n < blocks → writer.1/l.block = g/l.block →
      laneBase l writer.1+laneOf l writer.1 = row.val →
      let owner := TmlFa4Fwd.Correction.terminalStatsProducer l writer.1 stage
      Thread.Scores.StatisticsStore X (owner,pos) (Softmax.rescaleStore biased) a data →
      (Thread.Scores.before X (owner,pos)).notices = n →
      data = word.toBytes → RescaleFactorWord word α →
      α = maskedRescale (ref (n-1)) (ref n)) →
    Nonempty (RepeatedRowHistory p l X g batch stage) := by
  dsimp only
  intro hBlocks hSum hTiles hTerminal hFactors
  have hCuQ := ((hFrame X hX).metadataProtected hp).1
  apply repeatedRowHistoryOfSoftmax hp hX (hFrame X hX) hCuQ hOperands hStats
    stage hb hLo hHi ref sums hBlocks hSum hTiles hTerminal hFactors
  intro source index use block col hOwner visit hStage hKeep hRank
    prior d op accum mask hPrior hUse hSource
  let row : Fin 128 := ⟨TmlFa4Fwd.Correction.rowOf l g,Nat.mod_lt _ (by decide)⟩
  have hRow : laneBase l g+laneOf l g = row.val := by
    unfold row TmlFa4Fwd.Correction.rowOf laneBase laneOf
    change g % l.block / 32 % 4 * 32 + g % l.block % 32 = g % l.block % 128
    omega
  have hPrev := hStage.symm ▸ hPrior
  have hRead : ReadSource l X .acc (source,prior) (source,visit.issues 0)
      ⟨source/l.block,row.val,outputColumn (pvSite block).stage+col.val⟩ := by
    rw [hOwner,hStage]
    exact hSource
  obtain ⟨pos,biased,a,data,word,alpha,hPub,hOrdinal,hBytes,hFactor,hOne⟩ :=
    visit.directFactorOfCompletedCorrection hp hX hDone hFrame hOperands hStats hKeep hg hWarp
      hb hLo hHi hOwner.symm hRow hRank hPrev hUse hRead
  rw [hStage] at hPub hOrdinal
  have hPositive := (visit.keepOfValueUse hp hX).mp hKeep
  have hSemantic := hFactors (writer := (g,0)) hPositive hRank rfl hRow hPub hOrdinal hBytes hFactor
  exact hSemantic.symm.trans hOne

end
end PTX.Kernels.TmlFa4Fwd.Protocol
