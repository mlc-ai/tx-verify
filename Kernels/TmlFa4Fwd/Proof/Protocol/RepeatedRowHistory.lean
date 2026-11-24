-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.PvNumeratorHistory
public import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedNormalizedRow

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol
open PTX PTX.TcMma Thread Thread.Correction Thread.Scores Thread.Mma
open Scores (probabilityProducer)
open Epilogue (assignedCoordinates stageRow)
open PTX.Numeric PTX.Flow Softmax
open _root_.PTX.Kernels.TmlFa4Fwd.Mma

noncomputable section

/-- The score-side recurrence determines the numerator of the completed last V
visit, using the coefficients and packed probabilities of the same row. -/
theorem repeatedRowHistoryOfSoftmax {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) (hCuQ : Epilogue.DrainCuQProtected p X)
    (hOperands : Safety.CompletedMmaOperandsAreBf16 X)
    (hStats : Statistics.RescaleStoreValuesAreF32 X)
    {g batch : Nat} (stage : Fin 2) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (ref : Nat → Option ℝ) (sums : Nat → ℝ) :
    let coords := assignedCoordinates p batch (g/l.block)
    let row : Fin 128 := ⟨TmlFa4Fwd.Correction.rowOf l g,Nat.mod_lt _ (by decide)⟩
    let qrow := stageRow coords.1 stage+row.val
    let blocks := trips p batch coords.1
    let producer := probabilityProducer l (g/l.block) stage row.val
    let cell := fun (col : Fin 128) => ⟨g/l.block,row.val,outputColumn stage+col.val⟩
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
    (∀ {source index use : Nat} {block : Fin 4} {col : Fin 128},
      source/l.block = g/l.block →
      (v : PvVisit l X source block use row col index) →
      (pvSite block).stage = stage → v.keep = true → use/2 < blocks →
      ∀ {prior d op accum mask},
      PvInstruction X (source,prior) (firstPvBlock true stage) 7 d op accum mask →
      LatestValueReadyUse l X source prior (use-2) →
      ReadSource l X .acc (source,prior) (source,v.issues 0) (cell col) →
      maskedRescale (ref (use/2-1)) (ref (use/2)) = 1) →
    Nonempty (RepeatedRowHistory p l X g batch stage) := by
  dsimp only
  intro hBlocks hSum hTiles hTerminal hFactors hDirect
  let coords := assignedCoordinates p batch (g/l.block)
  let row : Fin 128 := ⟨TmlFa4Fwd.Correction.rowOf l g,Nat.mod_lt _ (by decide)⟩
  let qrow := stageRow coords.1 stage+row.val
  let blocks := trips p batch coords.1
  change 0 < blocks at hBlocks
  let acc := shiftedNumerator p batch coords.2 qrow blocks ref
  let run : SoftmaxRun p batch coords.2 qrow blocks ref sums acc := softmaxRunOfObservedSums hSum
  refine ⟨⟨ref,sums,acc,run,hTerminal,?_⟩⟩
  dsimp only
  intro col source hOwner hDone hPv
  obtain ⟨issuer,index⟩ := source
  have hCta : issuer/l.block = g/l.block := hOwner
  have hStage : (pvSite (firstPvBlock false stage)).stage = stage := by fin_cases stage <;> rfl
  have hRank : (2*blocks-1)/2 = blocks-1 := by omega
  have hValue := recordedPvNumeratorOfTiles hp hX hFrame hCuQ stage row col hb
    (hCta.symm ▸ hLo) (hCta.symm ▸ hHi) hOperands hStats ref sums acc
  simp only [hCta] at hValue
  exact hRank ▸ hValue run hTiles (hDirect hCta)
    (fun hPositive hVisited hC hR hPub hVisit hBytes hWord =>
      hFactors hPositive hVisited hC hR hPub hVisit hBytes hWord)
    hPv hStage (by change (2*blocks-1)/2 < blocks; omega) hDone

end
end PTX.Kernels.TmlFa4Fwd.Protocol
