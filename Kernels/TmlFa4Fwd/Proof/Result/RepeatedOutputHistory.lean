-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Result.RepeatedWriteback
public import Kernels.TmlFa4Fwd.Proof.Protocol.CompletedRepeatedRow
import Kernels.TmlFa4Fwd.Proof.Protocol.RescalePublicationValues
import Kernels.TmlFa4Fwd.Proof.Safety.MmaOperandCoverage
import Kernels.TmlFa4Fwd.Proof.Protocol.RepeatedProbabilityHistory
import Kernels.TmlFa4Fwd.Proof.Thread.RescaleStatisticsPublication
import Lemmas.Flow.MemTmpl

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Result
open PTX PTX.Numeric Thread Thread.Correction Thread.Scores Softmax Epilogue
open Protocol.Scores (probabilityProducer)
open _root_.PTX.Kernels.TmlFa4Fwd.Mma (trips)

noncomputable section

/-- The actual packed probabilities, rescale coefficients and terminal statistics
that belong to one logical row's scalar softmax recurrence. -/
structure SoftmaxRowVisits (p : Params) (l : Launch) (X : Execution)
    (correction batch : Nat) (stage : Fin 2) where
  reference : Nat → Option ℝ
  sum : Nat → ℝ
  recurrence :
    let coords := assignedCoordinates p batch (correction/l.block)
    let row := stageRow coords.1 stage + TmlFa4Fwd.Correction.rowOf l correction
    SoftmaxSumRun p batch coords.2 row (trips p batch coords.1) reference sum
  probabilities :
    let coords := assignedCoordinates p batch (correction/l.block)
    let row := stageRow coords.1 stage + TmlFa4Fwd.Correction.rowOf l correction
    let blocks := trips p batch coords.1
    let producer := TmlFa4Fwd.Correction.terminalStatsProducer l correction stage
    ∀ visit < blocks, ObservedProbabilityTile l X producer stage visit (fun k =>
      shiftedWeight p batch coords.2 row (visitKey blocks visit k) ((reference visit).getD 0))
  coefficient :
    let coords := assignedCoordinates p batch (correction/l.block)
    let producer := TmlFa4Fwd.Correction.terminalStatsProducer l correction stage
    ∀ {pos : Nat} {biased : Bool} {a : Acc} {data : List Byte}
        {word : Value} {alpha : ℝ} {visit : Nat},
      0 < visit → visit < trips p batch coords.1 →
      StatisticsStore X (producer,pos) (Softmax.rescaleStore biased) a data →
      (Thread.Scores.before X (producer,pos)).notices = visit →
      data = word.toBytes → RescaleFactorWord word alpha →
      alpha = maskedRescale (reference (visit-1)) (reference visit)
  terminal :
    let blocks := trips p batch (assignedCoordinates p batch (correction/l.block)).1
    ∀ pos, CorrectionWaits X (correction,pos) .terminal stage →
      pos+1 < (X.tr correction).length →
      ∃ pub maximum,
        TerminalPublishedWords l X correction stage pub
          (.float .f32 (sum (blocks-1))) (.float .f32 maximum) ∧
        TerminalGeneration l X correction stage (pub-2) pos

/-- A recorded coefficient for each positive visit identifies every possible
read of the same generation, independent of the chosen arithmetic branch. -/
theorem SoftmaxRowVisits.ofRecorded {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hX : Consistent l kernel Assumptions.all m X)
    {g batch : Nat} (stage : Fin 2) (reference : Nat → Option ℝ) (sums : Nat → ℝ) :
    let coords := assignedCoordinates p batch (g/l.block)
    let row := stageRow coords.1 stage + TmlFa4Fwd.Correction.rowOf l g
    let blocks := trips p batch coords.1
    let producer := TmlFa4Fwd.Correction.terminalStatsProducer l g stage
    SoftmaxSumRun p batch coords.2 row blocks reference sums →
    (∀ visit < blocks, ObservedProbabilityTile l X producer stage visit (fun k =>
      shiftedWeight p batch coords.2 row (visitKey blocks visit k) ((reference visit).getD 0))) →
    (∀ visit, 0 < visit → visit < blocks →
      ∃ pos biased a word,
        StatisticsStore X (producer,pos) (Softmax.rescaleStore biased) a word.toBytes ∧
        (Thread.Scores.before X (producer,pos)).notices = visit ∧
        RescaleFactorWord word (maskedRescale (reference (visit-1)) (reference visit))) →
    (∀ pos, CorrectionWaits X (g,pos) .terminal stage → pos+1 < (X.tr g).length →
      ∃ pub maximum,
        TerminalPublishedWords l X g stage pub (.float .f32 (sums (blocks-1)))
          (.float .f32 maximum) ∧ TerminalGeneration l X g stage (pub-2) pos) →
    Nonempty (SoftmaxRowVisits p l X g batch stage) := by
  dsimp only
  intro hRecurrence hTiles hRecorded hTerminal
  refine ⟨⟨reference,sums,hRecurrence,hTiles,?_,hTerminal⟩⟩
  dsimp only
  intro pos biased a data word alpha visit hPos hBound hStore hRank hData hWord
  obtain ⟨recorded,recordedBias,recordedAccess,recordedWord,hRecordedStore,hRecordedRank,hFactor⟩ :=
    hRecorded visit hPos hBound
  have hOrdinal := hRecordedRank.trans hRank.symm
  have hBytes := (rescaleStoreUniqueOfNotice hX hRecordedStore hStore hOrdinal).2
  have hActual := PTX.Proof.rebuild_scalar (v := word) (by rw [hWord.width]; decide) hWord.head
  have hChosen := PTX.Proof.rebuild_scalar (v := recordedWord)
    (by rw [hFactor.width]; decide) hFactor.head
  rw [← hData,hBytes,hChosen] at hActual
  have hSame := hFactor.value
  rw [Except.ok.inj hActual,hWord.value] at hSame
  exact Except.ok.inj hSame

/-- Completed scalar softmax histories suffice for all repeated output bytes.
The actual PV carry, selected V inputs and final writeback are derived. -/
theorem repeatedOutputValuesOfSoftmaxVisits {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hDone : Complete l X)
    (hFootprint : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y)
    (hVisits : ∀ g < l.threads, 8 ≤ Prologue.warpIndex l g → Prologue.warpIndex l g < 12 →
      ∀ (stage : Fin 2) (batch : Nat), batch < p.batch →
        let coords := assignedCoordinates p batch (g/l.block)
        tilePrefix p batch*p.heads ≤ g/l.block →
        g/l.block < tilePrefix p (batch+1)*p.heads →
        trips p batch coords.1 ≠ 1 →
        stageRow coords.1 stage+TmlFa4Fwd.Correction.rowOf l g < p.qLength batch →
        Nonempty (SoftmaxRowVisits p l X g batch stage)) :
    RepeatedOutputValues p X := by
  have hOperands := Safety.mmaOperandsOfProbabilities hp hX (hFootprint X hX)
    (Protocol.Scores.completedPvProbabilitiesOfExecution hp hX hFootprint)
  have hStats := Protocol.Statistics.rescaleStoreValuesOfOutputFootprint hp hX hFootprint
  apply repeatedOutputValuesOfHistories hp hX hDone hFootprint
  dsimp only
  intro g hg hLoWarp hHiWarp stage batch hb hLo hHi hRepeat hRow
  obtain ⟨history⟩ := hVisits g hg hLoWarp hHiWarp stage batch hb hLo hHi hRepeat hRow
  let coords := assignedCoordinates p batch (g/l.block)
  have hCover : p.keyCount batch (stageRow coords.1 stage + TmlFa4Fwd.Correction.rowOf l g) ≤
      128 * trips p batch coords.1 := by
    apply p.keyCount_le_kvBlocks
    have hr : TmlFa4Fwd.Correction.rowOf l g < 128 := Nat.mod_lt _ (by decide)
    have hs := stage.isLt
    unfold stageRow
    omega
  have hBlocks : 0 < trips p batch coords.1 := by
    have hPos : 0 < p.keyCount batch (stageRow coords.1 stage +
        TmlFa4Fwd.Correction.rowOf l g) := hp.keyCount_pos hb hRow
    omega
  apply Protocol.repeatedRowHistoryOfCompletedSoftmax hp hX hDone hFootprint hOperands hStats
    stage hg ⟨hLoWarp,hHiWarp⟩ hb hLo hHi history.reference history.sum hBlocks history.recurrence
    history.probabilities history.terminal
  dsimp only
  intro writer pos biased a data word alpha n hPositive hRank hCta hRowEq
    hStore hNotice hBytes hWord
  have hLocal : TmlFa4Fwd.Correction.rowOf l writer.1 = TmlFa4Fwd.Correction.rowOf l g := by
    change laneBase l writer.1+laneOf l writer.1 = TmlFa4Fwd.Correction.rowOf l g at hRowEq
    unfold laneBase laneOf at hRowEq
    unfold TmlFa4Fwd.Correction.rowOf at hRowEq ⊢
    omega
  have hLane : TmlFa4Fwd.Correction.terminalStatsProducer l writer.1 stage =
      TmlFa4Fwd.Correction.terminalStatsProducer l g stage := by
    unfold TmlFa4Fwd.Correction.terminalStatsProducer
    rw [hCta,hLocal]
  rw [hLane] at hStore hNotice
  exact history.coefficient hPositive hRank hStore hNotice hBytes hWord

end
end PTX.Kernels.TmlFa4Fwd.Result
