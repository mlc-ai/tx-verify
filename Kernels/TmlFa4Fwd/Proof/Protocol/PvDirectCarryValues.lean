-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.PvReferenceFactors
public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionRescaleWaitState
import Kernels.TmlFa4Fwd.Proof.Protocol.RescalePublicationValues
import Lemmas.Flow.MemTmpl

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol
open PTX PTX.Proof PTX.TcMma Thread Thread.Correction Thread.Mma
open _root_.PTX.Kernels.TmlFa4Fwd.Mma

private theorem alphaAtPublication_le_one {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFootprint : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y)
    {g index : Nat} {biased : Bool} {a : Acc} {data : List Byte} {word : Value} {alpha : ℝ}
    (hPub : Thread.Scores.StatisticsStore X (g,index) (Softmax.rescaleStore biased) a data)
    (hBytes : data = word.toBytes) (hWord : RescaleFactorWord word alpha) : alpha ≤ 1 := by
  obtain ⟨_,_,_,_,_,old,candidate,hData⟩ :=
    Thread.Scores.recordedRescaleMaximumAndData hp hX hFootprint biased hPub
  let canonical := Softmax.alphaWord (abiFloat p.scaleLog2Bits) old candidate
  let factor := Softmax.correctionAlpha (abiFloat p.scaleLog2Bits) old candidate
  have hCanonical : RescaleFactorWord canonical factor :=
    Statistics.rescaleFactorOfSoftmaxWord _ _ _
  have hFirst := PTX.Proof.rebuild_scalar (v := word) (by rw [hWord.width]; decide) hWord.head
  have hSecond := PTX.Proof.rebuild_scalar (v := canonical) (by rw [hCanonical.width]; decide)
    hCanonical.head
  have hBytesEq : word.toBytes = canonical.toBytes := hBytes.symm.trans hData
  rw [hBytesEq,hSecond] at hFirst
  have hVal := hCanonical.value
  rw [Except.ok.inj hFirst,hWord.value] at hVal
  exact (Except.ok.inj hVal).symm ▸ Softmax.correctionAlpha_le_one _ _ _

/-- A direct carry has factor one in a completed execution because the actual
correction lane did not take its rescale branch in that score generation. -/
theorem PvVisit.directFactorOfCompletedCorrection {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hDone : Complete l X)
    (hFootprint : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y)
    (hOperands : Safety.CompletedMmaOperandsAreBf16 X)
    (hStats : Statistics.RescaleStoreValuesAreF32 X)
    {g correction index use prior d batch : Nat} {block : Fin 4} {row col : Fin 128}
    {op : OperandSpec} {accum : Bool} {mask : List Nat}
    (visit : PvVisit l X g block use row col index) (hKeep : visit.keep = true)
    (hThread : correction < l.threads)
    (hWarp : 8 ≤ Prologue.warpIndex l correction ∧ Prologue.warpIndex l correction < 12)
    (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ correction/l.block)
    (hHi : correction/l.block < tilePrefix p (batch+1)*p.heads)
    (hCta : correction/l.block = g/l.block)
    (hRow : laneBase l correction+laneOf l correction = row.val) :
    let stage := (pvSite block).stage
    let cell : Cell := ⟨g/l.block,row.val,outputColumn stage+col.val⟩
    use/2 < trips p batch (Epilogue.assignedCoordinates p batch (correction/l.block)).1 →
    PvInstruction X (g,prior) (firstPvBlock true stage) 7 d op accum mask →
    LatestValueReadyUse l X g prior (use-2) →
    ReadSource l X .acc (g,prior) (g,visit.issues 0) cell →
    ∃ pos biased a data word alpha,
      Thread.Scores.StatisticsStore X
        (TmlFa4Fwd.Correction.terminalStatsProducer l correction stage,pos)
        (Softmax.rescaleStore biased) a data ∧
      (Thread.Scores.before X
        (TmlFa4Fwd.Correction.terminalStatsProducer l correction stage,pos)).notices = use/2 ∧
      data = word.toBytes ∧ RescaleFactorWord word alpha ∧ alpha = 1 := by
  dsimp only
  intro hBound hPrior hUse hSource
  let stage := (pvSite block).stage
  have hFrame := hFootprint X hX
  have hCuQ := (hFrame.metadataProtected hp).1
  have hPositive := (visit.keepOfValueUse hp hX).mp hKeep
  obtain ⟨pos,alpha,old,ballot,word,hVisit,hWord,hOrdinal⟩ :=
    rescaleVisitOfCompletedWork hp hX hDone hFrame hOperands hStats
      stage hThread hWarp hb hLo hHi hPositive hBound
  obtain ⟨hRead,hReadRank⟩ := rescaleVisitStatisticsRead hVisit
  obtain ⟨published,biased,data,hPub,hRank,hBytes⟩ :=
    Statistics.rescaleStatisticsReadSource hp hX hCuQ hRead
  have hExact : data = word.toBytes := by
    have h := congrArg (List.filterMap (id : Option Byte → Option Byte)) hBytes.symm
    simpa [List.filterMap_map] using h
  have hLe := alphaAtPublication_le_one hp hX hFootprint hPub hExact hWord
  have hOne := visit.directFactorOfRescaleVisit hp hX hCuQ hKeep hCta hRow hPrior hUse
    hSource hVisit hOrdinal hLe
  rw [hReadRank,hOrdinal] at hRank
  exact ⟨published,biased,_,data,word,alpha,hPub,Nat.add_right_cancel hRank,hExact,hWord,hOne⟩

end PTX.Kernels.TmlFa4Fwd.Protocol
