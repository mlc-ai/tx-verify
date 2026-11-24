-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.PvWeightedVisit
public import Kernels.TmlFa4Fwd.Proof.Protocol.PvCarryVisit
import Kernels.TmlFa4Fwd.Proof.Thread.TmemAccumulatorCompletion
import Kernels.TmlFa4Fwd.Proof.Thread.MmaPvOperandFields
import Kernels.TmlFa4Fwd.Proof.Thread.MmaValueUseRelease
import Kernels.TmlFa4Fwd.Proof.Thread.ProbabilityStoreOfCredit
import Kernels.TmlFa4Fwd.Proof.Protocol.RescaleStatisticsScore
import Kernels.TmlFa4Fwd.Proof.Safety.Mbar
import Kernels.TmlFa4Fwd.Proof.PollSafety
import Lemmas.Tcgen05.TcMmaResultLayout

public import Kernels.TmlFa4Fwd.Proof.Protocol.PvRescaledCarry
public import Kernels.TmlFa4Fwd.Proof.Safety.RescaleFiniteLoads

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol
open PTX PTX.TcMma PTX.Numeric Thread Thread.Correction
open PTX.Kernels.TmlFa4Fwd.Mma PTX.Kernels.TmlFa4Fwd.Softmax
open Epilogue (assignedCoordinates stageRow)
open Scores (probabilityProducer RescaleStatisticsScore)
open Thread.Scores (ObservedProbabilityTile scoreCommitOrdinal)
open Thread.Mma (LatestValueReadyUse)

noncomputable section

private theorem pvStageOfBank (steady : Bool) (stage : Fin 2) :
    (pvSite (firstPvBlock steady stage)).stage = stage := by
  cases steady <;> fin_cases stage <;> rfl

private theorem previousDirectCarryDone {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hCuQ : Epilogue.DrainCuQProtected p X)
    {g index use past d : Nat} {block : Fin 4} {row col : Fin 128}
    {op : OperandSpec} {accum : Bool} {mask : List Nat}
    (v : PvVisit l X g block use row col index)
    (hKeep : v.keep = true) (hDone : X.async.mmaDone (g,index) = true) :
    let stage := (pvSite block).stage
    let cell : Cell := ⟨g/l.block,row.val,outputColumn stage+col.val⟩
    PvInstruction X (g,past) (firstPvBlock true stage) 7 d op accum mask →
    ReadSource l X .acc (g,past) (g,v.issues 0) cell →
    X.async.mmaDone (g,past) = true := by
  dsimp only
  intro hPrev hReadSource
  let stage := (pvSite block).stage
  let cell : Cell := ⟨g/l.block,row.val,outputColumn stage+col.val⟩
  let reader := (g,v.issues 0)
  let operands := pvOperands l g block 0 use
  have hFragment : PvInstruction X reader block 0 (outputColumn stage) operands true
      (List.replicate 4 0) := by simpa [hKeep] using v.fragment 0
  have hRead : X.MmaReadCell reader cell :=
    ⟨_,_,_,row.val,col.val,⟨_,hFragment.decoded⟩,hFragment.outputCell hp hX row col⟩
  have hPreviousCell := hPrev.outputCell hp hX row col
  rw [pvStageOfBank] at hPreviousCell
  obtain ⟨_,_,hDesc,_,_⟩ := hPrev.valueOperand hp hX
  have hPrevious : X.MmaCell (g,past) cell := by
    refine ⟨d,op,accum,mask,row.val,col.val,⟨_,hPrev.decoded⟩,?_⟩
    rw [(hPrev.fixedOperandFields hX).2.2]
    exact writeCell_no_mask_128 (by rw [hDesc]; rfl) (by rw [hDesc]; rfl)
      row.isLt row.isLt hPreviousCell
  have hGuard := guardedOfTmaSafe hX (Safety.noTmaUnsafe hp hX hCuQ)
  exact (mmaAccumulatorMmaSourceDone hp hX hGuard hReadSource hRead hPrevious
    (v.fragmentDone hp hX hCuQ hDone 0)).2.2

/-- The reference-shifted numerator defined by the observed references. -/
def shiftedNumerator (p : Params) (batch head row blocks : Nat) (ref : Nat → Option ℝ) :
    Nat → Nat → ℝ
  | 0, col => (2 : ℝ) ^ (-(ref 0).getD 0) *
      maskedBlockSum (p.keyCount batch row) blocks 0 (weightedValue p batch head row col)
  | n+1, col =>
    shiftedNumerator p batch head row blocks ref n col * maskedRescale (ref n) (ref (n+1)) +
      (2 : ℝ) ^ (-(ref (n+1)).getD 0) *
        maskedBlockSum (p.keyCount batch row) blocks (n+1) (weightedValue p batch head row col)

/-- The row-sum recurrence extends with the numerator at the same references. -/
theorem softmaxRunOfObservedSums {p : Params} {batch head row blocks : Nat}
    {ref : Nat → Option ℝ} {sums : Nat → ℝ}
    (hSum : SoftmaxSumRun p batch head row blocks ref sums) :
    SoftmaxRun p batch head row blocks ref sums (shiftedNumerator p batch head row blocks ref) :=
  ⟨hSum,fun _ _ => rfl,fun _ _ _ _ => rfl⟩

/-- A completed PV bank has the reference-shifted numerator if its actual probability
tile and its matching correction carry have the specified visit values. -/
theorem recordedPvNumeratorOfTiles {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) (hCuQ : Epilogue.DrainCuQProtected p X)
    {g batch : Nat} (stage : Fin 2) (row col : Fin 128)
    (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hOperands : Safety.CompletedMmaOperandsAreBf16 X)
    (hStats : Statistics.RescaleStoreValuesAreF32 X)
    (ref : Nat → Option ℝ) (sums : Nat → ℝ) (acc : Nat → Nat → ℝ) :
    let coords := assignedCoordinates p batch (g/l.block)
    let qrow := stageRow coords.1 stage+row.val
    let blocks := trips p batch coords.1
    let cell : Cell := ⟨g/l.block,row.val,outputColumn stage+col.val⟩
    SoftmaxRun p batch coords.2 qrow blocks ref sums acc →
    (∀ n < blocks, ObservedProbabilityTile l X
      (probabilityProducer l (g/l.block) stage row.val) stage n
      (fun k => shiftedWeight p batch coords.2 qrow (visitKey blocks n k) ((ref n).getD 0))) →
    (∀ {index use block}, (v : PvVisit l X g block use row col index) →
      (pvSite block).stage = stage → v.keep = true → use/2 < blocks → ∀ {prior d op accum mask},
      PvInstruction X (g,prior) (firstPvBlock true stage) 7 d op accum mask →
      LatestValueReadyUse l X g prior (use-2) →
      ReadSource l X .acc (g,prior) (g,v.issues 0) cell →
      maskedRescale (ref (use/2-1)) (ref (use/2)) = 1) →
    (∀ {writer : EvId} {pos : Nat} {biased : Bool} {a : Acc} {data : List Byte}
        {word : Value} {α : ℝ} {n : Nat},
      0 < n → n < blocks → writer.1/l.block = g/l.block →
      laneBase l writer.1 + laneOf l writer.1 = row.val →
      let producer := TmlFa4Fwd.Correction.terminalStatsProducer l writer.1 stage
      Thread.Scores.StatisticsStore X (producer,pos) (Softmax.rescaleStore biased) a data →
      (Thread.Scores.before X (producer,pos)).notices = n →
      data = word.toBytes → RescaleFactorWord word α →
      α = maskedRescale (ref (n-1)) (ref n)) →
    ∀ {index use block}, PvVisit l X g block use row col index →
      (pvSite block).stage = stage → use/2 < blocks →
      X.async.mmaDone (g,index) = true →
      TcMma.Result l Assumptions.all X (g,index) cell (.float .f32 (acc (use/2) col.val)) := by
  dsimp only
  intro hRun hTiles hDirect hCoefficient
  let coords := assignedCoordinates p batch (g/l.block)
  let qrow := stageRow coords.1 stage + row.val
  let blocks := trips p batch coords.1
  let cell : Cell := ⟨g/l.block,row.val,outputColumn stage+col.val⟩
  have go : ∀ n, ∀ {index use block}, (v : PvVisit l X g block use row col index) →
      (pvSite block).stage = stage → use/2 = n → n < blocks →
      X.async.mmaDone (g,index) = true →
      TcMma.Result l Assumptions.all X (g,index) cell (.float .f32 (acc n col.val)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro index use block v hStage hRank hBound hDone
      have tile := hTiles n hBound
      have hTile := v.resultOfShiftedTile hp hX hFrame hCuQ hb hLo hHi
      have isCarry := v.keepOfValueUse hp hX
      have hUse : use % 2 = 1 := by obtain ⟨_,_,_,hOdd,_,_⟩ := v.ready 0; exact hOdd
      cases n with
      | zero =>
        have hZero : v.keep = false := Bool.eq_false_iff.mpr (fun h => by
          have hPositive := isCarry.mp h
          omega)
        have hOut := hTile ((ref 0).getD 0) 0 hDone
        simp only [hStage,hRank] at hOut
        have hResult := hOut tile (by simp [hZero]) (fun h => by rw [hZero] at h; cases h)
        rw [zero_add] at hResult
        simpa only [hRun.accInitial _ col.isLt] using hResult
      | succ prior =>
        have hKeep : v.keep = true := isCarry.mpr (by omega)
        let factor := maskedRescale (ref prior) (ref (prior+1))
        let carry := acc prior col.val * factor
        have hOut := hTile ((ref (prior+1)).getD 0) carry hDone
        simp only [hStage,hRank] at hOut
        have hSource := v.carrySource hp hX hCuQ hKeep
        rw [hStage] at hSource
        obtain ⟨writer,hRead,hOrigin⟩ := hSource
        have hCarry : TcMma.Result l Assumptions.all X writer cell (.float .f32 carry) ∨
            StoreValue l X writer cell (.float .f32 carry) := by
          rcases hOrigin with ⟨hOwner,hPrevious,hOldUse⟩ | ⟨hStore,hWords,seen,hGeneration⟩
          · have hWriter : writer = (g,writer.2) := Prod.ext hOwner rfl
            have hPrev : PvInstruction X (g,writer.2) (firstPvBlock true stage) 7 _ _ _ _ :=
              hWriter ▸ hPrevious
            have hRead' : ReadSource l X .acc (g,writer.2) (g,v.issues 0) cell := hWriter ▸ hRead
            have hPrev' := hStage.symm ▸ hPrev
            have hRead'' : ReadSource l X .acc (g,writer.2) (g,v.issues 0)
                ⟨g/l.block,row.val,outputColumn (pvSite block).stage+col.val⟩ := by
              rwa [hStage]
            have hCompleted := previousDirectCarryDone hp hX hCuQ v hKeep hDone hPrev' hRead''
            obtain ⟨prev⟩ := PvVisit.ofLast hp hX hCuQ hPrev hOldUse row col
            have hPast : (use-2)/2 = prior := by omega
            have hRec := ih prior (by omega) prev (pvStageOfBank true stage) hPast
              (by omega) hCompleted
            have hOne := hDirect v hStage hKeep (hRank.symm ▸ hBound) hPrev hOldUse hRead'
            have hEq : factor = 1 := by
              simpa only [hRank,Nat.add_sub_cancel] using hOne
            exact .inl (hWriter.symm ▸ (by simpa [carry,hEq] using hRec))
          · obtain ⟨previous,_,_,_,_,_,hPrevious,hPreviousUse⟩ :=
              v.previousValueBank hp hX hCuQ hKeep
            rw [hStage] at hPrevious
            obtain ⟨earlier⟩ := PvVisit.ofLast hp hX hCuQ hPrevious hPreviousUse row col
            obtain ⟨stored,hStored⟩ := hWords
            have hWritten : StoreCell l X writer cell := by
              obtain ⟨a,words,shape,j,he,hWord,hCell⟩ := hStored
              exact ⟨a,words,shape,j,he,(List.getElem?_eq_some_iff.mp hWord).1,hCell⟩
            obtain ⟨_,hFoot⟩ := tensorStoreFootprint hp hX hWritten
            have hOwner : writer.1/l.block = g/l.block := hFoot.cta.symm
            have hRow : laneBase l writer.1+laneOf l writer.1 = row.val := by
              have hLane := hFoot.lane.symm
              change TmlFa4Fwd.Correction.rowOf l writer.1 = row.val at hLane
              unfold TmlFa4Fwd.Correction.rowOf laneBase laneOf at *
              omega
            have hPriorRank : (use-2)/2 = prior := by omega
            have hCurrentRank : use/2 = (use-2)/2+1 := by omega
            have hNewBound : (use-2)/2+1 < blocks := by
              rw [hPriorRank]
              exact hBound
            have hSemantic : ∀ (pos : Nat) (biased : Bool) (a : Acc)
                (data : List Byte) (word : Value) (α : ℝ),
                let producer := TmlFa4Fwd.Correction.terminalStatsProducer l writer.1 stage
                Thread.Scores.StatisticsStore X (producer,pos) (Softmax.rescaleStore biased)
                  a data →
                (Thread.Scores.before X (producer,pos)).notices = (use-2)/2+1 →
                data = word.toBytes → RescaleFactorWord word α → α = factor := by
              dsimp only
              intro pos biased a data word α hPub hVisit hBytes hWord
              have hValue := hCoefficient (writer := writer) (n := (use-2)/2+1)
                (by omega) hNewBound hOwner hRow hPub hVisit hBytes hWord
              simpa only [hPriorRank,Nat.add_sub_cancel,factor] using hValue
            have hScaled := rescaledCarryOfPreviousPv hp hX hCuQ hStore hPrevious hPreviousUse
              seen (hGeneration.trans hCurrentRank) hStats hSemantic
              (fun _ _ _ _ _ he _ _ hw hr =>
                Safety.rescaleLoadWordOfOperandsAndStores hp hX hCuQ hOperands hStats hr he hw)
              ⟨stored,hStored⟩
              (ih prior (by omega) earlier (pvStageOfBank true stage) hPriorRank (by omega))
            exact .inr hScaled
        have hResult := hOut tile (fun h => by rw [hKeep] at h; cases h)
          (fun _ => ⟨writer,hRead,hCarry⟩)
        rw [hRun.accStep prior hBound _ col.isLt]
        exact hResult
  intro index use block v hStage hBound hDone
  exact go (use/2) v hStage rfl hBound hDone

end
end PTX.Kernels.TmlFa4Fwd.Protocol
