-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Safety.TmemMmaValues
public import Kernels.TmlFa4Fwd.Proof.Thread.TmemOutputRescaleGeometry
import Kernels.TmlFa4Fwd.Proof.Safety.TmemProbabilityReuse
import Kernels.TmlFa4Fwd.Proof.Thread.TmemInitialScoreStore
import Kernels.TmlFa4Fwd.Proof.Thread.MmaQueryBank
import Kernels.TmlFa4Fwd.Proof.Thread.MmaValueFrame
import Kernels.TmlFa4Fwd.Proof.Thread.MmaQkDestination
import Kernels.TmlFa4Fwd.Proof.Thread.MmaPvDestination
import Kernels.TmlFa4Fwd.Proof.Safety.Mbar
import Kernels.TmlFa4Fwd.Proof.PollSafety
import Lemmas.Tcgen05.TcMmaIdealEval

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Safety
open PTX PTX.TcMma Thread Thread.Scores Protocol.Scores
open _root_.PTX.Kernels.TmlFa4Fwd.Mma

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hCuQ : Epilogue.DrainCuQProtected p X)
include hp hX hCuQ

private theorem excludeProbabilityAccumulatorSource {i writer : EvId} {cell : Cell} {block : Fin 4}
    {frag : Fin 8} {d row col : Nat} {op : OperandSpec} {mask : List Nat}
    (hi : QkInstruction X i block frag d op true mask) (hCell : resultCell op d row col = some cell)
    (hStore : StoreCell l X writer cell)
    (hFoot : TensorStoreFootprint l writer cell (.probability (qkStage block)))
    (hSource : ReadSource l X .acc writer i cell) : False := by
  let stage := qkStage block
  have hGuard := guardedOfTmaSafe hX (noTmaUnsafe hp hX hCuQ)
  have hOn : MmaAccumulatorOn X i cell (.probability stage) :=
    ⟨block,frag,d,op,true,mask,row,col,rfl,hi,hCell⟩
  obtain ⟨_,_,_,_,_,hCta⟩ := probabilityOverlapIssuer hp hX hStore hFoot hOn
  by_cases hInitial : block.val < 2
  · have hBlock : block = initialQkBlock stage := by
      change block = initialQkBlock (qkStage block)
      revert hInitial
      have audit : ∀ b : Fin 4, b.val < 2 → b = initialQkBlock (qkStage b) := by decide
      exact audit block
    have hDone :=
      initialScoreDoneBeforeProbabilityStore hp hX stage (hBlock ▸ hi) hStore hFoot hCta.2.2
    exact writeBefore_asymm hX hGuard (.inl (.inl hDone)) hSource.2.2.1
  have hShard := Nat.pos_of_ne_zero (of_decide_eq_true (hi.issueFlags hX).1.symm)
  obtain ⟨k,dPrev,opPrev,accPrev,maskPrev,hK,hPrior,hWrite,hBefore⟩ :=
    hi.accumulatorCandidateAdjacent hp hX hShard hCell
  let prior := (i.1,k)
  obtain ⟨seen⟩ := probabilityStoreObservesScore hp hX stage hStore hFoot
  let hMma : X.MmaIssue i d op true mask := ⟨_,hi.decoded⟩
  have hCurrent : seen.commit.2 ≤ i.2 := by
    by_contra! hLater
    exact writeBefore_asymm hX hGuard
      (.inl (.inl (seen.doneBeforeEarlierMma hp hX hMma hCta hLater))) hSource.2.2.1
  have hDistinct := scoreCommitIndexNeMma hp hX seen.score hMma hCta.2.2
  have hCommit : seen.commit.2 ≤ prior.2 := by dsimp [prior]; omega
  have hMmaPrior : X.MmaIssue prior dPrev opPrev accPrev maskPrev := ⟨_,hPrior.decoded⟩
  have hCovered : MmaAccumulatorOn X prior cell (.probability stage) := by
    obtain ⟨_,_,_,_,r1,c1,hPrevious,hResult⟩ := hWrite
    obtain ⟨rfl,rfl,rfl,rfl⟩ := mmaIssue_params hPrevious hMmaPrior
    exact ⟨block,_,_,_,_,_,r1,c1,rfl,hPrior,writeCell_resultCell hResult⟩
  have hWait (packet : Fin 2) : ∃ wait, MmaProbabilityAcquire l X prior stage packet wait :=
    hPrior.recurringProbabilityAcquire hp hX (by omega) packet
  have hPast := probabilityStoreReuseOrder hp hX (correctionJointGuardsOfCuQ hp hX hCuQ)
    stage hStore hFoot hCovered seen hCommit hWait
  rcases hSource.2.2.2.1 prior (.inl hWrite) with hEq | hOld | hFuture
  · exact mmaIssueNeStore hMmaPrior hStore hEq
  · exact writeBefore_asymm hX hGuard hOld (.inr (.inl hPast))
  · exact tcStep_asymm hX hGuard (hFuture.tcStep (by
      intro h; have := congrArg Prod.snd h; dsimp [prior] at this; omega)) hBefore.tcStep

/-- An actual generic accumulator source is a correction rescale store. The
probability cache cannot displace the preceding fragment of a QK visit. -/
theorem storedAccumulatorIsRescale {i writer : EvId} {cell : Cell} (hRead : X.MmaReadCell i cell)
    (hSource : ReadSource l X .acc writer i cell) (hStore : StoreCell l X writer cell) :
    ∃ stage, TensorStoreFootprint l writer cell (.rescale stage) := by
  obtain ⟨tile,hFoot⟩ := tensorStoreFootprint hp hX hStore
  cases tile with
  | rescale stage => exact ⟨stage,hFoot⟩
  | probability stage =>
    obtain ⟨d,op,mask,row,col,hIssue,hCell⟩ := hRead
    have hLo := hFoot.columnLo
    have hHi := hFoot.columnHi
    simp only [TensorStoreTile.columns,probabilityColumn] at hLo hHi
    rcases actualMmaInstruction hX hIssue with ⟨block,frag,hQk⟩ | ⟨block,frag,hPv⟩
    · have hDesc := (hQk.queryOperand hp hX).descriptor
      obtain ⟨hr,hc⟩ := resultCell_rowcol hCell
      rw [hDesc] at hr hc
      have hr' : row < 128 := hr
      have hc' : col < 128 := hc
      have hResult := hQk.scoreCell hp hX ⟨row,hr'⟩ ⟨col,hc'⟩
      obtain rfl := Option.some.inj (hCell.symm.trans hResult)
      have hStage : qkStage block = stage := by
        apply Fin.ext
        dsimp only [scoreColumn] at hLo hHi
        omega
      exact (excludeProbabilityAccumulatorSource hp hX hCuQ hQk hCell hStore
        (hStage.symm ▸ hFoot) hSource).elim
    · obtain ⟨_,_,hDesc,_⟩ := hPv.valueOperand hp hX
      obtain ⟨hr,hc⟩ := resultCell_rowcol hCell
      rw [hDesc] at hr hc
      obtain rfl := Option.some.inj (hCell.symm.trans (hPv.outputCell hp hX ⟨row,hr⟩ ⟨col,hc⟩))
      have := stage.isLt
      dsimp only [scoreColumn,outputColumn] at hLo hHi
      omega

omit hp hX hCuQ in
/-- The remaining stored accumulator values are those of selected correction rescale stores. -/
def RescaleAccumulatorWordsAreF32 (l : Launch) (X : Execution) : Prop :=
  ∀ writer reader cell stage value, X.MmaReadCell reader cell →
    ReadSource l X .acc writer reader cell →
    TensorStoreFootprint l writer cell (.rescale stage) →
    StoreValue l X writer cell value → ∃ r, value = .float .f32 r

/-- Only correction rescale needs a stored FP32 premise in the MMA result proof. -/
theorem storedAccumulatorIsF32OfRescale (hValues : RescaleAccumulatorWordsAreF32 l X)
    : StoredAccumulatorIsF32 l X := by
  intro writer reader cell value hRead hSource hValue
  have hStore : StoreCell l X writer cell := by
    obtain ⟨address,values,shape,j,hTSt,hGet,hCell⟩ := hValue
    exact ⟨address,values,shape,j,hTSt,(List.getElem?_eq_some_iff.mp hGet).1,hCell⟩
  obtain ⟨stage,hFootprint⟩ := storedAccumulatorIsRescale hp hX hCuQ hRead hSource hStore
  exact hValues writer reader cell stage value hRead hSource hFootprint hValue

end PTX.Kernels.TmlFa4Fwd.Safety
