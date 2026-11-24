-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Safety.TmemConflicts
public import Kernels.TmlFa4Fwd.Proof.Thread.TmemInitialScoreStore
import Kernels.TmlFa4Fwd.Proof.Thread.MmaQueryBank
import Lemmas.Tcgen05.TcMmaResultLayout

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Safety
open PTX PTX.TcMma Thread
open PTX.Kernels.TmlFa4Fwd.Mma

/-- Repeated score writes to the upper half of a tile need its probability reuse order. -/
def RecurringScoreStoreOrder (l : Launch) (X : Execution) (stage : Fin 2) : Prop :=
  ∀ {mma store : EvId} {block : Fin 4} {frag : Fin 8} {d row col : Nat}
    {op : OperandSpec} {acc : Bool} {mask : List Nat} {cell : Cell},
    2 ≤ block.val → qkStage block = stage → QkInstruction X mma block frag d op acc mask →
    resultCell op d row col = some cell → StoreCell l X store cell →
    TensorStoreFootprint l store cell (.probability stage) →
    DoneBefore l X mma store ∨ StoreDoneBefore l X store mma

/-- Initial score completion is recovered from any reached probability store. -/
theorem TensorMixedWriteOrder.ofRecurringScores {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hRecurring : ∀ stage, RecurringScoreStoreOrder l X stage)
    (hRescale : ∀ stage, TensorMmaStoreOrder l X (.rescale stage)) :
    TensorMixedWriteOrder l X := by
  refine ⟨?_,hRescale⟩
  intro stage mma store cell hStore hFoot hSeen
  obtain ⟨block,frag,d,op,acc,mask,row,col,hStage,hQk,hResult⟩ := hSeen
  by_cases hBlock : 2 ≤ block.val
  · exact hRecurring stage hBlock hStage hQk hResult hStore hFoot
  · have hInitial : block = initialQkBlock stage := by
      apply Fin.ext
      change block.val = stage.val
      have hBank := congrArg Fin.val hStage
      change block.val%2 = stage.val at hBank
      omega
    have hOp := hQk.queryOperand hp hX
    have hCell : cell.cta = mma.1/l.block := by
      rcases resultCell_cta hResult with hLo | hHi
      · exact hLo.trans hOp.ctaLow
      · exact hHi.trans hOp.ctaHigh
    subst block
    exact .inl (initialScoreDoneBeforeProbabilityStore hp hX stage hQk hStore hFoot
      (hCell.symm.trans hFoot.cta))

end PTX.Kernels.TmlFa4Fwd.Safety
