-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Safety.TmemConflicts
public import Kernels.TmlFa4Fwd.Proof.Thread.TmemProbabilityReadGeometry
import Lemmas.Tcgen05.TcMmaResultLayout

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Safety
open PTX PTX.TcMma Thread

/-- The probability store and operand synchronization for one physical stage. -/
def ProbabilityStoreReadOrder (l : Launch) (X : Execution) (stage : Fin 2) : Prop :=
  ∀ reader store cell, MmaAOnProbabilityStage X reader cell stage → StoreCell l X store cell →
    TensorStoreFootprint l store cell (.probability stage) →
    StoreDoneBefore l X store reader ∨ DoneBefore l X reader store

/-- The earlier score and later probability operand synchronization for one physical stage. -/
def EarlierScoreToProbabilityRead (l : Launch) (X : Execution) (stage : Fin 2) : Prop :=
  ∀ reader writer cell, MmaAOnProbabilityStage X reader cell stage → X.MmaCell writer cell →
    MmaAccumulatorOn X writer cell (.probability stage) → writer.2 < reader.2 →
    WriteBefore l X writer reader ∨ ReadBefore l X .a reader writer

/-- Actual A cells overlap only matching-stage probability stores. -/
theorem TensorAStoreOrder.ofProbability {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (h : ∀ stage, ProbabilityStoreReadOrder l X stage) : TensorAStoreOrder l X := by
  intro reader store cell tile hRead hStore hFoot
  obtain ⟨stage,hOperand,hReadLo,hReadHi⟩ := mmaAProbabilityTile hp hX hRead
  have hLo := hFoot.columnLo
  have hHi := hFoot.columnHi
  cases tile with
  | probability written =>
    have hStage : written = stage := by
      apply Fin.ext
      simp only [TensorStoreTile.columns,probabilityColumn,scoreColumn] at hLo hHi hReadLo hReadHi
      omega
    subst written
    exact h stage reader store cell hOperand hStore hFoot
  | rescale written =>
    have hEnd := probabilityColumn_range stage
    have hScore := scoreColumn_range stage
    simp only [TensorStoreTile.columns,outputColumn] at hLo
    omega

/-- An earlier MMA writer sharing an actual A cell is a QK fragment of the same stage. -/
theorem EarlierMmaAOrder.ofScore {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (h : ∀ stage, EarlierScoreToProbabilityRead l X stage) : EarlierMmaAOrder l X := by
  intro reader writer cell hRead hWrite hEarlier
  obtain ⟨stage,hOperand,hLo,hHi⟩ := mmaAProbabilityTile hp hX hRead
  obtain ⟨d,op,accum,mask,row,col,hMma,hCell⟩ := hWrite
  have hScore := mmaAccumulatorOnTile hp hX (tile := .probability stage)
    ⟨hLo,hHi⟩ hMma (writeCell_resultCell hCell)
  exact h stage reader writer cell hOperand ⟨d,op,accum,mask,row,col,hMma,hCell⟩ hScore hEarlier

end PTX.Kernels.TmlFa4Fwd.Safety
