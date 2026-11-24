-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionTmemAddress
public import Kernels.TmlFa4Fwd.Proof.Thread.TensorLoadSites
import Kernels.TmlFa4Fwd.Proof.Thread.TensorStoreSites
import Kernels.TmlFa4Fwd.Proof.Thread.BiasReadAddress
import Kernels.TmlFa4Fwd.Proof.TmemGeometry

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX Softmax

private theorem columnAt {l : Launch} {i : EvId} {n j first : Nat}
    (hRange : first + n ≤ 512) (hj : j < n) :
    (tcDataCell l i.1 .s32x32b (2 ^ 16 * laneBase l i.1 + first) j).column < 512 := by
  rw [tcDataCell_warp32 _ _ _ (by omega)]
  exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj _) hRange

/-- A load's actual source cell belongs to its CTA and lies within its 512 columns. -/
theorem tensorLoadCellRange {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {j : Nat} {cell : TcMma.Cell} (h : TcMma.LoadCell l X i j cell) :
    TensorDataEvent X i ∧ cell.cta = i.1/l.block ∧ cell.column < 512 := by
  obtain ⟨address, vals, shape, ⟨site,he⟩, hj, rfl⟩ := h
  refine ⟨⟨_,he,.inl rfl⟩,rfl,?_⟩
  rcases tensorLoadSite hX he with ⟨round,q,rfl⟩ | ⟨stage,chunk,rfl⟩ | ⟨stage,chunk,rfl⟩
  · obtain ⟨w,_,rfl,hLength,rfl⟩ := Scores.scoreLoadAddress hp hX round q he
    have hStage := scoreColumn_range (stageOf w)
    have hQ := q.isLt
    exact columnAt (i := i) (n := 32) (by omega) (hLength ▸ hj)
  · obtain ⟨rfl,rfl,hLength⟩ := Correction.rescaleLoadActualAddress hp hX stage chunk he
    have hStage := outputColumn_range stage
    have hChunk := chunk.isLt
    exact columnAt (i := i) (n := 16) (by omega) (hLength ▸ hj)
  · obtain ⟨rfl,rfl,hLength⟩ := Correction.finalizeLoadActualAddress hp hX stage chunk he
    have hStage := outputColumn_range stage
    have hChunk := chunk.isLt
    exact columnAt (i := i) (n := 8) (by omega) (hLength ▸ hj)

/-- A store's actual destination cell belongs to its CTA and lies within its 512 columns. -/
theorem tensorStoreCellRange {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {cell : TcMma.Cell} (h : TcMma.StoreCell l X i cell) :
    TensorDataEvent X i ∧ cell.cta = i.1/l.block ∧ cell.column < 512 := by
  obtain ⟨address, vals, shape, j, ⟨site,he⟩, hj, rfl⟩ := h
  refine ⟨⟨_,he,.inl rfl⟩,rfl,?_⟩
  rcases tensorStoreSite hX he with ⟨round,q,rfl⟩ | ⟨stage,chunk,rfl⟩
  · obtain ⟨w,_,rfl,hLength,rfl⟩ := Scores.probabilityStoreAddress hp hX round q he
    have hStage := probabilityColumn_range (stageOf w)
    have hScore := scoreColumn_range (stageOf w)
    have hQ := q.isLt
    exact columnAt (i := i) (n := 16) (by omega) (hLength ▸ hj)
  · obtain ⟨rfl,rfl,hLength⟩ := Correction.rescaleStoreActualAddress hp hX stage chunk he
    have hStage := outputColumn_range stage
    have hChunk := chunk.isLt
    exact columnAt (i := i) (n := 16) (by omega) (hLength ▸ hj)

end PTX.Kernels.TmlFa4Fwd.Thread
