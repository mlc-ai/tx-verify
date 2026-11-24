-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderWarmRoundTailBranch
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderWarmRoundTail
public import Kernels.TmlFa4Fwd.Proof.LoaderBiasBudgetGeometry

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX Prologue Epilogue Softmax

/-- The number of biased visits of a softmax stage, the opening visit included. -/
def stageBiased (p : Params) (batch cta : Nat) (stage : Fin 2) : Nat :=
  let tile := (assignedCoordinates p batch cta).1
  let trips := Mma.trips p batch tile
  trips-firstPlainSplit trips (trips-stageGeometryBlocks p batch tile stage+10)

/-- The number of plain visits of a softmax stage. -/
def stageSplit (p : Params) (batch cta : Nat) (stage : Fin 2) : Nat :=
  let tile := (assignedCoordinates p batch cta).1
  let trips := Mma.trips p batch tile
  firstPlainSplit trips (trips-stageGeometryBlocks p batch tile stage+10)

set_option maxRecDepth 4096 in
private theorem geometryBounds (p : Params) (batch tile : Nat) (stage : Fin 2) :
    stageGeometryBlocks p batch tile stage ≤ Mma.trips p batch tile ∧
      Mma.trips p batch tile ≤ stageGeometryBlocks p batch tile stage+1 ∧
      (stage = 1 → stageGeometryBlocks p batch tile stage = Mma.trips p batch tile) := by
  have hs := stage.isLt
  unfold stageGeometryBlocks Mma.trips
  generalize (p.kLength batch+127)/128 = C
  generalize p.kLength batch-p.qLength batch = A
  refine ⟨?_,?_,fun h => ?_⟩
  · apply min_le_min_left
    omega
  · rcases Nat.le_total C ((A+256*(tile+1)+127)/128) with h | h <;>
    rcases Nat.le_total C ((A+128*(2*tile+stage.val+1)+127)/128) with h' | h' <;>
    simp only [Nat.min_eq_left,Nat.min_eq_right,h,h'] <;> omega
  · subst h
    simp only [Fin.isValue,Fin.val_one]
    congr 2
    omega

private theorem flagZero : Thread.Loader.warmResidueFlag 0 = false := by decide

private theorem flagMax : Thread.Loader.warmResidueFlag (2^32-1) = true := by decide

/-- The biased visits of a stage outnumber the warm loader rounds, and every biased visit
beyond the warm rounds is the single tail visit of stage zero, which exists exactly when the
loader's warm tail issues its extra Bias generation. -/
theorem biasScheduleMatch (p : Params) (l : Launch) {g batch : Nat} (hw : warpIndex l g = 14)
    (hPos : 0 < Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1) (stage : Fin 2) :
    let trips := Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1
    Thread.Loader.warmRounds p l g batch < stageBiased p batch (g/l.block) stage ∧
      stageBiased p batch (g/l.block) stage ≤ trips ∧
      stageSplit p batch (g/l.block) stage ≤ trips ∧
      stageBiased p batch (g/l.block) stage =
        trips-stageSplit p batch (g/l.block) stage ∧
      (∀ n, n < stageBiased p batch (g/l.block) stage →
        Thread.Loader.warmRounds p l g batch < n →
        stage = 0 ∧ n = Thread.Loader.warmRounds p l g batch+1 ∧
          Thread.Loader.warmTailSkips p l g batch = false) ∧
      (stage = 0 → Thread.Loader.warmTailSkips p l g batch = false →
        Thread.Loader.warmRounds p l g batch+1 < stageBiased p batch (g/l.block) stage) := by
  intro trips
  let tile := (assignedCoordinates p batch (g/l.block)).1
  obtain ⟨hLe,hGe,hOne⟩ := geometryBounds p batch tile stage
  obtain ⟨hLe0,hGe0,_⟩ := geometryBounds p batch tile 0
  have hResidual : Loader.vPrimingResidual p batch tile =
      (stageGeometryBlocks p batch tile 0+2^32-Mma.trips p batch tile)%2^32 := by
    unfold Loader.vPrimingResidual stageGeometryBlocks
    simp only [Fin.isValue,Fin.val_zero]
    congr 3
    omega
  have hSkip : Thread.Loader.warmTailSkips p l g batch = false ↔
      10 < Mma.trips p batch tile ∧
        stageGeometryBlocks p batch tile 0+1 = Mma.trips p batch tile := by
    unfold Thread.Loader.warmTailSkips
    change (decide (warpIndex l g ≠ 14) ||
      !(decide (10 < Mma.trips p batch tile) &&
        Thread.Loader.warmResidueFlag (Loader.vPrimingResidual p batch tile))) = false ↔ _
    rw [hResidual]
    by_cases hEq : stageGeometryBlocks p batch tile 0 = Mma.trips p batch tile
    · rw [hEq,show Mma.trips p batch tile+2^32-Mma.trips p batch tile = 2^32 by omega,
        Nat.mod_self,flagZero]
      simp [hw]
    · have e : stageGeometryBlocks p batch tile 0 = Mma.trips p batch tile-1 := by omega
      rw [e,show Mma.trips p batch tile-1+2^32-Mma.trips p batch tile = 2^32-1 by omega,
        Nat.mod_eq_of_lt (by omega),flagMax]
      simp [hw]
      omega
  have hW : Thread.Loader.warmRounds p l g batch = min (Mma.trips p batch tile-1) 9 := rfl
  have hB : stageBiased p batch (g/l.block) stage = Mma.trips p batch tile-
      firstPlainSplit (Mma.trips p batch tile)
        (Mma.trips p batch tile-stageGeometryBlocks p batch tile stage+10) := rfl
  have hS : stageSplit p batch (g/l.block) stage = firstPlainSplit (Mma.trips p batch tile)
      (Mma.trips p batch tile-stageGeometryBlocks p batch tile stage+10) := rfl
  change 0 < Mma.trips p batch tile at hPos
  change _ ∧ _ ≤ Mma.trips p batch tile ∧ _ ≤ Mma.trips p batch tile ∧
    _ = Mma.trips p batch tile-_ ∧ _
  unfold firstPlainSplit at hB hS
  rw [hB,hS,hW]
  have hSt := stage.isLt
  refine ⟨by omega,by omega,by omega,by omega,fun n hn hn' => ?_,fun h0 hT => ?_⟩
  · have hStage : stage = 0 := by
      by_contra hne
      have := hOne (by omega)
      omega
    subst hStage
    refine ⟨rfl,by omega,hSkip.mpr ⟨by omega,by omega⟩⟩
  · subst h0
    have := hSkip.mp hT
    omega

end PTX.Kernels.TmlFa4Fwd.Progress
