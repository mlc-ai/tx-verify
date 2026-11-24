-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderWarmBiasEntry
public import Kernels.TmlFa4Fwd.Proof.LoaderRepeatedBiasCoordinates
public import Kernels.TmlFa4Fwd.Proof.SoftmaxFirstBiasGeometry
public import Kernels.TmlFa4Fwd.Proof.SoftmaxFirstGeometry

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX Loader

/-- A row of the physical stage has the stage's clipped number of causal KV blocks. -/
theorem biasLaneStageBlocks (p : Params) (batch tile : Nat) (stage : Fin 2)
    {lane : Nat} (hLane : lane < 128) :
    biasStageBlocks p batch (256*tile + 128*stage.val + lane) =
      stageGeometryBlocks p batch tile stage := by
  have hRow : (256*tile + 128*stage.val + lane)/128 = 2*tile+stage.val := by omega
  unfold biasStageBlocks stageGeometryBlocks
  rw [hRow]
  omega

private theorem biasStageGap (p : Params) (batch tile : Nat) :
    let lo := stageGeometryBlocks p batch tile 0
    let hi := Mma.trips p batch tile
    lo ≤ hi ∧ hi ≤ lo+1 := by
  dsimp [stageGeometryBlocks,Mma.trips]
  omega

private theorem upperBiasStageTrips (p : Params) (batch tile : Nat) :
    stageGeometryBlocks p batch tile 1 = Mma.trips p batch tile := by
  unfold stageGeometryBlocks Mma.trips
  simp only [Fin.val_one]
  rw [show 128*(2*tile+1+1) = 256*(tile+1) by omega]

private theorem warmBiasModularResidual (p : Params) (batch tile : Nat) :
    vPrimingResidual p batch tile =
      (stageGeometryBlocks p batch tile 0+2^32-Mma.trips p batch tile)%2^32 := by
  let lo := stageGeometryBlocks p batch tile 0
  let hi := Mma.trips p batch tile
  have hLo : lo = min ((p.kLength batch+127)/128)
      ((p.kLength batch-p.qLength batch+256*tile+128+127)/128) := by
    dsimp only [lo,stageGeometryBlocks,Fin.val_zero]
    rw [show 128*(2*tile+0+1) = 256*tile+128 by omega]
    simp only [Nat.add_assoc]
  unfold vPrimingResidual
  rw [← hLo]

/-- The hardware's logical shift-right extracts the one-block discrepancy between stages. -/
theorem warmBiasResidualEqGap (p : Params) (batch tile : Nat) :
    warmBiasResidualBit p batch tile =
      Mma.trips p batch tile - stageGeometryBlocks p batch tile 0 := by
  let lo := stageGeometryBlocks p batch tile 0
  let hi := Mma.trips p batch tile
  have hResid : vPrimingResidual p batch tile = (lo+2^32-hi) % 2^32 :=
    warmBiasModularResidual p batch tile
  have hGap : lo ≤ hi ∧ hi ≤ lo+1 := biasStageGap p batch tile
  unfold warmBiasResidualBit
  rw [hResid]
  change (lo+2^32-hi)%2^32 /2^31 = hi-lo
  rcases Nat.eq_or_lt_of_le hGap.1 with h | h
  · rw [h,Nat.add_sub_cancel_left,Nat.mod_self,Nat.zero_div,Nat.sub_self]
  · have hOne : hi = lo+1 := by omega
    rw [hOne]
    have hMod : lo+2^32-(lo+1) = 2^32-1 := by omega
    rw [hMod]
    change (4294967295 : Nat)%4294967296 /2147483648 = lo+1-lo
    rw [Nat.add_sub_cancel_left,
      Nat.mod_eq_of_lt (show (4294967295 : Nat) < 4294967296 by omega)]


/-- An actual nonzero residual means the lower stage has one fewer causal block. -/
theorem warmBiasResidualBit_eq_one (p : Params) (batch tile : Nat)
    (hResidual : vPrimingResidual p batch tile ≠ 0) :
    warmBiasResidualBit p batch tile = 1 := by
  let lo := stageGeometryBlocks p batch tile 0
  let hi := Mma.trips p batch tile
  have hGap : lo ≤ hi ∧ hi ≤ lo+1 := biasStageGap p batch tile
  have hNe : lo ≠ hi := by
    intro h
    apply hResidual
    rw [warmBiasModularResidual]
    change (lo+2^32-hi)%2^32 = 0
    rw [h,Nat.add_sub_cancel_left,Nat.mod_self]
  rw [warmBiasResidualEqGap]
  change hi-lo = 1
  omega

/-- The physical stage differs from the selected visit count by its residual Bias adjustment. -/
theorem stageGeometryBiasAdjustment (p : Params) (batch tile : Nat) (stage : Fin 2) :
    stageGeometryBlocks p batch tile stage ≤ Mma.trips p batch tile ∧
    Mma.trips p batch tile - stageGeometryBlocks p batch tile stage =
      (if stage = 0 then warmBiasResidualBit p batch tile else 0) := by
  by_cases hs : stage = 0
  · subst stage
    rw [ite_eq_left rfl]
    exact ⟨(biasStageGap p batch tile).1,(warmBiasResidualEqGap p batch tile).symm⟩
  · have ht : stage = 1 := by
      apply Fin.ext
      have hv := stage.isLt
      have hn : stage.val ≠ 0 := fun h => hs (Fin.ext h)
      change stage.val = 1
      omega
    rw [ite_eq_right hs,ht,upperBiasStageTrips]
    exact ⟨Nat.le_refl _,Nat.sub_self _⟩

private theorem warmColumnArithmetic {trips blocks adjustment iteration col : Nat}
    (hBlocks : blocks ≤ trips) (hAdjustment : trips - blocks = adjustment)
    (hCount : iteration+2 ≤ trips) (hIter : iteration ≤ 8) :
    128*(10+((trips-1-(iteration+1) : Nat) : Int)-(blocks : Int))+col =
      (128*(8+adjustment-iteration)+64*(col/64)+col%64 : Nat) := by
  omega

/-- A warm Bias issue at iteration `k` addresses the logical Bias column for visit `k + 1`. -/
theorem warmBiasColumnMatchesVisit (p : Params) (batch tile : Nat) (stage : Fin 2)
    {iteration lane col : Nat} (hIter : iteration < min (Mma.trips p batch tile-1) 9)
    (hLane : lane < 128) (hCol : col < 128) :
    let row := 256*tile + 128*stage.val + lane
    let half : Fin 2 := ⟨col/64,by omega⟩
    p.biasColumn batch row (visitKey (Mma.trips p batch tile) (iteration+1) col) =
      (warmBiasColumn stage half iteration (warmBiasResidualBit p batch tile) + col%64 : Nat) := by
  dsimp only
  let trips := Mma.trips p batch tile
  let geom := stageGeometryBlocks p batch tile stage
  let row := 256*tile+128*stage.val+lane
  obtain ⟨hGeom,hGap⟩ := stageGeometryBiasAdjustment p batch tile stage
  have hCount : iteration+2 ≤ trips := by
    change iteration < min (trips-1) 9 at hIter
    omega
  have hIterBound : iteration ≤ 8 := by
    change iteration < min (trips-1) 9 at hIter
    omega
  change p.biasColumn batch row (128*(trips-1-(iteration+1))+col) = _
  rw [p.biasColumn_of_block]
  change 128*(10+((trips-1-(iteration+1) : Nat) : Int)-
    (biasStageBlocks p batch row : Int))+col = _
  rw [biasLaneStageBlocks p batch tile stage hLane]
  change 128*(10+((trips-1-(iteration+1) : Nat) : Int)-(geom : Int))+col = _
  change _ = ((128*(8+(if stage = 0 then warmBiasResidualBit p batch tile else 0)-
    iteration)+64*(col/64)+col%64 : Nat) : Int)
  exact warmColumnArithmetic hGeom hGap hCount hIterBound

private theorem residualColumnArithmetic {trips blocks col : Nat}
    (hTrips : 10 < trips) (hDelta : 1 = trips - blocks) :
    128*(10+((trips-1-10 : Nat) : Int)-(blocks : Int))+col =
      (128*(9-9)+64*(col/64)+col%64 : Nat) := by
  omega

/-- The optional low-stage packet supplies the final in-range Bias block. -/
theorem residualBiasColumnMatchesVisit (p : Params) (batch tile : Nat)
    {lane col : Nat} (hTrips : 10 < Mma.trips p batch tile)
    (hGap : warmBiasResidualBit p batch tile = 1) (hLane : lane < 128) (hCol : col < 128) :
    let row := 256*tile+lane
    let half : Fin 2 := ⟨col/64,by omega⟩
    p.biasColumn batch row (visitKey (Mma.trips p batch tile) 10 col) =
      (residualBiasColumn half 9 + col%64 : Nat) := by
  dsimp only
  let trips := Mma.trips p batch tile
  let row := 256*tile+128*(0 : Fin 2).val+lane
  have hStage : biasStageBlocks p batch row = stageGeometryBlocks p batch tile 0 :=
    biasLaneStageBlocks p batch tile 0 hLane
  have hDelta := warmBiasResidualEqGap p batch tile
  rw [hGap,← hStage] at hDelta
  change p.biasColumn batch row (128*(trips-1-10)+col) = _
  rw [p.biasColumn_of_block]
  change 128*(10+((trips-1-10 : Nat) : Int)-(biasStageBlocks p batch row : Int))+col = _
  exact residualColumnArithmetic hTrips hDelta

private theorem plainColumnArithmetic {trips blocks visit col : Nat}
    (hBlocks : blocks ≤ trips) (hCol : col < 128) (hVisit : visit < trips)
    (hUnbiased : trips-blocks+10 ≤ visit) :
    128*(10+((trips-1-visit : Nat) : Int)-(blocks : Int))+col < 0 := by
  omega

/-- After the stage's Bias extent is exhausted, every key in a valid visited
block lies before the launch Bias region. -/
theorem plainVisitBiasColumnNegative (p : Params) (batch tile : Nat) (stage : Fin 2)
    {visit lane col : Nat} (hLane : lane < 128) (hCol : col < 128)
    (hVisit : visit < Mma.trips p batch tile)
    (hUnbiased : Mma.trips p batch tile - stageGeometryBlocks p batch tile stage + 10 ≤ visit) :
    p.biasColumn batch (256*tile+128*stage.val+lane)
      (visitKey (Mma.trips p batch tile) visit col) < 0 := by
  let row := 256*tile+128*stage.val+lane
  let trips := Mma.trips p batch tile
  let blocks := stageGeometryBlocks p batch tile stage
  have hBlocks := (stageGeometryBiasAdjustment p batch tile stage).1
  change p.biasColumn batch row (128*(trips-1-visit)+col) < 0
  rw [p.biasColumn_of_block]
  change 128*(10+((trips-1-visit : Nat) : Int)-(biasStageBlocks p batch row : Int))+col < 0
  rw [biasLaneStageBlocks p batch tile stage hLane]
  change 128*(10+((trips-1-visit : Nat) : Int)-(blocks : Int))+col < 0
  exact plainColumnArithmetic hBlocks hCol hVisit hUnbiased

end PTX.Kernels.TmlFa4Fwd.Softmax
