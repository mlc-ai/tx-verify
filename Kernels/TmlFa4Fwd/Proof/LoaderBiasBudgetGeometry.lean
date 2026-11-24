-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingVAdmission
public import Kernels.TmlFa4Fwd.Proof.SoftmaxFirstLoopEntry
public import Kernels.TmlFa4Fwd.Proof.SoftmaxFirstGeometry

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow Softmax

/-- The optional final Bias packet extends the lower stage when it has one fewer visible block. -/
def biasTailExtra (p : Params) (batch tile : Nat) (stage : Fin 2) : Nat :=
  if stage = 0 ∧ 10 < Mma.trips p batch tile ∧ vPrimingResidual p batch tile ≠ 0 then 1 else 0

/-- The input schedule has a priming packet, at most nine warm packets, and an optional tail. -/
def biasLoaderBudget (p : Params) (batch tile : Nat) (stage : Fin 2) : Nat :=
  1 + min (Mma.trips p batch tile - 1) 9 + biasTailExtra p batch tile stage

/-- The consumer's decoded split covers the priming, warm and optional extra Bias packets. -/
theorem biasLoaderBudget_le_consumer (p : Params) (batch tile : Nat) (stage : Fin 2)
    (hPositive : 0 < Mma.trips p batch tile) :
    let trips := Mma.trips p batch tile
    let cap := trips - stageGeometryBlocks p batch tile stage + 10
    biasLoaderBudget p batch tile stage ≤ 1 + firstBiasedRepeats trips cap := by
  dsimp only
  let trips := Mma.trips p batch tile
  let geom := stageGeometryBlocks p batch tile stage
  let cap := trips - geom + 10
  have hCap : 10 ≤ cap := by dsimp [cap]; omega
  have hCount : 1 + firstBiasedRepeats trips cap = min trips cap := by
    unfold firstBiasedRepeats firstPlainSplit
    change 0 < trips at hPositive
    omega
  change biasLoaderBudget p batch tile stage ≤ 1 + firstBiasedRepeats trips cap
  rw [hCount]
  unfold biasLoaderBudget biasTailExtra
  change 1 + min (trips-1) 9 +
    (if stage = 0 ∧ 10 < trips ∧ vPrimingResidual p batch tile ≠ 0 then 1 else 0) ≤ min trips cap
  split
  · rename_i hExtra
    obtain ⟨hStage,hMany,hResidual⟩ := hExtra
    subst stage
    have hEq : vPrimingResidual p batch tile = (geom + 2^32 - trips) % 2^32 := by
      unfold vPrimingResidual
      have hGeometry : geom = min ((p.kLength batch + 127) / 128)
          ((p.kLength batch - p.qLength batch + 256*tile + 128 + 127)/128) := by
        dsimp [geom,stageGeometryBlocks]
        congr 2
        omega
      rw [hGeometry]
    have hUnder : geom < trips := by
      have hLe : geom ≤ trips := by
        dsimp [geom, stageGeometryBlocks, trips, Mma.trips]
        apply min_le_min_left
        omega
      by_contra! hEq'
      have he : geom = trips := by omega
      apply hResidual
      rw [hEq,he]
      have hCancel : trips + 2^32 - trips = 2^32 := by omega
      rw [hCancel, Nat.mod_self]
    dsimp [cap]
    omega
  · change 0 < trips at hPositive
    omega

end PTX.Kernels.TmlFa4Fwd.Loader
