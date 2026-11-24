-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxRecurringBiasGeometry
public import Kernels.TmlFa4Fwd.Proof.SoftmaxFirstScoreValues
public import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasAffine

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow

/-- Every visited key before the stage's Bias window is below even the first
row's causal bound. The window is wider than the stage and its ceiling slack. -/
theorem keyLiveOfNegativeBiasColumn (p : Params) (batch row key : Nat)
    (hBias : p.biasColumn batch row key < 0) :
    key < p.keyCount batch row := by
  unfold Params.biasColumn at hBias
  dsimp only at hBias
  unfold Params.keyCount
  have hEnd : (row/128+1)*128 ≤ row+128 := by omega
  omega

/-- A plain visit is wholly before the Bias window and contains no causal or tail padding. -/
theorem plainVisitLogitOfDot {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (stage : Fin 2) {batch tile head lane visit col : Nat}
    (hLane : lane < 128) (hCol : col < 128)
    (hVisit : visit < Mma.trips p batch tile)
    (hPlain : Mma.trips p batch tile-stageGeometryBlocks p batch tile stage+10 ≤ visit) :
    let row := 256*tile+128*stage.val+lane
    let key := visitKey (Mma.trips p batch tile) visit col
    key < p.keyCount batch row ∧
      maskedLogit p batch head row key = some (queryKeyDot p batch head row key) := by
  dsimp only
  have hBias := plainVisitBiasColumnNegative p batch tile stage hLane hCol hVisit hPlain
  have hLive := keyLiveOfNegativeBiasColumn p batch _ _ hBias
  refine ⟨hLive,?_⟩
  rw [maskedLogit,ite_eq_left hLive,score]
  have hOutside : ¬(0 ≤ p.biasColumn batch (256*tile+128*stage.val+lane)
      (visitKey (Mma.trips p batch tile) visit col) ∧
      p.biasColumn batch (256*tile+128*stage.val+lane)
        (visitKey (Mma.trips p batch tile) visit col) < 1280) :=
    fun h => (not_le_of_gt hBias h.1)
  simp only [ite_eq_right hOutside,mul_zero,add_zero,queryKeyDot]
  congr 1
  field_simp [(scalePositive hp).1.ne']

/-- Under the actual plain-loop extent, the observed QK dot-product formula
is the unmasked logical logit. -/
theorem plainVisitScoreDot {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (stage : Fin 2) {batch tile head g visit : Nat} (q : Fin 4) (k : Fin 32)
    (hb : batch < p.batch)
    (hRow : 256*tile+128*stage.val+(g%l.block)%128 < p.qLength batch)
    (hVisit : visit < Mma.trips p batch tile)
    (hPlain : Mma.trips p batch tile-stageGeometryBlocks p batch tile stage+10 ≤ visit) :
    let row := 256*tile+128*stage.val+(g%l.block)%128
    let key := visitKey (Mma.trips p batch tile) visit (firstScoreColumn q k).val
    maskedLogit p batch head row key =
      some (firstScoreDot p l g batch head (p.qOffset batch+256*tile+128*stage.val)
        (128*(Mma.trips p batch tile-1-visit)) q k) := by
  obtain ⟨hLive,hLogit⟩ := plainVisitLogitOfDot hp stage (head := head)
    (Nat.mod_lt (g%l.block) (by decide)) (firstScoreColumn q k).isLt hVisit hPlain
  dsimp only at hLive hLogit ⊢
  rw [hLogit]
  have hQ := hp.packedRow_lt hb hRow
  have hK := hLive.trans_le (Nat.min_le_left ..)
  simp only [queryKeyDot,firstScoreDot,scoreRow_eq_tid,visitKey,Mma.qkQuery,Mma.qkKey,
    Nat.add_assoc] at hQ hK ⊢
  simp only [ite_eq_left hQ,ite_eq_left hK]

end PTX.Kernels.TmlFa4Fwd.Softmax
