-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxFirstBiasSources
public import Kernels.TmlFa4Fwd.Proof.MmaGeometry
public import Kernels.TmlFa4Fwd.Proof.SoftmaxNumerics
import Kernels.TmlFa4Fwd.Proof.ResultGeometry

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX

noncomputable section

/-- The column extent of the 128-row causal stage containing this row. -/
def biasStageBlocks (p : Params) (batch row : Nat) : Nat :=
  (min ((row / 128 + 1) * 128 + (p.kLength batch - p.qLength batch))
    (p.kLength batch) + 127) / 128

/-- The priming copy selects the final two 64-column Bias boxes in either stage. -/
def firstVisitBiasBoxColumn (half : Fin 2) : Nat :=
  1152 + 64 * half.val

theorem firstVisitBiasBoxColumnBounds (half : Fin 2) :
    firstVisitBiasBoxColumn half + 64 ≤ 1280 := by
  have hHalf := half.isLt
  unfold firstVisitBiasBoxColumn
  omega

theorem keyCount_le_biasStageBlocks (p : Params) (batch row : Nat) :
    p.keyCount batch row ≤ 128 * biasStageBlocks p batch row := by
  unfold Params.keyCount biasStageBlocks
  have hRow : row + 1 ≤ (row / 128 + 1) * 128 := by omega
  omega

theorem biasStageBlocks_le_trips (p : Params) (batch tile row : Nat)
    (hTile : row < 256 * (tile + 1)) : biasStageBlocks p batch row ≤ Mma.trips p batch tile := by
  unfold biasStageBlocks Mma.trips
  have hRow : (row / 128 + 1) * 128 ≤ 256 * (tile + 1) := by omega
  omega

/-- For a visible first-visit key, the stage reaches the same final block as its pair of
query stages. The earlier stage's extra leading block can only contain masked keys. -/
theorem firstVisitLiveBiasStage {p : Params} {batch tile row col : Nat}
    (hTile : row < 256 * (tile + 1))
    (hLive : visitKey (Mma.trips p batch tile) 0 col < p.keyCount batch row) :
    biasStageBlocks p batch row = Mma.trips p batch tile := by
  have hLo := keyCount_le_biasStageBlocks p batch row
  have hHi := biasStageBlocks_le_trips p batch tile row hTile
  unfold visitKey at hLive
  omega

/-- Both physical Bias boxes read exactly the specification column for each live key of
the first visit. This covers a partial tail without assuming the dummy stage is visible. -/
theorem firstVisitLiveBiasColumn {p : Params} {batch tile row col : Nat}
    (hTile : row < 256 * (tile + 1)) (hCol : col < 128)
    (hLive : visitKey (Mma.trips p batch tile) 0 col < p.keyCount batch row) :
    let half : Fin 2 := ⟨col / 64, by omega⟩
    p.biasColumn batch row (visitKey (Mma.trips p batch tile) 0 col) =
      (firstVisitBiasBoxColumn half + col % 64 : Nat) := by
  let blocks := Mma.trips p batch tile
  have hStage := firstVisitLiveBiasStage hTile hLive
  have hCount := keyCount_le_biasStageBlocks p batch row
  have hp : 0 < blocks := by dsimp [blocks]; omega
  have hCast : ((blocks - 1 : Nat) : Int) = (blocks : Int) - 1 := Nat.cast_sub (by omega)
  change p.biasColumn batch row (128 * (blocks - 1) + col) = _
  rw [p.biasColumn_of_block]
  change 128 * (10 + ((blocks - 1 : Nat) : Int) - (biasStageBlocks p batch row : Int)) + col = _
  rw [hCast, hStage]
  unfold firstVisitBiasBoxColumn
  dsimp only [blocks]
  omega

/-- The logical columns of the two selected first-visit boxes, prior to the causal mask. -/
def firstVisitBiasValue (p : Params) (batch row head col : Nat) : Option ℝ :=
  let half : Fin 2 := ⟨col / 64 % 2, Nat.mod_lt _ (by decide)⟩
  biasBoxValue p (p.qOffset batch + row) head
    (firstVisitBiasBoxColumn half + col % 64)

/-- The actual physical first-visit column supplies the logical Bias value for every live key. -/
theorem firstVisitLiveBiasValue {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {batch tile row head col : Nat} (hb : batch < p.batch) (hRow : row < p.qLength batch)
    (hTile : row < 256 * (tile + 1)) (hCol : col < 128)
    (hLive : visitKey (Mma.trips p batch tile) 0 col < p.keyCount batch row) :
    let key := visitKey (Mma.trips p batch tile) 0 col
    let bc := p.biasColumn batch row key
    0 ≤ bc ∧ bc < 1280 ∧
      firstVisitBiasValue p batch row head col =
        p.bias (p.qOffset batch + row) head bc.toNat := by
  let half : Fin 2 := ⟨col / 64, by omega⟩
  let physical := firstVisitBiasBoxColumn half + col % 64
  have hColumn := firstVisitLiveBiasColumn hTile hCol hLive
  change p.biasColumn batch row (visitKey (Mma.trips p batch tile) 0 col) =
    (physical : Int) at hColumn
  have hBounds := firstVisitBiasBoxColumnBounds half
  have hPhysical : physical < 1280 := by dsimp [physical]; omega
  have hRowPack := hp.packedRow_lt hb hRow
  have hHalf : (⟨col / 64 % 2, Nat.mod_lt _ (by decide)⟩ : Fin 2) = half := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt half.isLt
  dsimp only
  rw [hColumn]
  refine ⟨by omega, by omega, ?_⟩
  simp only [firstVisitBiasValue, hHalf, Int.toNat_natCast, biasBoxValue]
  exact ite_eq_left (by omega)

/-- The box-based vector word consists of the two consecutive first-visit columns. -/
theorem firstVisitBiasSourceWord {p : Params} {l : Launch}
    {g batch base head : Nat} (i : Fin 16) {word : Nat} (hWord : word < 4) :
    let row := 128 * base + (g % l.block) % 128
    firstBiasSourceWord p l g (p.qOffset batch + 128 * base) head firstVisitBiasBoxColumn i word =
      biasLoadWord (firstVisitBiasValue p batch row head (8 * i.val + 2 * word))
        (firstVisitBiasValue p batch row head (8 * i.val + 2 * word + 1)) := by
  let row := 128 * base + (g % l.block) % 128
  have hVector := i.isLt
  have hValue (b : Nat) (hb : b < 2) :
      firstVisitBiasValue p batch row head (8 * i.val + 2 * word + b) =
        biasBoxValue p (p.qOffset batch + row) head
          (firstVisitBiasBoxColumn (biasVectorHalf i) + (8 * (i.val % 8) + 2 * word) + b) := by
    have hHalf : (⟨(8 * i.val + 2 * word + b) / 64 % 2, Nat.mod_lt _ (by decide)⟩ : Fin 2) =
        biasVectorHalf i := by
      apply Fin.ext
      change (8 * i.val + 2 * word + b) / 64 % 2 = i.val / 8
      omega
    have hWithin : (8 * i.val + 2 * word + b) % 64 = 8 * (i.val % 8) + 2 * word + b := by
      omega
    simp only [firstVisitBiasValue, hHalf, hWithin, ← Nat.add_assoc]
  have hLow := hValue 0 (by decide)
  simp only [Nat.add_zero] at hLow
  dsimp only
  rw [hLow, hValue 1 (by decide)]
  simp only [firstBiasSourceWord, row, Nat.add_assoc]

/-- The selected descriptor words unpack to the first-visit Bias values in logical key order. -/
theorem firstVisitBiasUnpackedOfBoxes {p : Params} {l : Launch} {u : TState}
    {g batch base head : Nat}
    (hWords : ∀ i,
      BiasUnpacked false i u (firstBiasSourceWord p l g (p.qOffset batch + 128 * base) head
        firstVisitBiasBoxColumn i)) :
    ∀ i : Fin 16,
      let row := 128 * base + (g % l.block) % 128
      let bias := firstVisitBiasValue p batch row head
      BiasUnpacked false i u (fun k => biasLoadWord (bias (8 * i.val + 2 * k))
        (bias (8 * i.val + 2 * k + 1))) := by
  intro i
  dsimp only [BiasUnpacked]
  intro k hk
  simpa only [firstVisitBiasSourceWord i hk] using hWords i k hk

end
end PTX.Kernels.TmlFa4Fwd.Softmax
