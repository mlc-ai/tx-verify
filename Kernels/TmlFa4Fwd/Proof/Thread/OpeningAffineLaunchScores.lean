-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningBiasAffineNumerics
import Kernels.TmlFa4Fwd.Proof.Thread.OpeningScoreLoadWords

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof Epilogue
open scoped BigOperators

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
    {g batch wait : Nat} {stage : Fin 2} (run : OpeningAffineLane p l X g batch stage wait)
    (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
include hp hX hFrame run hb hLo hHi

/-- The opening affine replay's dot is the canonical sum of the selected Q and K operands. -/
theorem OpeningAffineLane.dotOfLaunch (col : Fin 128) :
    let coords := assignedCoordinates p batch (g/l.block)
    let row := 128*(2*coords.1+stage.val)+(g%l.block)%128
    let key := visitKey (PTX.Kernels.TmlFa4Fwd.Mma.trips p batch coords.1) 0 col.val
    run.dot col.val = ∑ d ∈ Finset.range 128,
      Mma.qkQuery p (p.qOffset batch+row) coords.2 d * Mma.qkKey p batch coords.2 key d := by
  let q : Fin 4 := ⟨col.val/32, by have := col.isLt; omega⟩
  let k : Fin 32 := ⟨col.val%32, Nat.mod_lt _ (by decide)⟩
  have hColumn : 32*q.val+k.val = col.val := by dsimp [q,k]; omega
  have hSource := scoreLoadDotOfOpeningResult hp hX (hFrame.metadataProtected hp).1 hFrame
    hb q hLo hHi (run.entry.scores.values.1 q).2 run.entry.scores.acquire k
  have hWord := Option.some.inj ((run.words q k).symm.trans hSource)
  have hDot : run.dot (32*q.val+k.val) = _ := (Value.float.inj hWord).2
  let coords := assignedCoordinates p batch (g/l.block)
  have hBase : p.qOffset batch+256*coords.1+128*stage.val+(g%l.block)%128 =
      p.qOffset batch+(128*(2*coords.1+stage.val)+(g%l.block)%128) := by omega
  dsimp only at hDot ⊢
  simp only [firstScoreDot, firstScoreColumn, scoreRow_eq_tid, hColumn] at hDot
  change run.dot col.val = ∑ d ∈ Finset.range 128,
    Mma.qkQuery p (p.qOffset batch+256*coords.1+128*stage.val+(g%l.block)%128) coords.2 d *
      Mma.qkKey p batch coords.2 (visitKey (Mma.trips p batch coords.1) 0 col.val) d at hDot
  rwa [hBase] at hDot

/-- Masking the values computed by the actual first affine pass gives the specification logit. -/
theorem OpeningAffineLane.maskedLogitOfLaunch (col : Fin 128) :
    let coords := assignedCoordinates p batch (g/l.block)
    let row := 128*(2*coords.1+stage.val)+(g%l.block)%128
    let blocks := PTX.Kernels.TmlFa4Fwd.Mma.trips p batch coords.1
    row < p.qLength batch →
    firstMaskedValue p batch row blocks (firstBiasLogit (abiFloat p.invScaleBits)
      (firstBiasRegisterValue (openingBiasColumns p l g batch stage))
      (firstQkRegisterValue run.dot)) col.val =
        maskedLogit p batch coords.2 row (visitKey blocks 0 col.val) := by
  let coords := assignedCoordinates p batch (g/l.block)
  let row := 128*(2*coords.1+stage.val)+(g%l.block)%128
  let blocks := PTX.Kernels.TmlFa4Fwd.Mma.trips p batch coords.1
  let key := visitKey blocks 0 col.val
  change row < p.qLength batch → firstMaskedValue p batch row blocks
    (firstBiasLogit (abiFloat p.invScaleBits)
      (firstBiasRegisterValue (openingBiasColumns p l g batch stage))
      (firstQkRegisterValue run.dot)) col.val = maskedLogit p batch coords.2 row key
  intro hRow
  by_cases hKey : key < p.keyCount batch row
  · have hTile : row < 256*(coords.1+1) := by
      have hStage := stage.isLt
      have hLane : (g % l.block) % 128 < 128 := Nat.mod_lt _ (by decide)
      dsimp [row]
      omega
    have hHead : coords.2 < p.heads := (assignedCoordinates_valid hp hLo hHi).2
    obtain ⟨hBcLo,hBcHi,hBias⟩ :=
      firstVisitLiveBiasValue hp hb hRow hTile col.isLt hKey
    have hQ : p.qOffset batch+row < p.totalQ := hp.packedRow_lt hb hRow
    have hK : key < p.kLength batch := hKey.trans_le (Nat.min_le_left ..)
    have hDot : run.dot col.val = queryKeyDot p batch coords.2 row key := by
      have hValue := run.dotOfLaunch hp hX hFrame hb hLo hHi col
      change run.dot col.val = ∑ d ∈ Finset.range 128,
        Mma.qkQuery p (p.qOffset batch+row) coords.2 d * Mma.qkKey p batch coords.2 key d at hValue
      simpa only [queryKeyDot, Mma.qkQuery, Mma.qkKey, ite_eq_left hQ, ite_eq_left hK] using hValue
    rw [firstMaskedValue, ite_eq_left hKey, firstBiasLogitOfColumns _ _ _ col.isLt, hDot]
    change affineScore (abiFloat p.invScaleBits) (queryKeyDot p batch coords.2 row key)
      (firstVisitBiasValue p batch row coords.2 col.val) = _
    rw [hBias]
    exact biasedLogit_eq hp hb hRow hHead hBcLo hBcHi
  · simp only [firstMaskedValue, maskedLogit, key, hKey, ite_false]

end PTX.Kernels.TmlFa4Fwd.Softmax
