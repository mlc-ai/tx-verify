-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Values.TileGeom
public import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.InputBytes

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Values

variable {p : Params} {L : Launch} {m : Mem0} {b row h j : Nat}

/-- A key to the left of the ten packed bias blocks is in the causal prefix. -/
theorem attended_left (hq : row < p.qLength b) (hleft : p.biasColumn b row j < 0) :
    j < p.keyCount b row := by
  dsimp only [Params.biasColumn] at hleft
  unfold Params.keyCount
  omega

/-- At a valid row and head, the physical bias element of an attended key is its named
bias, including the zero fill outside the descriptor. -/
theorem tile_bias_input (hp : Pre p L m) (hb : b < p.batch) (hh : h < p.heads)
    (hq : row < p.qLength b) (c : Fin 3 → Int) (hc : c 0 = p.biasColumn b row j)
    (hr : c 1 = p.qOffset b + (row : Int)) (hhead : c 2 = h)
    (hcut : j < p.keyCount b row ∨ p.biasColumn b row j < 1280) :
    inputVal p true c = if j < p.keyCount b row then some (biasAt p b h row j) else none := by
  have ht := hp.qOffset_le_total (show b+1 ≤ p.batch by omega)
  have hq' := hq
  unfold Params.qLength at hq'
  have rrange : 0 ≤ c 1 ∧ c 1 < (p.totalQ + 128 : Nat) := by rw [hr]; push_cast; omega
  have headRange : 0 ≤ c 2 ∧ c 2 < p.heads := by rw [hhead]; omega
  have inside : Inside 1280 (p.totalQ+128) p.heads c ↔
      0 ≤ p.biasColumn b row j ∧ p.biasColumn b row j < 1280 := by
    simp only [Inside,hc,rrange.1,rrange.2,headRange.1,headRange.2,and_true,Nat.cast_ofNat]
  have rowNat : (c 1).toNat = p.qOffset b + row := by rw [hr]; omega
  simp only [inputVal, ite_true, inside, rowNat, hhead, Int.toNat_natCast, hc, biasAt]
  split <;> rename_i hcol
  · obtain ⟨hlo,hhi⟩ := hcol
    have mask := hp.biasMask b hb row hq h hh j hlo hhi
    by_cases hk : j < p.keyCount b row <;>
      cases eq : p.bias (p.qOffset b + row) h (p.biasColumn b row j).toNat <;>
      simp [eq,hk] at mask ⊢
  · have key : j < p.keyCount b row := by
      rcases hcut with key | hi
      · exact key
      · exact attended_left hq (by omega)
    simp only [key, ite_true]

end PTX.Kernels.TmlFa4Fwd.Proof.Values
