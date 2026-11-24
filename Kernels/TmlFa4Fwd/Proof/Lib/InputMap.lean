-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Spec
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring

@[expose] public section

/-! # The packed Q and bias descriptors' lookups -/

namespace PTX.Kernels.TmlFa4Fwd

open TensorDescriptor
noncomputable section

/-- The rank-three input coordinates are column, absolute packed row and head. -/
def inputCoordinate (col row head : Nat) : Fin 3 → Int := ![(col : Int), (row : Int), (head : Int)]

private def packedInput (base cols rows heads : Nat) : TensorAddress.Geometry 3 :=
  ⟨base, 2, ![cols, rows, heads], ![2, 2 * cols * heads, 2 * cols]⟩

private theorem packedInput_lookup (base cols rows heads col row head byte : Nat) :
    TensorAddress.lookup (packedInput base cols rows heads) (inputCoordinate col row head) byte =
      if (col < cols ∧ row < rows ∧ head < heads) ∧ byte < 2 then
        some (base + 2 * ((row * heads + head) * cols + col) + byte)
      else none := by
  have hb : TensorAddress.InBounds (packedInput base cols rows heads)
      (inputCoordinate col row head) ↔ col < cols ∧ row < rows ∧ head < heads := by
    constructor
    · intro h
      exact ⟨by simpa [packedInput, inputCoordinate] using (h 0).2,
        by simpa [packedInput, inputCoordinate] using (h 1).2,
        by simpa [packedInput, inputCoordinate] using (h 2).2⟩
    · intro h axis
      fin_cases axis <;> simp [packedInput, inputCoordinate, h.1, h.2.1, h.2.2]
  have haddr :
      TensorAddress.byteAddress (packedInput base cols rows heads) (inputCoordinate col row head)
        byte = base + 2 * ((row * heads + head) * cols + col) + byte := by
    unfold TensorAddress.byteAddress
    rw [Fin.sum_univ_three]
    change base + ((col : Int).toNat * 2 + (row : Int).toNat * (2 * cols * heads) +
      (head : Int).toNat * (2 * cols)) + byte = _
    simp only [Int.toNat_natCast]
    ring
  unfold TensorAddress.lookup
  by_cases h : (col < cols ∧ row < rows ∧ head < heads) ∧ byte < 2
  · rw [ite_eq_left ⟨hb.mpr h.1, h.2⟩, ite_eq_left h, haddr]
  · rw [ite_eq_right (fun ht => h ⟨hb.mp ht.1, ht.2⟩), ite_eq_right h]

/-- Exact lookup for any nonnegative coordinates of the packed Q descriptor. -/
theorem qLookup_eq (p : Params) (col row head byte : Nat) :
    TensorAddress.lookup (geometry p.qMap) (inputCoordinate col row head) byte =
      if (col < 128 ∧ row < p.totalQ ∧ head < p.heads) ∧ byte < 2 then
        some ((p.qLoc row head col).at byte).addr else none :=
  packedInput_lookup p.qBase 128 p.totalQ p.heads col row head byte

/-- Exact lookup for the packed bias, including its 128 rows after the last packed query. -/
theorem biasLookup_eq (p : Params) (col row head byte : Nat) :
    TensorAddress.lookup (geometry p.biasMap) (inputCoordinate col row head) byte =
      if (col < 1280 ∧ row < p.totalQ + 128 ∧ head < p.heads) ∧ byte < 2 then
        some ((p.biasLoc row head col).at byte).addr else none :=
  packedInput_lookup p.biasBase 1280 (p.totalQ + 128) p.heads col row head byte

end
end PTX.Kernels.TmlFa4Fwd
