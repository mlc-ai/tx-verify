-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tcgen05.TcMmaResultLayout

@[expose] public section

/-! # Zero output masks write every result cell

A proof tool for kernels whose MMAs have `M = 64`, one CTA in the group and zero output lane masks:
every result cell (`resultCell`) is a written cell (`writeCell`), so the accumulator read of such an
MMA (`MmaReadCell`) is a write of the same cell. -/

namespace PTX.TcMma

/-- A represented result cell lies inside the logical matrix dimensions. -/
theorem resultCell_rows {s : OperandSpec} {base row col : Nat} {cell : Cell}
    (h : resultCell s base row col = some cell) : row < s.descriptor.m ∧ col < s.descriptor.n := by
  unfold resultCell at h
  dsimp only at h
  split at h
  · rename_i hguard
    obtain ⟨-, -, hr, hc, -⟩ := hguard
    exact ⟨hr, hc⟩
  · cases h

/-- **Zero output masks write every result cell** of an M 64 group-one MMA. -/
theorem writeCell_zeroMask {s : OperandSpec} {base row col : Nat} {cell : Cell}
    (hg : s.descriptor.group = .one) (hm : s.descriptor.m = 64)
    (hc : resultCell s base row col = some cell) :
    writeCell s base [0, 0, 0, 0] row col = some cell := by
  have hr : row < 64 := hm ▸ (resultCell_rows hc).1
  have hl : cell.lane < 128 := (resultCell_bounds hc).1
  have hv : OutputMaskValid s.descriptor.group [0, 0, 0, 0] := by
    rw [hg]
    decide
  have hrow : row / (s.descriptor.m / s.descriptor.group.size) = 0 := by
    rw [hm, hg]
    exact Nat.div_eq_of_lt hr
  have hword : ([0, 0, 0, 0] : List Nat)[cell.lane / 32]? = some 0 := by
    have he : cell.lane / 32 < 4 := by omega
    have h4 : cell.lane / 32 = 0 ∨ cell.lane / 32 = 1 ∨ cell.lane / 32 = 2 ∨
        cell.lane / 32 = 3 := by omega
    rcases h4 with h | h | h | h <;> rw [h] <;> rfl
  simp only [writeCell, hv, not_true_eq_false, ite_false, hc, hrow, Nat.zero_mul,
    Nat.zero_add, bind, Option.bind, hword, Nat.zero_div, Nat.zero_mod, ite_true]

end PTX.TcMma
