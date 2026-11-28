-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.TmemCells

@[expose] public section

/-! # QK MMA `k`'s A cells are copy `k`'s cells

The A byte `index` of QK MMA `k` (A at column `256 + 8 k`, M 64, 128 rows of 32 bytes) is in the
cell that byte `index` of a `128x256b` copy to column `256 + 8 k` writes: lane `index / 32`,
column `256 + 8 k + index % 32 / 4`, in the issuing CTA. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TmemRow
open PTX

noncomputable section

/-- **The A cell of a QK MMA is the cell of the copy** of the same column. -/
theorem qk_aCell_eq {L : Launch} {g : Nat} {s : TcMma.OperandSpec} {k index b cta : Nat}
    {cell : TcMma.Cell} (hk : k < 16) (hs : MmaOps L g s (some (256 + 8 * k)) qkIdesc)
    (hlo : s.lowCta = cta) (hhi : s.highCta = cta)
    (h : TcMma.aCell s index = some (cell, b)) :
    index < 4096 ∧ cell = TcCopy.cell .s128x256b (256 + 8 * k) cta (index / 32) index := by
  obtain ⟨hidx, rfl⟩ := qk_aCell_cell hk hs h
  refine ⟨hidx, ?_⟩
  have h1 : (256 + 8 * k) % 2 ^ 16 = 256 + 8 * k := Nat.mod_eq_of_lt (by omega)
  have h2 : (256 + 8 * k) / 2 ^ 16 = 0 := Nat.div_eq_of_lt (by omega)
  simp only [TcCopy.cell, TcCpShape.rowBytes, h1, h2, hlo, hhi, Nat.zero_add]
  split <;> rfl

end

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TmemRow
