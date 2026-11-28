-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.MmaFoot

@[expose] public section

/-! # The cell of a QK result

A written cell of a QK MMA (M 64, N 128, `.ws`, two column blocks, D at 400) for output
`(row, col)` is lane `row + 64 (col / 64)`, column `400 + col % 64`; the A row of the output is
that lane (`qk_cell_geom`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MmaFoot
open PTX

noncomputable section

/-- **The geometry of a QK result cell.** -/
theorem qk_cell_geom {s : TcMma.OperandSpec} (hD : s.descriptor = qkD) {row col : Nat}
    {cell : TcMma.Cell} (h : TcMma.writeCell s 400 [0, 0, 0, 0] row col = some cell) :
    row < 64 ∧ col < 128 ∧ cell.lane = row + 64 * (col / 64) ∧ cell.column = 400 + col % 64 ∧
      TcMma.operandRow s.descriptor row col = cell.lane := by
  have hr : TcMma.resultCell s 400 row col = some cell := by
    simp only [TcMma.writeCell] at h
    split at h
    · cases h
    · cases hr : TcMma.resultCell s 400 row col with
      | none => simp [hr] at h
      | some c =>
        simp only [hr, Option.bind_eq_bind, Option.bind_some] at h
        cases hw : ([0, 0, 0, 0] : List Nat)[((row / (s.descriptor.m /
          s.descriptor.group.size)) * 128 + c.lane) / 32]? <;>
          simp only [hw, Option.bind_none, Option.bind_some, reduceCtorEq] at h
        split at h
        · exact (Option.some.inj h) ▸ rfl
        · cases h
  simp only [TcMma.resultCell, hD, qkD] at hr
  split at hr
  · rename_i hok
    obtain ⟨-, -, hrow, hcol, -⟩ := hok
    simp only [TcMma.columnBlocks, TcMma.halfDatapath] at hr hrow hcol
    simp at hr hrow hcol
    have hs : (CtaGroup.one).size = 1 := rfl
    simp only [hs, show ¬ (64 = 128 * 1) by decide, ↓reduceIte, Nat.div_one,
      Option.some.injEq] at hr
    subst hr
    refine ⟨hrow, hcol, ?_, rfl, ?_⟩
    · simp only [show 128 / 64 = 2 by decide, Nat.mod_eq_of_lt hrow]
    · simp only [hD, TcMma.operandRow, qkD, TcMma.columnBlocks, hs, Nat.div_one,
        Nat.mod_eq_of_lt hrow]
      simp
  · cases hr

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MmaFoot
