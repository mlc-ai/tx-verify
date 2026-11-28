-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Lib.MmaFoot
public import Lemmas.Tcgen05.TcMmaZeroMask

@[expose] public section

/-! # The cells of a PV issue's A operand

Pure geometry. Row `r = index / 32` of the A operand (Layout F, `M = 64`, half datapath) is in the
lane `16 (r / 16) * 2 + r % 16`, that is `32 (r / 16) + r % 16`, of the issue's CTA, and the byte
`index % 32` is in column `a + index % 32 / 4`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Tmem
open PTX PTX.TcMma

/-- **The cell of a byte of a PV issue's A operand.** -/
theorem a_cell_form {s : OperandSpec} {a index : Nat} {cell : Cell} {b : Nat}
    (hv : s.descriptor = Lib.pvDesc) (haT : s.aTmem = some a) (ha : a < 2 ^ 16)
    (hcta : s.lowCta = s.highCta) (hc : aCell s index = some (cell, b)) :
    cell.cta = s.lowCta ∧ cell.lane = 32 * (index / 32 / 16) + index / 32 % 16 ∧
      cell.column = a + index % 32 / 4 ∧ index / 32 < 64 ∧ b = index % 32 % 4 := by
  unfold aCell at hc
  simp only [hv, haT, Option.bind_some] at hc
  split at hc
  · rename_i hcond
    obtain ⟨-, hrow, -, -⟩ := hcond
    simp only [Option.some.injEq, Prod.mk.injEq] at hc
    obtain ⟨rfl, hb⟩ := hc
    simp only [Lib.pvDesc, TcMma.Operand.rows, TcMma.Operand.extent, CtaGroup.size,
      TcMma.Kind.k, TcMma.Kind.width, halfDatapath] at hrow ⊢
    have ha0 : a / 2 ^ 16 = 0 := by omega
    have ham : a % 2 ^ 16 = a := by omega
    have hr : index / 32 < 64 := by simpa using hrow
    refine ⟨by simp [hcta], ?_, ?_, hr, ?_⟩
    · simp
      omega
    · simp
      omega
    · simp only [Lib.pvDesc, TcMma.Kind.k, TcMma.Kind.width] at hb
      omega
  · cases hc

end PTX.Kernels.InklingRelDecode.Proof.Tmem
