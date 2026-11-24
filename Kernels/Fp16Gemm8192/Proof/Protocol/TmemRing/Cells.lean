-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Protocol.TmemRing.Values

@[expose] public section

/-! # The cells of the accumulator ring

An MMA of the kernel (`InputRing.mmaSpec`, at column `256 * (w % 2)`, unmasked) writes, for row
`row < 256` and column `col < 256` of its result, the cell of lane `row % 128` and column
`256 * (w % 2) + col` in CTA `row / 128` of its pair (`writeCell_mma`, `writeCell_mma_of`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof TcMma

noncomputable section

namespace TmemRing

variable {L : Launch}

/-- The result layout of the kernel's MMAs: the full-datapath layout of the CTA pair. -/
theorem resultCell_mma {cta w s j row col : Nat} :
    resultCell (InputRing.mmaSpec L cta w s j) (256 * (w % 2)) row col =
      if row < 256 ∧ col < 256 then
        some ⟨cta / 2 * 2 + row / 128, row % 128, 256 * (w % 2) + col⟩
      else none := by
  have hw : w % 2 < 2 := Nat.mod_lt _ (by decide)
  have hv : Valid InputRing.mmaDescriptor := by decide
  have h1 : 256 * (w % 2) / 2 ^ 16 = 0 := by omega
  have h2 : 256 * (w % 2) % 2 ^ 16 = 256 * (w % 2) := by omega
  unfold resultCell
  simp only [InputRing.mmaSpec, h1, h2, CtaGroup.size, LaneAligned, resultColumns,
    InputRing.mmaDescriptor] at hv ⊢
  by_cases hr : row < 256 <;> by_cases hc : col < 256
  · have h3 : 256 * (w % 2) + 256 ≤ 512 := by omega
    simp only [hv, hr, hc, true_or, and_self, h3, ↓reduceIte]
    by_cases hlo : row < 128
    · simp [hlo, show row / 128 = 0 by omega]
    · simp [hlo, show row / 128 = 1 by omega]
  all_goals simp [hr, hc]

/-- **The cell an MMA writes.** -/
theorem writeCell_mma {cta w s j row col : Nat} {cell : Cell}
    (h : writeCell (InputRing.mmaSpec L cta w s j) (256 * (w % 2)) (List.replicate 8 0) row col =
      some cell) :
    row < 256 ∧ col < 256 ∧
      cell = ⟨cta / 2 * 2 + row / 128, row % 128, 256 * (w % 2) + col⟩ := by
  have h1 := writeCell_resultCell h
  rw [resultCell_mma] at h1
  split_ifs at h1 with hrc
  · exact ⟨hrc.1, hrc.2, (Option.some.inj h1).symm⟩

/-- **An MMA writes each cell of its rows and columns.** -/
theorem writeCell_mma_of {cta w s j row col : Nat} (hr : row < 256) (hc : col < 256) :
    writeCell (InputRing.mmaSpec L cta w s j) (256 * (w % 2)) (List.replicate 8 0) row col =
      some ⟨cta / 2 * 2 + row / 128, row % 128, 256 * (w % 2) + col⟩ := by
  have hrc := resultCell_mma (L := L) (cta := cta) (w := w) (s := s) (j := j) (row := row)
    (col := col)
  simp only [hr, hc, and_self, ↓reduceIte] at hrc
  unfold writeCell
  have hm : OutputMaskValid (InputRing.mmaSpec L cta w s j).descriptor.group
      (List.replicate 8 0) := by
    simp [OutputMaskValid, InputRing.mmaSpec, InputRing.mmaDescriptor, CtaGroup.size]
  simp only [hm, not_true_eq_false, ↓reduceIte, hrc, Option.bind_eq_bind, Option.bind_some]
  have hl : (row / ((InputRing.mmaSpec L cta w s j).descriptor.m /
      (InputRing.mmaSpec L cta w s j).descriptor.group.size) * 128 + row % 128) / 32 < 8 := by
    simp only [InputRing.mmaSpec, InputRing.mmaDescriptor, CtaGroup.size]
    omega
  rw [List.getElem?_replicate_of_lt hl]
  simp

end TmemRing

end
end PTX.Kernels.Fp16Gemm8192.Proof
