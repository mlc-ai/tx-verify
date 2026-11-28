-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Lib.MmaFoot
public import Lemmas.Tcgen05.TcMmaZeroMask

@[expose] public section

/-! # A QK issue writes every cell a PV issue reads as A

Pure geometry. The A operand of a PV issue (Layout F, 64 rows of 32 bytes at Tensor Memory address
`a < 256`) reads the cells `(lane (row), a + c)` with `c < 8`; a QK issue with destination `d` and
`d ≤ a`, `a + 8 ≤ d + 128` writes every one of them (the same lane map of Layout F, zero masks). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Tmem
open PTX PTX.TcMma

theorem qk_writes_a {s s' : OperandSpec} {d a index : Nat} {cell : Cell} {b : Nat}
    (hq : s.descriptor = Lib.qkDesc) (hv : s'.descriptor = Lib.pvDesc)
    (haT : s'.aTmem = some a) (hlo : s.lowCta = s'.lowCta) (hhi : s.highCta = s'.highCta)
    (hd : d + 128 ≤ 512) (hda : d ≤ a) (hae : a + 8 ≤ d + 128) (_ha : a < 2 ^ 16)
    (hc : aCell s' index = some (cell, b)) :
    ∃ row col, writeCell s d [0, 0, 0, 0] row col = some cell := by
  unfold aCell at hc
  simp only [hv, haT, Option.bind_some] at hc
  split at hc
  · rename_i hcond
    obtain ⟨-, hrow, hcol, hfield⟩ := hcond
    simp only [Option.some.injEq, Prod.mk.injEq] at hc
    obtain ⟨rfl, -⟩ := hc
    simp only [Lib.pvDesc, TcMma.Operand.rows, TcMma.Operand.extent, CtaGroup.size,
      TcMma.Kind.k, TcMma.Kind.width, halfDatapath] at hrow hcol hfield ⊢
    have hr : index / 32 < 64 := by simpa using hrow
    have ha0 : a / 2 ^ 16 = 0 := by omega
    have ham : a % 2 ^ 16 = a := by omega
    have hdm : d % 2 ^ 16 = d := by omega
    have hd0 : d / 2 ^ 16 = 0 := by omega
    have hsmall : index % 32 / 4 < 8 := by omega
    refine ⟨index / 32, a + index % 32 / 4 - d, ?_⟩
    have hg : s.descriptor.group = .one := by rw [hq]; rfl
    have hm : s.descriptor.m = 64 := by rw [hq]; rfl
    refine writeCell_zeroMask hg hm ?_
    simp only [resultCell, hq, Lib.qkDesc, hd0, hdm, halfDatapath, resultColumns, CtaGroup.size]
    rw [ite_eq_left_of_eq_true _ _
      (eq_true ⟨Lib.qkDesc_valid, .inl rfl, hr, by omega, by simp; omega⟩)]
    simp only [hlo, hhi]
    simp
    omega
  · cases hc
/-- **An issue of the kernel writes every cell of its 128 columns in the lanes of its half
datapath** (the `q`-th group of 16 lanes at lane `32 q`), in its CTA. -/
theorem mma_writes_cell {s : OperandSpec} {d q l col cta : Nat} (hv : Valid s.descriptor)
    (hg : s.descriptor.group = .one) (hm : s.descriptor.m = 64) (hn : s.descriptor.n = 128)
    (hws : s.descriptor.ws = false) (hcta : cta = s.lowCta) (hhi : s.highCta = s.lowCta)
    (hd : d + 128 ≤ 512) (hq4 : q < 4) (hl : l < 16) (hlo : d ≤ col) (hhc : col < d + 128) :
    ∃ row c, writeCell s d [0, 0, 0, 0] row c = some ⟨cta, q * 32 + l, col⟩ := by
  have hd0 : d / 2 ^ 16 = 0 := by omega
  have hdm : d % 2 ^ 16 = d := by omega
  refine ⟨q * 16 + l, col - d, writeCell_zeroMask hg hm ?_⟩
  simp only [resultCell, hd0, hdm, halfDatapath, hg, hm, hn, hws, resultColumns, CtaGroup.size]
  rw [ite_eq_left_of_eq_true _ _
    (eq_true ⟨hv, .inl rfl, by omega, by omega, by simp; omega⟩)]
  simp only [hcta, hhi]
  simp
  omega

end PTX.Kernels.InklingRelDecode.Proof.Tmem
