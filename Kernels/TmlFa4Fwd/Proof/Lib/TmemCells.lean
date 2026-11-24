-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Lib.TmemRegion
public import Core.Tc.TcMmaResultLayout

@[expose] public section

/-! # The Tensor Memory cells of the QK and PV MMAs

An MMA of tml-fa4 is 128 × 128 of one CTA with zero lane masks: result element `(row, col)` is the
cell of lane `row`, column `base + col`. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Tm
open PTX PTX.Flow TcMma

noncomputable section

theorem qkDsc_valid : Valid qkDsc := by decide
theorem pvDsc_valid : Valid pvDsc := by decide

/-- The operands of one CTA's 128 × 128 MMA. -/
structure Spec128 (s : OperandSpec) (c : Nat) : Prop where
  dsc : s.descriptor = qkDsc ∨ s.descriptor = pvDsc
  low : s.lowCta = c
  high : s.highCta = c

theorem resultCell_128 {s : OperandSpec} {c base row col : Nat} (hs : Spec128 s c)
    (hb : base + 128 ≤ 512) (hr : row < 128) (hc : col < 128) :
    resultCell s base row col = some ⟨c, row, base + col⟩ := by
  obtain ⟨hd, hl, hh⟩ := hs
  have e1 : base / 2 ^ 16 = 0 := by omega
  have e2 : base % 2 ^ 16 = base := by omega
  unfold resultCell
  simp only [e1, e2]
  rcases hd with hd | hd <;> rw [hd] <;>
    simp [qkDsc_valid, pvDsc_valid, LaneAligned, resultColumns, CtaGroup.size, hl, hh] <;>
    simp [qkDsc, pvDsc, hr, hc, hb]

theorem resultCell_128_iff {s : OperandSpec} {c base row col : Nat} {cell : Cell}
    (hs : Spec128 s c) (hb : base + 128 ≤ 512) (h : resultCell s base row col = some cell) :
    row < 128 ∧ col < 128 ∧ cell = ⟨c, row, base + col⟩ := by
  have hrc : row < 128 ∧ col < 128 := by
    unfold resultCell at h
    simp only at h
    split at h
    · rename_i hv
      obtain ⟨-, -, h1, h2, -⟩ := hv
      rcases hs.dsc with hd | hd <;> rw [hd] at h1 h2 <;> exact ⟨h1, h2⟩
    · cases h
  refine ⟨hrc.1, hrc.2, ?_⟩
  rw [resultCell_128 hs hb hrc.1 hrc.2] at h
  exact (Option.some.inj h).symm

theorem writeCell_zero {s : OperandSpec} {c base row col : Nat} (hs : Spec128 s c)
    (hb : base + 128 ≤ 512) :
    writeCell s base [0, 0, 0, 0] row col = resultCell s base row col := by
  have hm : OutputMaskValid s.descriptor.group [0, 0, 0, 0] := by
    rcases hs.dsc with hd | hd <;> rw [hd] <;> decide
  unfold writeCell
  simp only [hm, not_true_eq_false, ↓reduceIte]
  cases h : resultCell s base row col with
  | none => rfl
  | some cell =>
    obtain ⟨hr, hc, rfl⟩ := resultCell_128_iff hs hb h
    have hsz : row / (s.descriptor.m / s.descriptor.group.size) = 0 := by
      rcases hs.dsc with hd | hd <;> rw [hd] <;>
        exact Nat.div_eq_of_lt (by simpa [qkDsc, pvDsc, CtaGroup.size] using hr)
    simp only [Option.bind_eq_bind, Option.bind_some, hsz, Nat.zero_mul, Nat.zero_add]
    have hi : row / 32 < 4 := by omega
    have : ([0, 0, 0, 0] : List Nat)[row / 32]? = some 0 := by
      interval_cases row / 32 <;> rfl
    rw [this]
    simp

end
end PTX.Kernels.TmlFa4Fwd.Proof.Tm
