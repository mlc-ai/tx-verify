-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Lib.MmaFoot
import Mathlib.Tactic.IntervalCases

@[expose] public section

/-! # The cell of a QK result element

Element `(row, col)` of the `64 × 128` result of a QK MMA is written to the lane
`32 (row / 16) + row % 16` of the Tensor Memory of its CTA, at the column `dst + col`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX

theorem desc_cell {D : TcMma.Descriptor} {s : TcMma.OperandSpec} {dst row col : Nat}
    {mask : List Nat} {cell : TcMma.Cell} (hv : TcMma.Valid D) (hn : D.n = 128) (hM : D.m = 64)
    (rc : TcMma.resultColumns D = 128) (hd128 : TcMma.halfDatapath D = true)
    (gs : D.group.size = 1) (hmv : TcMma.OutputMaskValid D.group [0, 0, 0, 0])
    (hD : s.descriptor = D) (hb : dst ≤ 384) (hm : mask = [0, 0, 0, 0])
    (h : TcMma.writeCell s dst mask row col = some cell) :
    row < 64 ∧ col < 128 ∧ cell = ⟨s.lowCta, 32 * (row / 16) + row % 16, dst + col⟩ := by
  unfold TcMma.writeCell TcMma.resultCell at h
  simp only [hD, hm] at h
  have e0 : dst / 2 ^ 16 = 0 := by omega
  have e1 : dst % 2 ^ 16 = dst := by omega
  by_cases hr : row < 64
  · by_cases hc : col < 128
    · have hcond : TcMma.Valid D ∧ TcMma.LaneAligned D (dst / 2 ^ 16) ∧
          row < D.m ∧ col < D.n ∧ dst % 2 ^ 16 + TcMma.resultColumns D ≤ 512 :=
        ⟨hv, Or.inl e0, by omega, by omega, by rw [rc]; omega⟩
      have gm2 : ¬ D.m = 128 * D.group.size := by omega
      simp only [hmv, not_true_eq_false, hcond, ↓reduceIte, hd128, gs, hM, e0, e1] at h
      have hc2 : True ∧ TcMma.LaneAligned D 0 ∧ row < 64 ∧ True ∧
          dst + TcMma.resultColumns D ≤ 512 :=
        ⟨trivial, Or.inl rfl, hr, trivial, by rw [rc]; omega⟩
      have rd : row / 64 = 0 := by omega
      have idx : ((row % 16 + 32 * (row / 16)) / 32) < 4 := by omega
      simp only [hc2, ↓reduceIte, rd, show ¬ (64 = 128 * 1) by decide, Nat.zero_mul,
        Nat.zero_add, Nat.div_one, Nat.mod_eq_of_lt hr] at h
      have gi : ([0, 0, 0, 0] : List ℕ)[(row % 16 + 32 * (row / 16)) / 32]? = some 0 := by
        generalize (row % 16 + 32 * (row / 16)) / 32 = n at idx
        interval_cases n <;> rfl
      simp only [and_self, ↓reduceIte, Option.bind_eq_bind, Option.bind_some, gi] at h
      simp only [Nat.zero_div, Nat.zero_mod, ↓reduceIte] at h
      obtain rfl := Option.some.inj h
      exact ⟨hr, hc, by simp [Nat.add_comm]⟩
    · simp [hn, hc] at h
  · simp [hM, hr] at h

theorem qk_cell {s : TcMma.OperandSpec} {dst b row col : Nat} {mask : List Nat} {cell : TcMma.Cell}
    (hD : s.descriptor = qkDesc) (hd : dst = 128 * (b % 2)) (hm : mask = [0, 0, 0, 0])
    (h : TcMma.writeCell s dst mask row col = some cell) :
    row < 64 ∧ col < 128 ∧ cell = ⟨s.lowCta, 32 * (row / 16) + row % 16, dst + col⟩ :=
  desc_cell qkDesc_valid rfl rfl (by decide) (by decide) rfl (by decide) hD (by omega) hm h

theorem pv_cell {s : TcMma.OperandSpec} {row col : Nat} {mask : List Nat} {cell : TcMma.Cell}
    (hD : s.descriptor = pvDesc) (hm : mask = [0, 0, 0, 0])
    (h : TcMma.writeCell s 256 mask row col = some cell) :
    row < 64 ∧ col < 128 ∧ cell = ⟨s.lowCta, 32 * (row / 16) + row % 16, 256 + col⟩ :=
  desc_cell pvDesc_valid rfl rfl (by decide) (by decide) rfl (by decide) hD (by omega) hm h

end PTX.Kernels.InklingRelDecode.Proof.Lib
