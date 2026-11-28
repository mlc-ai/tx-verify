-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.ExpVal5
public import Kernels.InklingRelDecode.Proof.Softmax.Data.ExpWindow

@[expose] public section

/-! # The exponent window on exact inputs

From the exact values of the masked scores `xs`, the scale `sc` and the shift `c` (`Ev` of the
registers the window reads), the registers after the window are exact: word `c'` of the
probability store is `pWord X c'` and the row sum (register 1529) is the sum of `pw2 (X r)`, where
`X r = xs (srcTab ((r - 1288) / 2)) * sc + c` is the shifted score of register `r`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Flow PTX.Proof PTX.Assumption

set_option maxRecDepth 100000
noncomputable section

/-- **What the exponent window reads, exactly**. -/
structure ExpInX (V : Nat → Value) (xs : Nat → EReal) (sc c : ℝ) : Prop where
  hs : ∀ r ∈ scoreRegs, Ev (V r) (xs r)
  h498 : Ev (V 498) sc
  pos : 0 < sc
  hc : Ev (Gen.ex1_v1848 V) c
  q179 : ∃ q, V 179 = .pred q
  q180 : ∃ q, V 180 = .pred q

/-- The shifted score of register `r`. -/
def shifted (xs : Nat → EReal) (sc c : ℝ) (r : Nat) : EReal := xs (srcTab ((r - 1288) / 2)) * sc + c

theorem swY_ev {v : Value} {x : EReal} (h : Ev v x) : swY v = .float .f32 (pw2 x) := by
  simp only [swY, h.read, pw2, Real.rpow_eq_pow]

theorem swTab_eq : ∀ i < 16, swX (swPc i) = swTab i := by decide +kernel

theorem vE1_ev {V : Nat → Value} {xs : Nat → EReal} {sc c : ℝ} (h : ExpInX V xs sc c) :
    ∀ r ∈ xRegs, Ev (vE1 V r) (shifted xs sc c r) :=
  fun _ hr => V'_out runE1 runE1_ok (P := fun r v => Ev v (shifted xs sc c r))
    (e1_ev h.hs h.h498 h.pos h.hc) hr

theorem vE2_ev {V : Nat → Value} {xs : Nat → EReal} {sc c : ℝ} (h : ExpInX V xs sc c) :
    (∀ r ∈ xRegs, Ev (vE2 V r) (shifted xs sc c r)) ∧
    (∀ r, 1271 ≤ r → r < 1287 → vE2 V r = .float .f32 (pw2 (shifted xs sc c (swTab (r - 1271))))) ∧
    (∃ q, vE2 V 179 = .pred q) ∧ ∃ q, vE2 V 180 = .pred q := by
  obtain ⟨-, -, -, -, k4, k5⟩ := kE_ok
  refine ⟨fun r hr => ?_, fun r h1 h2 => ?_, ?_, ?_⟩
  · have hn := List.all_eq_true.mp k4 r hr
    rw [vE2, swVs_other fun j hj => by simpa using List.all_eq_true.mp hn j (by simpa using hj)]
    exact vE1_ev h r hr
  · obtain ⟨i, hi, rfl⟩ : ∃ i, i < 16 ∧ r = 1271 + i := ⟨r - 1271, by omega, by omega⟩
    have e : swR (swPc i) = 1271 + i := by
      simpa using List.all_eq_true.mp k5 i (by simpa using hi)
    have hx : swTab i ∈ xRegs := by
      have : ∀ i < 16, swTab i ∈ xRegs := by decide +kernel
      exact this i hi
    have hxe := vE1_ev h (swTab i) hx
    have o := swVs_out (V := vE1 V) hi (le_refl 16)
    rw [e, swTab_eq i hi, swY_ev hxe] at o
    rw [vE2, o, Nat.add_sub_cancel_left]
  · have n : (179 : Nat) ∉ runE1.outs := by decide +kernel
    have s : ∀ j < 16, (179 : Nat) ≠ swR (swPc j) := by decide +kernel
    rw [vE2, swVs_other s, vE1, V'_notin runE1 runE1_ok V n]
    exact h.q179
  · have n : (180 : Nat) ∉ runE1.outs := by decide +kernel
    have s : ∀ j < 16, (180 : Nat) ≠ swR (swPc j) := by decide +kernel
    rw [vE2, swVs_other s, vE1, V'_notin runE1 runE1_ok V n]
    exact h.q180

/-- **The window's words, exactly**: word `c'` of the probability store and the row sum. -/
theorem exp_exact {V : Nat → Value} {xs : Nat → EReal} {sc c : ℝ} (h : ExpInX V xs sc c) :
    (∀ c' < 32, vP2 (vP1 (vE3 V)) (1677 + c') = pWord (shifted xs sc c) c') ∧
      vE3 V 1529 = .float .f32 ((xRegs.map fun r => pw2 (shifted xs sc c r)).sum) := by
  obtain ⟨hx, hy, ⟨q, hq⟩, ⟨q', hq'⟩⟩ := vE2_ev h
  refine ⟨fun c' hc => ?_, ?_⟩
  · have := p_words hx hy hq hq' c' hc
    rwa [Nat.add_sub_cancel_left] at this
  · have m : (1529 : Nat) ∈ runE2.outs := by decide +kernel
    exact V'_out runE2 runE2_ok (P := fun r v => 1529 = r → v = .float .f32
      ((xRegs.map fun r => pw2 (shifted xs sc c r)).sum))
      (fun p hp => (e2_regs hx hy hq hq' p hp).2.2) m rfl

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
