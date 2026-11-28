-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.AlphaNum
public import Lemmas.Flow.CvtBf
import Lemmas.Flow.W0Reads
import Lemmas.Flow.Step.RuleStep

@[expose] public section

/-! # Words that read as numbers: the exponent and the probability pack

Closure lemmas for the operations of the exponent window and of the probability pack, in the style
of `NumLib.lean`: the scaled score minus the maximum (`fma`), the product of two numbers (the
rescale), and the conversion of two numbers to a pair of `bf16` numbers (`cvt.rn.bf16x2.f32`,
`bf16Exact`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Flow PTX.Proof PTX.Assumption

noncomputable section

/-- **A number or `-inf` times a positive number plus a number is a number or `-inf`.** -/
theorem fma_has {fz : Bool} {d a b c : Value} (ha : (Kd.s .ni).Has a) (hb : (Kd.s .pw).Has b)
    (hc : (Kd.s .fl).Has c) : (Kd.s .ni).Has (okVal d (floatE (fmaI .rn fz) [a, b, c])) := by
  obtain ⟨x, hx, lx⟩ := SK.lane_of (k := .ni) (by decide) ha
  obtain ⟨-, r, hr, hy⟩ := hb
  obtain ⟨z, hz, lz⟩ := SK.lane_of (k := .fl) (by decide) hc
  obtain ⟨s, rfl⟩ := lz
  have hw : ∃ w, (mulEReal x (r : EReal)).bind (addEReal · (s : EReal)) = some w ∧
      SK.ni.Lane w := by
    rcases lx with ⟨q, rfl⟩ | rfl
    · exact ⟨_, by rw [mulEReal_coe]; exact addEReal_coe .., .inl ⟨_, rfl⟩⟩
    · exact ⟨⊥, by rw [mulEReal_bot_pos hr]; exact addEReal_bot_coe _, .inr rfl⟩
  obtain ⟨w, hw, lw⟩ := hw
  rw [okVal_ok (fmaE_reads hx hy hz hw)]
  exact SK.has_erealValue lw

/-- **The product of two numbers is a number.** -/
theorem mul_fl_has {fz : Bool} {d a b : Value} (ha : (Kd.s .fl).Has a) (hb : (Kd.s .fl).Has b) :
    (Kd.s .fl).Has (okVal d (mulE fz a b)) := by
  obtain ⟨-, r, hr⟩ := ha
  obtain ⟨-, s, hs⟩ := hb
  rw [okVal_ok (mulE_reads hr hs (mulEReal_coe r s))]
  rw [erealValue_coe]
  exact has_float_fl _

/-- A pair of `bf16` numbers (the words of the probability store). -/
def BfNum (v : Value) : Prop := ∃ x y : ℝ, v = .pair (.float .bf16 x) (.float .bf16 y)

/-- **Two numbers convert to a pair of `bf16` numbers.** -/
theorem cvtBf_has {d a b : Value} (ha : (Kd.s .fl).Has a) (hb : (Kd.s .fl).Has b) :
    BfNum (okVal d (cvtBfE a b)) := by
  obtain ⟨-, r, hr⟩ := ha
  obtain ⟨-, s, hs⟩ := hb
  have e : cvtBfE a b = .ok (.pair (.float .bf16 s) (.float .bf16 r)) := by
    simp only [cvtBfE, hr, hs, erealValue_bf16_coe]
  rw [okVal_ok e]
  exact ⟨s, r, rfl⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
