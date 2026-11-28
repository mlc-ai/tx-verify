-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.ShiftExact
public import Kernels.InklingRelDecode.Proof.Softmax.Data.ExpVal6
public import Kernels.InklingRelDecode.Proof.Softmax.Data.ExpTyped

@[expose] public section

/-! # The exponent window's exact inputs

From the exact maximum of the state (`Ev`), the exact maximum the round used and the exact scale,
the registers the exponent window reads are exact (`ExpInX`): the scores, the scale, the shift
`(if Keep a then m else m_safe) * (-scale)` and the two predicates. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Flow PTX.Proof PTX.Assumption Lib.SoftFold Classical

set_option maxRecDepth 100000
noncomputable section

theorem ev_ni {v : Value} {x : EReal} (h : Ev v x) : (Kd.s .ni).Has v := by
  obtain ⟨rfl, hx⟩ := h
  induction x using EReal.rec with
  | bot => exact Or.inr (erealValue_bot)
  | coe r =>
    rw [erealValue_coe]
    exact Or.inl ⟨clean_float r, r, readEReal_float r⟩
  | top => exact absurd rfl hx

theorem alpha_168 (c m mx : Value) : ∃ b, Lib.alphaVal c m mx 168 = .pred b := by
  simp [Lib.alphaVal, Lib.alphaRest, xFinal, XItem.upd, XItem.vals, OItem.vals,
    Function.update, Lib.alphaIn, opndVal]

/-- **The exponent window's inputs are exact.** -/
theorem expInX_of {V : Nat → Value} {xs : Nat → EReal} {c m mx : Value} {sc : ℝ}
    {mE xE : EReal} (hc : Ev c sc) (hpos : 0 < sc) (hm : Ev m mE) (hmx : Ev mx xE)
    (hV : ∀ r, (r = 168 ∨ r = 498 ∨ r = 1914 ∨ r = 1523) → V r = Lib.alphaVal c m mx r)
    (h499 : Ev (V 499) ((-sc : ℝ) : EReal)) (hs : ∀ r ∈ scoreRegs, Ev (V r) (xs r))
    (q179 : ∃ q, V 179 = .pred q) (q180 : ∃ q, V 180 = .pred q) :
    ExpInX V xs sc ((if Keep (alphaLog2 sc mE xE) then mE.toReal else mSafe xE) * (-sc)) := by
  obtain ⟨hmu, hp, -⟩ := alpha_exact hc hpos hm hmx
  have e1914 : V 1914 = m := by rw [hV 1914 (by simp), alphaVal_m]
  have e1523 : V 1523 = Lib.alphaVal c m mx 1523 := hV 1523 (by simp)
  obtain ⟨b, hb⟩ := alpha_168 c m mx
  have byt : (V 1523).bytes = 4 := by
    rw [e1523]
    obtain ⟨hcl, -⟩ := alpha_mu (c := c) (m := m) (ev_ni hmx)
    obtain ⟨h4, -⟩ := hcl
    exact h4
  refine ⟨hs, by rw [hV 498 (by simp), alphaVal_c]; exact hc, hpos, ?_, q179, q180⟩
  refine shift_ev hpos (by rw [e1914]; exact hm) (by rw [e1523]; exact hmu) byt
    (b := b) (by rw [hV 168 (by simp), hb]) ?_ h499
  rw [hb, predOf] at hp
  exact hp

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
