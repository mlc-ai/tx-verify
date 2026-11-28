-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.ExpVal6
public import Kernels.InklingRelDecode.Proof.Lib.SoftFold
import Kernels.InklingRelDecode.Proof.Softmax.Data.ExpTyped
import Lemmas.Flow.MulERealBot
import Lemmas.Flow.SetpReads

@[expose] public section

/-! # The rescale factor on exact inputs

With the running maximum `m` and the round's maximum `mx` (exact words) and the positive scale
`sc`, the rescale window's registers are `SoftFold`'s: the maximum used (register 1523) is
`mSafe`, the test `p168` is `Keep a` and the factor (507) is `1` or `pow2 a`, with
`a = alphaLog2 sc m mx`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Flow PTX.Proof PTX.Assumption PTX.Kernels.InklingRelDecode.Proof
open Lib.SoftFold Classical

set_option maxRecDepth 100000
noncomputable section

theorem rd_zero : Rd (.bits 32 0) ((0 : ℝ) : EReal) := by
  have hz := classify_bits (fmt := .f32) (n := 0) (x := .zero false) (by decide) (by decide)
  change readEReal.ofDatum (classify .f32 (.bits 32 (BitVec.ofNat 64 0))) = some (.ok 0)
  change classify .f32 (.bits 32 (BitVec.ofNat 64 0)) = .ok (.zero false) at hz
  rw [hz]; rfl

theorem sel_mx_rd {mx : Value} {xE : EReal} (h : Ev mx xE) :
    Rd (if predOf (.pred (okPred (setpE (.ord .eq) false mx (.bits 32 4286578688)))) = true
      then Value.bits 32 0 else mx) ((mSafe xE : ℝ) : EReal) := by
  have hy : readEReal .f32 (.bits 32 4286578688) = some (.ok ⊥) := readEReal_negInf
  rw [setpE_reads (cmp := .eq) (Or.inl rfl) h.read hy]
  induction xE using EReal.rec with
  | bot => simpa [mSafe, okPred, erealCompare, predOf] using rd_zero
  | coe r => simpa [mSafe_coe, okPred, erealCompare, predOf, Rd] using h.read
  | top => exact absurd rfl h.2

theorem mulEReal_real_left {x : EReal} (hx : x ≠ ⊤) {y : ℝ} (hy : 0 < y) :
    mulEReal (y : EReal) x = some (x * y) := by
  induction x using EReal.rec with
  | bot => rw [mulEReal_coe_bot_pos hy, EReal.bot_mul_coe_of_pos hy]
  | coe r => rw [mulEReal_coe, ← EReal.coe_mul, mul_comm y r]
  | top => exact absurd rfl hx

theorem rd_one : Rd (.bits 32 1065353216) ((1 : ℝ) : EReal) :=
  readEReal_of_valFloat valFloat_one

/-- **The rescale factor, exactly**: with `a = (m - m_safe) * sc`, the test `p168` is `Keep a`, the
maximum used (register 1523) is `m_safe`, and the factor (507) is `1` or `2 ^ a`. -/
theorem alpha_exact {c m mx : Value} {sc : ℝ} {mE xE : EReal} (hc : Ev c sc) (hpos : 0 < sc)
    (hm : Ev m mE) (hmx : Ev mx xE) :
    Rd (Lib.alphaVal c m mx 1523) ((mSafe xE : ℝ) : EReal) ∧
    (predOf (Lib.alphaVal c m mx 168) = true ↔ Keep (alphaLog2 sc mE xE)) ∧
    Rd (Lib.alphaVal c m mx 507)
      ((if Keep (alphaLog2 sc mE xE) then 1 else pow2 (alphaLog2 sc mE xE) : ℝ) : EReal) := by
  have hmu := sel_mx_rd hmx
  simp [Lib.alphaVal, Lib.alphaRest, xFinal, XItem.upd, XItem.vals, OItem.vals,
    Function.update, Lib.alphaIn, opndVal]
  generalize (if predOf (Value.pred (okPred (setpE (FCmp.ord Cmp.eq) false mx
    (Value.bits 32 4286578688#64)))) = true then Value.bits 32 0#64 else mx) = mu at hmu ⊢
  have hS : Ev (okVal (Value.bits 32 0#64) (subE false m mu))
      (mE + (((-(mSafe xE) : ℝ)) : EReal)) :=
    ⟨by rw [okVal_ok (subE_reads hm.read hmu (by
        rw [← EReal.coe_neg]; exact addEReal_real hm.2 _))],
      ne_top_add hm.2 _⟩
  have hM : Ev (okVal (Value.bits 32 0#64) (mulE false c (okVal (Value.bits 32 0#64)
      (subE false m mu)))) (alphaLog2 sc mE xE) := by
    have e : alphaLog2 sc mE xE = (mE + (((-(mSafe xE) : ℝ)) : EReal)) * (sc : EReal) := by
      simp only [alphaLog2, sub_eq_add_neg, EReal.coe_neg]
    rw [e]
    refine ⟨?_, ne_top_mul hS.2 hpos⟩
    have hz : mulEReal (sc : EReal) (mE + (((-(mSafe xE) : ℝ)) : EReal)) =
        some ((mE + (((-(mSafe xE) : ℝ)) : EReal)) * (sc : EReal)) :=
      mulEReal_real_left hS.2 hpos
    rw [okVal_ok (mulE_reads hc.read hS.read hz)]
  have hP : predOf (Value.pred (okPred (setpE (FCmp.ord Cmp.ge) false (okVal (Value.bits 32 0#64)
      (mulE false c (okVal (Value.bits 32 0#64) (subE false m mu))))
      (Value.bits 32 3238002688#64))))
      = true ↔ Keep (alphaLog2 sc mE xE) := by
    rw [setpE_reads (cmp := .ge) (Or.inl rfl) hM.read read_m8]
    simp [okPred, predOf, erealCompare, Keep]
  refine ⟨hmu, hP, ?_⟩
  by_cases hk : Keep (alphaLog2 sc mE xE)
  · simp only [hP.mpr hk, hk, ↓reduceIte]
    exact rd_one
  · simp only [mt hP.mp hk, hk, ↓reduceIte]
    exact (ev_ex2 (fz := true) (d := Value.bits 32 0#64) hM).read

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
