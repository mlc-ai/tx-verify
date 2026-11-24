-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Data.Round
public import Kernels.TmlFa4Fwd.Proof.Softmax.GenRules
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsNarr1Kinds
import Kernels.TmlFa4Fwd.Proof.Softmax.NegScale

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Data
open PTX.Proof PTX.Flow PTX.Assumption

noncomputable section

/-- A register holding either a finite single or the machine's masked pattern. -/
structure Reads (v : Value) (x : EReal) : Prop where
  clean : Clean v
  read : readEReal .f32 v = some (.ok x)

theorem reads_float (x : ℝ) : Reads (.float .f32 x) x := ⟨clean_float _, readEReal_float _⟩

theorem reads_bot : Reads ninf32 ⊥ := ⟨clean_negInf, readEReal_negInf⟩

theorem reads_join {a b : Value} {x y : EReal} (ha : Reads a x) (hb : Reads b y) :
    pairRead (joinValue a b) = some (.ok (x,y)) := by
  have h := split_join_clean ha.clean hb.clean
  apply pairRead_of_reads <;> rw [h]
  · exact ha.read
  · exact hb.read

theorem reads_scale {p L m} (hp : Pre p L m) :
    Reads (.bits 32 (Epilogue.paramW p.scaleLog2Bits)) (scl p : ℝ) ∧ 0 < (scl p : ℝ) := by
  obtain ⟨s, hs, hpos, hword⟩ := scale_word hp
  simp only [scl, hs, Option.getD_some]
  exact ⟨⟨(paramW_pw hs hpos hword).1, readEReal_bits_fin (classify_word hs hpos.ne' hword)⟩,
    by exact_mod_cast hpos⟩

theorem reads_sel {x : EReal} (h : x < ⊤) : Reads (selMax x) (x.toReal : ℝ) := by
  refine ⟨(selMax_fl h).1, ?_⟩
  by_cases hb : x = ⊥
  · subst x
    simpa [selMax] using readEReal_zero32
  · rw [selMax, ite_eq_right hb, ← EReal.coe_toReal h.ne hb, erealValue_coe]
    simpa using readEReal_float x.toReal

theorem reads_first (p L g v i) :
    Reads (elemVal (mcnt p L g v) (bpf v) (bps p v) i) (score p L g v .first i) := by
  unfold score elemVal mre bpeB bpe bv32
  split_ifs <;> first | exact reads_bot | exact reads_float _

def shift (x : EReal) (s z : ℝ) : EReal := if x = ⊥ then ⊥ else (x.toReal * s + z : ℝ)

private theorem shift_eval {s : ℝ} (hs : 0 < s) {x : EReal} (hx : x < ⊤) (z : ℝ) :
    (mulEReal x (s : EReal)).bind (addEReal · (z : EReal)) = some (shift x s z) := by
  by_cases hb : x = ⊥
  · subst x
    simp only [shift, ite_true, mulEReal_bot_pos hs, Option.bind_some, Flow.addEReal_bot_coe]
  · obtain ⟨a, rfl⟩ : ∃ a : ℝ, x = a := ⟨_, (EReal.coe_toReal hx.ne hb).symm⟩
    simp only [shift, EReal.coe_ne_bot, ite_false, EReal.toReal_coe, mulEReal_coe,
      Option.bind_some, addEReal_coe]

/-- The scaled score FMA used before both exp2 implementations. -/
theorem shifted_pair {ab s z : Value} {x y : EReal} {u w : ℝ}
    (h : pairRead ab = some (.ok (x,y))) (hs : Reads s u) (hz : Reads z w)
    (hu : 0 < u) (hx : x < ⊤) (hy : y < ⊤) :
    okVal (.bits 64 0) (fma2E ab (joinValue s s) (joinValue z z)) =
      .pair (erealValue .f32 (shift x u w)) (erealValue .f32 (shift y u w)) := by
  rw [fma2E_reads h (reads_join hs hs) (reads_join hz hz) (shift_eval hu hx w)
    (shift_eval hu hy w)]
  rfl

def offset (a b : Value) := okVal (.bits 32 0) (mulE false a b)

theorem offset_val {a b : Value} {x y : ℝ} (ha : Reads a x) (hb : Reads b y) :
    offset a b = .float .f32 (x*y) := by
  rw [offset, mulE_reads ha.read hb.read (mulEReal_coe x y), erealValue_coe]
  rfl

theorem hw_exp (p : Params) (M x : EReal) :
    okVal (.bits 32 0) (ex2E true (erealValue .f32 (shift x (scl p) (M.toReal * -(scl p : ℝ))))) =
      .float .f32 (probability p M x) := by
  by_cases h : x = ⊥
  · simp only [probability, shift, h, ite_true, erealValue_bot, ex2E_negInf, okVal]
  · simp only [probability, shift, ite_eq_right h, erealValue_coe, ex2E_real (readEReal_float _),
      okVal, Real.rpow_eq_pow]

theorem sw_exp (p : Params) (M x : EReal) :
    laneR (erealValue .f32 (shift x (scl p) (M.toReal * -(scl p : ℝ)))) = probability p M x := by
  by_cases h : x = ⊥
  · simp only [shift, probability, h, ite_true, erealValue_bot]
    rfl
  · simp only [shift, probability, ite_eq_right h, erealValue_coe]
    rfl

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Data
