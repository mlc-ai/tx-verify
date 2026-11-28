-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.AlphaNum
public import Kernels.InklingRelDecode.Proof.Softmax.Data.NumExp
public import Kernels.InklingRelDecode.Proof.Lib.EvWord
import Lemmas.Flow.W0Reads
import Lemmas.Flow.Step.RuleStep

@[expose] public section

/-! # Words that are the exact value of an extended real

`Ev v x` says the word `v` is `erealValue .f32 x` (`.float .f32 r` for a real, the `-inf`
pattern for `⊥`) and `x` is no `+inf`. Each lemma gives the outcome of an instruction on such
words: the word of the exact result (`idealArith` is exact on reals, `-inf` times a positive real
or plus a real stays `-inf`). The generated values of a window are terms of these outcomes, so a
window's registers are read off by applying the lemmas. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Flow PTX.Proof PTX.Assumption

noncomputable section

export Lib (Ev Rd)

theorem ev_real (r : ℝ) : Ev (.float .f32 r) (r : EReal) :=
  ⟨(erealValue_coe .f32 r).symm, EReal.coe_ne_top r⟩

theorem ev_bot : Ev negInf32 ⊥ := ⟨(erealValue_bot).symm, (by simp)⟩

/-- The `f32` product of a number or `-inf` and a positive number. -/
theorem mulEReal_pos {x : EReal} (hx : x ≠ ⊤) {y : ℝ} (hy : 0 < y) :
    mulEReal x (y : EReal) = some (x * y) := by
  induction x using EReal.rec with
  | bot => rw [mulEReal_bot_pos hy, EReal.bot_mul_coe_of_pos hy]
  | coe r => rw [mulEReal_coe, EReal.coe_mul]
  | top => exact absurd rfl hx

theorem addEReal_real {x : EReal} (hx : x ≠ ⊤) (z : ℝ) :
    addEReal x (z : EReal) = some (x + z) := by
  induction x using EReal.rec with
  | bot => rw [addEReal_bot_coe, EReal.bot_add]
  | coe r => rw [addEReal_coe, EReal.coe_add]
  | top => exact absurd rfl hx

theorem ne_top_mul {x : EReal} (hx : x ≠ ⊤) {y : ℝ} (hy : 0 < y) : x * y ≠ ⊤ := by
  induction x using EReal.rec with
  | bot => rw [EReal.bot_mul_coe_of_pos hy]; exact (by simp)
  | coe r => rw [← EReal.coe_mul]; exact EReal.coe_ne_top _
  | top => exact absurd rfl hx

theorem ne_top_add {x : EReal} (hx : x ≠ ⊤) (z : ℝ) : x + z ≠ ⊤ := by
  induction x using EReal.rec with
  | bot => rw [EReal.bot_add]; exact (by simp)
  | coe r => rw [← EReal.coe_add]; exact EReal.coe_ne_top _
  | top => exact absurd rfl hx

theorem ev_mul {fz : Bool} {d a b : Value} {x : EReal} {y : ℝ} (ha : Ev a x) (hb : Ev b y)
    (hy : 0 < y) : Ev (okVal d (mulE fz a b)) (x * y) :=
  ⟨by rw [okVal_ok (mulE_reads ha.read hb.read (mulEReal_pos ha.2 hy))],
    ne_top_mul ha.2 hy⟩

theorem ev_fma {fz : Bool} {d a b c : Value} {x : EReal} {y z : ℝ} (ha : Ev a x) (hb : Ev b y)
    (hc : Ev c z) (hy : 0 < y) : Ev (okVal d (floatE (fmaI .rn fz) [a, b, c])) (x * y + z) := by
  have h : (mulEReal x (y : EReal)).bind (addEReal · (z : EReal)) = some (x * y + z) := by
    rw [mulEReal_pos ha.2 hy]; exact addEReal_real (ne_top_mul ha.2 hy) z
  exact ⟨by rw [okVal_ok (fmaE_reads ha.read hb.read hc.read h)],
    ne_top_add (ne_top_mul ha.2 hy) z⟩

/-- `2 ^ x`, `0` for `-inf`. -/
def pw2 (x : EReal) : ℝ := if x = ⊥ then 0 else (2 : ℝ) ^ x.toReal

theorem ev_ex2 {fz : Bool} {d a : Value} {x : EReal} (ha : Ev a x) :
    Ev (okVal d (ex2E fz a)) (pw2 x : ℝ) := by
  have hx := ha.2
  have : Ev (okVal d (ex2E fz a)) ((pw2 x : ℝ) : EReal) := by
    induction x using EReal.rec with
    | bot =>
      rw [ha.1, erealValue_bot, okVal_ok (ex2E_negInf fz)]
      simpa [pw2] using ev_real 0
    | coe r =>
      rw [okVal_ok (ex2E_real ha.read)]
      simpa [pw2] using ev_real _
    | top => exact absurd rfl hx
  exact this

theorem ev_add {fz : Bool} {d a b : Value} {x y : ℝ} (ha : Ev a x) (hb : Ev b y) :
    Ev (okVal d (floatE (addI fz) [a, b])) ((x + y : ℝ) : EReal) :=
  ⟨by rw [okVal_ok (addE_reads ha.read hb.read (addEReal_coe x y))],
    EReal.coe_ne_top _⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
