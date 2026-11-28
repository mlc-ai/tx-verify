-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Lemmas.Flow.OutKinds
public import Kernels.InklingRelDecode.Proof.Softmax.GenRules
import Lemmas.Flow.Recip

@[expose] public section

/-! # Words that read as numbers: closure under the operations of the first window

A word of kind `Kd.s .fl` reads as an `f32` number, one of kind `Kd.s .ni` as a number or `-inf`
(never `+inf`, never NaN), and one of kind `Kd.pr k` is two such halves
(`Lemmas/Flow/OutKinds.lean`). A generated run's value is a term of `okVal (.bits 32 0) (E ..)` of
the operations `E`; each lemma here says that `E` on words of a kind gives a word of a kind, so a
term is typed by applying them (the outcome of a faulting instruction is the default `.bits 32 0`,
which reads as zero, so the claims need no condition). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Flow PTX.Proof PTX.Assumption

noncomputable section

/-- A word that reads as a `bf16` number (a payload, or the 16-bit zero of an absent bias). -/
def Bf16 (v : Value) : Prop := ∃ r : ℝ, readEReal .bf16 v = some (.ok (r : EReal))

/-- A 32-bit word whose two halves read as `bf16` numbers. -/
def Bf16Pair (v : Value) : Prop := Bf16 (splitValue 32 v).1 ∧ Bf16 (splitValue 32 v).2

theorem widen_has {d h : Value} (hh : Bf16 h) : (Kd.s .fl).Has (okVal d (widenBfE [h])) := by
  obtain ⟨r, hr⟩ := hh
  have e : widenBfE [h] = .ok (erealValue .f32 (r : EReal)) := by simp [widenBfE, hr]
  rw [okVal_ok e, erealValue_coe]
  exact has_float_fl r

theorem fma2_has {a b c : Value} (ha : (Kd.pr .fl).Has a) (hb : (Kd.pr .fl).Has b)
    (hc : (Kd.pr .fl).Has c) : (Kd.pr .fl).Has (okVal (.bits 64 0) (fma2E a b c)) := by
  let V : Nat → Value := fun r => if r = 0 then a else if r = 1 then b else c
  let K : Nat → Kd := fun _ => .pr .fl
  have h : kItem K (.base (.fma2 3 0 1 2)) = some (Function.update K 3 (.pr .fl)) := rfl
  have hV : ∀ r, (K r).Has (V r) := by
    intro r
    simp only [V, K]
    split_ifs <;> assumption
  have := (kItem_sound h hV trivial).2 3
  have e := upd_one V (.base (.fma2 3 0 1 2)) (d := 3) (v := okVal (.bits 64 0) (fma2E a b c))
    (by simp [XItem.vals, OItem.vals, V])
  rw [e] at this
  simpa using this

theorem max2_has {a b d : Value} (ha : (Kd.s .ni).Has a) (hb : (Kd.s .ni).Has b) :
    (Kd.s .ni).Has (okVal d (maxE [a, b])) := by
  obtain ⟨r, hr, hk⟩ := maxE_maxSpec .ni (.inr rfl) [a, b] (.inl rfl)
    (by intro v hv; simp at hv; rcases hv with rfl | rfl <;> assumption)
  rw [okVal_ok hr]
  exact hk

theorem max3_has {a b c d : Value} (ha : (Kd.s .ni).Has a) (hb : (Kd.s .ni).Has b)
    (hc : (Kd.s .ni).Has c) : (Kd.s .ni).Has (okVal d (maxE [a, b, c])) := by
  obtain ⟨r, hr, hk⟩ := maxE_maxSpec .ni (.inr rfl) [a, b, c] (.inr rfl)
    (by intro v hv; simp at hv; rcases hv with rfl | rfl | rfl <;> assumption)
  rw [okVal_ok hr]
  exact hk

theorem split1_has {k : SK} {w : Value} (h : (Kd.pr k).Has w) :
    (Kd.s k).Has (splitValue 64 w).1 := h.2.1

theorem split2_has {k : SK} {w : Value} (h : (Kd.pr k).Has w) :
    (Kd.s k).Has (splitValue 64 w).2 := h.2.2

theorem join_fl_has {a b : Value} (ha : (Kd.s .fl).Has a) (hb : (Kd.s .fl).Has b) :
    (Kd.pr .fl).Has (joinValue a b) :=
  join_has (ka := .fl) (kb := .fl) (a := a) (b := b) ha hb

theorem join_ni_has {a b : Value} (ha : (Kd.s .ni).Has a) (hb : (Kd.s .ni).Has b) :
    (Kd.pr .ni).Has (joinValue a b) :=
  join_has (ka := .ni) (kb := .ni) (a := a) (b := b) ha hb

theorem pr_mono {v : Value} (h : (Kd.pr .fl).Has v) : (Kd.pr .ni).Has v :=
  ⟨h.1, SK.mono (a := .fl) (b := .ni) (by decide) h.2.1,
    SK.mono (a := .fl) (b := .ni) (by decide) h.2.2⟩

theorem zero_has : (Kd.s .fl).Has (.bits 32 0) := by
  refine ⟨⟨rfl, (fun _ _ _ h => by cases h), fun w x h => ?_⟩, 0, ?_⟩
  · cases h; simp
  · have hz := classify_bits (fmt := .f32) (n := 0) (x := .zero false) (by decide) (by decide)
    change readEReal.ofDatum (classify .f32 (.bits 32 (BitVec.ofNat 64 0))) = some (.ok 0)
    change classify .f32 (.bits 32 (BitVec.ofNat 64 0)) = .ok (.zero false) at hz
    rw [hz]; rfl

theorem one_has : (Kd.s .fl).Has (.bits 32 1065353216) :=
  ⟨⟨rfl, (fun _ _ _ h => by cases h), fun w x h => by cases h; simp⟩, 1,
    readEReal_of_valFloat valFloat_one⟩

/-- The mask select of a score: the score, `-inf`, or (on a fault) the zero word. -/
theorem sel_has {d a p : Nat} {x pv : Value} (hx : (Kd.s .fl).Has x) :
    (Kd.s .ni).Has (okVal (.bits 32 0) (coreF (.int ⟨.selp, .float .f32, false, [some d],
      [.reg a, .f32imm 4286578688, .reg p]⟩) [a, p] [x, pv])) := by
  have hx' : (Kd.s .ni).Has x := SK.mono (a := .fl) (b := .ni) (by decide) hx
  unfold coreF coreW
  cases hp : lk [a, p] [x, pv] p <;> simp only [hp, bind, Except.bind, throw, throwThe,
    MonadExceptOf.throw, okVal]
  all_goals try exact SK.mono (a := .fl) (b := .ni) (by decide) zero_has
  rename_i b
  have hxa : lk [a, p] [x, pv] a = x := by simp [lk]
  cases b
  · simp only [oVal, oBits, bind, Except.bind, pure, Except.pure]
    exact Or.inr rfl
  · have h4 : x.bytes = (DType.float FType.f32).width / 8 := (SK.clean (k := .ni) (v := x) hx').1
    simp only [oVal, hxa, h4, pure, Except.pure, ite_true]
    exact hx'

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
