-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.TypedWidenF

@[expose] public section

/-! # The typed float family, in one rule

`absF` tries the integer family (`absIntF`), the data-movement family (`absMoveF`), `max.f32` and
`fma.rn.f32x2` (`absFloat`) and `cvt.f32.bf16` (`absWiden`). `FloatPlain A L g a b` collects what
a kernel supplies for a stretch `[a, b)`: no assumption takes an integer, move or integer
conversion (`PlainShape`) and no assumption takes a segment (`PlainSegs`); the ideal reading of
`max.f32` and `fma.rn.f32x2` (`IdealRules`); and the reading of `cvt.f32.bf16` (`WidenRules`).
With it `absF` is sound (`absF_sound`), so a stretch is a strict segment under the tag
invariant by one `decide`-checked Boolean (`segQF_of_typed`). -/

namespace PTX.Flow.TyG
open PTX PTX.Proof PTX.Flow PTX.Flow.Tagged PTX.Flow.Havoc

variable {A : List Assumption} {L : Launch} {g : Nat}

/-- An instruction the integer rule accepts is an integer, a move or an integer conversion. -/
theorem absOp_plain {env : Env} {op : Op} (h : (absOp env op).isSome) : PlainOp op := by
  cases op <;> simp only [absOp, Option.isSome_none, Bool.false_eq_true] at h
  · exact .inl ⟨_, rfl⟩
  · exact .inr (.inl ⟨_, rfl⟩)
  · rename_i c
    obtain ⟨dst, src, rnd, ftz, sat, relu, satfinite, pzo, scaled, pack, d', ext, srcs⟩ := c
    unfold absCvt at h
    simp only at h
    split at h
    · rename_i k w _ _ _
      exact .inr (.inr ⟨_, k, w, rfl, rfl⟩)
    · simp at h

theorem PlainRules.of_shape {a b : Nat} (h : PlainShape A L g a b) : PlainRules A L g a b :=
  fun t ha hb op ⟨env, hop⟩ => h t ha hb op (absOp_plain (env := env) (by simpa using hop))

/-- What a kernel supplies for a stretch `[a, b)` of the typed float family. -/
structure FloatPlain (A : List Assumption) (L : Launch) (g a b : Nat) : Prop where
  shape : PlainShape A L g a b
  segs : PlainSegs A a b
  ideal : IdealRules A L g a b
  widen : WidenRules A L g a b
  bra : ∀ (t : TState) (x : Assumption) (target : Nat) (uni : Bool), x ∈ A →
    x.localRule L g t (.bra target uni) = none

/-- The whole family: integer, data movement, `max.f32`, `fma.rn.f32x2`, `cvt.f32.bf16`. -/
def absF (env : EnvF) (op : Op) : Option (List (Nat × TagF)) :=
  (absIntF env op).or ((absMoveF env op).or ((absFloat env op).or (absWiden env op)))

theorem absF_sound {a b : Nat} (h : FloatPlain A L g a b) : AbsSound A L g a b absF :=
  (absIntF_sound (PlainRules.of_shape h.shape) h.segs).or
    ((absMoveF_sound h.shape h.segs).or ((absFloat_sound h.ideal).or (absWiden_sound h.widen)))

end PTX.Flow.TyG
