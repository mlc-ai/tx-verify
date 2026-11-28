-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.SegQFH
public import Lemmas.Flow.TypedFloatJ

@[expose] public section

/-! # Typed runs with `ex2.approx.f32` and `setp.cmp.f32`

`absF3` is `absF2` with the rule of `TypedFloatJ.lean`; `segQF3_runW` is `segQF2_runW` for it. -/

namespace PTX.Flow.TyG
open PTX PTX.Proof PTX.Flow PTX.Flow.Tagged PTX.Flow.Havoc

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- The whole family of `SegQFH.lean` and `TypedFloatJ.lean`. -/
def absF3 (env : EnvF) (op : Op) : Option (List (Nat × TagF)) :=
  (absF2 env op).or (absFloat3 env op)

/-- What a kernel supplies for a stretch `[a, b)` of the family `absF3`. -/
structure FloatPlain3 (A : List Assumption) (L : Launch) (g a b : Nat) : Prop where
  plain : FloatPlain2 A L g a b
  ideal3 : IdealRules3 A L g a b

theorem FloatPlain3.mono {a b a' b' : Nat} (h : FloatPlain3 A L g a b) (h1 : a ≤ a')
    (h2 : b' ≤ b) : FloatPlain3 A L g a' b' where
  plain := h.plain.mono h1 h2
  ideal3 t ha hb := h.ideal3 t (le_trans h1 ha) (lt_of_lt_of_le hb h2)

theorem absF3_sound {a b : Nat} (h : FloatPlain3 A L g a b) : AbsSound A L g a b absF3 :=
  (absF2_sound h.plain).or (absFloat3_sound h.ideal3)

/-- A typed run of the family `absF3` whose abstract run writes exactly `W`. -/
theorem segQF3_runW (qt : Nat → EnvF) {a b : Nat} {F G : List (Nat × Value)} {W : List Nat}
    (hab : a ≤ b) (hlen : b ≤ K.code.length) (hP : FloatPlain3 A L g a b)
    (hc : checkW absF3 qt a b ((K.code.drop a).take (b - a)) W = true)
    (hw : ∀ p ∈ G, p.1 ∉ W) (hG : ∀ p ∈ G, p ∈ F) : SegQ K A L g (QTF qt) a F b G := by
  obtain ⟨h0, hW⟩ := checkW_sound hc
  exact segQF_of_typed qt (Ft := []) hab hlen (absF3_sound hP) trivial
    (checkF_gk h0 fun k hk => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hk
      exact hW ▸ hw p hp) hG

end PTX.Flow.TyG
