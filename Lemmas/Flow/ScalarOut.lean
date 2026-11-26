-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.MaxCore
public import Lemmas.Flow.ArithCore
public import Lemmas.Flow.EmuStep
public import Lemmas.Flow.MemTmpl

@[expose] public section

/-! # One-lane float outcomes are scalar values

A value is scalar when every byte of its stored form is `(v, k)`: it rebuilds from its own bytes
(`rebuild_scalar`). The outcome of a one-lane floating instruction (`floatE`, `mulE`, `maxFE`) is
the number's `erealValue` or the Core rule's `FVal.toValue`, so it is scalar. -/

namespace PTX.Flow
open PTX PTX.Proof PTX.Assumption

noncomputable section

/-- A scalar value: the byte `k` of its stored form is `(v, k)`. -/
def Scal (v : Value) : Prop := ∀ k, v.byteAt k = (v, k)

/-- A scalar value of at least one byte rebuilds from its own bytes. -/
theorem rebuild_of_scal {v : Value} (hb : 0 < v.bytes) (hs : Scal v) :
    rebuild 3 (v.toBytes.map some) = .ok v :=
  PTX.Proof.rebuild_scalar hb (hs 0)

theorem scal_bits (w : Nat) (x : BitVec 64) : Scal (.bits w x) := fun _ => rfl

theorem scal_float (f : FloatFmt) (x : ℝ) : Scal (.float f x) := fun _ => rfl

theorem scal_toValue (fmt : FloatFmt) (v : FVal) : Scal (v.toValue fmt) := by
  cases v with
  | zero b => cases b <;> exact fun _ => rfl
  | fin q => exact fun _ => rfl
  | inf b => exact fun _ => rfl
  | nan o => cases o <;> exact fun _ => rfl

theorem scal_erealValue (fmt : FloatFmt) (x : EReal) : Scal (erealValue fmt x) := by
  unfold erealValue
  split_ifs
  · exact scal_toValue _ _
  · exact scal_toValue _ _
  · exact scal_float _ _

/-- A one-lane `coreFloat` outcome is scalar. -/
theorem scal_coreFloat {f : FloatInstr} (hl : f.ty.lanes = 1) {vs : List Value} {v : Value}
    (h : coreFloat f vs = .ok v) : Scal v := by
  unfold coreFloat at h
  rw [hl] at h
  simp only [List.range_one, List.mapM_cons, List.mapM_nil, bind, Except.bind, pure,
    Except.pure] at h
  split at h
  · simp at h
  · split at h
    · rename_i q
      simp only [Except.ok.injEq] at h
      subst h
      exact scal_toValue _ _
    · rename_i hxs
      split at hxs <;> simp at hxs
    · simp at h

/-- The last step of an ideal outcome: a `pure (erealValue ..)` that is `ok v` gives a scalar. -/
theorem scal_pure_ereal {fmt : FloatFmt} {r : Option EReal} {v : Value}
    (h : (r.map fun r => (pure (erealValue fmt r) : Exec Value)) = some (.ok v)) : Scal v := by
  cases r with
  | none => simp at h
  | some r =>
    simp only [Option.map_some, Option.some.injEq, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact scal_erealValue _ _

theorem scal_idealVal {f : FloatInstr} (hl : f.ty.lanes = 1) {vs : List Value} {v : Value}
    (hr : idealVal f vs = some (.ok v)) : Scal v := by
  unfold idealVal at hr
  rw [hl] at hr
  split at hr
  · obtain ⟨_, -, h⟩ := bindRead_ok hr
    obtain ⟨_, -, h⟩ := bindRead_ok h
    exact scal_pure_ereal h
  · obtain ⟨_, -, h⟩ := bindRead_ok hr
    obtain ⟨_, -, h⟩ := bindRead_ok h
    obtain ⟨_, -, h⟩ := bindRead_ok h
    exact scal_pure_ereal h
  · rename_i hh; exact absurd hh (by omega)
  · simp [throw, throwThe, MonadExceptOf.throw] at hr

theorem scal_floatE {f : FloatInstr} (hl : f.ty.lanes = 1) {vs : List Value} {v : Value}
    (h : floatE f vs = .ok v) : Scal v := by
  unfold floatE at h
  cases hi : idealVal f vs with
  | some r =>
    rw [hi] at h
    cases r with
    | error e => cases h
    | ok w => cases h; exact scal_idealVal hl hi
  | none => rw [hi] at h; exact scal_coreFloat hl h

theorem scal_idealMax {vs : List Value} {v : Value} (hr : idealMax vs = some (.ok v)) :
    Scal v := by
  unfold idealMax at hr
  split at hr
  · obtain ⟨_, -, h⟩ := bindRead_ok hr
    obtain ⟨_, -, h⟩ := bindRead_ok h
    simp only [Option.some.injEq, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact scal_erealValue _ _
  · obtain ⟨_, -, h⟩ := bindRead_ok hr
    obtain ⟨_, -, h⟩ := bindRead_ok h
    obtain ⟨_, -, h⟩ := bindRead_ok h
    simp only [Option.some.injEq, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact scal_erealValue _ _
  · simp [throw, throwThe, MonadExceptOf.throw] at hr

theorem scal_maxFE {a b v : Value} (h : maxFE a b = .ok v) : Scal v := by
  unfold maxFE at h
  cases hi : idealMax [a, b] with
  | some r =>
    rw [hi] at h
    cases r with
    | error e => cases h
    | ok w => cases h; exact scal_idealMax hi
  | none => rw [hi] at h; exact scal_coreFloat rfl h

theorem scal_mulE {fz : Bool} {a b v : Value} (h : mulE fz a b = .ok v) : Scal v := by
  unfold mulE at h
  cases hi : idealMul a b with
  | some r =>
    rw [hi] at h
    cases r with
    | error e => cases h
    | ok w =>
      cases h
      unfold idealMul at hi
      obtain ⟨_, -, h⟩ := bindRead_ok hi
      obtain ⟨_, -, h⟩ := bindRead_ok h
      exact scal_pure_ereal h
  | none => rw [hi] at h; exact scal_coreFloat rfl h

/-- An `okVal` with a scalar default is scalar when every outcome is. -/
theorem scal_okVal {d : Value} {e : Exec Value} (hd : Scal d) (h : ∀ v, e = .ok v → Scal v) :
    Scal (okVal d e) := by
  cases he : e with
  | ok v => exact h v he
  | error _ => exact hd

end

end PTX.Flow
