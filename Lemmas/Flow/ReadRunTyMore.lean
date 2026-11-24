-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.ReadRunTy
public import Lemmas.Flow.FmaDead
public import Lemmas.Flow.PackMul

@[expose] public section

/-! # Shapes from a table, packs and products

A proof tool, with `ReadRunTy`: the shapes of a list of registers (`tyOf`, any other register
unconstrained) hold when each listed register's value has its shape (`all_tyOf`); packs of
single-precision words have four-byte sources (`packsOk_of_ty`); a product item whose sources
are single-precision words, or whose source is a pair of them, continues (`FmaItem.ok_of_ty`). -/

namespace PTX.Flow
open PTX PTX.Proof

noncomputable section

/-- The shapes of the listed registers. -/
def tyOf (tys : List (Nat × RTy)) (r : Nat) : RTy := (tys.lookup r).getD .any

theorem mem_of_lookup_ty {tys : List (Nat × RTy)} {r : Nat} {ty : RTy}
    (h : tys.lookup r = some ty) : (r, ty) ∈ tys := by
  induction tys with
  | nil => simp at h
  | cons p ps ih =>
    obtain ⟨r', ty'⟩ := p
    by_cases hr : r = r'
    · subst hr
      simp only [List.lookup_cons, beq_self_eq_true, Option.some.injEq] at h
      subst h
      exact List.mem_cons_self ..
    · have hb : (r == r') = false := by simpa using hr
      simp only [List.lookup_cons, hb] at h
      exact List.mem_cons_of_mem _ (ih h)

/-- **The shapes of the listed registers hold** when each listed value has its shape. -/
theorem all_tyOf {tys : List (Nat × RTy)} {V : Nat → Value}
    (h : ∀ p ∈ tys, p.2.Has (V p.1)) : RTy.All (tyOf tys) V := by
  intro r
  unfold tyOf
  cases hl : tys.lookup r with
  | none => trivial
  | some ty => exact h (r, ty) (mem_of_lookup_ty hl)

/-- Packs of single-precision words have four-byte sources. -/
theorem packsOk_of_ty {T : Nat → RTy} {V : Nat → Value} (h : RTy.All T V)
    {ps : List (Nat × Nat × Nat)}
    (hc : ps.all (fun p => T p.2.1 == .f32 && T p.2.2 == .f32) = true) : packsOk V ps = true := by
  unfold packsOk
  rw [List.all_eq_true] at hc ⊢
  intro p hp
  have := hc p hp
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  obtain ⟨h1, h2⟩ := this
  have a1 := h p.2.1
  have a2 := h p.2.2
  rw [h1] at a1
  rw [h2] at a2
  obtain ⟨x, hx⟩ := a1
  obtain ⟨y, hy⟩ := a2
  simp [hx, hy, Value.bytes, FloatFmt.bytes]

/-- The shape check of a product item. -/
def FmaItem.tyOk (T : Nat → RTy) (it : FmaItem) : Bool :=
  match it.pk with
  | some (lo, hi) => T lo == .f32 && T hi == .f32
  | none => T it.a == .f32x2

/-- **A product item whose sources have the checked shapes continues.** -/
theorem FmaItem.ok_of_ty {T : Nat → RTy} {v : Nat → Value} (h : RTy.All T v) {it : FmaItem}
    (hc : it.tyOk T = true) : it.Ok v := by
  unfold FmaItem.tyOk at hc
  unfold FmaItem.Ok FmaItem.packOk FmaItem.src
  cases hp : it.pk with
  | some p =>
    obtain ⟨lo, hi⟩ := p
    rw [hp] at hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    have a1 := h lo
    have a2 := h hi
    rw [hc.1] at a1
    rw [hc.2] at a2
    obtain ⟨x, hx⟩ := a1
    obtain ⟨y, hy⟩ := a2
    refine ⟨by simp [hx, hy, Value.bytes, FloatFmt.bytes], ⟨(x, y), ?_⟩⟩
    simp [hx, hy, joinValue, splitValue, f32x2Elems, valFloat, pure, Except.pure]
  | none =>
    rw [hp] at hc
    simp only [beq_iff_eq] at hc
    have a := h it.a
    rw [hc] at a
    obtain ⟨x, y, hxy⟩ := a
    refine ⟨rfl, ⟨(x, y), ?_⟩⟩
    simp [hxy, splitValue, f32x2Elems, valFloat, pure, Except.pure]

end
end PTX.Flow
