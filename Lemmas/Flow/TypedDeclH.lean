-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.TypedDeclF
public import Lemmas.Flow.Mul2NReads

@[expose] public section

/-! # `add`, `sub` and `mul` without a rounding modifier, where the ideal rule does not decline

The ideal-real reading of these forms is all that is needed: where it does not decline, `IdealAt`
gives the step, and the product, sum or difference of two data is a datum. -/

namespace PTX.Flow.TyG
open PTX PTX.Proof PTX.Flow PTX.Flow.Tagged PTX.Assumption

noncomputable section

variable {A : List Assumption} {L : Launch} {g : Nat}

/-- The scalar forms: `add`, `sub` and `mul` of one `.f32` lane without a rounding modifier. -/
def scalarOp (o : FOp) (fz : Bool) (d : Nat) (a b : Opnd) : Op :=
  .float { op := o, ty := ty1 .f32, ftz := fz, dsts := [some d], srcs := [a, b] }

private theorem scalar_dat {o : FOp} {fz : Bool} {d : Nat} {a b : Opnd} {t : TState} {va vb : Value}
    {f : EReal → EReal → Option EReal}
    (hexe : execIdealFloat L g t (scalarOp o fz d a b) =
      bindRead (readERealOpnd t .f32 a) fun x => bindRead (readERealOpnd t .f32 b) fun y =>
        (f x y).map fun r => pure (PTX.next (setReg t d (erealValue .f32 r))))
    (ha : OpndIs L g t a va) (hb : OpndIs L g t b vb) (hda : Dat32 va) (hdb : Dat32 vb)
    (hnd : execIdealFloat L g t (scalarOp o fz d a b) ≠ none) :
    ∃ v, execIdealFloat L g t (scalarOp o fz d a b) = some (.ok (PTX.next (setReg t d v))) ∧
      Dat32 v := by
  rw [hexe, ha.2, hb.2] at hnd ⊢
  rcases readEReal_dat hda.1 with hx | ⟨x, hx⟩
  · simp [hx, bindRead] at hnd
  rcases readEReal_dat hdb.1 with hy | ⟨y, hy⟩
  · simp [hx, hy, bindRead] at hnd
  rcases hm : f x y with _ | r
  · simp [hx, hy, hm, bindRead] at hnd
  · exact ⟨_, by simp [hx, hy, hm, bindRead, pure, Except.pure], dat32_erealValue r⟩

theorem addD_step {t : TState} (hI : IdealAt A (.add .f32) L g t) {fz : Bool} {d : Nat}
    {a b : Opnd} {va vb : Value} (ha : OpndIs L g t a va) (hb : OpndIs L g t b vb)
    (hda : Dat32 va) (hdb : Dat32 vb) (hnd : execIdealFloat L g t (scalarOp .add fz d a b) ≠ none) :
    ∃ v, execLocalA A L g t (scalarOp .add fz d a b) = .ok (PTX.next (setReg t d v)) ∧
      Dat32 v := by
  obtain ⟨v, hv, hd⟩ := scalar_dat (f := addEReal) rfl ha hb hda hdb hnd
  exact ⟨v, hI _ (by simp [scalarOp, FloatForm.ofOp]) _ hv, hd⟩

theorem subD_step {t : TState} (hI : IdealAt A (.subRn .f32) L g t) {fz : Bool} {d : Nat}
    {a b : Opnd} {va vb : Value} (ha : OpndIs L g t a va) (hb : OpndIs L g t b vb)
    (hda : Dat32 va) (hdb : Dat32 vb) (hnd : execIdealFloat L g t (scalarOp .sub fz d a b) ≠ none) :
    ∃ v, execLocalA A L g t (scalarOp .sub fz d a b) = .ok (PTX.next (setReg t d v)) ∧
      Dat32 v := by
  obtain ⟨v, hv, hd⟩ := scalar_dat (f := fun x y => addEReal x (-y)) rfl ha hb hda hdb hnd
  exact ⟨v, hI _ (by simp [scalarOp, FloatForm.ofOp]) _ hv, hd⟩

theorem mulD_step' {t : TState} (hI : IdealAt A (.mul .f32) L g t) {fz : Bool} {d : Nat}
    {a b : Opnd} {va vb : Value} (ha : OpndIs L g t a va) (hb : OpndIs L g t b vb)
    (hda : Dat32 va) (hdb : Dat32 vb) (hnd : execIdealFloat L g t (scalarOp .mul fz d a b) ≠ none) :
    ∃ v, execLocalA A L g t (scalarOp .mul fz d a b) = .ok (PTX.next (setReg t d v)) ∧
      Dat32 v := by
  obtain ⟨v, hv, hd⟩ := scalar_dat (f := mulEReal) rfl ha hb hda hdb hnd
  exact ⟨v, hI _ (by simp [scalarOp, FloatForm.ofOp]) _ hv, hd⟩

/-- The pair forms: `add`, `sub` and `mul` of `.f32x2` of two registers. -/
def pairOp (o : FOp) (d a b : Nat) : Op :=
  .float { op := o, ty := ⟨.f32, 2⟩, dsts := [some d], srcs := [.reg a, .reg b] }

private theorem pair_dat {o : FOp} {d a b : Nat} {t : TState} {va vb : Value}
    {f : EReal → EReal → Option EReal}
    (hexe : execIdealFloat L g t (pairOp o d a b) =
      bindRead (readERealPair L g t (.reg a)) fun (x0, x1) =>
        bindRead (readERealPair L g t (.reg b)) fun (y0, y1) =>
          match f x0 y0, f x1 y1 with
          | some r0, some r1 => some (pure (PTX.next (setReg t d
              (.pair (erealValue .f32 r0) (erealValue .f32 r1)))))
          | _, _ => none)
    (ha : t.regs a = some va) (hb : t.regs b = some vb) (hda : Dat64 va) (hdb : Dat64 vb)
    (hnd : execIdealFloat L g t (pairOp o d a b) ≠ none) :
    ∃ v, execIdealFloat L g t (pairOp o d a b) = some (.ok (PTX.next (setReg t d v))) ∧
      Dat64 v := by
  rw [hexe, readERealPair_reg_val ha, readERealPair_reg_val hb] at hnd ⊢
  rcases pairRead_dat hda with hx | ⟨⟨x0, x1⟩, hx⟩
  · simp [hx, bindRead] at hnd
  rcases pairRead_dat hdb with hy | ⟨⟨y0, y1⟩, hy⟩
  · simp [hx, hy, bindRead] at hnd
  rcases h0 : f x0 y0 with _ | r0
  · simp [hx, hy, h0, bindRead] at hnd
  rcases h1 : f x1 y1 with _ | r1
  · simp [hx, hy, h0, h1, bindRead] at hnd
  exact ⟨.pair (erealValue .f32 r0) (erealValue .f32 r1),
    by simp [hx, hy, h0, h1, bindRead, pure, Except.pure],
    .inr ⟨_, _, rfl, dat32_erealValue _, dat32_erealValue _⟩⟩

theorem add2D_step {t : TState} (hI : IdealAt A .addRnF32x2 L g t) {d a b : Nat} {va vb : Value}
    (ha : t.regs a = some va) (hb : t.regs b = some vb) (hda : Dat64 va) (hdb : Dat64 vb)
    (hnd : execIdealFloat L g t (pairOp .add d a b) ≠ none) :
    ∃ v, execLocalA A L g t (pairOp .add d a b) = .ok (PTX.next (setReg t d v)) ∧ Dat64 v := by
  obtain ⟨v, hv, hd⟩ := pair_dat (f := addEReal) rfl ha hb hda hdb hnd
  exact ⟨v, hI _ (by simp [pairOp, FloatForm.ofOp]) _ hv, hd⟩

theorem mul2D_step {t : TState} (hI : IdealAt A .mulF32x2 L g t) {d a b : Nat} {va vb : Value}
    (ha : t.regs a = some va) (hb : t.regs b = some vb) (hda : Dat64 va) (hdb : Dat64 vb)
    (hnd : execIdealFloat L g t (pairOp .mul d a b) ≠ none) :
    ∃ v, execLocalA A L g t (pairOp .mul d a b) = .ok (PTX.next (setReg t d v)) ∧ Dat64 v := by
  obtain ⟨v, hv, hd⟩ := pair_dat (f := mulEReal) rfl ha hb hda hdb hnd
  exact ⟨v, hI _ (by simp [pairOp, FloatForm.ofOp]) _ hv, hd⟩

end
end PTX.Flow.TyG
