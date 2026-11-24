-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.ReadRun

@[expose] public section

/-! # Accepting a read run by its operand types

A proof tool. A read run (`rCond`) is accepted when every register it reads holds a value of a
known shape: a single-precision number, a pair of them, a known 32-bit word, a known predicate.
`RTy.Has` states the shape; `RItem.tyStep` computes the shapes after an item, or fails when the
item's condition does not follow from the shapes; `rTy` runs the items. When the run's shape
check succeeds (`rTy T its ≠ none`, decided on concrete shapes) and the values have the shapes,
the run is accepted (`rCond_of_rTy`). -/

namespace PTX.Flow
open PTX PTX.Proof

noncomputable section

/-- A shape of a register value. -/
inductive RTy where
  | f32 | f32x2 | bits (x : BitVec 64) | pred (b : Bool) | any
  deriving DecidableEq

/-- A value of a shape. -/
def RTy.Has : RTy → Value → Prop
  | .f32, v => ∃ x, v = .float .f32 x
  | .f32x2, v => ∃ x y, v = .pair (.float .f32 x) (.float .f32 y)
  | .bits x, v => v = .bits 32 x
  | .pred b, v => v = .pred b
  | .any, _ => True

/-- The shapes after the item writes `tys`. -/
def tyUpd (T : Nat → RTy) (tys : List (Nat × RTy)) : Nat → RTy :=
  tys.foldl (fun (T : Nat → RTy) (p : Nat × RTy) => Function.update T p.1 p.2) T

/-- The shape of a register or `0f` operand when it holds four bytes. -/
def opndTy (T : Nat → RTy) : Opnd → Option RTy
  | .reg r => match T r with
    | .f32 => some .f32
    | .bits x => some (.bits x)
    | _ => none
  | .f32imm b => some (.bits (BitVec.ofNat 64 b))
  | _ => none

/-- The shapes an item writes, or `none` when its condition does not follow from the shapes. -/
def RItem.tyVals (T : Nat → RTy) : RItem → Option (List (Nat × RTy))
  | .andImm d a k => match T a with
    | .bits x => some [(d, .bits (truncBits 32 x &&& truncBits 32 (BitVec.ofInt 64 k)))]
    | _ => none
  | .setpImm cmp ty p a k => match T a with
    | .bits x => some [(p, .pred (compare cmp ty 32 (truncBits 32 x)
        (truncBits 32 (BitVec.ofInt 64 k))))]
    | _ => none
  | .unpack lo hi a => match T a with
    | .f32x2 => some [(lo, .f32), (hi, .f32)]
    | _ => none
  | .selp d a b p => match T p with
    | .pred bb => (opndTy T (if bb then a else b)).map fun ty => [(d, ty)]
    | _ => none
  | .fmax d a b c =>
    if T a = .f32 ∧ T b = .f32 ∧ ∀ c' ∈ c.toList, T c' = .f32 then some [(d, .f32)] else none

/-- The shapes after an item. -/
def RItem.tyStep (T : Nat → RTy) (it : RItem) : Option (Nat → RTy) :=
  (it.tyVals T).map (tyUpd T)

/-- The shapes after a run, or `none` when an item's condition does not follow. -/
def rTy (T : Nat → RTy) : List RItem → Option (Nat → RTy)
  | [] => some T
  | it :: its => (it.tyStep T).bind fun T' => rTy T' its

/-- Values of shapes `T`. -/
def RTy.All (T : Nat → RTy) (V : Nat → Value) : Prop := ∀ r, (T r).Has (V r)

theorem RTy.All.upd {T : Nat → RTy} {V : Nat → Value} (h : RTy.All T V) :
    ∀ {tys : List (Nat × RTy)} {vs : List (Nat × Value)},
      List.Forall₂ (fun p q => p.1 = q.1 ∧ p.2.Has q.2) tys vs →
      RTy.All (tyUpd T tys)
        (vs.foldl (fun (V : Nat → Value) (p : Nat × Value) => Function.update V p.1 p.2) V)
  | [], [], .nil => h
  | (r, ty) :: tys, (r', v) :: vs, .cons ⟨hr, hv⟩ hrest => by
    simp only at hr hv
    subst hr
    have h' : RTy.All (Function.update T r ty) (Function.update V r v) := by
      intro x
      by_cases hx : x = r
      · subst hx; simpa using hv
      · simp only [Function.update_of_ne hx]; exact h x
    exact RTy.All.upd h' hrest

theorem opndTy_has {T : Nat → RTy} {V : Nat → Value} (h : RTy.All T V) {o : Opnd} {ty : RTy}
    (ho : opndTy T o = some ty) : ty.Has (opndVal V o) ∧ (opndVal V o).bytes = 4 := by
  cases o with
  | reg r =>
    have hr := h r
    simp only [opndTy] at ho
    split at ho <;> simp only [Option.some.injEq, reduceCtorEq] at ho <;> subst ho <;>
      rename_i hT <;> rw [hT] at hr
    · obtain ⟨x, hx⟩ := hr
      simp [opndVal, hx, RTy.Has, Value.bytes, FloatFmt.bytes]
    · simp only [RTy.Has] at hr
      simp [opndVal, hr, RTy.Has, Value.bytes]
  | f32imm b =>
    simp only [opndTy, Option.some.injEq] at ho
    subst ho
    simp [opndVal, RTy.Has, Value.bytes]
  | _ => simp [opndTy] at ho

/-- **An item whose shape check succeeds is accepted**, and its values have the new shapes. -/
theorem RItem.tyStep_sound {T T' : Nat → RTy} {V : Nat → Value} {it : RItem}
    (h : RTy.All T V) (hs : it.tyStep T = some T') : it.cond V ∧ RTy.All T' (it.upd V) := by
  unfold RItem.tyStep at hs
  cases hv : it.tyVals T with
  | none => rw [hv] at hs; cases hs
  | some tys =>
    rw [hv] at hs
    simp only [Option.map_some, Option.some.injEq] at hs
    subst hs
    cases it with
    | andImm d a k =>
      simp only [RItem.tyVals] at hv
      split at hv <;> simp only [Option.some.injEq, reduceCtorEq] at hv
      rename_i x hT
      subst hv
      have ha := h a
      rw [hT] at ha
      simp only [RTy.Has] at ha
      refine ⟨trivial, RTy.All.upd h (.cons ⟨rfl, ?_⟩ .nil)⟩
      simp [RTy.Has, ha, bitsOf]
    | setpImm cmp ty p a k =>
      simp only [RItem.tyVals] at hv
      split at hv <;> simp only [Option.some.injEq, reduceCtorEq] at hv
      rename_i x hT
      subst hv
      have ha := h a
      rw [hT] at ha
      simp only [RTy.Has] at ha
      refine ⟨trivial, RTy.All.upd h (.cons ⟨rfl, ?_⟩ .nil)⟩
      simp [RTy.Has, ha, bitsOf]
    | unpack lo hi a =>
      simp only [RItem.tyVals] at hv
      split at hv <;> simp only [Option.some.injEq, reduceCtorEq] at hv
      rename_i hT
      subst hv
      have ha := h a
      rw [hT] at ha
      obtain ⟨x, y, hxy⟩ := ha
      refine ⟨by simp [RItem.cond, hxy, splitValue, Value.bytes, FloatFmt.bytes], ?_⟩
      exact RTy.All.upd h (.cons ⟨rfl, by simp [RTy.Has, hxy, splitValue]⟩
        (.cons ⟨rfl, by simp [RTy.Has, hxy, splitValue]⟩ .nil))
    | selp d a b p =>
      simp only [RItem.tyVals] at hv
      split at hv
      case h_2 => cases hv
      rename_i bb hT
      cases ho : opndTy T (if bb then a else b) with
      | none => rw [ho] at hv; cases hv
      | some ty =>
        rw [ho] at hv
        simp only [Option.map_some, Option.some.injEq] at hv
        subst hv
        have hp := h p
        rw [hT] at hp
        simp only [RTy.Has] at hp
        obtain ⟨h1, h2⟩ := opndTy_has h ho
        refine ⟨by simp only [RItem.cond, hp, predOf]; exact h2, ?_⟩
        exact RTy.All.upd h (.cons ⟨rfl, by simp only [hp, predOf]; exact h1⟩ .nil)
    | fmax d a b c =>
      simp only [RItem.tyVals] at hv
      split at hv <;> simp only [Option.some.injEq, reduceCtorEq] at hv
      rename_i hc
      subst hv
      obtain ⟨ha, hb, hcs⟩ := hc
      have hfa := h a
      have hfb := h b
      rw [ha] at hfa
      rw [hb] at hfb
      obtain ⟨x, hx⟩ := hfa
      obtain ⟨y, hy⟩ := hfb
      have vx : valFloat .f32 (V a) = .ok x := by simp [hx, valFloat, pure, Except.pure]
      have vy : valFloat .f32 (V b) = .ok y := by simp [hy, valFloat, pure, Except.pure]
      have hm : ∃ z, maxE (RItem.maxSrcs V a b c) = .ok (.float .f32 z) := by
        cases c with
        | none => exact ⟨_, maxE_fin2 vx vy⟩
        | some c =>
          have hfc := h c
          rw [hcs c (by simp)] at hfc
          obtain ⟨z, hz⟩ := hfc
          have vz : valFloat .f32 (V c) = .ok z := by simp [hz, valFloat, pure, Except.pure]
          exact ⟨_, maxE_fin3 vx vy vz⟩
      obtain ⟨z, hz⟩ := hm
      refine ⟨⟨_, hz⟩, RTy.All.upd h (.cons ⟨rfl, ⟨z, by simp [hz, okVal]⟩⟩ .nil)⟩

/-- **A run whose shape check succeeds is accepted.** -/
theorem rCond_of_rTy : ∀ {its : List RItem} {T : Nat → RTy} {V : Nat → Value},
    RTy.All T V → (rTy T its).isSome = true → rCond V its
  | [], _, _, _, _ => trivial
  | it :: its, T, V, h, hs => by
    simp only [rTy] at hs
    cases hT : it.tyStep T with
    | none => rw [hT] at hs; cases hs
    | some T' =>
      rw [hT] at hs
      obtain ⟨hc, h'⟩ := RItem.tyStep_sound h hT
      exact ⟨hc, rCond_of_rTy h' hs⟩

end
end PTX.Flow
