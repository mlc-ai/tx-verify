-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.FloatOutcome

@[expose] public section

/-! # The outcome of `max.f32` on any operand values

A proof tool. Under an ideal-real assumption that names `max.f32` (ASM-IDEAL), the instruction
reads its two or three operands in the extended reals: an infinity is that infinity, and a NaN
makes the ideal rule decline, so that the Core rule (THREAD-FLOAT, `minMaxOp`) gives the result,
which is the maximum of the operands that are no NaN. An operand without a datum of `.f32`
faults under both rules. The outcome is one `Exec Value` (`maxE`), the ideal result where the
ideal rule applies and the Core rule's (`coreFloat`) where it declines; the local step writes its
value or faults (`exec_maxE`). On operands that read as numbers the outcome is the number of
their maximum (`maxE_fin`, `maxE_float`). -/

namespace PTX.Flow
open PTX PTX.Proof PTX.Assumption

noncomputable section

/-- `max.f32` (no `.ftz`, `.NaN`, `.xorsign` or `.abs`). -/
abbrev maxI : FloatInstr := { op := .max, ty := ty1 .f32, dsts := [], srcs := [] }

/-- The ideal-real outcome of `max.f32` on two or three source values, as `execIdealFloat`
computes it for registers that hold them; `none` where the rule declines (a NaN). -/
def idealMax : List Value → Option (Exec Value)
  | [a, b] => bindRead (readEReal .f32 a) fun x => bindRead (readEReal .f32 b) fun y =>
      some (pure (erealValue .f32 (max x y)))
  | [a, b, c] => bindRead (readEReal .f32 a) fun x => bindRead (readEReal .f32 b) fun y =>
      bindRead (readEReal .f32 c) fun z => some (pure (erealValue .f32 (max (max x y) z)))
  | _ => some (throw .noRule)

/-- **The outcome of `max.f32`**: the ideal outcome, or the Core rule's where the ideal rule
declines. -/
@[irreducible] def maxE (vs : List Value) : Exec Value :=
  match idealMax vs with
  | some r => r
  | none => coreFloat maxI vs

/-- A maximum of two numbers as extended reals is the maximum of the numbers. -/
theorem coe_max {x y : ℝ} : max (x : EReal) (y : EReal) = ((max x y : ℝ) : EReal) := by
  rcases le_total x y with h | h
  · rw [max_eq_right h, max_eq_right (EReal.coe_le_coe h)]
  · rw [max_eq_left h, max_eq_left (EReal.coe_le_coe h)]

/-- At a state, `A` leaves an operation of the floating form `f` whose operands make the ideal
rule decline to the Core rule. -/
def DeclineAt (A : List Assumption) (f : FloatForm) (L : Launch) (g : Nat) (t : TState) : Prop :=
  ∀ op, FloatForm.ofOp op = some f → execIdealFloat L g t op = none →
    execLocalA A L g t op = execLocal L g t op

/-- A head ideal-real assumption leaves a declined operation to the Core rule at a state where no
assumption takes a segment and no other assumption names the form. -/
theorem declineAt_head {name why : String} {s : IdealScope} {A' : List Assumption}
    {f : FloatForm} {L : Launch} {g : Nat} {t : TState}
    (hL : ∀ a ∈ A', ∀ op, FloatForm.ofOp op = some f → a.localRule L g t op = none)
    (hS : SegFreePc A' t.pc) : DeclineAt (idealReal name s why :: A') f L g t := by
  intro op hf hn
  have hA : SegFreeAt (idealReal name s why :: A') L g t := by
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · rfl
    · exact hS a ha L g t rfl
  rw [hA.exec, execLocalRule_of_none]
  intro a ha
  rcases List.mem_cons.mp ha with rfl | ha
  · simp only [idealReal, hf]
    split_ifs
    · exact hn
    · rfl
  · exact hL a ha op hf

/-- An operation of a `max` form is no approximate form. -/
theorem approxForm_none_of_max {op : Op} {fmt : FloatFmt}
    (h : FloatForm.ofOp op = some (.max fmt)) : ApproxForm.ofOp op = none := by
  cases op with
  | float f =>
    simp only [FloatForm.ofOp] at h
    simp only [ApproxForm.ofOp]
    cases hop : f.op <;> simp only [hop] at h <;> (try split_ifs at h) <;> simp_all
  | cvt c => simp only [FloatForm.ofOp] at h; split_ifs at h <;> simp_all
  | _ => simp [FloatForm.ofOp] at h

variable {A : List Assumption} {L : Launch} {g : Nat}

/-- The `max.f32` instruction of destination `d` and register sources `srcs`. -/
abbrev maxOp (d : Nat) (srcs : List Nat) : Op :=
  .float { op := .max, ty := FTy.mk .f32 1, dsts := [some d], srcs := srcs.map .reg }

theorem maxOp_form (d : Nat) (srcs : List Nat) :
    FloatForm.ofOp (maxOp d srcs) = some (.max .f32) := by
  simp [FloatForm.ofOp]

theorem execLocal_max2_core {t : TState} {d a b : Nat} {va vb : Value}
    (ha : t.regs a = some va) (hb : t.regs b = some vb) :
    execLocal L g t (maxOp d [a, b]) =
      (coreFloat maxI [va, vb]).map fun v => PTX.next (setReg t d v) := by
  have hl : ∀ xs, FloatInstr.lane
      { op := .max, ty := FTy.mk .f32 1, dsts := [some d], srcs := [.reg a, .reg b] } xs =
      FloatInstr.lane maxI xs := fun _ => rfl
  cases hxa : classify .f32 va with
  | error e => core_float_reg
  | ok xa =>
  cases hxb : classify .f32 vb with
  | error e => core_float_reg
  | ok xb =>
  cases hlane : FloatInstr.lane maxI [xa, xb] with
  | none => core_float_reg
  | some o => cases o <;> core_float_reg

theorem execLocal_max3_core {t : TState} {d a b c : Nat} {va vb vc : Value}
    (ha : t.regs a = some va) (hb : t.regs b = some vb) (hc : t.regs c = some vc) :
    execLocal L g t (maxOp d [a, b, c]) =
      (coreFloat maxI [va, vb, vc]).map fun v => PTX.next (setReg t d v) := by
  have hl : ∀ xs, FloatInstr.lane
      { op := .max, ty := FTy.mk .f32 1, dsts := [some d], srcs := [.reg a, .reg b, .reg c] }
        xs = FloatInstr.lane maxI xs := fun _ => rfl
  cases hxa : classify .f32 va with
  | error e => core_float_reg
  | ok xa =>
  cases hxb : classify .f32 vb with
  | error e => core_float_reg
  | ok xb =>
  cases hxc : classify .f32 vc with
  | error e => core_float_reg
  | ok xc =>
  cases hlane : FloatInstr.lane maxI [xa, xb, xc] with
  | none => core_float_reg
  | some o => cases o <;> core_float_reg

theorem execIdeal_max2 {t : TState} {d a b : Nat} {va vb : Value}
    (ha : t.regs a = some va) (hb : t.regs b = some vb) :
    execIdealFloat L g t (maxOp d [a, b]) =
      (idealMax [va, vb]).map (Except.map fun v => PTX.next (setReg t d v)) := by
  simp only [List.map_cons, List.map_nil, execIdealFloat, idealMax, readERealOpnd_reg ha,
    readERealOpnd_reg hb, bindRead_map, beq_self_eq_true, ↓reduceIte, Option.map_some,
    Except.map, pure, Except.pure]

theorem execIdeal_max3 {t : TState} {d a b c : Nat} {va vb vc : Value}
    (ha : t.regs a = some va) (hb : t.regs b = some vb) (hc : t.regs c = some vc) :
    execIdealFloat L g t (maxOp d [a, b, c]) =
      (idealMax [va, vb, vc]).map (Except.map fun v => PTX.next (setReg t d v)) := by
  simp only [List.map_cons, List.map_nil, execIdealFloat, idealMax, readERealOpnd_reg ha,
    readERealOpnd_reg hb, readERealOpnd_reg hc, bindRead_map, beq_self_eq_true, ↓reduceIte,
    Option.map_some, Except.map, pure, Except.pure]

/-- **The local step of `max.f32 d, a, b`** writes the outcome's value or faults. -/
theorem exec_maxE2 {t : TState} (hI : IdealAt A (.max .f32) L g t)
    (hD : DeclineAt A (.max .f32) L g t) {d a b : Nat} {va vb : Value}
    (ha : t.regs a = some va) (hb : t.regs b = some vb) :
    execLocalA A L g t (maxOp d [a, b]) =
      (maxE [va, vb]).map fun v => PTX.next (setReg t d v) := by
  have hi := execIdeal_max2 (L := L) (g := g) (d := d) ha hb
  unfold maxE
  cases hv : idealMax [va, vb] with
  | none => rw [hD _ (maxOp_form d [a, b]) (by rw [hi, hv]; rfl), execLocal_max2_core ha hb]
  | some r => rw [hI _ (maxOp_form d [a, b]) _ (by rw [hi, hv]; rfl)]

/-- **The local step of `max.f32 d, a, b, c`** writes the outcome's value or faults. -/
theorem exec_maxE3 {t : TState} (hI : IdealAt A (.max .f32) L g t)
    (hD : DeclineAt A (.max .f32) L g t) {d a b c : Nat} {va vb vc : Value}
    (ha : t.regs a = some va) (hb : t.regs b = some vb) (hc : t.regs c = some vc) :
    execLocalA A L g t (maxOp d [a, b, c]) =
      (maxE [va, vb, vc]).map fun v => PTX.next (setReg t d v) := by
  have hi := execIdeal_max3 (L := L) (g := g) (d := d) ha hb hc
  unfold maxE
  cases hv : idealMax [va, vb, vc] with
  | none =>
    rw [hD _ (maxOp_form d [a, b, c]) (by rw [hi, hv]; rfl), execLocal_max3_core ha hb hc]
  | some r => rw [hI _ (maxOp_form d [a, b, c]) _ (by rw [hi, hv]; rfl)]

/-- On operands that read as numbers the outcome is the number of their maximum. -/
theorem maxE_fin2 {va vb : Value} {x y : ℝ} (hx : valFloat .f32 va = .ok x)
    (hy : valFloat .f32 vb = .ok y) : maxE [va, vb] = .ok (.float .f32 (max x y)) := by
  unfold maxE
  simp only [idealMax, readEReal_of_valFloat hx, readEReal_of_valFloat hy, bindRead, coe_max,
    erealValue_coe .f32, pure, Except.pure]

theorem maxE_fin3 {va vb vc : Value} {x y z : ℝ} (hx : valFloat .f32 va = .ok x)
    (hy : valFloat .f32 vb = .ok y) (hz : valFloat .f32 vc = .ok z) :
    maxE [va, vb, vc] = .ok (.float .f32 (max (max x y) z)) := by
  unfold maxE
  simp only [idealMax, readEReal_of_valFloat hx, readEReal_of_valFloat hy,
    readEReal_of_valFloat hz, bindRead, coe_max, erealValue_coe .f32, pure, Except.pure]

end
end PTX.Flow
