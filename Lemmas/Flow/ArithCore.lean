-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.MulPairCore
public import Lemmas.Flow.FmaPairCore
public import Lemmas.Flow.Ex2Core

@[expose] public section

/-! # The outcomes of scalar and packed additions and products at a state

A proof tool. Under an ideal-real assumption (ASM-IDEAL) that leaves its declines to the Core
rule, `mul.f32`, `sub.f32` and `add.f32` (without a rounding modifier) and `add.rn.f32x2` read their
operands in the extended reals: an operand without a datum of `.f32` faults, an infinity is that
infinity, and a NaN operand (or `∞ - ∞`, `0 · ∞`) makes the ideal rule decline, so that the Core
rule (THREAD-FLOAT) gives the result. The outcome on the values of the sources is one
`Exec Value` (`mulE`, `subE`, `add2E`, and `floatE (addI fz)` of `FloatOutcome`): the ideal value
where the ideal rule applies, the Core rule's (`coreFloat`) where it declines. The local step at a
state where the assumption list reads the form ideally (`IdealAt`) and leaves its declines to the
Core rule (`DeclineAt`) writes the outcome's value or faults (`exec_mulE`, `exec_subE`,
`exec_addE_at`, `exec_add2E`). A comparison with an infinite constant operand (the form
`setpInf`) has the outcome `setpE` of `SetpCore` (`exec_setpInfE`). Every value of an outcome has
the destination's width (`mulE_four`, `subE_four`, `add2E_pair4`), and on numbers the outcome is the
exact result (`mulE_fin`, `subE_fin`, `add2E_fin`). -/

namespace PTX.Flow
open PTX PTX.Proof PTX.Assumption

noncomputable section

variable {A : List Assumption} {L : Launch} {g : Nat}

/-- `mul{.ftz}.f32` without a rounding modifier. -/
abbrev mulI (fz : Bool) : FloatInstr :=
  { op := .mul, ty := ty1 .f32, ftz := fz, dsts := [], srcs := [] }

/-- `sub{.ftz}.f32` without a rounding modifier. -/
abbrev subI (fz : Bool) : FloatInstr :=
  { op := .sub, ty := ty1 .f32, ftz := fz, dsts := [], srcs := [] }

/-- `add.rn.f32x2`. -/
abbrev add2I : FloatInstr :=
  { op := .add, ty := ⟨.f32, 2⟩, rnd := some .rn, dsts := [], srcs := [] }

theorem execLocal_mul_core {t : TState} {fz : Bool} {d : Nat} {a b : Opnd} {va vb : Value}
    (ha : OpndIs L g t a va) (hb : OpndIs L g t b vb) :
    execLocal L g t (.float { mulI fz with dsts := [some d], srcs := [a, b] }) =
      (coreFloat (mulI fz) [va, vb]).map fun v => PTX.next (setReg t d v) := by
  have hl : FloatInstr.lane { mulI fz with dsts := [some d], srcs := [a, b] } =
      FloatInstr.lane (mulI fz) := rfl
  obtain ⟨ha, -⟩ := ha; obtain ⟨hb, -⟩ := hb
  cases hxa : classify .f32 va with
  | error e => core_float
  | ok xa =>
  cases hxb : classify .f32 vb with
  | error e => core_float
  | ok xb =>
  cases hlane : FloatInstr.lane (mulI fz) [xa, xb] with
  | none => core_float
  | some o => cases o <;> core_float

theorem execLocal_sub_core {t : TState} {fz : Bool} {d : Nat} {a b : Opnd} {va vb : Value}
    (ha : OpndIs L g t a va) (hb : OpndIs L g t b vb) :
    execLocal L g t (.float { subI fz with dsts := [some d], srcs := [a, b] }) =
      (coreFloat (subI fz) [va, vb]).map fun v => PTX.next (setReg t d v) := by
  have hl : FloatInstr.lane { subI fz with dsts := [some d], srcs := [a, b] } =
      FloatInstr.lane (subI fz) := rfl
  obtain ⟨ha, -⟩ := ha; obtain ⟨hb, -⟩ := hb
  cases hxa : classify .f32 va with
  | error e => core_float
  | ok xa =>
  cases hxb : classify .f32 vb with
  | error e => core_float
  | ok xb =>
  cases hlane : FloatInstr.lane (subI fz) [xa, xb] with
  | none => core_float
  | some o => cases o <;> core_float

theorem execLocal_add2_core {t : TState} {d a b : Nat} {va vb : Value}
    (ha : t.regs a = some va) (hb : t.regs b = some vb) :
    execLocal L g t (.float { add2I with dsts := [some d], srcs := [.reg a, .reg b] }) =
      (coreFloat add2I [va, vb]).map fun v => PTX.next (setReg t d v) := by
  have hl : FloatInstr.lane { add2I with dsts := [some d], srcs := [.reg a, .reg b] } =
      FloatInstr.lane add2I := rfl
  have h2 : List.range 2 = [0, 1] := rfl
  cases hxa : classify .f32 (splitValue 64 va).1 with
  | error e => core_float_reg
  | ok xa =>
  cases hxb : classify .f32 (splitValue 64 vb).1 with
  | error e => core_float_reg
  | ok xb =>
  cases hl0 : FloatInstr.lane add2I [xa, xb] with
  | none => core_float_reg
  | some o =>
  cases hya : classify .f32 (splitValue 64 va).2 with
  | error e => core_float_reg
  | ok ya =>
  cases hyb : classify .f32 (splitValue 64 vb).2 with
  | error e => core_float_reg
  | ok yb =>
  cases hl1 : FloatInstr.lane add2I [ya, yb] with
  | none => core_float_reg
  | some o' => cases o <;> cases o' <;> core_float_reg

/-! ### The ideal values and the outcomes -/

/-- The ideal-real outcome of `mul.f32` on source values; `none` where the rule declines. -/
def idealMul (va vb : Value) : Option (Exec Value) :=
  bindRead (readEReal .f32 va) fun x => bindRead (readEReal .f32 vb) fun y =>
    (mulEReal x y).map fun r => pure (erealValue .f32 r)

/-- The ideal-real outcome of `sub.f32` on source values; `none` where the rule declines. -/
def idealSub (va vb : Value) : Option (Exec Value) :=
  bindRead (readEReal .f32 va) fun x => bindRead (readEReal .f32 vb) fun y =>
    (addEReal x (-y)).map fun r => pure (erealValue .f32 r)

/-- The ideal-real outcome of `add.rn.f32x2` on source values; `none` where the rule declines in
a lane. -/
def idealAdd2 (va vb : Value) : Option (Exec Value) :=
  bindRead (pairRead va) fun (x0, x1) => bindRead (pairRead vb) fun (y0, y1) =>
    match addEReal x0 y0, addEReal x1 y1 with
    | some r0, some r1 => some (pure (.pair (erealValue .f32 r0) (erealValue .f32 r1)))
    | _, _ => none

/-- **The outcome of `mul.f32`**: the ideal outcome, or the Core rule's where it declines. -/
@[irreducible] def mulE (fz : Bool) (va vb : Value) : Exec Value :=
  match idealMul va vb with
  | some r => r
  | none => coreFloat (mulI fz) [va, vb]

/-- **The outcome of `sub.f32`**: the ideal outcome, or the Core rule's where it declines. -/
@[irreducible] def subE (fz : Bool) (va vb : Value) : Exec Value :=
  match idealSub va vb with
  | some r => r
  | none => coreFloat (subI fz) [va, vb]

/-- **The outcome of `add.rn.f32x2`**: the ideal outcome, or the Core rule's where it declines. -/
@[irreducible] def add2E (va vb : Value) : Exec Value :=
  match idealAdd2 va vb with
  | some r => r
  | none => coreFloat add2I [va, vb]

/-! ### The local steps -/

/-- **The local step of `mul.f32 d, a, b`** writes the outcome's value or faults. -/
theorem exec_mulE {t : TState} (hI : IdealAt A (.mul .f32) L g t)
    (hD : DeclineAt A (.mul .f32) L g t) {fz : Bool} {d : Nat} {a b : Opnd} {va vb : Value}
    (ha : OpndIs L g t a va) (hb : OpndIs L g t b vb) :
    execLocalA A L g t (.float { mulI fz with dsts := [some d], srcs := [a, b] }) =
      (mulE fz va vb).map fun v => PTX.next (setReg t d v) := by
  have hf : FloatForm.ofOp (.float { mulI fz with dsts := [some d], srcs := [a, b] }) =
      some (.mul .f32) := by simp [FloatForm.ofOp]
  have hi : execIdealFloat L g t (.float { mulI fz with dsts := [some d], srcs := [a, b] }) =
      (idealMul va vb).map (Except.map fun v => PTX.next (setReg t d v)) := by
    simp only [execIdealFloat, idealMul, ha.2, hb.2, bindRead_map, Option.map_map,
      Function.comp_def, Except.map, pure, Except.pure]
  unfold mulE
  cases hv : idealMul va vb with
  | none => rw [hD _ hf (by rw [hi, hv]; rfl), execLocal_mul_core ha hb]
  | some r => rw [hI _ hf _ (by rw [hi, hv]; rfl)]

/-- **The local step of `sub.f32 d, a, b`** writes the outcome's value or faults. -/
theorem exec_subE {t : TState} (hI : IdealAt A (.subRn .f32) L g t)
    (hD : DeclineAt A (.subRn .f32) L g t) {fz : Bool} {d : Nat} {a b : Opnd} {va vb : Value}
    (ha : OpndIs L g t a va) (hb : OpndIs L g t b vb) :
    execLocalA A L g t (.float { subI fz with dsts := [some d], srcs := [a, b] }) =
      (subE fz va vb).map fun v => PTX.next (setReg t d v) := by
  have hf : FloatForm.ofOp (.float { subI fz with dsts := [some d], srcs := [a, b] }) =
      some (.subRn .f32) := by simp [FloatForm.ofOp]
  have hi : execIdealFloat L g t (.float { subI fz with dsts := [some d], srcs := [a, b] }) =
      (idealSub va vb).map (Except.map fun v => PTX.next (setReg t d v)) := by
    simp only [execIdealFloat, idealSub, ha.2, hb.2, bindRead_map, Option.map_map,
      Function.comp_def, Except.map, pure, Except.pure]
  unfold subE
  cases hv : idealSub va vb with
  | none => rw [hD _ hf (by rw [hi, hv]; rfl), execLocal_sub_core ha hb]
  | some r => rw [hI _ hf _ (by rw [hi, hv]; rfl)]

/-- **The local step of `add.f32 d, a, b`** at a state writes the outcome's value or faults. -/
theorem exec_addE_at {t : TState} (hI : IdealAt A (.add .f32) L g t)
    (hD : DeclineAt A (.add .f32) L g t) {fz : Bool} {d : Nat} {a b : Opnd} {va vb : Value}
    (ha : OpndIs L g t a va) (hb : OpndIs L g t b vb) :
    execLocalA A L g t (.float { addI fz with dsts := [some d], srcs := [a, b] }) =
      (floatE (addI fz) [va, vb]).map fun v => PTX.next (setReg t d v) := by
  have hf : FloatForm.ofOp (.float { addI fz with dsts := [some d], srcs := [a, b] }) =
      some (.add .f32) := by simp [FloatForm.ofOp]
  have hi : execIdealFloat L g t (.float { addI fz with dsts := [some d], srcs := [a, b] }) =
      (idealVal (addI fz) [va, vb]).map (Except.map fun v => PTX.next (setReg t d v)) := by
    simp only [execIdealFloat, idealVal, ha.2, hb.2, bindRead_map, Option.map_map,
      Function.comp_def, Except.map, pure, Except.pure]
  unfold floatE
  cases hv : idealVal (addI fz) [va, vb] with
  | none => rw [hD _ hf (by rw [hi, hv]; rfl), execLocal_add_core ha hb]
  | some r => rw [hI _ hf _ (by rw [hi, hv]; rfl)]

/-- **The local step of `add.rn.f32x2 d, a, b`** writes the outcome's value or faults. -/
theorem exec_add2E {t : TState} (hI : IdealAt A .addRnF32x2 L g t)
    (hD : DeclineAt A .addRnF32x2 L g t) {d a b : Nat} {va vb : Value}
    (ha : t.regs a = some va) (hb : t.regs b = some vb) :
    execLocalA A L g t (.float { add2I with dsts := [some d], srcs := [.reg a, .reg b] }) =
      (add2E va vb).map fun v => PTX.next (setReg t d v) := by
  have hf : FloatForm.ofOp (.float { add2I with dsts := [some d], srcs := [.reg a, .reg b] }) =
      some .addRnF32x2 := by simp [FloatForm.ofOp]
  have hi : execIdealFloat L g t
      (.float { add2I with dsts := [some d], srcs := [.reg a, .reg b] }) =
      (idealAdd2 va vb).map (Except.map fun v => PTX.next (setReg t d v)) := by
    simp only [execIdealFloat, idealAdd2, readERealPair_reg_val (L := L) (g := g) ha,
      readERealPair_reg_val (L := L) (g := g) hb, bindRead_map]
    rcases pairRead va with _ | (e | ⟨x0, x1⟩)
    · rfl
    · rfl
    rcases pairRead vb with _ | (e | ⟨y0, y1⟩)
    · rfl
    · rfl
    simp only [bindRead]
    rcases addEReal x0 y0 with _ | r0 <;> rcases addEReal x1 y1 with _ | r1 <;> rfl
  unfold add2E
  cases hv : idealAdd2 va vb with
  | none => rw [hD _ hf (by rw [hi, hv]; rfl), execLocal_add2_core ha hb]
  | some r => rw [hI _ hf _ (by rw [hi, hv]; rfl)]

/-- **The local step of a comparison with an infinite constant operand** (the form `setpInf`)
writes the outcome `setpE` or faults. -/
theorem exec_setpInfE {t : TState} (hA : IdealAt A (.setpInf .f32) L g t)
    (hD : DeclineAt A (.setpInf .f32) L g t) {c : FCmp} {cmp : Cmp} {fz : Bool} {p : Nat}
    {a b : Opnd} {va vb : Value} (hc : c = .ord cmp ∨ c = .unord cmp)
    (hinf : (isInfConst a || isInfConst b) = true)
    (ha : OpndIs L g t a va) (hb : OpndIs L g t b vb) :
    execLocalA A L g t (.float { setpI c fz with dsts := [some p], srcs := [a, b] }) =
      (setpE c fz va vb).map fun r => PTX.next (setReg t p (.pred r)) := by
  have hf : FloatForm.ofOp (.float { setpI c fz with dsts := [some p], srcs := [a, b] }) =
      some (.setpInf .f32) := by
    rcases hc with rfl | rfl <;> simp [FloatForm.ofOp, hinf]
  have hbase : fcmpBase c = some cmp := by rcases hc with rfl | rfl <;> rfl
  have hI : execIdealFloat L g t (.float { setpI c fz with dsts := [some p], srcs := [a, b] }) =
      (idealSetp c va vb).map (Except.map fun r => PTX.next (setReg t p (.pred r))) := by
    rw [idealSetp, hbase]
    rcases hc with rfl | rfl <;>
    · simp only [execIdealFloat, ha.2, hb.2, bindRead_map_bool]
      rcases readEReal .f32 va with _ | (e | x)
      · rfl
      · rfl
      rcases readEReal .f32 vb with _ | (e | y) <;> rfl
  unfold setpE
  cases hv : idealSetp c va vb with
  | none => rw [hD _ hf (by rw [hI, hv]; rfl), execLocal_setp_core ha hb]
  | some r => rw [hA _ hf _ (by rw [hI, hv]; rfl)]

/-! ### Widths -/

theorem erealValue_map_four {o : Option EReal} {v : Value}
    (h : o.map (fun r => (pure (erealValue .f32 r) : Exec Value)) = some (.ok v)) :
    v.bytes = 4 := by
  obtain ⟨r, rfl⟩ := map_pure_ok h
  exact erealValue_f32_bytes r

/-- Every value of `mulE` has four bytes. -/
theorem mulE_four (fz : Bool) (va vb : Value) : Four (mulE fz va vb) := by
  intro v hv
  unfold mulE at hv
  split at hv
  · rename_i r hr
    subst hv
    obtain ⟨x, -, hr⟩ := bindRead_ok hr
    obtain ⟨y, -, hr⟩ := bindRead_ok hr
    exact erealValue_map_four hr
  · exact coreFloat_four rfl _ v hv

/-- Every value of `subE` has four bytes. -/
theorem subE_four (fz : Bool) (va vb : Value) : Four (subE fz va vb) := by
  intro v hv
  unfold subE at hv
  split at hv
  · rename_i r hr
    subst hv
    obtain ⟨x, -, hr⟩ := bindRead_ok hr
    obtain ⟨y, -, hr⟩ := bindRead_ok hr
    exact erealValue_map_four hr
  · exact coreFloat_four rfl _ v hv

/-- Every value of `add2E` is a pair of four-byte halves. -/
theorem add2E_pair4 (va vb : Value) : Pair4 (add2E va vb) := by
  intro v hv
  unfold add2E at hv
  split at hv
  · rename_i r hr
    subst hv
    obtain ⟨⟨x0, x1⟩, -, hr⟩ := bindRead_ok hr
    obtain ⟨⟨y0, y1⟩, -, hr⟩ := bindRead_ok hr
    simp only at hr
    split at hr
    · simp only [Option.some.injEq, pure, Except.pure, Except.ok.injEq] at hr
      exact ⟨_, _, hr.symm, erealValue_f32_bytes _, erealValue_f32_bytes _⟩
    · cases hr
  · exact coreFloat_pair4 rfl _ v hv

/-! ### Numbers -/

/-- **A product of numbers** is the number of the exact product. -/
theorem mulE_fin {fz : Bool} {va vb : Value} {x y : ℝ} (hx : valFloat .f32 va = .ok x)
    (hy : valFloat .f32 vb = .ok y) : mulE fz va vb = .ok (.float .f32 (x * y)) := by
  simp only [mulE, idealMul, readEReal_of_valFloat hx, readEReal_of_valFloat hy, bindRead,
    mulEReal_coe, Option.map_some, erealValue_coe, pure, Except.pure]

/-- **A difference of numbers** is the number of the exact difference. -/
theorem subE_fin {fz : Bool} {va vb : Value} {x y : ℝ} (hx : valFloat .f32 va = .ok x)
    (hy : valFloat .f32 vb = .ok y) : subE fz va vb = .ok (.float .f32 (x - y)) := by
  have h : addEReal (x : EReal) (-(y : EReal)) = some ((x - y : ℝ) : EReal) := by
    rw [← EReal.coe_neg, addEReal_coe, sub_eq_add_neg]
  simp only [subE, idealSub, readEReal_of_valFloat hx, readEReal_of_valFloat hy, bindRead, h,
    Option.map_some, erealValue_coe, pure, Except.pure]

/-- **A packed sum of numbers** is the pair of the exact sums. -/
theorem add2E_fin {va vb : Value} {x0 x1 y0 y1 : ℝ}
    (hx0 : valFloat .f32 (splitValue 64 va).1 = .ok x0)
    (hx1 : valFloat .f32 (splitValue 64 va).2 = .ok x1)
    (hy0 : valFloat .f32 (splitValue 64 vb).1 = .ok y0)
    (hy1 : valFloat .f32 (splitValue 64 vb).2 = .ok y1) :
    add2E va vb = .ok (.pair (.float .f32 (x0 + y0)) (.float .f32 (x1 + y1))) := by
  simp only [add2E, idealAdd2, pairRead_of hx0 hx1, pairRead_of hy0 hy1, bindRead, addEReal_coe,
    erealValue_coe, pure, Except.pure]


/-! ### Conversions to a pair of halves -/

/-- Every value of `cvtPairE` is a pair of two-byte halves. -/
theorem cvtPairE_ok {va vb v : Value} (h : cvtPairE va vb = .ok v) :
    ∃ x y, v = .pair x y ∧ x.bytes = 2 ∧ y.bytes = 2 := by
  have hcore : ∀ {w : Value}, coreCvtPair va vb = .ok w →
      ∃ x y, w = .pair x y ∧ x.bytes = 2 ∧ y.bytes = 2 := by
    intro w hw
    unfold coreCvtPair at hw
    obtain ⟨xa, -, hw⟩ := exec_bind_ok hw
    obtain ⟨xb, -, hw⟩ := exec_bind_ok hw
    obtain ⟨hi, -, hw⟩ := exec_bind_ok hw
    obtain ⟨lo, -, hw⟩ := exec_bind_ok hw
    cases hw
    exact ⟨_, _, rfl, toValue_f16_bytes _, toValue_f16_bytes _⟩
  unfold cvtPairE at h
  split at h
  · cases h
  · split at h
    · cases h
    · cases h
      exact ⟨_, _, rfl, erealValue_f16_bytes _, erealValue_f16_bytes _⟩
    · exact hcore h
  · exact hcore h

/-- The value of a conversion (`0` where it faults) has four bytes. -/
theorem okVal_cvtPairE_bytes (va vb : Value) : (okVal (.bits 32 0) (cvtPairE va vb)).bytes = 4 := by
  rcases h : cvtPairE va vb with e | v
  · rfl
  · obtain ⟨x, y, rfl, hx, hy⟩ := cvtPairE_ok h
    simp [okVal, Value.bytes, hx, hy]

/-- The value of a conversion is no slice. -/
theorem okVal_cvtPairE_ns (va vb : Value) :
    ∀ w o n, okVal (.bits 32 0) (cvtPairE va vb) ≠ .slice w o n := by
  intro w o n
  rcases h : cvtPairE va vb with e | v
  · simp [okVal]
  · obtain ⟨x, y, rfl, -, -⟩ := cvtPairE_ok h
    simp [okVal]

end
end PTX.Flow
