-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.SegDead
public import Lemmas.Flow.FloatOp

@[expose] public section

/-! # The outcome of a floating instruction on any operand values

A proof tool. Under an ideal-real assumption (ASM-IDEAL) or an approximate-as-exact one
(ASM-APPROX), a floating instruction reads its operands in the extended reals: an operand without
a value of the format faults, an infinite operand is that infinity, and a NaN operand (or `∞ - ∞`,
`0 · ∞`, an infinite operand of an approximation) makes the assumption decline, so that the Core
rule gives the result. The outcome of the instruction on the values of its sources is therefore
one `Exec Value` (`floatE`, `approxE`, `widenE`): the ideal result where the ideal rule applies,
the Core rule's (`coreFloat`, `coreWiden`) where it declines, and a fault exactly where the
instruction faults. Its local step writes the outcome's value or faults (`exec_floatE_fma`,
`exec_floatE_add`, `exec_floatE_mul2`, `exec_approxE_div`, `exec_approxE_rsqrt`,
`exec_widenE`), and so do the moves (`exec_movE`, `exec_packE`, `exec_unpackE`). An `add`
without a rounding modifier has no Core rule, so it faults where the ideal rule declines
(`floatE_add_decline`).

`SegD.one` and `SegD.two` take one such instruction as a piece between facts by one table: the
thread continues when the outcome does not fault and is dead otherwise. Every value of an outcome
has the destination's width (`floatE_fma_four`, `floatE_add_four`, `floatE_mul2_pair4`,
`approxE_four`, `widenE_four`), and on finite operands the outcome is the number of the exact
real result (`floatE_fma_fin`, `floatE_add_fin`, `floatE_mul2_fin`, `approxE_div_fin`,
`approxE_rsqrt_fin`, `widenE_fin`), so a kernel whose inputs are real numbers reads its values as
reals. -/

namespace PTX.Flow
open PTX PTX.Proof PTX.Assumption

noncomputable section

/-- The value of an outcome, `dflt` where it faults. -/
def okVal (dflt : Value) : Exec Value → Value
  | .ok v => v
  | .error _ => dflt

theorem okVal_of_ok {dflt v : Value} {e : Exec Value} (h : e = .ok v) : okVal dflt e = v := by
  rw [h]; rfl

/-- The value the Core rule (THREAD-FLOAT) writes for a one-destination floating instruction `f`
that is no comparison, from the values `vs` of its sources: each lane's datum in the destination
format, the pair of the two lanes' data for a packed form. -/
def coreFloat (f : FloatInstr) (vs : List Value) : Exec Value := do
  let outs ← (List.range f.ty.lanes).mapM fun j => do
    let xs ← vs.mapM fun v => classify f.ty.fmt (floatLane f.ty v j)
    match f.lane xs with
    | some o => pure o
    | none => throw .noRule
  match outs with
  | [.val v] => pure (v.toValue f.ty.fmt)
  | [.val v0, .val v1] => pure (.pair (v0.toValue f.ty.fmt) (v1.toValue f.ty.fmt))
  | _ => throw .noRule

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- The operand `o` of a 32-bit floating source reads as `v`, for data movement and as the ideal
rule reads it. -/
def OpndIs (L : Launch) (g : Nat) (t : TState) (o : Opnd) (v : Value) : Prop :=
  readValue L g t 32 o = .ok v ∧ readERealOpnd t .f32 o = readEReal .f32 v

theorem OpndIs.reg {t : TState} {r : Nat} {v : Value} (h : t.regs r = some v) :
    OpndIs L g t (.reg r) v :=
  ⟨by simp [readValue, readReg, h, pure, Except.pure], readERealOpnd_reg h⟩

theorem OpndIs.imm {t : TState} {b : Nat} :
    OpndIs L g t (.f32imm b) (.bits 32 (BitVec.ofNat 64 b)) :=
  ⟨rfl, rfl⟩

/-- `fma.rnd{.ftz}.f32`. -/
abbrev fmaI (rnd : FloatRound) (fz : Bool) : FloatInstr :=
  { op := .fma, ty := ty1 .f32, rnd := some rnd, ftz := fz, dsts := [], srcs := [] }

/-- `add{.ftz}.f32` without a rounding modifier. -/
abbrev addI (fz : Bool) : FloatInstr :=
  { op := .add, ty := ty1 .f32, ftz := fz, dsts := [], srcs := [] }

/-- `mul.rnd{.ftz}.f32x2`. -/
abbrev mul2I (rnd : FloatRound) (fz : Bool) : FloatInstr :=
  { op := .mul, ty := ⟨.f32, 2⟩, rnd := some rnd, ftz := fz, dsts := [], srcs := [] }

/-- `div.approx{.ftz}.f32`. -/
abbrev divI (fz : Bool) : FloatInstr :=
  { op := .div, ty := ty1 .f32, mode := .approx, ftz := fz, dsts := [], srcs := [] }

/-- `rsqrt.approx{.ftz}.f32`. -/
abbrev rsqrtI (fz : Bool) : FloatInstr :=
  { op := .rsqrt, ty := ty1 .f32, mode := .approx, ftz := fz, dsts := [], srcs := [] }

/-- The steps of the Core rules below: read the sources' data, then the lane rule. -/
macro "core_float" : tactic => `(tactic|
  simp [execLocal, Op.rule, FloatInstr.rule, execFloat, boolCombine, coreFloat, ty1,
    FloatFmt.bytes, floatLane, bind, Except.bind, Except.map, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw, *])

/-- `core_float` for register sources. -/
macro "core_float_reg" : tactic => `(tactic|
  simp [execLocal, Op.rule, FloatInstr.rule, execFloat, boolCombine, coreFloat, ty1,
    FloatFmt.bytes, floatLane, readValue, readReg, bind, Except.bind, Except.map, pure,
    Except.pure, throw, throwThe, MonadExceptOf.throw, *])

theorem execLocal_fma_core {t : TState} {rnd : FloatRound} {fz : Bool} {d : Nat}
    {a b c : Opnd} {va vb vc : Value}
    (ha : OpndIs L g t a va) (hb : OpndIs L g t b vb) (hc : OpndIs L g t c vc) :
    execLocal L g t (.float { fmaI rnd fz with dsts := [some d], srcs := [a, b, c] }) =
      (coreFloat (fmaI rnd fz) [va, vb, vc]).map fun v => PTX.next (setReg t d v) := by
  have hl : FloatInstr.lane { fmaI rnd fz with dsts := [some d], srcs := [a, b, c] } =
      FloatInstr.lane (fmaI rnd fz) := rfl
  obtain ⟨ha, -⟩ := ha; obtain ⟨hb, -⟩ := hb; obtain ⟨hc, -⟩ := hc
  cases hxa : classify .f32 va with
  | error e => core_float
  | ok xa =>
  cases hxb : classify .f32 vb with
  | error e => core_float
  | ok xb =>
  cases hxc : classify .f32 vc with
  | error e => core_float
  | ok xc =>
  cases hlane : FloatInstr.lane (fmaI rnd fz) [xa, xb, xc] with
  | none => core_float
  | some o => cases o <;> core_float

theorem execLocal_add_core {t : TState} {fz : Bool} {d : Nat} {a b : Opnd} {va vb : Value}
    (ha : OpndIs L g t a va) (hb : OpndIs L g t b vb) :
    execLocal L g t (.float { addI fz with dsts := [some d], srcs := [a, b] }) =
      (coreFloat (addI fz) [va, vb]).map fun v => PTX.next (setReg t d v) := by
  have hl : FloatInstr.lane { addI fz with dsts := [some d], srcs := [a, b] } =
      FloatInstr.lane (addI fz) := rfl
  obtain ⟨ha, -⟩ := ha; obtain ⟨hb, -⟩ := hb
  cases hxa : classify .f32 va with
  | error e => core_float
  | ok xa =>
  cases hxb : classify .f32 vb with
  | error e => core_float
  | ok xb =>
  cases hlane : FloatInstr.lane (addI fz) [xa, xb] with
  | none => core_float
  | some o => cases o <;> core_float

theorem execLocal_div_core {t : TState} {fz : Bool} {d : Nat} {a b : Opnd} {va vb : Value}
    (ha : OpndIs L g t a va) (hb : OpndIs L g t b vb) :
    execLocal L g t (.float { divI fz with dsts := [some d], srcs := [a, b] }) =
      (coreFloat (divI fz) [va, vb]).map fun v => PTX.next (setReg t d v) := by
  have hl : FloatInstr.lane { divI fz with dsts := [some d], srcs := [a, b] } =
      FloatInstr.lane (divI fz) := rfl
  obtain ⟨ha, -⟩ := ha; obtain ⟨hb, -⟩ := hb
  cases hxa : classify .f32 va with
  | error e => core_float
  | ok xa =>
  cases hxb : classify .f32 vb with
  | error e => core_float
  | ok xb =>
  cases hlane : FloatInstr.lane (divI fz) [xa, xb] with
  | none => core_float
  | some o => cases o <;> core_float

theorem execLocal_rsqrt_core {t : TState} {fz : Bool} {d : Nat} {a : Opnd} {va : Value}
    (ha : OpndIs L g t a va) :
    execLocal L g t (.float { rsqrtI fz with dsts := [some d], srcs := [a] }) =
      (coreFloat (rsqrtI fz) [va]).map fun v => PTX.next (setReg t d v) := by
  have hl : FloatInstr.lane { rsqrtI fz with dsts := [some d], srcs := [a] } =
      FloatInstr.lane (rsqrtI fz) := rfl
  obtain ⟨ha, -⟩ := ha
  cases hxa : classify .f32 va with
  | error e => core_float
  | ok xa =>
  cases hlane : FloatInstr.lane (rsqrtI fz) [xa] with
  | none => core_float
  | some o => cases o <;> core_float

theorem execLocal_mul2_core {t : TState} {rnd : FloatRound} {fz : Bool} {d a b : Nat}
    {va vb : Value} (ha : t.regs a = some va) (hb : t.regs b = some vb) :
    execLocal L g t (.float { mul2I rnd fz with dsts := [some d], srcs := [.reg a, .reg b] }) =
      (coreFloat (mul2I rnd fz) [va, vb]).map fun v => PTX.next (setReg t d v) := by
  have hl : FloatInstr.lane { mul2I rnd fz with dsts := [some d], srcs := [.reg a, .reg b] } =
      FloatInstr.lane (mul2I rnd fz) := rfl
  have h2 : List.range 2 = [0, 1] := rfl
  cases hxa : classify .f32 (splitValue 64 va).1 with
  | error e => core_float_reg
  | ok xa =>
  cases hxb : classify .f32 (splitValue 64 vb).1 with
  | error e => core_float_reg
  | ok xb =>
  cases hl0 : FloatInstr.lane (mul2I rnd fz) [xa, xb] with
  | none => core_float_reg
  | some o =>
  cases hya : classify .f32 (splitValue 64 va).2 with
  | error e => core_float_reg
  | ok ya =>
  cases hyb : classify .f32 (splitValue 64 vb).2 with
  | error e => core_float_reg
  | ok yb =>
  cases hl1 : FloatInstr.lane (mul2I rnd fz) [ya, yb] with
  | none => core_float_reg
  | some o' => cases o <;> cases o' <;> core_float_reg

/-! ### The ideal rule and the outcome -/

/-- The ideal-real outcome (ASM-IDEAL) of `fma`, `add` and `mul` of one lane and of `mul` of
`.f32x2` on source values, as `execIdealFloat` computes it for operands that hold them; `none`
where the rule declines (a NaN, `∞ - ∞`, `0 · ∞`). -/
def idealVal (f : FloatInstr) (vs : List Value) : Option (Exec Value) :=
  let fmt := f.ty.fmt
  match f.op, f.ty.lanes, vs with
  | .add, 1, [a, b] => bindRead (readEReal fmt a) fun x => bindRead (readEReal fmt b) fun y =>
      (addEReal x y).map fun r => pure (erealValue fmt r)
  | .fma, 1, [a, b, c] => bindRead (readEReal fmt a) fun x => bindRead (readEReal fmt b) fun y =>
      bindRead (readEReal fmt c) fun z =>
        ((mulEReal x y).bind fun p => addEReal p z).map fun r => pure (erealValue fmt r)
  | .mul, 2, [a, b] => bindRead (pairRead a) fun (x0, x1) => bindRead (pairRead b) fun (y0, y1) =>
      match mulEReal x0 y0, mulEReal x1 y1 with
      | some r0, some r1 => some (pure (.pair (erealValue .f32 r0) (erealValue .f32 r1)))
      | _, _ => none
  | _, _, _ => some (throw .noRule)

/-- **The outcome of a floating instruction** under an ideal-real assumption that leaves its
declines to the Core rule: the ideal outcome, or the Core rule's where the ideal rule declines. -/
@[irreducible] def floatE (f : FloatInstr) (vs : List Value) : Exec Value :=
  match idealVal f vs with
  | some r => r
  | none => coreFloat f vs

theorem bindRead_map {α β γ : Type} (x : Option (Exec α)) (k : α → Option (Exec β))
    (F : β → γ) :
    (bindRead x k).map (Except.map F) = bindRead x fun a => (k a).map (Except.map F) := by
  rcases x with _ | (e | a) <;> rfl

theorem exec_floatE_fma (hA : IdealFor A (.fma .f32)) (hD : DeclineCore A (.fma .f32))
    {t : TState} {rnd : FloatRound} {fz : Bool} {d : Nat} {a b c : Opnd} {va vb vc : Value}
    (ha : OpndIs L g t a va) (hb : OpndIs L g t b vb) (hc : OpndIs L g t c vc) :
    execLocalA A L g t (.float { fmaI rnd fz with dsts := [some d], srcs := [a, b, c] }) =
      (floatE (fmaI rnd fz) [va, vb, vc]).map fun v => PTX.next (setReg t d v) := by
  have hf : FloatForm.ofOp (.float { fmaI rnd fz with dsts := [some d], srcs := [a, b, c] }) =
      some (.fma .f32) := by simp [FloatForm.ofOp]
  have hI : execIdealFloat L g t (.float { fmaI rnd fz with dsts := [some d], srcs := [a, b, c] }) =
      (idealVal (fmaI rnd fz) [va, vb, vc]).map (Except.map fun v => PTX.next (setReg t d v)) := by
    simp only [execIdealFloat, idealVal, ha.2, hb.2, hc.2, bindRead_map, Option.map_map,
      Function.comp_def, Except.map, pure, Except.pure]
  unfold floatE
  cases hv : idealVal (fmaI rnd fz) [va, vb, vc] with
  | none => rw [hD L g t _ hf (by rw [hI, hv]; rfl), execLocal_fma_core ha hb hc]
  | some r => rw [hA L g t _ hf _ (by rw [hI, hv]; rfl)]

theorem exec_floatE_add (hA : IdealFor A (.add .f32)) (hD : DeclineCore A (.add .f32))
    {t : TState} {fz : Bool} {d : Nat} {a b : Opnd} {va vb : Value}
    (ha : OpndIs L g t a va) (hb : OpndIs L g t b vb) :
    execLocalA A L g t (.float { addI fz with dsts := [some d], srcs := [a, b] }) =
      (floatE (addI fz) [va, vb]).map fun v => PTX.next (setReg t d v) := by
  have hf : FloatForm.ofOp (.float { addI fz with dsts := [some d], srcs := [a, b] }) =
      some (.add .f32) := by simp [FloatForm.ofOp]
  have hI : execIdealFloat L g t (.float { addI fz with dsts := [some d], srcs := [a, b] }) =
      (idealVal (addI fz) [va, vb]).map (Except.map fun v => PTX.next (setReg t d v)) := by
    simp only [execIdealFloat, idealVal, ha.2, hb.2, bindRead_map, Option.map_map,
      Function.comp_def, Except.map, pure, Except.pure]
  unfold floatE
  cases hv : idealVal (addI fz) [va, vb] with
  | none => rw [hD L g t _ hf (by rw [hI, hv]; rfl), execLocal_add_core ha hb]
  | some r => rw [hA L g t _ hf _ (by rw [hI, hv]; rfl)]

theorem exec_floatE_mul2 (hA : IdealFor A .mulF32x2) (hD : DeclineCore A .mulF32x2)
    {t : TState} {rnd : FloatRound} {fz : Bool} {d a b : Nat} {va vb : Value}
    (ha : t.regs a = some va) (hb : t.regs b = some vb) :
    execLocalA A L g t (.float { mul2I rnd fz with dsts := [some d], srcs := [.reg a, .reg b] }) =
      (floatE (mul2I rnd fz) [va, vb]).map fun v => PTX.next (setReg t d v) := by
  have hf : FloatForm.ofOp
      (.float { mul2I rnd fz with dsts := [some d], srcs := [.reg a, .reg b] }) =
      some .mulF32x2 := by simp [FloatForm.ofOp]
  have hI : execIdealFloat L g t
      (.float { mul2I rnd fz with dsts := [some d], srcs := [.reg a, .reg b] }) =
      (idealVal (mul2I rnd fz) [va, vb]).map (Except.map fun v => PTX.next (setReg t d v)) := by
    simp only [execIdealFloat, idealVal, readERealPair_reg_val (L := L) (g := g) ha,
      readERealPair_reg_val (L := L) (g := g) hb, bindRead_map]
    rcases pairRead va with _ | (e | ⟨x0, x1⟩)
    · rfl
    · rfl
    rcases pairRead vb with _ | (e | ⟨y0, y1⟩)
    · rfl
    · rfl
    simp only [bindRead]
    rcases mulEReal x0 y0 with _ | r0 <;> rcases mulEReal x1 y1 with _ | r1 <;> rfl
  unfold floatE
  cases hv : idealVal (mul2I rnd fz) [va, vb] with
  | none => rw [hD L g t _ hf (by rw [hI, hv]; rfl), execLocal_mul2_core ha hb]
  | some r => rw [hA L g t _ hf _ (by rw [hI, hv]; rfl)]

/-- An `add` without a rounding modifier has no Core rule: where the ideal rule declines (a NaN
operand, `∞ - ∞`), it faults. -/
theorem coreFloat_add_error {fz : Bool} (va vb : Value) :
    ∃ e, coreFloat (addI fz) [va, vb] = .error e := by
  have hl : ∀ xs, FloatInstr.lane (addI fz) xs = none := fun xs => by
    simp [FloatInstr.lane, FloatInstr.rule, FloatInstr.ieee, FloatInstr.arith, Option.bind]
  cases hxa : classify .f32 va with
  | error e => exact ⟨e, by simp [coreFloat, floatLane, hxa, bind, Except.bind]⟩
  | ok xa =>
  cases hxb : classify .f32 vb with
  | error e => exact ⟨e, by simp [coreFloat, floatLane, hxa, hxb, bind, Except.bind]⟩
  | ok xb => exact ⟨.noRule, by simp [coreFloat, floatLane, hxa, hxb, hl, bind, Except.bind,
      pure, Except.pure, throw, throwThe, MonadExceptOf.throw]⟩

theorem floatE_add_decline {fz : Bool} {va vb : Value} (h : idealVal (addI fz) [va, vb] = none) :
    ∃ e, floatE (addI fz) [va, vb] = .error e := by
  unfold floatE
  rw [h]
  exact coreFloat_add_error va vb

/-! ### Approximations read as exact functions -/

/-- `A` reads the approximate form `f` as its exact function (ASM-APPROX) where the rule
applies. -/
def ApproxFor (A : List Assumption) (f : ApproxForm) : Prop :=
  ∀ L g t op, ApproxForm.ofOp op = some f → ∀ e, execApproxExact t op = some e →
    execLocalA A L g t op = e

/-- `A` leaves an approximation of the form `f` whose operand is infinite or NaN to the Core
rule. -/
def ApproxDecline (A : List Assumption) (f : ApproxForm) : Prop :=
  ∀ L g t op, ApproxForm.ofOp op = some f → execApproxExact t op = none →
    execLocalA A L g t op = execLocal L g t op

/-- A list without segments whose local rules give the approximate-as-exact rule for the form
`f` reads it as exact and leaves its declines to the Core rule. -/
theorem approx_of_rules {f : ApproxForm} (hS : NoSegments A)
    (hR : ∀ L g t op, ApproxForm.ofOp op = some f →
      A.findSome? (fun a => a.localRule L g t op) = execApproxExact t op) :
    ApproxFor A f ∧ ApproxDecline A f := by
  constructor
  · intro L g t op hf e he
    rw [(hS.segFreePc (pc := t.pc)).at rfl |>.exec]
    unfold execLocalRule
    rw [hR L g t op hf, he]
  · intro L g t op hf he
    rw [(hS.segFreePc (pc := t.pc)).at rfl |>.exec]
    unfold execLocalRule
    rw [hR L g t op hf, he]

/-- An operation that is an approximate form is no floating form of the ideal-real reading. -/
theorem floatForm_none_of_approx {op : Op} {f : ApproxForm} (h : ApproxForm.ofOp op = some f) :
    FloatForm.ofOp op = none := by
  cases op with
  | float fi =>
    simp only [ApproxForm.ofOp] at h
    split_ifs at h
    rcases hop : fi.op <;> simp [hop] at h <;> simp [FloatForm.ofOp, hop]
  | _ => simp [ApproxForm.ofOp] at h

/-- An operation that is a floating form of the ideal-real reading is no approximate form. -/
theorem approxForm_none_of_float {op : Op} {f : FloatForm} (h : FloatForm.ofOp op = some f) :
    ApproxForm.ofOp op = none := by
  cases hA : ApproxForm.ofOp op with
  | none => rfl
  | some f' => rw [floatForm_none_of_approx hA] at h; cases h

/-- A finite operand of an approximation as a real; `none` for an infinite or NaN one. -/
def finiteVal (v : Value) : Option (Exec ℝ) :=
  bindRead (readEReal .f32 v) fun x => if x = ⊤ ∨ x = ⊥ then none else some (pure x.toReal)

/-- The exact function of `div.approx.f32` and `rsqrt.approx.f32` on source values (ASM-APPROX),
`none` where an operand is infinite or NaN. -/
def approxVal (f : FloatInstr) (vs : List Value) : Option (Exec Value) :=
  match f.op, vs with
  | .div, [a, b] => bindRead (finiteVal a) fun x => bindRead (finiteVal b) fun y =>
      some (if y = 0 then throw .badValue else pure (.float .f32 (x / y)))
  | .rsqrt, [a] => bindRead (finiteVal a) fun x =>
      some (if x ≤ 0 then throw .badValue else pure (.float .f32 (1 / Real.sqrt x)))
  | _, _ => some (throw .noRule)

/-- **The outcome of an approximation** read as its exact function: the exact value, or the Core
table's where the rule declines. -/
@[irreducible] def approxE (f : FloatInstr) (vs : List Value) : Exec Value :=
  match approxVal f vs with
  | some r => r
  | none => coreFloat f vs

theorem readFinite_of {t : TState} {a : Opnd} {v : Value}
    (h : readERealOpnd t .f32 a = readEReal .f32 v) : readFinite t .f32 a = finiteVal v := by
  simp only [readFinite, finiteVal, h]

theorem exec_approxE_div (hA : ApproxFor A (.div .f32)) (hD : ApproxDecline A (.div .f32))
    {t : TState} {fz : Bool} {d : Nat} {a b : Opnd} {va vb : Value}
    (ha : OpndIs L g t a va) (hb : OpndIs L g t b vb) :
    execLocalA A L g t (.float { divI fz with dsts := [some d], srcs := [a, b] }) =
      (approxE (divI fz) [va, vb]).map fun v => PTX.next (setReg t d v) := by
  have hf : ApproxForm.ofOp (.float { divI fz with dsts := [some d], srcs := [a, b] }) =
      some (.div .f32) := by simp [ApproxForm.ofOp]
  have hI : execApproxExact t (.float { divI fz with dsts := [some d], srcs := [a, b] }) =
      (approxVal (divI fz) [va, vb]).map (Except.map fun v => PTX.next (setReg t d v)) := by
    simp only [execApproxExact, approxVal, readFinite_of ha.2, readFinite_of hb.2, bindRead_map]
    rcases finiteVal va with _ | (e | x)
    · rfl
    · rfl
    rcases finiteVal vb with _ | (e | y)
    · rfl
    · rfl
    simp only [bindRead]
    split_ifs <;> rfl
  unfold approxE
  cases hv : approxVal (divI fz) [va, vb] with
  | none => rw [hD L g t _ hf (by rw [hI, hv]; rfl), execLocal_div_core ha hb]
  | some r => rw [hA L g t _ hf _ (by rw [hI, hv]; rfl)]

theorem exec_approxE_rsqrt (hA : ApproxFor A (.rsqrt .f32)) (hD : ApproxDecline A (.rsqrt .f32))
    {t : TState} {fz : Bool} {d : Nat} {a : Opnd} {va : Value} (ha : OpndIs L g t a va) :
    execLocalA A L g t (.float { rsqrtI fz with dsts := [some d], srcs := [a] }) =
      (approxE (rsqrtI fz) [va]).map fun v => PTX.next (setReg t d v) := by
  have hf : ApproxForm.ofOp (.float { rsqrtI fz with dsts := [some d], srcs := [a] }) =
      some (.rsqrt .f32) := by simp [ApproxForm.ofOp]
  have hI : execApproxExact t (.float { rsqrtI fz with dsts := [some d], srcs := [a] }) =
      (approxVal (rsqrtI fz) [va]).map (Except.map fun v => PTX.next (setReg t d v)) := by
    simp only [execApproxExact, approxVal, readFinite_of ha.2, bindRead_map]
    rcases finiteVal va with _ | (e | x)
    · rfl
    · rfl
    simp only [bindRead]
    split_ifs <;> rfl
  unfold approxE
  cases hv : approxVal (rsqrtI fz) [va] with
  | none => rw [hD L g t _ hf (by rw [hI, hv]; rfl), execLocal_rsqrt_core ha]
  | some r => rw [hA L g t _ hf _ (by rw [hI, hv]; rfl)]

/-! ### Widening a half to single precision -/

/-- `cvt.f32.f16 d, a`. -/
abbrev widenC (d : Nat) (a : Opnd) : CvtInstr :=
  { dst := .float .f32, src := .float .f16, d := d, srcs := [a] }

/-- The value the Core conversion rule (THREAD-CVT) writes for `cvt.f32.f16` of a register that
holds `h`: its low half read as a half-precision datum, widened. -/
def coreWiden (h : Value) : Exec Value :=
  (if 2 < h.bytes then lowValue 2 h >>= classify .f16 else classify .f16 h) >>= fun x =>
    widenElem (widenC 0 (.reg 0)) .f32 FloatFmt.f32.layout false x >>= fun y =>
      pure (y.toValue .f32)

/-- **The outcome of `cvt.f32.f16`** under an ideal-real assumption for the form: the extended
real of the half, the fault of a value the ideal rule rejects, the Core rule's value for a NaN. -/
@[irreducible] def widenE (h : Value) : Exec Value :=
  match readEReal .f16 h with
  | some (.error e) => .error e
  | some (.ok x) => .ok (erealValue .f32 x)
  | none => coreWiden h

theorem execLocal_widen_core {t : TState} {d r : Nat} {v : Value} (h : t.regs r = some v) :
    execLocal L g t (.cvt (widenC d (.reg r))) =
      (coreWiden v).map fun w => PTX.next (setReg t d w) := by
  have hw : widenElem (widenC d (.reg r)) = widenElem (widenC 0 (.reg 0)) := rfl
  have hr : (Op.cvt (widenC d (.reg r))).rule = some .threadCvt := by
    simp [Op.rule, CvtInstr.rule, CvtInstr.exact, CvtInstr.widens]
  simp only [execLocal, hr]
  simp [execCvt, readCvtFloat, readReg, h, FType.fmt?, hw, coreWiden, bind, Except.bind,
    Except.map, pure, Except.pure]
  rw [show FloatFmt.f16.bytes = 2 from rfl]
  split_ifs
  · cases lowValue 2 v with
    | error e => rfl
    | ok w =>
      dsimp only
      cases classify .f16 w with
      | error e => rfl
      | ok x =>
        dsimp only
        cases widenElem (widenC 0 (.reg 0)) .f32 FloatFmt.f32.layout false x <;> rfl
  · cases classify .f16 v with
    | error e => rfl
    | ok x =>
      dsimp only
      cases widenElem (widenC 0 (.reg 0)) .f32 FloatFmt.f32.layout false x <;> rfl

theorem exec_widenE (hA : IdealFor A .cvtF32F16) (hD : DeclineCore A .cvtF32F16) {t : TState}
    {d r : Nat} {v : Value} (h : t.regs r = some v) :
    execLocalA A L g t (.cvt (widenC d (.reg r))) =
      (widenE v).map fun w => PTX.next (setReg t d w) := by
  have hf : FloatForm.ofOp (.cvt (widenC d (.reg r))) = some .cvtF32F16 := by
    simp [FloatForm.ofOp, CvtInstr.widenF16?, CvtInstr.plain]
  have hI : execIdealFloat L g t (.cvt (widenC d (.reg r))) =
      bindRead (readEReal .f16 v) fun x =>
        some (pure (PTX.next (setReg t d (erealValue .f32 x)))) := by
    simp [execIdealFloat, CvtInstr.widenF16?, CvtInstr.packF16?, CvtInstr.plain,
      readERealOpnd_reg (fmt := .f16) h]
  unfold widenE
  rcases hx : readEReal .f16 v with _ | (e | x)
  · rw [hD L g t _ hf (by rw [hI, hx]; rfl), execLocal_widen_core h]
  · rw [hA L g t _ hf _ (by rw [hI, hx]; rfl)]; rfl
  · rw [hA L g t _ hf _ (by rw [hI, hx]; rfl)]; rfl

/-! ### Moves -/

/-- No assumption of `A` has a local rule for a move: the Core rule applies. -/
def CoreMoves (A : List Assumption) : Prop :=
  ∀ (m : MoveInstr) (L : Launch) (g : Nat) (t : TState), ∀ a ∈ A, a.localRule L g t (.move m) = none

/-- The outcome of `mov.b32 d, a` on the value of `a`. -/
def movE (v : Value) : Exec Value := if v.bytes = 4 then .ok v else .error .typeMismatch

/-- The outcome of `mov.b64 d, {a, b}` on the values of `a` and `b`. -/
def packE (va vb : Value) : Exec Value :=
  if va.bytes = 4 ∧ vb.bytes = 4 then .ok (joinValue va vb) else .error .typeMismatch

/-- The outcome of `mov.b<w> {lo, hi}, a` on the value of `a`: its two halves. -/
def unpackE (w : Nat) (v : Value) : Exec (Value × Value) :=
  if v.bytes = w / 8 ∧ (splitValue w v).1.bytes = w / 16 ∧ (splitValue w v).2.bytes = w / 16
  then .ok (splitValue w v) else .error .typeMismatch

theorem exec_movE (hM : CoreMoves A) (hS : NoSegments A) {t : TState} {d a : Nat} {v : Value}
    (h : t.regs a = some v) :
    execLocalA A L g t (.move ⟨.scalar, .int .b 32, [some d], [.reg a]⟩) =
      (movE v).map fun x => PTX.next (setReg t d x) := by
  rw [((hS.segFreePc (pc := t.pc)).at rfl).exec, execLocalRule_of_none (hM _ L g t)]
  by_cases h4 : v.bytes = 4 <;>
    simp [execLocal, Op.rule, MoveInstr.rule, execMove, DType.width, readValue, readReg, h, h4,
      movE, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw,
      Except.map]

theorem exec_packE (hM : CoreMoves A) (hS : NoSegments A) {t : TState} {d a b : Nat}
    {va vb : Value} (ha : t.regs a = some va) (hb : t.regs b = some vb) :
    execLocalA A L g t (.move ⟨.pack, .int .b 64, [some d], [.reg a, .reg b]⟩) =
      (packE va vb).map fun x => PTX.next (setReg t d x) := by
  rw [((hS.segFreePc (pc := t.pc)).at rfl).exec, execLocalRule_of_none (hM _ L g t)]
  by_cases h4 : va.bytes = 4 ∧ vb.bytes = 4 <;>
    simp [execLocal, Op.rule, MoveInstr.rule, execMove, DType.width, readValue, readReg, ha, hb,
      h4, packE, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw,
      Except.map]

theorem exec_unpackE (hM : CoreMoves A) (hS : NoSegments A) {t : TState} {w lo hi a : Nat}
    {v : Value} (hw : w = 32 ∨ w = 64) (h : t.regs a = some v) :
    execLocalA A L g t (.move ⟨.unpack, .int .b w, [some lo, some hi], [.reg a]⟩) =
      (unpackE w v).map fun x => PTX.next (setReg (setReg t lo x.1) hi x.2) := by
  rw [((hS.segFreePc (pc := t.pc)).at rfl).exec, execLocalRule_of_none (hM _ L g t)]
  rcases hw with rfl | rfl
  · by_cases h1 : v.bytes = 4 <;>
    by_cases h2 : (splitValue 32 v).1.bytes = 2 ∧ (splitValue 32 v).2.bytes = 2 <;>
    simp [execLocal, Op.rule, MoveInstr.rule, execMove, DType.width, readValue, readReg, h,
      unpackE, h1, h2, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw,
      Except.map]
  · by_cases h1 : v.bytes = 8 <;>
    by_cases h2 : (splitValue 64 v).1.bytes = 4 ∧ (splitValue 64 v).2.bytes = 4 <;>
    simp [execLocal, Op.rule, MoveInstr.rule, execMove, DType.width, readValue, readReg, h,
      unpackE, h1, h2, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw,
      Except.map]

theorem movE_ok {v : Value} (h : v.bytes = 4) : (movE v).toBool = true := by
  simp [movE, h, Except.toBool]

theorem movE_eq {v x : Value} (h : movE v = .ok x) : x = v := by
  unfold movE at h
  split_ifs at h
  cases h; rfl

theorem packE_ok {va vb : Value} (ha : va.bytes = 4) (hb : vb.bytes = 4) :
    (packE va vb).toBool = true := by
  simp [packE, ha, hb, Except.toBool]

theorem packE_eq {va vb x : Value} (h : packE va vb = .ok x) : x = joinValue va vb := by
  unfold packE at h
  split_ifs at h
  cases h; rfl

theorem unpackE_eq {w : Nat} {v : Value} {x : Value × Value} (h : unpackE w v = .ok x) :
    x = splitValue w v := by
  unfold unpackE at h
  split_ifs at h
  cases h; rfl

/-- A pair of four-byte values unpacks into its halves. -/
theorem unpackE_pair {a b : Value} (ha : a.bytes = 4) (hb : b.bytes = 4) :
    unpackE 64 (.pair a b) = .ok (a, b) := by
  simp [unpackE, splitValue, Value.bytes, ha, hb]

/-! ### One instruction as a piece -/

/-- **One instruction that writes `d` with the outcome `E`, as a piece**: between facts by one
table `v`, under the condition that `E` does not fault; where it faults the thread is dead. The
table gives `d` the outcome's value where `d` is live after it. -/
theorem SegD.one {pc d : Nat} {op : Op} {liveS liveT : List Nat} {v : Nat → Value}
    {E : Exec Value} (hc : K.code[pc]? = some ⟨none, op⟩) (hl : op.isLocal = true)
    (hex : ∀ t, At t pc (factsFrom liveS v) →
      execLocalA A L g t op = E.map fun x => PTX.next (setReg t d x))
    (hd : ∀ x, E = .ok x → d ∈ liveT → v d = x)
    (hcov : ∀ r ∈ liveT, r = d ∨ (r ≠ d ∧ r ∈ liveS)) :
    SegD K A L g 1 pc (factsFrom liveS v) (pc + 1) (factsFrom liveT v) (E.toBool = true) := by
  intro t ht
  have he := hex t ht
  refine ⟨fun hok => ?_, fun hno => ?_⟩
  · rcases hE : E with e | x
    · rw [hE] at hok; cases hok
    rw [hE] at he
    refine ⟨_, run_local hc hl ht he, by simp [PTX.next, setReg, ht.1], ht.2.1, ht.2.2.1,
      ht.2.2.2.1, holds_of_pointwise fun r hr => ?_⟩
    rcases hcov r hr with rfl | ⟨hne, hrS⟩
    · simp [PTX.next, setReg, hd x hE hr]
    · simp only [PTX.next, setReg, Function.update_of_ne hne]
      exact holds_mem ht.2.2.2.2 (mem_factsFrom hrS)
  · rcases hE : E with e | x
    · rw [hE] at he
      exact dead_of_error (hc.symm ▸ by rw [ht.1]) hl ht.2.2.2.1 he
    · rw [hE] at hno; exact absurd rfl hno

/-- **One instruction that writes `lo` and `hi` with the outcome `E`, as a piece.** -/
theorem SegD.two {pc lo hi : Nat} {op : Op} {liveS liveT : List Nat} {v : Nat → Value}
    {E : Exec (Value × Value)} (hc : K.code[pc]? = some ⟨none, op⟩) (hl : op.isLocal = true)
    (hex : ∀ t, At t pc (factsFrom liveS v) →
      execLocalA A L g t op = E.map fun x => PTX.next (setReg (setReg t lo x.1) hi x.2))
    (hne : lo ≠ hi)
    (hd : ∀ x, E = .ok x → (lo ∈ liveT → v lo = x.1) ∧ (hi ∈ liveT → v hi = x.2))
    (hcov : ∀ r ∈ liveT, r = lo ∨ r = hi ∨ (r ≠ lo ∧ r ≠ hi ∧ r ∈ liveS)) :
    SegD K A L g 1 pc (factsFrom liveS v) (pc + 1) (factsFrom liveT v) (E.toBool = true) := by
  intro t ht
  have he := hex t ht
  refine ⟨fun hok => ?_, fun hno => ?_⟩
  · rcases hE : E with e | x
    · rw [hE] at hok; cases hok
    rw [hE] at he
    refine ⟨_, run_local hc hl ht he, by simp [PTX.next, setReg, ht.1], ht.2.1, ht.2.2.1,
      ht.2.2.2.1, holds_of_pointwise fun r hr => ?_⟩
    rcases hcov r hr with rfl | rfl | ⟨h1, h2, hrS⟩
    · simp [PTX.next, setReg, Function.update_of_ne hne, (hd x hE).1 hr]
    · simp [PTX.next, setReg, (hd x hE).2 hr]
    · simp only [PTX.next, setReg, Function.update_of_ne h1, Function.update_of_ne h2]
      exact holds_mem ht.2.2.2.2 (mem_factsFrom hrS)
  · rcases hE : E with e | x
    · rw [hE] at he
      exact dead_of_error (hc.symm ▸ by rw [ht.1]) hl ht.2.2.2.1 he
    · rw [hE] at hno; exact absurd rfl hno

/-- A piece without condition, then a piece. -/
theorem SegD.seg_comp {m n s p b : Nat} {F G H : List (Nat × Value)} {C : Prop}
    (h1 : Seg K A L g m s F p G) (h2 : SegD K A L g n p G b H C) :
    SegD K A L g (m + n) s F b H C :=
  (SegD.comp (SegD.of_seg h1) h2).iff ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩

/-- A piece, then a piece without condition. -/
theorem SegD.comp_seg {m n s p b : Nat} {F G H : List (Nat × Value)} {C : Prop}
    (h1 : SegD K A L g m s F p G C) (h2 : Seg K A L g n p G b H) :
    SegD K A L g (m + n) s F b H C :=
  (SegD.comp h1 (SegD.of_seg h2)).iff ⟨fun h => h.1, fun h => ⟨h, trivial⟩⟩

/-! ### Widths -/

theorem toValue_f32_bytes (x : FVal) : (x.toValue .f32).bytes = 4 := by
  rcases x with neg | q | neg | p
  · cases neg <;> rfl
  · rfl
  · rfl
  · cases p <;> rfl

theorem erealValue_f32_bytes (x : EReal) : (erealValue .f32 x).bytes = 4 := by
  unfold erealValue
  split_ifs <;> rfl

theorem erealValue_coe (fmt : FloatFmt) (x : ℝ) : erealValue fmt (x : EReal) = .float fmt x := by
  unfold erealValue
  rw [ite_eq_right (EReal.coe_ne_top x), ite_eq_right (EReal.coe_ne_bot x)]
  rfl

/-- Every value of the outcome has four bytes. -/
def Four (E : Exec Value) : Prop := ∀ v, E = .ok v → v.bytes = 4

/-- Every value of the outcome is a pair of four-byte halves. -/
def Pair4 (E : Exec Value) : Prop :=
  ∀ v, E = .ok v → ∃ a b, v = .pair a b ∧ a.bytes = 4 ∧ b.bytes = 4

theorem okVal_bytes {E : Exec Value} (h : Four E) : (okVal (b32 0) E).bytes = 4 := by
  rcases hE : E with e | v
  · rfl
  · exact h v hE

theorem okVal_pair {E : Exec Value} (h : Pair4 E) :
    ∃ a b, okVal (.pair (b32 0) (b32 0)) E = .pair a b ∧ a.bytes = 4 ∧ b.bytes = 4 := by
  rcases hE : E with e | v
  · exact ⟨_, _, rfl, rfl, rfl⟩
  · exact h v hE

theorem coreFloat_four {f : FloatInstr} (h1 : f.ty = ty1 .f32) (vs : List Value) :
    Four (coreFloat f vs) := by
  intro v hv
  simp only [coreFloat, h1, ty1, show List.range 1 = [0] from rfl, List.mapM_cons,
    List.mapM_nil, bind, Except.bind, pure, Except.pure] at hv
  generalize (List.mapM (m := Exec) _ vs : Exec (List FVal)) = M at hv
  rcases M with e | xs
  · cases hv
  dsimp only at hv
  generalize f.lane xs = o at hv
  rcases o with _ | (_ | v0) <;> simp [throw, throwThe, MonadExceptOf.throw] at hv
  subst hv; exact toValue_f32_bytes _

theorem coreFloat_pair4 {f : FloatInstr} (h2 : f.ty = ⟨.f32, 2⟩) (vs : List Value) :
    Pair4 (coreFloat f vs) := by
  intro v hv
  simp only [coreFloat, h2, show List.range 2 = [0, 1] from rfl, List.mapM_cons,
    List.mapM_nil, bind, Except.bind, pure, Except.pure] at hv
  generalize (List.mapM (m := Exec) _ vs : Exec (List FVal)) = M at hv
  rcases M with e | xs
  · cases hv
  dsimp only at hv
  generalize f.lane xs = o at hv
  rcases o with _ | o
  · simp [throw, throwThe, MonadExceptOf.throw] at hv
  dsimp only at hv
  generalize (List.mapM (m := Exec) _ vs : Exec (List FVal)) = M' at hv
  rcases M' with e | ys
  · cases hv
  dsimp only at hv
  generalize f.lane ys = o' at hv
  rcases o' with _ | o'
  · simp [throw, throwThe, MonadExceptOf.throw] at hv
  rcases o with _ | v0 <;> rcases o' with _ | v1 <;>
    simp [throw, throwThe, MonadExceptOf.throw] at hv
  subst hv; exact ⟨_, _, rfl, toValue_f32_bytes _, toValue_f32_bytes _⟩

theorem exec_bind_ok {α β : Type} {m : Exec α} {k : α → Exec β} {v : β}
    (h : (m >>= k) = .ok v) : ∃ a, m = .ok a ∧ k a = .ok v := by
  rcases m with e | a
  · cases h
  · exact ⟨a, rfl, h⟩

theorem bindRead_ok {α β : Type} {x : Option (Exec α)} {k : α → Option (Exec β)} {v : β}
    (h : bindRead x k = some (.ok v)) : ∃ a, x = some (.ok a) ∧ k a = some (.ok v) := by
  rcases x with _ | (e | a)
  · cases h
  · cases h
  · exact ⟨a, rfl, h⟩

theorem map_pure_ok {α : Type} {o : Option α} {F : α → Value} {v : Value}
    (h : o.map (fun r => (pure (F r) : Exec Value)) = some (.ok v)) : ∃ r, v = F r := by
  rcases o with _ | r
  · cases h
  · simp only [Option.map_some, Option.some.injEq, pure, Except.pure, Except.ok.injEq] at h
    exact ⟨r, h.symm⟩

theorem floatE_fma_four (rnd : FloatRound) (fz : Bool) (vs : List Value) :
    Four (floatE (fmaI rnd fz) vs) := by
  intro v hv
  unfold floatE at hv
  split at hv
  · rename_i r hr
    subst hv
    rcases vs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | _⟩⟩⟩ <;> simp [idealVal, throw, throwThe,
      MonadExceptOf.throw] at hr
    obtain ⟨x, -, hr⟩ := bindRead_ok hr
    obtain ⟨y, -, hr⟩ := bindRead_ok hr
    obtain ⟨z, -, hr⟩ := bindRead_ok hr
    obtain ⟨p, -, hr⟩ := Option.bind_eq_some_iff.mp hr
    obtain ⟨r, rfl⟩ := map_pure_ok hr
    exact erealValue_f32_bytes r
  · exact coreFloat_four rfl vs v hv

theorem floatE_add_four (fz : Bool) (vs : List Value) : Four (floatE (addI fz) vs) := by
  intro v hv
  unfold floatE at hv
  split at hv
  · rename_i r hr
    subst hv
    rcases vs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> simp [idealVal, throw, throwThe,
      MonadExceptOf.throw] at hr
    obtain ⟨x, -, hr⟩ := bindRead_ok hr
    obtain ⟨y, -, hr⟩ := bindRead_ok hr
    obtain ⟨r, rfl⟩ := map_pure_ok hr
    exact erealValue_f32_bytes r
  · exact coreFloat_four rfl vs v hv

theorem floatE_mul2_pair4 (rnd : FloatRound) (fz : Bool) (vs : List Value) :
    Pair4 (floatE (mul2I rnd fz) vs) := by
  intro v hv
  unfold floatE at hv
  split at hv
  · rename_i r hr
    subst hv
    rcases vs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> simp [idealVal, throw, throwThe,
      MonadExceptOf.throw] at hr
    obtain ⟨⟨x0, x1⟩, -, hr⟩ := bindRead_ok hr
    obtain ⟨⟨y0, y1⟩, -, hr⟩ := bindRead_ok hr
    simp only at hr
    split at hr
    · simp only [Option.some.injEq, pure, Except.pure, Except.ok.injEq] at hr
      exact ⟨_, _, hr.symm, erealValue_f32_bytes _, erealValue_f32_bytes _⟩
    · cases hr
  · exact coreFloat_pair4 rfl vs v hv

theorem approxE_four {f : FloatInstr} (h1 : f.ty = ty1 .f32) (vs : List Value) :
    Four (approxE f vs) := by
  intro v hv
  unfold approxE at hv
  split at hv
  · rename_i r hr
    subst hv
    unfold approxVal at hr
    split at hr
    · obtain ⟨x, -, hr⟩ := bindRead_ok hr
      obtain ⟨y, -, hr⟩ := bindRead_ok hr
      split_ifs at hr
      · cases hr
      · cases hr; rfl
    · obtain ⟨x, -, hr⟩ := bindRead_ok hr
      split_ifs at hr
      · cases hr
      · cases hr; rfl
    · cases hr
  · exact coreFloat_four h1 vs v hv

theorem widenE_four (h : Value) : Four (widenE h) := by
  intro v hv
  unfold widenE at hv
  split at hv
  · cases hv
  · cases hv; exact erealValue_f32_bytes _
  · unfold coreWiden at hv
    obtain ⟨x, -, hv⟩ := exec_bind_ok hv
    obtain ⟨y, -, hv⟩ := exec_bind_ok hv
    cases hv; exact toValue_f32_bytes _

/-! ### Finite operands -/

theorem addEReal_coe (x y : ℝ) : addEReal (x : EReal) (y : EReal) = some ((x + y : ℝ) : EReal) := by
  rw [addEReal, ite_eq_right (by simp)]
  push_cast; ring_nf

theorem mulEReal_coe (x y : ℝ) : mulEReal (x : EReal) (y : EReal) = some ((x * y : ℝ) : EReal) := by
  rw [mulEReal, ite_eq_right (by simp)]
  push_cast; ring_nf

theorem pairRead_of {v : Value} {x0 x1 : ℝ} (h0 : valFloat .f32 (splitValue 64 v).1 = .ok x0)
    (h1 : valFloat .f32 (splitValue 64 v).2 = .ok x1) :
    pairRead v = some (.ok ((x0 : EReal), (x1 : EReal))) := by
  simp only [pairRead, readEReal_of_valFloat h0, readEReal_of_valFloat h1, pure, Except.pure]

theorem finiteVal_of {v : Value} {x : ℝ} (h : valFloat .f32 v = .ok x) :
    finiteVal v = some (.ok x) := by
  simp [finiteVal, readEReal_of_valFloat h, bindRead, pure, Except.pure]

/-- **A fused multiply-add of numbers** is the number of the exact result. -/
theorem floatE_fma_fin {rnd : FloatRound} {fz : Bool} {va vb vc : Value} {x y z : ℝ}
    (hx : valFloat .f32 va = .ok x) (hy : valFloat .f32 vb = .ok y)
    (hz : valFloat .f32 vc = .ok z) :
    floatE (fmaI rnd fz) [va, vb, vc] = .ok (.float .f32 (x * y + z)) := by
  simp only [floatE, idealVal, readEReal_of_valFloat hx, readEReal_of_valFloat hy,
    readEReal_of_valFloat hz, bindRead, mulEReal_coe, Option.bind_some, addEReal_coe,
    Option.map_some, erealValue_coe, pure, Except.pure]

/-- **An addition of numbers** is the number of the exact sum. -/
theorem floatE_add_fin {fz : Bool} {va vb : Value} {x y : ℝ} (hx : valFloat .f32 va = .ok x)
    (hy : valFloat .f32 vb = .ok y) : floatE (addI fz) [va, vb] = .ok (.float .f32 (x + y)) := by
  simp only [floatE, idealVal, readEReal_of_valFloat hx, readEReal_of_valFloat hy, bindRead,
    addEReal_coe, Option.map_some, erealValue_coe, pure, Except.pure]

/-- **A packed multiplication of numbers** is the pair of the exact products. -/
theorem floatE_mul2_fin {rnd : FloatRound} {fz : Bool} {va vb : Value} {x0 x1 y0 y1 : ℝ}
    (hx0 : valFloat .f32 (splitValue 64 va).1 = .ok x0)
    (hx1 : valFloat .f32 (splitValue 64 va).2 = .ok x1)
    (hy0 : valFloat .f32 (splitValue 64 vb).1 = .ok y0)
    (hy1 : valFloat .f32 (splitValue 64 vb).2 = .ok y1) :
    floatE (mul2I rnd fz) [va, vb] =
      .ok (.pair (.float .f32 (x0 * y0)) (.float .f32 (x1 * y1))) := by
  simp only [floatE, idealVal, pairRead_of hx0 hx1, pairRead_of hy0 hy1, bindRead, mulEReal_coe,
    erealValue_coe, pure, Except.pure]

/-- **A division of numbers by a nonzero number** is the exact quotient. -/
theorem approxE_div_fin {fz : Bool} {va vb : Value} {x y : ℝ} (hx : valFloat .f32 va = .ok x)
    (hy : valFloat .f32 vb = .ok y) (hy0 : y ≠ 0) :
    approxE (divI fz) [va, vb] = .ok (.float .f32 (x / y)) := by
  simp [approxE, approxVal, finiteVal_of hx, finiteVal_of hy, bindRead, hy0, pure, Except.pure]

/-- **The inverse square root of a positive number** is the exact one. -/
theorem approxE_rsqrt_fin {fz : Bool} {va : Value} {x : ℝ} (hx : valFloat .f32 va = .ok x)
    (hpos : 0 < x) : approxE (rsqrtI fz) [va] = .ok (.float .f32 (1 / Real.sqrt x)) := by
  simp [approxE, approxVal, finiteVal_of hx, bindRead, not_le.mpr hpos, pure, Except.pure]

/-- **A half-precision number widens to itself.** -/
theorem widenE_fin {h : Value} {x : ℝ} (hx : valFloat .f16 h = .ok x) :
    widenE h = .ok (.float .f32 x) := by
  simp only [widenE, readEReal_of_valFloat hx, erealValue_coe]

end
end PTX.Flow
