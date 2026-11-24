-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.FloatDat

@[expose] public section

/-! # Outcomes of the instructions of a software power-of-two template

A proof tool, in the form of `ArithCore` and `FloatOutcome`. A software `exp2` template (a clamp
`max.ftz.f32` with a constant, `add.rm.ftz.f32` and `sub.rn.ftz.f32` with a constant, a second
`sub.rn.ftz.f32`, `fma.rn.ftz.f32` with constants, `mov.b32`, `shl.b32` and `add.s32`) runs one
instruction at a time where no segment assumption takes it. Under an ideal-real assumption that
leaves its declines to the Core rule, each floating instruction has one outcome on the values of
its sources: the ideal value where the ideal rule applies, the Core rule's where it declines
(`maxFE`, `floatE addRmI`, `subRnE`, `floatE (fmaI .rn true)`). The local steps at a state write
the outcome's value or fault (`exec_maxFE`, `exec_floatE_addRm`, `exec_subRnE`,
`exec_floatE_fma_at`). The integer instructions read their sources as bits (`readBitsOf`): a value
without a bit pattern faults (`execInt_shl_imm`, `execInt_add_regs`).

The moves (`exec_movE_at`, `exec_packE_at`, `exec_unpackE_at`) and the packed sum without a
rounding modifier (`add2NE`, `exec_add2NE`) are stated at a state where no assumption takes a
segment (`SegFreeAt`), for kernels whose segment assumptions start at some pcs only. -/

namespace PTX.Flow
open PTX PTX.Proof PTX.Assumption

noncomputable section

variable {A : List Assumption} {L : Launch} {g : Nat}

/-! ### `fma` at a state -/

theorem exec_floatE_fma_at {t : TState} (hA : IdealAt A (.fma .f32) L g t)
    (hD : DeclineAt A (.fma .f32) L g t) {rnd : FloatRound} {fz : Bool} {d : Nat}
    {a b c : Opnd} {va vb vc : Value}
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
  | none => rw [hD _ hf (by rw [hI, hv]; rfl), execLocal_fma_core ha hb hc]
  | some r => rw [hA _ hf _ (by rw [hI, hv]; rfl)]

/-! ### `max.ftz.f32` -/

/-- `max.ftz.f32`. -/
abbrev maxFI : FloatInstr := { op := .max, ty := ty1 .f32, ftz := true, dsts := [], srcs := [] }

/-- **The outcome of `max.ftz.f32` of two sources**: the ideal outcome, or the Core rule's where
the ideal rule declines. -/
@[irreducible] def maxFE (va vb : Value) : Exec Value :=
  match idealMax [va, vb] with
  | some r => r
  | none => coreFloat maxFI [va, vb]

theorem execLocal_maxF_core {t : TState} {d : Nat} {a b : Opnd} {va vb : Value}
    (ha : OpndIs L g t a va) (hb : OpndIs L g t b vb) :
    execLocal L g t (.float { maxFI with dsts := [some d], srcs := [a, b] }) =
      (coreFloat maxFI [va, vb]).map fun v => PTX.next (setReg t d v) := by
  have hl : FloatInstr.lane { maxFI with dsts := [some d], srcs := [a, b] } =
      FloatInstr.lane maxFI := rfl
  obtain ⟨ha, -⟩ := ha; obtain ⟨hb, -⟩ := hb
  cases hxa : classify .f32 va with
  | error e => core_float
  | ok xa =>
  cases hxb : classify .f32 vb with
  | error e => core_float
  | ok xb =>
  cases hlane : FloatInstr.lane maxFI [xa, xb] with
  | none => core_float
  | some o => cases o <;> core_float

theorem exec_maxFE {t : TState} (hA : IdealAt A (.max .f32) L g t)
    (hD : DeclineAt A (.max .f32) L g t) {d : Nat} {a b : Opnd} {va vb : Value}
    (ha : OpndIs L g t a va) (hb : OpndIs L g t b vb) :
    execLocalA A L g t (.float { maxFI with dsts := [some d], srcs := [a, b] }) =
      (maxFE va vb).map fun v => PTX.next (setReg t d v) := by
  have hf : FloatForm.ofOp (.float { maxFI with dsts := [some d], srcs := [a, b] }) =
      some (.max .f32) := by simp [FloatForm.ofOp]
  have hI : execIdealFloat L g t (.float { maxFI with dsts := [some d], srcs := [a, b] }) =
      (idealMax [va, vb]).map (Except.map fun v => PTX.next (setReg t d v)) := by
    simp only [execIdealFloat, idealMax, ha.2, hb.2, bindRead_map]
    rcases readEReal .f32 va with _ | (e | x)
    · rfl
    · rfl
    rcases readEReal .f32 vb with _ | (e | y) <;> rfl
  unfold maxFE
  cases hv : idealMax [va, vb] with
  | none => rw [hD _ hf (by rw [hI, hv]; rfl), execLocal_maxF_core ha hb]
  | some r => rw [hA _ hf _ (by rw [hI, hv]; rfl)]

/-- Where the first source reads as no extended real (a NaN), the ideal rule of `max` declines,
so that the step needs no ideal reading at the state. -/
theorem exec_maxFE_nan {t : TState} (hD : DeclineAt A (.max .f32) L g t) {d : Nat}
    {a b : Opnd} {va vb : Value} (hn : readEReal .f32 va = none)
    (ha : OpndIs L g t a va) (hb : OpndIs L g t b vb) :
    execLocalA A L g t (.float { maxFI with dsts := [some d], srcs := [a, b] }) =
      (maxFE va vb).map fun v => PTX.next (setReg t d v) := by
  have hf : FloatForm.ofOp (.float { maxFI with dsts := [some d], srcs := [a, b] }) =
      some (.max .f32) := by simp [FloatForm.ofOp]
  have hv : idealMax [va, vb] = none := by simp [idealMax, hn, bindRead]
  have hI : execIdealFloat L g t (.float { maxFI with dsts := [some d], srcs := [a, b] }) =
      none := by
    simp only [execIdealFloat, ha.2, hn, bindRead]
  unfold maxFE
  rw [hv, hD _ hf hI, execLocal_maxF_core ha hb]

/-! ### `add.rm.ftz.f32` -/

/-- `add.rm.ftz.f32`. -/
abbrev addRmI : FloatInstr :=
  { op := .add, ty := ty1 .f32, rnd := some .rm, ftz := true, dsts := [], srcs := [] }

theorem execLocal_addRm_core {t : TState} {d : Nat} {a b : Opnd} {va vb : Value}
    (ha : OpndIs L g t a va) (hb : OpndIs L g t b vb) :
    execLocal L g t (.float { addRmI with dsts := [some d], srcs := [a, b] }) =
      (coreFloat addRmI [va, vb]).map fun v => PTX.next (setReg t d v) := by
  have hl : FloatInstr.lane { addRmI with dsts := [some d], srcs := [a, b] } =
      FloatInstr.lane addRmI := rfl
  obtain ⟨ha, -⟩ := ha; obtain ⟨hb, -⟩ := hb
  cases hxa : classify .f32 va with
  | error e => core_float
  | ok xa =>
  cases hxb : classify .f32 vb with
  | error e => core_float
  | ok xb =>
  cases hlane : FloatInstr.lane addRmI [xa, xb] with
  | none => core_float
  | some o => cases o <;> core_float

theorem exec_floatE_addRm {t : TState} (hA : IdealAt A (.add .f32) L g t)
    (hD : DeclineAt A (.add .f32) L g t) {d : Nat} {a b : Opnd} {va vb : Value}
    (ha : OpndIs L g t a va) (hb : OpndIs L g t b vb) :
    execLocalA A L g t (.float { addRmI with dsts := [some d], srcs := [a, b] }) =
      (floatE addRmI [va, vb]).map fun v => PTX.next (setReg t d v) := by
  have hf : FloatForm.ofOp (.float { addRmI with dsts := [some d], srcs := [a, b] }) =
      some (.add .f32) := by simp [FloatForm.ofOp]
  have hI : execIdealFloat L g t (.float { addRmI with dsts := [some d], srcs := [a, b] }) =
      (idealVal addRmI [va, vb]).map (Except.map fun v => PTX.next (setReg t d v)) := by
    simp only [execIdealFloat, idealVal, ha.2, hb.2, bindRead_map, Option.map_map,
      Function.comp_def, Except.map, pure, Except.pure]
  unfold floatE
  cases hv : idealVal addRmI [va, vb] with
  | none => rw [hD _ hf (by rw [hI, hv]; rfl), execLocal_addRm_core ha hb]
  | some r => rw [hA _ hf _ (by rw [hI, hv]; rfl)]

/-! ### `sub.rn.ftz.f32` -/

/-- `sub.rn.ftz.f32`. -/
abbrev subRnI : FloatInstr :=
  { op := .sub, ty := ty1 .f32, rnd := some .rn, ftz := true, dsts := [], srcs := [] }

/-- **The outcome of `sub.rn.ftz.f32`**: the ideal outcome, or the Core rule's where it
declines. -/
@[irreducible] def subRnE (va vb : Value) : Exec Value :=
  match idealSub va vb with
  | some r => r
  | none => coreFloat subRnI [va, vb]

theorem execLocal_subRn_core {t : TState} {d : Nat} {a b : Opnd} {va vb : Value}
    (ha : OpndIs L g t a va) (hb : OpndIs L g t b vb) :
    execLocal L g t (.float { subRnI with dsts := [some d], srcs := [a, b] }) =
      (coreFloat subRnI [va, vb]).map fun v => PTX.next (setReg t d v) := by
  have hl : FloatInstr.lane { subRnI with dsts := [some d], srcs := [a, b] } =
      FloatInstr.lane subRnI := rfl
  obtain ⟨ha, -⟩ := ha; obtain ⟨hb, -⟩ := hb
  cases hxa : classify .f32 va with
  | error e => core_float
  | ok xa =>
  cases hxb : classify .f32 vb with
  | error e => core_float
  | ok xb =>
  cases hlane : FloatInstr.lane subRnI [xa, xb] with
  | none => core_float
  | some o => cases o <;> core_float

theorem exec_subRnE {t : TState} (hI : IdealAt A (.subRn .f32) L g t)
    (hD : DeclineAt A (.subRn .f32) L g t) {d : Nat} {a b : Opnd} {va vb : Value}
    (ha : OpndIs L g t a va) (hb : OpndIs L g t b vb) :
    execLocalA A L g t (.float { subRnI with dsts := [some d], srcs := [a, b] }) =
      (subRnE va vb).map fun v => PTX.next (setReg t d v) := by
  have hf : FloatForm.ofOp (.float { subRnI with dsts := [some d], srcs := [a, b] }) =
      some (.subRn .f32) := by simp [FloatForm.ofOp]
  have hi : execIdealFloat L g t (.float { subRnI with dsts := [some d], srcs := [a, b] }) =
      (idealSub va vb).map (Except.map fun v => PTX.next (setReg t d v)) := by
    simp only [execIdealFloat, idealSub, ha.2, hb.2, bindRead_map, Option.map_map,
      Function.comp_def, Except.map, pure, Except.pure]
  unfold subRnE
  cases hv : idealSub va vb with
  | none => rw [hD _ hf (by rw [hi, hv]; rfl), execLocal_subRn_core ha hb]
  | some r => rw [hI _ hf _ (by rw [hi, hv]; rfl)]

/-! ### `add.f32x2` without a rounding modifier -/

/-- `add.f32x2` (no rounding modifier: round to nearest by default). -/
abbrev add2NI : FloatInstr := { op := .add, ty := ⟨.f32, 2⟩, dsts := [], srcs := [] }

/-- **The outcome of `add.f32x2`**: the ideal outcome, or the Core rule's where it declines. -/
@[irreducible] def add2NE (va vb : Value) : Exec Value :=
  match idealAdd2 va vb with
  | some r => r
  | none => coreFloat add2NI [va, vb]

theorem execLocal_add2N_core {t : TState} {d a b : Nat} {va vb : Value}
    (ha : t.regs a = some va) (hb : t.regs b = some vb) :
    execLocal L g t (.float { add2NI with dsts := [some d], srcs := [.reg a, .reg b] }) =
      (coreFloat add2NI [va, vb]).map fun v => PTX.next (setReg t d v) := by
  have hl : FloatInstr.lane { add2NI with dsts := [some d], srcs := [.reg a, .reg b] } =
      FloatInstr.lane add2NI := rfl
  have h2 : List.range 2 = [0, 1] := rfl
  cases hxa : classify .f32 (splitValue 64 va).1 with
  | error e => core_float_reg
  | ok xa =>
  cases hxb : classify .f32 (splitValue 64 vb).1 with
  | error e => core_float_reg
  | ok xb =>
  cases hl0 : FloatInstr.lane add2NI [xa, xb] with
  | none => core_float_reg
  | some o =>
  cases hya : classify .f32 (splitValue 64 va).2 with
  | error e => core_float_reg
  | ok ya =>
  cases hyb : classify .f32 (splitValue 64 vb).2 with
  | error e => core_float_reg
  | ok yb =>
  cases hl1 : FloatInstr.lane add2NI [ya, yb] with
  | none => core_float_reg
  | some o' => cases o <;> cases o' <;> core_float_reg

theorem exec_add2NE {t : TState} (hI : IdealAt A .addRnF32x2 L g t)
    (hD : DeclineAt A .addRnF32x2 L g t) {d a b : Nat} {va vb : Value}
    (ha : t.regs a = some va) (hb : t.regs b = some vb) :
    execLocalA A L g t (.float { add2NI with dsts := [some d], srcs := [.reg a, .reg b] }) =
      (add2NE va vb).map fun v => PTX.next (setReg t d v) := by
  have hf : FloatForm.ofOp (.float { add2NI with dsts := [some d], srcs := [.reg a, .reg b] }) =
      some .addRnF32x2 := by simp [FloatForm.ofOp]
  have hi : execIdealFloat L g t
      (.float { add2NI with dsts := [some d], srcs := [.reg a, .reg b] }) =
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
  unfold add2NE
  cases hv : idealAdd2 va vb with
  | none => rw [hD _ hf (by rw [hi, hv]; rfl), execLocal_add2N_core ha hb]
  | some r => rw [hI _ hf _ (by rw [hi, hv]; rfl)]

/-! ### Moves at a state without a segment -/

theorem exec_movE_at (hM : CoreMoves A) {t : TState} (hS : SegFreeAt A L g t) {d a : Nat}
    {v : Value} (h : t.regs a = some v) :
    execLocalA A L g t (.move ⟨.scalar, .int .b 32, [some d], [.reg a]⟩) =
      (movE v).map fun x => PTX.next (setReg t d x) := by
  rw [hS.exec, execLocalRule_of_none (hM _ L g t)]
  by_cases h4 : v.bytes = 4 <;>
    simp [execLocal, Op.rule, MoveInstr.rule, execMove, DType.width, readValue, readReg, h, h4,
      movE, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw,
      Except.map]

theorem exec_packE_at (hM : CoreMoves A) {t : TState} (hS : SegFreeAt A L g t) {d a b : Nat}
    {va vb : Value} (ha : t.regs a = some va) (hb : t.regs b = some vb) :
    execLocalA A L g t (.move ⟨.pack, .int .b 64, [some d], [.reg a, .reg b]⟩) =
      (packE va vb).map fun x => PTX.next (setReg t d x) := by
  rw [hS.exec, execLocalRule_of_none (hM _ L g t)]
  by_cases h4 : va.bytes = 4 ∧ vb.bytes = 4 <;>
    simp [execLocal, Op.rule, MoveInstr.rule, execMove, DType.width, readValue, readReg, ha, hb,
      h4, packE, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw,
      Except.map]

theorem exec_unpackE_at (hM : CoreMoves A) {t : TState} (hS : SegFreeAt A L g t)
    {lo hi a : Nat} {v : Value} (h : t.regs a = some v) :
    execLocalA A L g t (.move ⟨.unpack, .int .b 64, [some lo, some hi], [.reg a]⟩) =
      (unpackE 64 v).map fun x => PTX.next (setReg (setReg t lo x.1) hi x.2) := by
  rw [hS.exec, execLocalRule_of_none (hM _ L g t)]
  by_cases h1 : v.bytes = 8 <;>
  by_cases h2 : (splitValue 64 v).1.bytes = 4 ∧ (splitValue 64 v).2.bytes = 4 <;>
  simp [execLocal, Op.rule, MoveInstr.rule, execMove, DType.width, readValue, readReg, h,
    unpackE, h1, h2, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw,
    Except.map]

/-! ### Integer instructions on any values -/

/-- The bits a register holding `v` reads as at width `w` (`readBits` of a register). -/
def readBitsOf (w : Nat) (v : Value) : Exec (BitVec 64) :=
  match v with
  | .bits _ x => pure (truncBits w x)
  | .ptr .. | .policy => throw .noRule
  | v => match v.bitPattern with
    | some n => pure (truncBits w (BitVec.ofNat 64 n))
    | none => throw .typeMismatch

theorem readBits_reg_bitsOf {t : TState} {w r : Nat} {v : Value} (h : t.regs r = some v) :
    readBits L g t w (.reg r) = readBitsOf w v := by
  cases v <;> simp [readBits, readReg, h, readBitsOf, bind, Except.bind, pure, Except.pure] <;> rfl

/-- **The outcome of `shl.b32 d, a, n`** on the value of `a`. -/
def shlE (v : Value) (n : Int) : Exec Value := do
  let x ← readBitsOf 32 v
  let s := truncBits 32 (BitVec.ofInt 64 n)
  pure (.bits 32 (if s.toNat ≥ 32 then 0 else truncBits 32 (x <<< s.toNat)))

theorem execInt_shl_imm {t : TState} {ty : DType} {d a : Nat} {n : Int} {v : Value}
    (hw : ty.width = 32) (h : t.regs a = some v) :
    execInt L g t ⟨.shl, ty, false, [some d], [.reg a, .imm n]⟩ =
      (shlE v n).map fun x => PTX.next (setReg t d x) := by
  simp only [execInt, hw, readBits_reg_bitsOf h, shlE]
  rcases readBitsOf 32 v with e | x
  · rfl
  · simp [readBits, bind, Except.bind, pure, Except.pure, Except.map]

/-- **The outcome of `add.s32 d, a, b`** on the values of `a` and `b` (neither a pointer). -/
def addIE (va vb : Value) : Exec Value := do
  let x ← readBitsOf 32 va
  let y ← readBitsOf 32 vb
  pure (.bits 32 (truncBits 32 (x + y)))

theorem execInt_add_bits {t : TState} {d a b : Nat} {va : Value} {y : BitVec 64}
    (ha : t.regs a = some va) (hb : t.regs b = some (.bits 32 y))
    (hpa : ∀ w gn tg off, va ≠ .ptr w gn tg off) :
    execInt L g t ⟨.add, .int .s 32, false, [some d], [.reg a, .reg b]⟩ =
      (addIE va (.bits 32 y)).map fun x => PTX.next (setReg t d x) := by
  cases va with
  | ptr w gn tg off => exact absurd rfl (hpa w gn tg off)
  | _ =>
    simp only [execInt, readValue, readReg, ha, hb, DType.width, readBits, addIE, readBitsOf, bind,
      Except.bind, pure, Except.pure, Except.map]
    try rfl
    try (generalize Value.bitPattern _ = o; rcases o with _ | n <;> rfl)

/-- An `.f32` datum is no pointer. -/
theorem F32Dat.not_ptr {v : Value} (h : F32Dat v) : ∀ w gn tg off, v ≠ .ptr w gn tg off := by
  rintro w gn tg off rfl
  obtain ⟨c, hc⟩ := h
  simp [classify, Value.bitPattern, throw, throwThe, MonadExceptOf.throw] at hc

/-! ### The data of the outcomes -/

/-- Every value of a one-lane `.f32` `floatE` is an `.f32` datum. -/
theorem floatE_dat {f : FloatInstr} (h1 : f.ty = ty1 .f32) {vs : List Value} {v : Value}
    (hv : floatE f vs = .ok v) : F32Dat v := by
  unfold floatE at hv
  split at hv
  · rename_i r hr
    subst hv
    unfold idealVal at hr
    rw [h1] at hr
    split at hr
    · obtain ⟨x, -, hr⟩ := bindRead_ok hr
      obtain ⟨y, -, hr⟩ := bindRead_ok hr
      exact erealValue_map_dat hr
    · obtain ⟨x, -, hr⟩ := bindRead_ok hr
      obtain ⟨y, -, hr⟩ := bindRead_ok hr
      obtain ⟨z, -, hr⟩ := bindRead_ok hr
      obtain ⟨r, rfl⟩ := map_pure_ok hr
      exact f32Dat_erealValue r
    · simp [ty1] at *
    · simp [throw, throwThe, MonadExceptOf.throw] at hr
  · exact coreFloat_dat h1 hv

theorem subRnE_dat {va vb v : Value} (hv : subRnE va vb = .ok v) : F32Dat v := by
  unfold subRnE at hv
  split at hv
  · rename_i r hr
    subst hv
    obtain ⟨x, -, hr⟩ := bindRead_ok hr
    obtain ⟨y, -, hr⟩ := bindRead_ok hr
    exact erealValue_map_dat hr
  · exact coreFloat_dat rfl hv

theorem maxFE_dat {va vb v : Value} (hv : maxFE va vb = .ok v) : F32Dat v := by
  unfold maxFE at hv
  split at hv
  · rename_i r hr
    subst hv
    unfold idealMax at hr
    obtain ⟨x, -, hr⟩ := bindRead_ok hr
    obtain ⟨y, -, hr⟩ := bindRead_ok hr
    simp only [Option.some.injEq, pure, Except.pure, Except.ok.injEq] at hr
    rw [← hr]
    exact f32Dat_erealValue _
  · exact coreFloat_dat rfl hv

end
end PTX.Flow
