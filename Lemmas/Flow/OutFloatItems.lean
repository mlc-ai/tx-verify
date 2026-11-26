-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.OutCore
public import Lemmas.Flow.EmuStep
public import Lemmas.Flow.RcpCore

@[expose] public section

/-! # Run items for floating forms with literal operands, and two Core forms

A proof tool for `Tools/out_gen.py`. An `XItem.fn` item is a local instruction with one
destination whose value is `f` of its source registers' values. For a floating instruction whose
operands are registers or `0f` constants (`fPlain`), `fOp f d os` is the instruction and
`fF E os` its outcome function: `E` on the operands' values, a constant's value being its bits
(`fOpnd`). `XItem.float_rule` turns a state-wise step lemma into the item's rule. The forms:

* `max.ftz.f32` (`maxFL`, by `exec_maxFE`), `add.f32x2` without rounding modifier (`add2NL`, by
  `exec_add2NE`), `mul{.ftz}.f32` with a constant (`mulL`, by `exec_mulE`), `fma.rnd{.ftz}.f32`
  (`floatE (fmaI rnd fz)`, by `exec_floatE_fma_at`), under an ideal reading at the state;
* `mul.f32x2` without rounding modifier (`mul2NL`) and `neg{.ftz}.f32` (`negL`), whose Core steps
  and ideal outcomes are stated here (`exec_mul2NE`, `exec_negE`);
* `div.approx{.ftz}.f32` (`approxE (divI fz)`) under an approximate-as-exact reading at the state
  (`exec_divE_at`, the state-wise form of `exec_approxE_div`).

Two Core forms with no `coreW` arm are `fn` items with Core's value (`XItem.local_of`, the
analogue of `XItem.core_of` for an outcome function of its own): `bfe` with literal position and
length (`bfeW`, `XItem.core_bfe`) and the unpack `mov.b<w> {lo, _}` / `{_, hi}` whose other half is
the sink (`sinkW`, `XItem.core_sink`). -/

namespace PTX.Flow
open PTX PTX.Proof PTX.Assumption

noncomputable section

variable {A : List Assumption} {L : Launch} {g : Nat}

/-! ### Floating items with literal operands -/

/-- A floating operand of a generated item: a register or a `0f` constant. -/
def fPlain : Opnd → Bool
  | .reg _ | .f32imm _ => true
  | _ => false

/-- The value of a floating operand: the register's, or the constant's bits. -/
def fOpnd (W : Nat → Value) : Opnd → Value
  | .reg r => W r
  | .f32imm b => .bits 32 (BitVec.ofNat 64 b)
  | _ => .bits 32 0

/-- The floating instruction `f` with destination `d` and operands `os`. -/
def fOp (f : FloatInstr) (d : Nat) (os : List Opnd) : Op :=
  .float { f with dsts := [some d], srcs := os }

/-- The outcome function of a floating item: `E` on the operands' values, a register's taken
from the source values `vs` in the order of `regsOf os`. -/
def fF (E : List Value → Exec Value) (os : List Opnd) (vs : List Value) : Exec Value :=
  E (os.map (fOpnd (lk (regsOf os) vs)))

theorem opndIs_of {t : TState} {W : Nat → Value} {o : Opnd} (hp : fPlain o = true)
    (hW : ∀ r ∈ regOf o, t.regs r = some (W r)) : OpndIs L g t o (fOpnd W o) := by
  cases o <;> simp [fPlain] at hp
  · exact OpndIs.reg (hW _ (by simp [regOf]))
  · exact OpndIs.imm

theorem fF_map {E : List Value → Exec Value} {os : List Opnd} {W : Nat → Value} :
    fF E os ((regsOf os).map W) = E (os.map (fOpnd W)) := by
  unfold fF
  congr 1
  apply List.map_congr_left
  intro o ho
  cases o <;> simp only [fOpnd]
  exact lk_map (List.mem_flatMap.mpr ⟨_, ho, by simp [regOf]⟩)

/-- **A floating item's rule** from its step on operands that hold their values. -/
theorem XItem.float_rule {t : TState} {E : List Value → Exec Value} {f : FloatInstr} {d : Nat}
    {os : List Opnd} (hp : os.all fPlain = true)
    (hx : ∀ W : Nat → Value, (∀ o ∈ os, OpndIs L g t o (fOpnd W o)) →
      execLocalA A L g t (fOp f d os) =
        (E (os.map (fOpnd W))).map fun v => PTX.next (setReg t d v)) :
    (XItem.fn (fOp f d os) d (regsOf os) (fF E os)).Rule A L g t := by
  intro W hW
  rw [fF_map]
  exact hx W fun o ho => opndIs_of (List.all_eq_true.mp hp o ho)
    fun r hr => hW r (List.mem_flatMap.mpr ⟨o, ho, hr⟩)

/-- `max.ftz.f32` on a list of two values. -/
def maxFL : List Value → Exec Value
  | [a, b] => maxFE a b
  | _ => .error .noRule

/-- `add.f32x2` on a list of two values. -/
def add2NL : List Value → Exec Value
  | [a, b] => add2NE a b
  | _ => .error .noRule

/-- `mul{.ftz}.f32` on a list of two values. -/
def mulL (fz : Bool) : List Value → Exec Value
  | [a, b] => mulE fz a b
  | _ => .error .noRule

theorem XItem.maxF_rule {t : TState} (hI : IdealAt A (.max .f32) L g t)
    (hD : DeclineAt A (.max .f32) L g t) {d : Nat} {a b : Opnd}
    (hp : [a, b].all fPlain = true) :
    (XItem.fn (fOp maxFI d [a, b]) d (regsOf [a, b]) (fF maxFL [a, b])).Rule A L g t :=
  XItem.float_rule hp fun _ hW => exec_maxFE hI hD (hW a (by simp)) (hW b (by simp))

theorem XItem.add2N_rule {t : TState} (hI : IdealAt A .addRnF32x2 L g t)
    (hD : DeclineAt A .addRnF32x2 L g t) {d a b : Nat} :
    (XItem.fn (fOp add2NI d [.reg a, .reg b]) d (regsOf [.reg a, .reg b])
      (fF add2NL [.reg a, .reg b])).Rule A L g t :=
  fun W hW => by
    rw [fF_map]
    exact exec_add2NE hI hD (hW a (by simp [regsOf, regOf])) (hW b (by simp [regsOf, regOf]))

theorem XItem.mul_rule {t : TState} (hI : IdealAt A (.mul .f32) L g t)
    (hD : DeclineAt A (.mul .f32) L g t) {fz : Bool} {d : Nat} {a b : Opnd}
    (hp : [a, b].all fPlain = true) :
    (XItem.fn (fOp (mulI fz) d [a, b]) d (regsOf [a, b]) (fF (mulL fz) [a, b])).Rule A L g t :=
  XItem.float_rule hp fun _ hW => exec_mulE hI hD (hW a (by simp)) (hW b (by simp))

theorem XItem.fma_rule {t : TState} (hI : IdealAt A (.fma .f32) L g t)
    (hD : DeclineAt A (.fma .f32) L g t) {rnd : FloatRound} {fz : Bool} {d : Nat}
    {a b c : Opnd} (hp : [a, b, c].all fPlain = true) :
    (XItem.fn (fOp (fmaI rnd fz) d [a, b, c]) d (regsOf [a, b, c])
      (fF (floatE (fmaI rnd fz)) [a, b, c])).Rule A L g t :=
  XItem.float_rule hp fun _ hW =>
    exec_floatE_fma_at hI hD (hW a (by simp)) (hW b (by simp)) (hW c (by simp))

/-! ### `mul.f32x2` without a rounding modifier -/

/-- `mul.f32x2` (no rounding modifier). -/
abbrev mul2NI : FloatInstr := { op := .mul, ty := ⟨.f32, 2⟩, dsts := [], srcs := [] }

theorem execLocal_mul2N_core {t : TState} {d a b : Nat} {va vb : Value}
    (ha : t.regs a = some va) (hb : t.regs b = some vb) :
    execLocal L g t (.float { mul2NI with dsts := [some d], srcs := [.reg a, .reg b] }) =
      (coreFloat mul2NI [va, vb]).map fun v => PTX.next (setReg t d v) := by
  have hl : FloatInstr.lane { mul2NI with dsts := [some d], srcs := [.reg a, .reg b] } =
      FloatInstr.lane mul2NI := rfl
  have h2 : List.range 2 = [0, 1] := rfl
  cases hxa : classify .f32 (splitValue 64 va).1 with
  | error e => core_float_reg
  | ok xa =>
  cases hxb : classify .f32 (splitValue 64 vb).1 with
  | error e => core_float_reg
  | ok xb =>
  cases hl0 : FloatInstr.lane mul2NI [xa, xb] with
  | none => core_float_reg
  | some o =>
  cases hya : classify .f32 (splitValue 64 va).2 with
  | error e => core_float_reg
  | ok ya =>
  cases hyb : classify .f32 (splitValue 64 vb).2 with
  | error e => core_float_reg
  | ok yb =>
  cases hl1 : FloatInstr.lane mul2NI [ya, yb] with
  | none => core_float_reg
  | some o' => cases o <;> cases o' <;> core_float_reg

/-- **The local step of `mul.f32x2 d, a, b`** writes the outcome `floatE mul2NI` or faults. -/
theorem exec_mul2NE {t : TState} (hA : IdealAt A .mulF32x2 L g t)
    (hD : DeclineAt A .mulF32x2 L g t) {d a b : Nat} {va vb : Value}
    (ha : t.regs a = some va) (hb : t.regs b = some vb) :
    execLocalA A L g t (.float { mul2NI with dsts := [some d], srcs := [.reg a, .reg b] }) =
      (floatE mul2NI [va, vb]).map fun v => PTX.next (setReg t d v) := by
  have hf : FloatForm.ofOp (.float { mul2NI with dsts := [some d], srcs := [.reg a, .reg b] }) =
      some .mulF32x2 := by simp [FloatForm.ofOp]
  have hI : execIdealFloat L g t
      (.float { mul2NI with dsts := [some d], srcs := [.reg a, .reg b] }) =
      (idealVal mul2NI [va, vb]).map (Except.map fun v => PTX.next (setReg t d v)) := by
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
  cases hv : idealVal mul2NI [va, vb] with
  | none => rw [hD _ hf (by rw [hI, hv]; rfl), execLocal_mul2N_core ha hb]
  | some r => rw [hA _ hf _ (by rw [hI, hv]; rfl)]

/-- `mul.f32x2` on a list of two values. -/
def mul2NL : List Value → Exec Value
  | [a, b] => floatE mul2NI [a, b]
  | _ => .error .noRule

theorem XItem.mul2N_rule {t : TState} (hI : IdealAt A .mulF32x2 L g t)
    (hD : DeclineAt A .mulF32x2 L g t) {d a b : Nat} :
    (XItem.fn (fOp mul2NI d [.reg a, .reg b]) d (regsOf [.reg a, .reg b])
      (fF mul2NL [.reg a, .reg b])).Rule A L g t :=
  fun W hW => by
    rw [fF_map]
    exact exec_mul2NE hI hD (hW a (by simp [regsOf, regOf])) (hW b (by simp [regsOf, regOf]))

/-! ### `neg{.ftz}.f32` -/

/-- `neg{.ftz}.f32`. -/
abbrev negI (fz : Bool) : FloatInstr :=
  { op := .neg, ty := ty1 .f32, ftz := fz, dsts := [], srcs := [] }

theorem execLocal_neg_core {t : TState} {fz : Bool} {d : Nat} {a : Opnd} {va : Value}
    (ha : OpndIs L g t a va) :
    execLocal L g t (.float { negI fz with dsts := [some d], srcs := [a] }) =
      (coreFloat (negI fz) [va]).map fun v => PTX.next (setReg t d v) := by
  have hl : FloatInstr.lane { negI fz with dsts := [some d], srcs := [a] } =
      FloatInstr.lane (negI fz) := rfl
  obtain ⟨ha, -⟩ := ha
  cases hxa : classify .f32 va with
  | error e => core_float
  | ok xa =>
  cases hlane : FloatInstr.lane (negI fz) [xa] with
  | none => core_float
  | some o => cases o <;> core_float

/-- The ideal-real outcome of `neg.f32` on a source value; `none` where the rule declines. -/
def idealNeg (va : Value) : Option (Exec Value) :=
  bindRead (readEReal .f32 va) fun x => some (pure (erealValue .f32 (-x)))

/-- **The outcome of `neg{.ftz}.f32`**: the ideal outcome, or the Core rule's where it
declines. -/
@[irreducible] def negE (fz : Bool) (va : Value) : Exec Value :=
  match idealNeg va with
  | some r => r
  | none => coreFloat (negI fz) [va]

theorem exec_negE {t : TState} (hA : IdealAt A (.neg .f32) L g t)
    (hD : DeclineAt A (.neg .f32) L g t) {fz : Bool} {d : Nat} {a : Opnd} {va : Value}
    (ha : OpndIs L g t a va) :
    execLocalA A L g t (.float { negI fz with dsts := [some d], srcs := [a] }) =
      (negE fz va).map fun v => PTX.next (setReg t d v) := by
  have hf : FloatForm.ofOp (.float { negI fz with dsts := [some d], srcs := [a] }) =
      some (.neg .f32) := by simp [FloatForm.ofOp]
  have hI : execIdealFloat L g t (.float { negI fz with dsts := [some d], srcs := [a] }) =
      (idealNeg va).map (Except.map fun v => PTX.next (setReg t d v)) := by
    simp only [execIdealFloat, idealNeg, ha.2, bindRead_map]
    rcases readEReal .f32 va with _ | (e | x) <;> rfl
  unfold negE
  cases hv : idealNeg va with
  | none => rw [hD _ hf (by rw [hI, hv]; rfl), execLocal_neg_core ha]
  | some r => rw [hA _ hf _ (by rw [hI, hv]; rfl)]

/-- `neg{.ftz}.f32` on a list of one value. -/
def negL (fz : Bool) : List Value → Exec Value
  | [a] => negE fz a
  | _ => .error .noRule

theorem XItem.neg_rule {t : TState} (hI : IdealAt A (.neg .f32) L g t)
    (hD : DeclineAt A (.neg .f32) L g t) {fz : Bool} {d : Nat} {a : Opnd}
    (hp : [a].all fPlain = true) :
    (XItem.fn (fOp (negI fz) d [a]) d (regsOf [a]) (fF (negL fz) [a])).Rule A L g t :=
  XItem.float_rule hp fun _ hW => exec_negE hI hD (hW a (by simp))

/-! ### `div.approx{.ftz}.f32` at a state -/

theorem exec_divE_at {t : TState} (hA : ApproxAt A (.div .f32) L g t)
    (hD : ApproxDeclineAt A (.div .f32) L g t) {fz : Bool} {d : Nat} {a b : Opnd}
    {va vb : Value} (ha : OpndIs L g t a va) (hb : OpndIs L g t b vb) :
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
  | none => rw [hD _ hf (by rw [hI, hv]; rfl), execLocal_div_core ha hb]
  | some r => rw [hA _ hf _ (by rw [hI, hv]; rfl)]

theorem XItem.div_rule {t : TState} (hA : ApproxAt A (.div .f32) L g t)
    (hD : ApproxDeclineAt A (.div .f32) L g t) {fz : Bool} {d : Nat} {a b : Opnd}
    (hp : [a, b].all fPlain = true) :
    (XItem.fn (fOp (divI fz) d [a, b]) d (regsOf [a, b])
      (fF (approxE (divI fz)) [a, b])).Rule A L g t :=
  XItem.float_rule hp fun _ hW => exec_divE_at hA hD (hW a (by simp)) (hW b (by simp))

/-! ### Two Core forms with an outcome function of their own -/

/-- **A `fn` item reads Core's value `F`**, from Core's equation at every state whose source
registers hold `W`. -/
theorem XItem.local_of {pc d : Nat} {op : Op} {srcs : List Nat}
    {F : (Nat → Value) → Exec Value} (hS : SegFreePc A pc) (hn : NoLocalRule A L g pc op)
    (hc : ∀ (t : TState) (W : Nat → Value), (∀ r ∈ srcs, t.regs r = some (W r)) →
      execLocal L g t op = (F W).map fun v => PTX.next (setReg t d v)) :
    ∀ s : TState, s.pc = pc → (XItem.fn op d srcs (fun vs => F (lk srcs vs))).Rule A L g s := by
  intro s hs W hW
  rw [hS.exec hs, execLocalRule_of_none (hn s hs),
    hc s (lk srcs (srcs.map W)) (fun r hr => by rw [lk_map hr]; exact hW r hr)]

/-- Core's value of `bfe.<k><w> d, a, b, c` from the register values `W`. -/
def bfeW (k : IType) (w : Nat) (a b c : Opnd) (W : Nat → Value) : Exec Value := do
  let x := (← oBits W w a).toNat
  let pos := (← oBits W 32 b).toNat % 256
  let len := (← oBits W 32 c).toNat % 256
  pure (.bits w (BitVec.ofNat 64 (bfeBits k w x pos len)))

/-- `bfe.<k><w> d, a, b, c`. -/
def bfeOp (k : IType) (w d : Nat) (a b c : Opnd) : Op :=
  .int { op := .bfe, ty := .int k w, sat := false, dsts := [some d], srcs := [a, b, c] }

theorem XItem.core_bfe {pc d w : Nat} {k : IType} {a b c : Opnd} (hS : SegFreePc A pc)
    (hn : NoLocalRule A L g pc (bfeOp k w d a b c))
    (hr : (bfeOp k w d a b c).rule = some .threadInt)
    (hp : (plainB a && plainB b && plainB c) = true) :
    ∀ s : TState, s.pc = pc → (XItem.fn (bfeOp k w d a b c) d (regsOf [a, b, c])
      (fun vs => bfeW k w a b c (lk (regsOf [a, b, c]) vs))).Rule A L g s := by
  simp only [Bool.and_eq_true] at hp
  obtain ⟨⟨ha, hb⟩, hc⟩ := hp
  refine XItem.local_of hS hn fun t W hW => ?_
  simp only [execLocal, hr]
  simp only [bfeOp, execInt, intResult,
    readBits_oBits ha (reg_of_mem (by simp) hW), readBits_oBits hb (reg_of_mem (by simp) hW),
    readBits_oBits hc (reg_of_mem (by simp) hW), bfeW, DType.intLanes?, DType.width]
  cases oBits W w a <;> cases oBits W 32 b <;> cases oBits W 32 c <;> rfl

/-- Core's value of the kept half of `mov.b<w> {lo, _}, a` (`lo := true`) or
`mov.b<w> {_, hi}, a`. -/
def sinkW (w : Nat) (lo : Bool) (a : Nat) (W : Nat → Value) : Exec Value :=
  if (W a).bytes = w / 8 then
    if (splitValue w (W a)).1.bytes = w / 16 ∧ (splitValue w (W a)).2.bytes = w / 16 then
      .ok (if lo then (splitValue w (W a)).1 else (splitValue w (W a)).2)
    else .error .typeMismatch
  else .error .typeMismatch

/-- `mov.b<w> {d, _}, a` (`lo := true`) or `mov.b<w> {_, d}, a`. -/
def sinkOp (w : Nat) (lo : Bool) (d a : Nat) : Op :=
  .move
    { kind := .unpack
      ty := DType.int .b w
      dsts := if lo then [some d, none] else [none, some d]
      srcs := [.reg a] }

theorem XItem.core_sink {pc w d a : Nat} {lo : Bool} (hS : SegFreePc A pc)
    (hn : NoLocalRule A L g pc (sinkOp w lo d a))
    (hr : (sinkOp w lo d a).rule = some .threadMove) :
    ∀ s : TState, s.pc = pc →
      (XItem.fn (sinkOp w lo d a) d [a] (fun vs => sinkW w lo a (lk [a] vs))).Rule A L g s := by
  refine XItem.local_of hS hn fun t W hW => ?_
  have ha := hW a (by simp)
  simp only [execLocal, hr]
  cases lo <;>
    simp only [sinkOp, execMove, readValue, readReg, ha, sinkW, Bool.false_eq_true,
      ↓reduceIte, bind, Except.bind, pure, Except.pure, DType.width] <;>
    by_cases h1 : (W a).bytes = w / 8 <;>
    by_cases h2 : (splitValue w (W a)).1.bytes = w / 16 ∧ (splitValue w (W a)).2.bytes = w / 16 <;>
    simp [h1, h2, setDst, throw, throwThe, MonadExceptOf.throw, Except.map]

end
end PTX.Flow
