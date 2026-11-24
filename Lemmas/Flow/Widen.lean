-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Machine
public import Lemmas.Assumption.Facts
public import Lemmas.Flow.Facts
public import Lemmas.Flow.FloatRead

@[expose] public section

/-! # Packed halves widened to single precision, and packed multiplications

A proof tool. Under the ideal-real assumption:

* `mov.b32 {lo, hi}, w` followed by `cvt.f32.f16 dlo, lo` and `cvt.f32.f16 dhi, hi` (a
  `Widen` step) splits a 32-bit word into its two halves and reads each as a half-precision
  float. It fails unless the word has four bytes, its halves two each, and both halves read as
  `f16` operands (`wideOk`). For a run of such steps (`widen_chain`): when every word is
  accepted, local steps write each destination with its half's reading (`rd16`) and keep every
  register they do not write; otherwise the thread is dead (`widen_chain_dead`).
* `mov.b64 d, {a, b}` followed by `mul.f32x2 d', d, c` (`pack_mul`) packs two 32-bit words and
  multiplies the pair elementwise by the pair in `c`. It fails unless both words have four bytes
  and the four elements read as `f32` operands (`pairOk`); otherwise the thread is dead. -/

namespace PTX.Flow
open PTX PTX.Proof

noncomputable section

/-- The real an `f16` operand reads as (`0` if it does not read). -/
def rd16 (v : Value) : ℝ := (valFloat .f16 v).toOption.getD 0

/-- The real an `f32` operand reads as (`0` if it does not read). -/
def rd32 (v : Value) : ℝ := (valFloat .f32 v).toOption.getD 0

/-- A word that the unpack into halves and the two conversions to `f32` accept. -/
def wideOk (v : Value) : Bool :=
  v.bytes == 4 && (splitValue 32 v).1.bytes == 2 && (splitValue 32 v).2.bytes == 2 &&
    (valFloat .f16 (splitValue 32 v).1).toBool && (valFloat .f16 (splitValue 32 v).2).toBool

/-- Two words that the pack into a pair accepts, and whose packed elements and the elements of
`c` read as `f32` operands. -/
def pairOk (a b c : Value) : Bool :=
  a.bytes == 4 && b.bytes == 4 && (valFloat .f32 (splitValue 64 (joinValue a b)).1).toBool &&
    (valFloat .f32 (splitValue 64 (joinValue a b)).2).toBool &&
    (valFloat .f32 (splitValue 64 c).1).toBool && (valFloat .f32 (splitValue 64 c).2).toBool

/-- The product a packed multiplication of the pair of `a`, `b` with `c` writes. -/
def pairMul (a b c : Value) : Value :=
  .pair (.float .f32 (rd32 (splitValue 64 (joinValue a b)).1 * rd32 (splitValue 64 c).1))
    (.float .f32 (rd32 (splitValue 64 (joinValue a b)).2 * rd32 (splitValue 64 c).2))

/-- The two `.f32` elements of a pair value in the extended reals, as the ideal rule reads the
register that holds it: low half first, `none` when either is a NaN (the rule declines it and the
Core rule then applies), and the fault of the first element that has no value. -/
def pairRead (v : Value) : Option (Exec (EReal × EReal)) :=
  match Assumption.readEReal .f32 (splitValue 64 v).1,
    Assumption.readEReal .f32 (splitValue 64 v).2 with
  | some (.ok x0), some (.ok x1) => some (pure (x0, x1))
  | some (.error e), _ => some (.error e)
  | some (.ok _), some (.error e) => some (.error e)
  | _, _ => none

/-- The pair read of a register is the pair read of its value. -/
theorem readERealPair_reg_val {t : TState} {r : Nat} {v : Value}
    (h : t.regs r = some v) :
    Assumption.readERealPair L g t (.reg r) = pairRead v := by
  simp only [Assumption.readERealPair, pairRead, readValue, readReg, h, pure, Except.pure]
  rfl

/-- A packed multiplication of the pair `w` by the pair `c` faults: the first pair whose read has
no value, the reads before it having one. A NaN or an infinity operand is no such case: the ideal
rule declines a NaN, so the Core rule applies, and reads an infinity as that infinity. -/
def PairFault (w c : Value) : Prop :=
  (∃ f, pairRead w = some (.error f)) ∨
    (∃ p, pairRead w = some (.ok p)) ∧ ∃ f, pairRead c = some (.error f)

/-- The three ways a pair read can go: a fault (the thread is dead), a NaN (the rule declines and
the Core rule applies) or two numbers. -/
theorem pairRead_cases (v : Value) :
    (∃ f, pairRead v = some (.error f)) ∨ pairRead v = none ∨
      ∃ p, pairRead v = some (.ok p) := by
  unfold pairRead
  match Assumption.readEReal .f32 (splitValue 64 v).1 with
  | none => simp
  | some (.error e) => simp
  | some (.ok x0) =>
    match Assumption.readEReal .f32 (splitValue 64 v).2 with
    | none => simp
    | some (.error e) => simp
    | some (.ok x1) => exact .inr (.inr ⟨(x0, x1), by simp [pure, Except.pure]⟩)

theorem ok_of_toBool {fmt : FloatFmt} {v : Value} (h : (valFloat fmt v).toBool = true) :
    ∃ x, valFloat fmt v = .ok x := by
  cases hv : valFloat fmt v with
  | ok x => exact ⟨x, rfl⟩
  | error f => rw [hv] at h; cases h

/-- One step: the source word, the two halves and the two destinations. -/
structure Widen where
  src : Nat
  lo : Nat
  hi : Nat
  dlo : Nat
  dhi : Nat

/-- The registers a step writes. -/
def Widen.writes (w : Widen) : List Nat := [w.lo, w.hi, w.dlo, w.dhi]

/-- The code holds the steps `ws` from `pc` on. -/
def WidenCode (K : Kernel) : Nat → List Widen → Prop
  | _, [] => True
  | pc, w :: ws =>
    K.code[pc]? = some ⟨none, .move ⟨.unpack, .int .b 32, [some w.lo, some w.hi], [.reg w.src]⟩⟩ ∧
      K.code[pc + 1]? = some ⟨none, .cvt {
            dst := .float .f32, src := .float .f16,
            d := w.dlo, srcs := [.reg w.lo] }⟩ ∧
      K.code[pc + 2]? = some ⟨none, .cvt {
            dst := .float .f32, src := .float .f16,
            d := w.dhi, srcs := [.reg w.hi] }⟩ ∧ WidenCode K (pc + 3) ws

/-- The registers a step writes are distinct, and no step writes a register a later one
reads or writes. -/
def WidenFresh : List Widen → Prop
  | [] => True
  | w :: ws => (w.lo ≠ w.hi ∧ w.lo ≠ w.dlo ∧ w.lo ≠ w.dhi ∧ w.hi ≠ w.dlo ∧ w.hi ≠ w.dhi ∧
      w.dlo ≠ w.dhi) ∧ (∀ w' ∈ ws, ∀ r ∈ w.writes, r ≠ w'.src ∧ r ∉ w'.writes) ∧ WidenFresh ws

instance decWidenFresh : (ws : List Widen) → Decidable (WidenFresh ws)
  | [] => isTrue trivial
  | w :: ws =>
    have := decWidenFresh ws
    inferInstanceAs (Decidable ((w.lo ≠ w.hi ∧ w.lo ≠ w.dlo ∧ w.lo ≠ w.dhi ∧ w.hi ≠ w.dlo ∧
      w.hi ≠ w.dhi ∧ w.dlo ≠ w.dhi) ∧ (∀ w' ∈ ws, ∀ r ∈ w.writes, r ≠ w'.src ∧ r ∉ w'.writes) ∧
      WidenFresh ws))

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- No assumption of `A` names the unpack of a word into two halves. -/
def NoUnpack (A : List Assumption) : Prop :=
  ∀ (lo hi src : Nat) (L : Launch) (g : Nat) (t : TState), ∀ a ∈ A,
    a.localRule L g t (.move ⟨.unpack, .int .b 32, [some lo, some hi], [.reg src]⟩) = none

/-- No assumption of `A` names the pack of two words into one. -/
def NoPack (A : List Assumption) : Prop :=
  ∀ (d a b : Nat) (L : Launch) (g : Nat) (t : TState), ∀ a' ∈ A,
    a'.localRule L g t (.move ⟨.pack, .int .b 64, [some d], [.reg a, .reg b]⟩) = none

theorem exec_unpack (hN : NoUnpack A) {t : TState} {lo hi src : Nat} {v : Value}
    (h : t.regs src = some v)
    (hS : Assumption.SegFreePc A t.pc := by seg_free) :
    execLocalA A L g t (.move ⟨.unpack, .int .b 32, [some lo, some hi], [.reg src]⟩) =
      (if v.bytes = 4 then
        (if (splitValue 32 v).1.bytes = 2 ∧ (splitValue 32 v).2.bytes = 2 then
          .ok (PTX.next (setReg (setReg t lo (splitValue 32 v).1) hi (splitValue 32 v).2))
        else .error .typeMismatch)
      else .error .typeMismatch) := by
  simp only [hS.exec, execLocalRule_of_none (hN lo hi src L g t), execLocal, Op.rule,
    MoveInstr.rule, execMove, readValue, readReg]
  by_cases h4 : v.bytes = 4 <;> by_cases h2 : (splitValue 32 v).1.bytes = 2 ∧
    (splitValue 32 v).2.bytes = 2 <;>
    simp [h, h4, h2, DType.width, bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw]

/-- **The ideal step of a widening**: with the source as a half-precision number, the local step
writes its single-precision reading. -/
theorem exec_widen (hA : Assumption.IdealFor A .cvtF32F16) {t : TState} {d r : Nat} {v : Value}
    {x : ℝ} (h : t.regs r = some v) (hx : valFloat .f16 v = .ok x) :
    execLocalA A L g t (.cvt { dst := .float .f32, src := .float .f16, d := d, srcs := [.reg r] }) =
      .ok (PTX.next (setReg t d (.float .f32 x))) := by
  have hr : Assumption.readERealOpnd t .f16 (.reg r) = some (.ok (x : EReal)) := by
    rw [readERealOpnd_reg h]; exact readEReal_of_valFloat hx
  have hex : Assumption.execIdealFloat L g t
      (.cvt { dst := .float .f32, src := .float .f16, d := d, srcs := [.reg r] }) =
      some (.ok (PTX.next (setReg t d (Assumption.erealValue .f32 (x : EReal))))) := by
    simp [Assumption.execIdealFloat, CvtInstr.widenF16?, CvtInstr.packF16?, CvtInstr.plain, hr,
      Assumption.bindRead, pure, Except.pure]
  rw [hA L g t _ rfl _ hex]
  simp [Assumption.erealValue]

/-- **The ideal step of a widening the ideal rule rejects**: it faults. -/
theorem exec_widen_error (hA : Assumption.IdealFor A .cvtF32F16) {t : TState} {d r : Nat}
    {v : Value} {f : Fault} (h : t.regs r = some v)
    (hx : Assumption.readEReal .f16 v = some (.error f)) :
    execLocalA A L g t (.cvt { dst := .float .f32, src := .float .f16, d := d, srcs := [.reg r] }) =
      .error f := by
  have hr : Assumption.readERealOpnd t .f16 (.reg r) = some (.error f) := by
    rw [readERealOpnd_reg h]; exact hx
  have hex : Assumption.execIdealFloat L g t
      (.cvt { dst := .float .f32, src := .float .f16, d := d, srcs := [.reg r] }) =
      some (.error f) := by
    simp [Assumption.execIdealFloat, CvtInstr.widenF16?, CvtInstr.packF16?, CvtInstr.plain, hr,
      Assumption.bindRead]
  rw [hA L g t _ rfl _ hex]

/-- The state after a step whose word is accepted. -/
def widenStep (t : TState) (w : Widen) (v : Value) : TState :=
  PTX.next (setReg (PTX.next (setReg (PTX.next (setReg (setReg t w.lo (splitValue 32 v).1) w.hi
    (splitValue 32 v).2)) w.dlo (.float .f32 (rd16 (splitValue 32 v).1)))) w.dhi
    (.float .f32 (rd16 (splitValue 32 v).2)))

theorem widenStep_regs {t : TState} {w : Widen} {v : Value} {r : Nat} (h : r ∉ w.writes) :
    (widenStep t w v).regs r = t.regs r := by
  simp only [Widen.writes, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  simp [widenStep, PTX.next, setReg, Function.update_of_ne h.1, Function.update_of_ne h.2.1,
    Function.update_of_ne h.2.2.1, Function.update_of_ne h.2.2.2]

/-- **One step whose word is accepted**: three local steps. -/
theorem widen_step (hA : Assumption.IdealFor A .cvtF32F16) (hN : NoUnpack A) {t : TState}
    {w : Widen} {v : Value}
    (hc : WidenCode K t.pc [w]) (hfr : WidenFresh [w]) (hf : t.fault = none)
    (hv : t.regs w.src = some v) (hok : wideOk v = true)
    (hS : Assumption.NoSegments A := by hooks_off) :
    run K A L g 3 t = some (widenStep t w v) := by
  obtain ⟨h1, h2, h3, -⟩ := hc
  obtain ⟨⟨hlh, hll, hlH, hhl, hhh, hdd⟩, -, -⟩ := hfr
  simp only [wideOk, Bool.and_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨⟨⟨h4, hb1⟩, hb2⟩, hx⟩, hy⟩ := hok
  obtain ⟨x, hx⟩ := ok_of_toBool hx
  obtain ⟨y, hy⟩ := ok_of_toBool hy
  have o1 : out K A L g t = .tau (PTX.next (setReg (setReg t w.lo (splitValue 32 v).1) w.hi
      (splitValue 32 v).2)) := by
    simp only [out, hf, h1, guardHolds, pure, Except.pure, Op.isLocal, Op.varyingSregs,
        Opnd.varying?, List.filterMap, List.isEmpty_nil, ↓reduceIte,
      exec_unpack (A := A) (L := L) (g := g) hN hv hS.segFreePc, h4, hb1, hb2,
      and_self]
  set t1 := PTX.next (setReg (setReg t w.lo (splitValue 32 v).1) w.hi (splitValue 32 v).2)
  have r1 : t1.regs w.lo = some (splitValue 32 v).1 := by
    simp [t1, PTX.next, setReg, Function.update_of_ne hlh]
  have p1 : t1.pc = t.pc + 1 := rfl
  have o2 : out K A L g t1 = .tau
    (PTX.next (setReg t1 w.dlo (.float .f32 (rd16 (splitValue 32 v).1)))) := by
    have hc2 : K.code[t1.pc]? = some ⟨none, .cvt {
          dst := .float .f32, src := .float .f16,
          d := w.dlo, srcs := [.reg w.lo] }⟩ := by rw [p1]; exact h2
    simp only [out, show t1.fault = none from hf, hc2, guardHolds, pure, Except.pure,
      Op.isLocal, Op.varyingSregs, Opnd.varying?, List.filterMap, List.isEmpty_nil, ↓reduceIte,
      exec_widen hA r1 hx, rd16, hx, Except.toOption, Option.getD_some]
  set t2 := PTX.next (setReg t1 w.dlo (.float .f32 (rd16 (splitValue 32 v).1)))
  have r2 : t2.regs w.hi = some (splitValue 32 v).2 := by
    simp [t2, t1, PTX.next, setReg, Function.update_of_ne hhl]
  have o3 : out K A L g t2 = .tau
    (PTX.next (setReg t2 w.dhi (.float .f32 (rd16 (splitValue 32 v).2)))) := by
    have hc3 : K.code[t2.pc]? = some ⟨none, .cvt {
          dst := .float .f32, src := .float .f16,
          d := w.dhi, srcs := [.reg w.hi] }⟩ := by
      show K.code[t.pc + 1 + 1]? = _; exact h3
    simp only [out, show t2.fault = none from hf, hc3, guardHolds, pure, Except.pure,
      Op.isLocal, Op.varyingSregs, Opnd.varying?, List.filterMap, List.isEmpty_nil, ↓reduceIte,
      exec_widen hA r2 hy, rd16, hy, Except.toOption, Option.getD_some]
  simp only [run, tauStep, o1, Option.bind_some, o2, o3]
  rfl

/-- A word the ideal rule rejects: no four-byte word, halves of two bytes, or a half the ideal
rule rejects. A half that is a NaN or an infinity is no such case: the ideal rule declines it and
the Core conversion rule converts that datum, so the thread does not fault. -/
def WideRejects (v : Value) : Prop :=
  v.bytes ≠ 4 ∨ (splitValue 32 v).1.bytes ≠ 2 ∨ (splitValue 32 v).2.bytes ≠ 2 ∨
    (∃ f, Assumption.readEReal .f16 (splitValue 32 v).1 = some (.error f)) ∨
      (∃ x : ℝ, valFloat .f16 (splitValue 32 v).1 = .ok x) ∧
        ∃ f, Assumption.readEReal .f16 (splitValue 32 v).2 = some (.error f)

/-- A word the unpack and the two conversions accept is no word the ideal rule rejects. -/
theorem not_wideRejects_of_wideOk {v : Value} (h : wideOk v = true) : ¬ WideRejects v := by
  intro hb
  simp only [wideOk, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨h4, hb1⟩, hb2⟩, hx⟩, hy⟩ := h
  obtain ⟨x, hx⟩ := ok_of_toBool hx
  obtain ⟨y, hy⟩ := ok_of_toBool hy
  rcases hb with h | h | h | ⟨f, hf⟩ | ⟨⟨z, hz⟩, f, hf⟩
  · exact h h4
  · exact h hb1
  · exact h hb2
  · rw [readEReal_of_valFloat hx] at hf; cases hf
  · rw [readEReal_of_valFloat hy] at hf; cases hf

/-- **One step whose word the ideal rule rejects**: the thread is dead. -/
theorem widen_step_dead (hA : Assumption.IdealFor A .cvtF32F16) (hN : NoUnpack A) {t : TState}
    {w : Widen}
    {v : Value} (hc : WidenCode K t.pc [w]) (hfr : WidenFresh [w]) (hf : t.fault = none)
    (hv : t.regs w.src = some v) (hbad : WideRejects v)
    (hS : Assumption.NoSegments A := by hooks_off) :
    Machine.Dead (K := K) (A := A) (L := L) (g := g) t := by
  obtain ⟨h1, h2, h3, -⟩ := hc
  obtain ⟨⟨hlh, hll, hlH, hhl, hhh, hdd⟩, -, -⟩ := hfr
  by_cases h4 : v.bytes = 4
  swap
  · exact Machine.dead_of_ub (f := .typeMismatch) (by
      simp only [out, hf, h1, guardHolds, pure, Except.pure, Op.isLocal, Op.varyingSregs,
        Opnd.varying?, List.filterMap, List.isEmpty_nil, ↓reduceIte,
        exec_unpack (A := A) (L := L) (g := g) hN hv hS.segFreePc, h4])
  by_cases hb : (splitValue 32 v).1.bytes = 2 ∧ (splitValue 32 v).2.bytes = 2
  swap
  · exact Machine.dead_of_ub (f := .typeMismatch) (by
      simp only [out, hf, h1, guardHolds, pure, Except.pure, Op.isLocal, Op.varyingSregs,
        Opnd.varying?, List.filterMap, List.isEmpty_nil, ↓reduceIte,
        exec_unpack (A := A) (L := L) (g := g) hN hv hS.segFreePc, h4, hb])
  have o1 : out K A L g t = .tau (PTX.next (setReg (setReg t w.lo (splitValue 32 v).1) w.hi
      (splitValue 32 v).2)) := by
    simp only [out, hf, h1, guardHolds, pure, Except.pure, Op.isLocal, Op.varyingSregs,
      Opnd.varying?, List.filterMap, List.isEmpty_nil, ↓reduceIte,
      exec_unpack (A := A) (L := L) (g := g) hN hv hS.segFreePc, h4, hb, and_self]
  refine Machine.dead_of_tau o1 ?_
  set t1 := PTX.next (setReg (setReg t w.lo (splitValue 32 v).1) w.hi (splitValue 32 v).2)
  have r1 : t1.regs w.lo = some (splitValue 32 v).1 := by
    simp [t1, PTX.next, setReg, Function.update_of_ne hlh]
  -- the word has the width and its halves, so the rejection is at a half
  have hrej : (∃ f, Assumption.readEReal .f16 (splitValue 32 v).1 = some (.error f)) ∨
      (∃ x : ℝ, valFloat .f16 (splitValue 32 v).1 = .ok x) ∧
        ∃ f, Assumption.readEReal .f16 (splitValue 32 v).2 = some (.error f) := by
    rcases hbad with h | h | h | h | h
    · exact absurd h4 h
    · exact absurd hb.1 h
    · exact absurd hb.2 h
    · exact .inl h
    · exact .inr h
  have hc2 : K.code[t1.pc]? = some ⟨none, .cvt
      { dst := .float .f32, src := .float .f16, d := w.dlo, srcs := [.reg w.lo] }⟩ := h2
  rcases hrej with ⟨fe, hg⟩ | ⟨⟨x, hx⟩, fe, hg⟩
  · exact Machine.dead_of_ub (f := fe) (by
      simp only [out, show t1.fault = none from hf, hc2, guardHolds, pure, Except.pure,
        Op.isLocal, Op.varyingSregs, Opnd.varying?, List.filterMap, List.isEmpty_nil, ↓reduceIte,
        exec_widen_error hA r1 hg])
  · have o2 : out K A L g t1 = .tau (PTX.next (setReg t1 w.dlo (.float .f32 x))) := by
      simp only [out, show t1.fault = none from hf, hc2, guardHolds, pure, Except.pure,
        Op.isLocal, Op.varyingSregs, Opnd.varying?, List.filterMap, List.isEmpty_nil,
        ↓reduceIte, exec_widen hA r1 hx]
    refine Machine.dead_of_tau o2 ?_
    set t2 := PTX.next (setReg t1 w.dlo (.float .f32 x))
    have r2 : t2.regs w.hi = some (splitValue 32 v).2 := by
      simp [t2, t1, PTX.next, setReg, Function.update_of_ne hhl]
    have hc3 : K.code[t2.pc]? = some ⟨none, .cvt
        { dst := .float .f32, src := .float .f16, d := w.dhi, srcs := [.reg w.hi] }⟩ := h3
    exact Machine.dead_of_ub (f := fe) (by
      simp only [out, show t2.fault = none from hf, hc3, guardHolds, pure, Except.pure,
        Op.isLocal, Op.varyingSregs, Opnd.varying?, List.filterMap, List.isEmpty_nil,
        ↓reduceIte, exec_widen_error hA r2 hg])

theorem widenStep_pc (t : TState) (w : Widen) (v : Value) : (widenStep t w v).pc = t.pc + 3 := rfl

/-- **A run of accepted steps**: local steps write each destination with its half's reading
and keep every register they do not write. -/
theorem widen_chain (hA : Assumption.IdealFor A .cvtF32F16) (hN : NoUnpack A)
    (hS : Assumption.NoSegments A) :
    ∀ (ws : List Widen) (t : TState), WidenCode K t.pc ws → WidenFresh ws → t.fault = none →
      t.sub = 0 → t.acc = [] →
      (∀ w ∈ ws, ∃ v, t.regs w.src = some v ∧ wideOk v = true) →
      ∃ t', run K A L g (3 * ws.length) t = some t' ∧ t'.pc = t.pc + 3 * ws.length ∧
        t'.sub = 0 ∧ t'.acc = [] ∧ t'.fault = none ∧
        (∀ w ∈ ws, ∀ v, t.regs w.src = some v →
          t'.regs w.dlo = some (.float .f32 (rd16 (splitValue 32 v).1)) ∧
          t'.regs w.dhi = some (.float .f32 (rd16 (splitValue 32 v).2))) ∧
        ∀ r, (∀ w ∈ ws, r ∉ w.writes) → t'.regs r = t.regs r
  | [], t, _, _, hf, hs, ha, _ => ⟨t, rfl, rfl, hs, ha, hf, by simp, fun _ _ => rfl⟩
  | w :: ws, t, hc, hfr, hf, hs, ha, hok => by
    obtain ⟨v, hv, hwv⟩ := hok w (by simp)
    have h1 := widen_step (K := K) (L := L) (g := g) hA hN ⟨hc.1, hc.2.1, hc.2.2.1, trivial⟩
      ⟨hfr.1, by simp, trivial⟩ hf hv hwv
    set t1 := widenStep t w v
    have hreg : ∀ r, r ∉ w.writes → t1.regs r = t.regs r := fun r hr => widenStep_regs hr
    obtain ⟨t', hr, hpc, hs', ha', hf', hd, ho⟩ := widen_chain hA hN hS ws t1
      (by rw [widenStep_pc]; exact hc.2.2.2) hfr.2.2 hf hs ha
      (fun w' hw' => by
        obtain ⟨v', hv', hok'⟩ := hok w' (by simp [hw'])
        have hsrc : w'.src ∉ w.writes := fun hm => ((hfr.2.1 w' hw') _ hm).1 rfl
        exact ⟨v', by rw [hreg _ hsrc]; exact hv', hok'⟩)
    refine ⟨t', ?_, ?_, hs', ha', hf', ?_, ?_⟩
    · rw [List.length_cons, show 3 * (ws.length + 1) = 3 + 3 * ws.length by omega, run_add, h1,
        Option.bind_some]
      exact hr
    · rw [hpc, widenStep_pc]; simp only [List.length_cons]; omega
    · intro w' hw' v' hv'
      rcases List.mem_cons.mp hw' with rfl | hw'
      · rw [hv] at hv'
        cases hv'
        have hn : ∀ r ∈ w'.writes, ∀ w'' ∈ ws, r ∉ w''.writes := fun r hr w'' hw'' =>
          ((hfr.2.1 w'' hw'') r hr).2
        refine ⟨?_, ?_⟩
        · rw [ho _ (hn _ (by simp [Widen.writes]))]
          obtain ⟨⟨_, _, _, _, _, hdd⟩, -, -⟩ := hfr
          simp [t1, widenStep, PTX.next, setReg, Function.update_of_ne hdd]
        · rw [ho _ (hn _ (by simp [Widen.writes]))]
          simp [t1, widenStep, PTX.next, setReg]
      · have hsrc : w'.src ∉ w.writes := fun hm => ((hfr.2.1 w' hw') _ hm).1 rfl
        exact hd w' hw' v' (by rw [hreg _ hsrc]; exact hv')
    · intro r hr
      rw [ho r (fun w' hw' => hr w' (by simp [hw'])), hreg r (hr w (by simp))]

/-- **A run with a step whose word the ideal rule rejects**: the thread is dead. Every step is
one the operands decide: its word is accepted, or the ideal rule rejects it. -/
theorem widen_chain_dead (hA : Assumption.IdealFor A .cvtF32F16) (hN : NoUnpack A)
    (hS : Assumption.NoSegments A) :
    ∀ (ws : List Widen) (t : TState), WidenCode K t.pc ws → WidenFresh ws → t.fault = none →
      (∀ w ∈ ws, ∃ v, t.regs w.src = some v) →
      (∀ w ∈ ws, ∀ v, t.regs w.src = some v → wideOk v = true ∨ WideRejects v) →
      (∃ w ∈ ws, ∀ v, t.regs w.src = some v → WideRejects v) →
      Machine.Dead (K := K) (A := A) (L := L) (g := g) t
  | [], _, _, _, _, _, _, ⟨_, hw, _⟩ => by simp at hw
  | w :: ws, t, hc, hfr, hf, hval, hdec, hbad => by
    obtain ⟨v, hv⟩ := hval w (by simp)
    have hreg : ∀ r, r ∉ w.writes → (widenStep t w v).regs r = t.regs r :=
      fun r hr => widenStep_regs hr
    have hregs : ∀ w' ∈ ws, ∀ v', t.regs w'.src = some v' →
        (widenStep t w v).regs w'.src = some v' := by
      intro w' hw' v' hv'
      have hsrc : w'.src ∉ w.writes := fun hm => ((hfr.2.1 w' hw') _ hm).1 rfl
      rw [hreg _ hsrc]; exact hv'
    rcases hdec w (by simp) v hv with hwv | hwv
    · have h1 := widen_step (K := K) (L := L) (g := g) hA hN ⟨hc.1, hc.2.1, hc.2.2.1, trivial⟩
        ⟨hfr.1, by simp, trivial⟩ hf hv hwv
      have hbad' : ∃ w' ∈ ws, ∀ v', (widenStep t w v).regs w'.src = some v' → WideRejects v' := by
        obtain ⟨w', hw', hb⟩ := hbad
        rcases List.mem_cons.mp hw' with rfl | hw'
        · exact absurd (hb v hv) (not_wideRejects_of_wideOk hwv)
        · refine ⟨w', hw', fun v' hv' => hb v' ?_⟩
          have hsrc : w'.src ∉ w.writes := fun hm => ((hfr.2.1 w' hw') _ hm).1 rfl
          rwa [hreg _ hsrc] at hv'
      obtain ⟨d, f, hd1, hd2⟩ := widen_chain_dead hA hN hS ws (widenStep t w v)
        (by rw [widenStep_pc]; exact hc.2.2.2) hfr.2.2 hf
        (fun w' hw' => by
          obtain ⟨v', hv'⟩ := hval w' (by simp [hw'])
          exact ⟨v', hregs w' hw' v' hv'⟩)
        (fun w' hw' v' hv' => hdec w' (by simp [hw']) v' (by
          have hsrc : w'.src ∉ w.writes := fun hm => ((hfr.2.1 w' hw') _ hm).1 rfl
          rwa [hreg _ hsrc] at hv'))
        hbad'
      exact ⟨d, f, Relation.ReflTransGen.trans (run_rtg h1) hd1, hd2⟩
    · exact widen_step_dead hA hN ⟨hc.1, hc.2.1, hc.2.2.1, trivial⟩ ⟨hfr.1, by simp, trivial⟩
        hf hv hwv

/-- **The register facts after a run of accepted steps**: the facts `live'` under `v` hold when
each is a destination of a step whose value `v` gives as the reading of its source's half, or a
register of `live` that no step writes. -/
theorem widen_holds {R R' : Nat → Option Value} {live live' : List Nat} {v : Nat → Value}
    {ws : List Widen} (h : Holds R (factsFrom live v))
    (hfr : ∀ r, (∀ w ∈ ws, r ∉ w.writes) → R' r = R r)
    (hw : ∀ w ∈ ws, ∀ x, R w.src = some x →
      R' w.dlo = some (.float .f32 (rd16 (splitValue 32 x).1)) ∧
      R' w.dhi = some (.float .f32 (rd16 (splitValue 32 x).2)))
    (hsrc : ∀ w ∈ ws, w.src ∈ live)
    (hval : ∀ w ∈ ws, v w.dlo = .float .f32 (rd16 (splitValue 32 (v w.src)).1) ∧
      v w.dhi = .float .f32 (rd16 (splitValue 32 (v w.src)).2))
    (hcov : ∀ r ∈ live', (∃ w ∈ ws, r = w.dlo ∨ r = w.dhi) ∨ (r ∈ live ∧ ∀ w ∈ ws, r ∉ w.writes)) :
    Holds R' (factsFrom live' v) := by
  refine holds_of_pointwise fun r hr => ?_
  rcases hcov r hr with ⟨w, hm, hr' | hr'⟩ | ⟨hl, hn⟩
  · have hs := holds_mem h (mem_factsFrom (hsrc w hm))
    rw [hr', (hw w hm _ hs).1, (hval w hm).1]
  · have hs := holds_mem h (mem_factsFrom (hsrc w hm))
    rw [hr', (hw w hm _ hs).2, (hval w hm).2]
  · rw [hfr r hn]
    exact holds_mem h (mem_factsFrom hl)

/-! ### Single-precision addition of two registers -/

/-- **The ideal step of an addition**: with both operands as single-precision numbers, the local
step is their sum. -/
theorem exec_fadd (hA : Assumption.IdealFor A (.add .f32)) {t : TState} {ftz : Bool}
    {d a b : Nat}
    {va vb : Value} {x y : ℝ} (ha : t.regs a = some va) (hb : t.regs b = some vb)
    (hx : valFloat .f32 va = .ok x) (hy : valFloat .f32 vb = .ok y) :
    execLocalA A L g t (.float
      { op := .add, ty := FTy.mk .f32 1, ftz := ftz, dsts := [some d],
        srcs := [.reg a, .reg b] }) =
      .ok (PTX.next (setReg t d (.float .f32 (x + y)))) := by
  have hbr : Assumption.readERealOpnd t .f32 (.reg a) = some (.ok (x : EReal)) := by
    rw [readERealOpnd_reg ha]; exact readEReal_of_valFloat hx
  have hbi : Assumption.readERealOpnd t .f32 (.reg b) = some (.ok (y : EReal)) := by
    rw [readERealOpnd_reg hb]; exact readEReal_of_valFloat hy
  have hadd : ((x : EReal) + (y : EReal)) = ((x + y : ℝ) : EReal) := by
    push_cast; ring_nf
  have hadd' : Assumption.addEReal (x : EReal) (y : EReal) = some ((x + y : ℝ) : EReal) := by
    rw [Assumption.addEReal, ite_eq_right (by simp), hadd]
  have hval : Assumption.erealValue .f32 ((x + y : ℝ) : EReal) = .float .f32 (x + y) := by
    unfold Assumption.erealValue
    rw [ite_eq_right (by simp), ite_eq_right (by simp)]
    rfl
  have hex : Assumption.execIdealFloat L g t (.float
      { op := .add, ty := FTy.mk .f32 1, ftz := ftz, dsts := [some d],
        srcs := [.reg a, .reg b] }) =
      some (.ok (PTX.next (setReg t d (Assumption.erealValue .f32 ((x + y : ℝ) : EReal))))) := by
    simp only [Assumption.execIdealFloat, hbr, hbi, Assumption.bindRead, hadd', pure,
      Except.pure]
    rfl
  rw [hA L g t _ (by simp [Assumption.FloatForm.ofOp]) _ hex, hval]

/-- **An addition whose operands read as floats** is a local step to their sum. -/
theorem fadd_tau (hA : Assumption.IdealFor A (.add .f32)) {t : TState} {ftz : Bool}
    {d a b : Nat}
    {va vb : Value} {x y : ℝ}
    (hc : K.code[t.pc]? = some ⟨none, .float
      { op := .add, ty := FTy.mk .f32 1, ftz := ftz, dsts := [some d],
        srcs := [.reg a, .reg b] }⟩)
    (hf : t.fault = none)
    (ha : t.regs a = some va) (hb : t.regs b = some vb) (hx : valFloat .f32 va = .ok x)
    (hy : valFloat .f32 vb = .ok y) :
    out K A L g t = .tau (PTX.next (setReg t d (.float .f32 (x + y)))) := by
  simp only [out, hf, hc, guardHolds, pure, Except.pure, Op.isLocal, ↓reduceIte,
    exec_fadd hA ha hb hx hy]

/-- **The ideal rule rejects one operand of an addition**: the ideal step faults. -/
theorem exec_fadd_error {t : TState} {ftz : Bool} {d a b : Nat}
    {va vb : Value} (hA : Assumption.IdealFor A (.add .f32)) (ha : t.regs a = some va)
    (hb : t.regs b = some vb)
    (hbad : (∃ f, Assumption.readEReal .f32 va = some (.error f)) ∨
      (∃ x : EReal, Assumption.readEReal .f32 va = some (.ok x)) ∧
        ∃ f, Assumption.readEReal .f32 vb = some (.error f)) :
    ∃ f, execLocalA A L g t (.float
      { op := .add, ty := FTy.mk .f32 1, ftz := ftz, dsts := [some d],
        srcs := [.reg a, .reg b] }) =
      .error f := by
  have hop := (by simp [Assumption.FloatForm.ofOp] : Assumption.FloatForm.ofOp (.float
    { op := .add, ty := FTy.mk .f32 1, ftz := ftz, dsts := [some d],
      srcs := [.reg a, .reg b] }) = some (.add .f32))
  rcases hbad with ⟨f, hf⟩ | ⟨⟨x, hx⟩, f, hf⟩
  · have hr : Assumption.readERealOpnd t .f32 (.reg a) = some (.error f) := by
      rw [readERealOpnd_reg ha]; exact hf
    exact ⟨f, by
      have hex : Assumption.execIdealFloat L g t (.float
          { op := .add, ty := FTy.mk .f32 1, ftz := ftz, dsts := [some d],
            srcs := [.reg a, .reg b] }) = some (.error f) := by
        simp only [Assumption.execIdealFloat, hr, Assumption.bindRead]
      rw [hA L g t _ hop _ hex]⟩
  · have hi : Assumption.readERealOpnd t .f32 (.reg a) = some (.ok x) := by
      rw [readERealOpnd_reg ha]; exact hx
    have hr : Assumption.readERealOpnd t .f32 (.reg b) = some (.error f) := by
      rw [readERealOpnd_reg hb]; exact hf
    exact ⟨f, by
      have hex : Assumption.execIdealFloat L g t (.float
          { op := .add, ty := FTy.mk .f32 1, ftz := ftz, dsts := [some d],
            srcs := [.reg a, .reg b] }) = some (.error f) := by
        simp only [Assumption.execIdealFloat, hi, hr, Assumption.bindRead]
      rw [hA L g t _ hop _ hex]⟩

/-- **An addition with an operand that the ideal rule rejects**: the thread is dead. An operand
that is a NaN or an infinity is no such case: the ideal rule declines it and the Core addition
converts that datum, so the thread does not fault. -/
theorem fadd_dead (hA : Assumption.IdealFor A (.add .f32)) {t : TState} {ftz : Bool}
    {d a b : Nat}
    {va vb : Value} (hc : K.code[t.pc]? = some ⟨none, .float
      { op := .add, ty := FTy.mk .f32 1, ftz := ftz, dsts := [some d],
        srcs := [.reg a, .reg b] }⟩)
    (hf : t.fault = none) (ha : t.regs a = some va) (hb : t.regs b = some vb)
    (hbad : (∃ f, Assumption.readEReal .f32 va = some (.error f)) ∨
      (∃ x : EReal, Assumption.readEReal .f32 va = some (.ok x)) ∧
        ∃ f, Assumption.readEReal .f32 vb = some (.error f)) :
    Machine.Dead (K := K) (A := A) (L := L) (g := g) t := by
  obtain ⟨fe, hfl⟩ := exec_fadd_error hA ha hb hbad
  exact Machine.dead_of_ub (f := fe) (by
    simp only [out, hf, hc, guardHolds, pure, Except.pure, Op.isLocal, ↓reduceIte]
    rw [hfl])

/-! ### Packed multiplication of a packed pair -/

theorem exec_pack (hN : NoPack A) {t : TState} {d a b : Nat} {va vb : Value}
    (ha : t.regs a = some va) (hb : t.regs b = some vb)
    (hS : Assumption.SegFreePc A t.pc := by seg_free) :
    execLocalA A L g t (.move ⟨.pack, .int .b 64, [some d], [.reg a, .reg b]⟩) =
      (if va.bytes = 4 ∧ vb.bytes = 4 then .ok (PTX.next (setReg t d (joinValue va vb)))
      else .error .typeMismatch) := by
  simp only [hS.exec, execLocalRule_of_none (hN d a b L g t), execLocal, Op.rule,
    MoveInstr.rule, execMove, readValue, readReg]
  by_cases h : va.bytes = 4 ∧ vb.bytes = 4 <;>
    simp [h, ha, hb, DType.width, bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw]

/-- The two `.f32` elements of a pair register operand, as the ideal rule reads them. -/
theorem readERealPair_reg {L : Launch} {g : Nat} {t : TState} {r : Nat} {v : Value}
    (h : t.regs r = some v) {x0 x1 : ℝ}
    (hx0 : valFloat .f32 (splitValue 64 v).1 = .ok x0)
    (hx1 : valFloat .f32 (splitValue 64 v).2 = .ok x1) :
    Assumption.readERealPair L g t (.reg r) = some (.ok ((x0 : EReal), (x1 : EReal))) := by
  have h0 := readEReal_of_valFloat hx0
  have h1 := readEReal_of_valFloat hx1
  simp only [Assumption.readERealPair, readValue, readReg, h, pure, Except.pure]
  rw [h0, h1]

/-- **The ideal step of a packed multiplication**: with all four elements as single-precision
numbers, the local step is their elementwise product. -/
theorem exec_fmul2 (hA : Assumption.IdealAt A .mulF32x2 L g t) {d a b : Nat}
    {va vb : Value} {x0 x1 y0 y1 : ℝ} (ha : t.regs a = some va) (hb : t.regs b = some vb)
    (hx0 : valFloat .f32 (splitValue 64 va).1 = .ok x0)
    (hx1 : valFloat .f32 (splitValue 64 va).2 = .ok x1)
    (hy0 : valFloat .f32 (splitValue 64 vb).1 = .ok y0)
    (hy1 : valFloat .f32 (splitValue 64 vb).2 = .ok y1) :
    execLocalA A L g t
      (.float { op := .mul, ty := FTy.mk .f32 2, dsts := [some d], srcs := [.reg a, .reg b] }) =
      .ok (PTX.next (setReg t d (.pair (.float .f32 (x0 * y0)) (.float .f32 (x1 * y1))))) := by
  have hra := readERealPair_reg (L := L) (g := g) ha hx0 hx1
  have hrb := readERealPair_reg (L := L) (g := g) hb hy0 hy1
  have hm0 : Assumption.mulEReal (x0 : EReal) (y0 : EReal) =
      some ((x0 * y0 : ℝ) : EReal) := by
    rw [Assumption.mulEReal, ite_eq_right (by simp)]
    push_cast
    ring
  have hm1 : Assumption.mulEReal (x1 : EReal) (y1 : EReal) =
      some ((x1 * y1 : ℝ) : EReal) := by
    rw [Assumption.mulEReal, ite_eq_right (by simp)]
    push_cast
    ring
  have hv0 : Assumption.erealValue .f32 ((x0 * y0 : ℝ) : EReal) = .float .f32 (x0 * y0) := by
    unfold Assumption.erealValue
    rw [ite_eq_right (EReal.coe_ne_top (x0 * y0)), ite_eq_right (EReal.coe_ne_bot (x0 * y0))]
    rfl
  have hv1 : Assumption.erealValue .f32 ((x1 * y1 : ℝ) : EReal) = .float .f32 (x1 * y1) := by
    unfold Assumption.erealValue
    rw [ite_eq_right (EReal.coe_ne_top (x1 * y1)), ite_eq_right (EReal.coe_ne_bot (x1 * y1))]
    rfl
  have hex : Assumption.execIdealFloat L g t
      (.float { op := .mul, ty := FTy.mk .f32 2, dsts := [some d], srcs := [.reg a, .reg b] }) =
      some (.ok (PTX.next (setReg t d
        (.pair (Assumption.erealValue .f32 ((x0 * y0 : ℝ) : EReal))
          (Assumption.erealValue .f32 ((x1 * y1 : ℝ) : EReal)))))) := by
    simp only [Assumption.execIdealFloat, hra, hrb, Assumption.bindRead, hm0, hm1, pure,
      Except.pure]
  rw [hA _ (by simp [Assumption.FloatForm.ofOp]) _ hex, hv0, hv1]

/-- **A packed multiplication whose pair operand does not read**: the ideal rule faults. -/
theorem exec_fmul2_error (hA : Assumption.IdealAt A .mulF32x2 L g t) {d a b : Nat}
    {va vb : Value} (ha : t.regs a = some va) (hb : t.regs b = some vb)
    (hbad : PairFault va vb) :
    ∃ f, execLocalA A L g t (.float {
        op := .mul, ty := FTy.mk .f32 2, dsts := [some d], srcs := [.reg a, .reg b] }) =
      .error f := by
  have hop : Assumption.FloatForm.ofOp (.float {
      op := .mul, ty := FTy.mk .f32 2, dsts := [some d], srcs := [.reg a, .reg b] }) =
      some .mulF32x2 := by
    simp [Assumption.FloatForm.ofOp]
  have hra := readERealPair_reg_val (L := L) (g := g) ha
  have hrb := readERealPair_reg_val (L := L) (g := g) hb
  rcases hbad with ⟨f, hf⟩ | ⟨⟨p, hp⟩, f, hf⟩
  · refine ⟨f, ?_⟩
    have hex : Assumption.execIdealFloat L g t (.float {
        op := .mul, ty := FTy.mk .f32 2, dsts := [some d], srcs := [.reg a, .reg b] }) =
        some (.error f) := by
      simp only [Assumption.execIdealFloat, hra, hf, Assumption.bindRead]
    rw [hA _ hop _ hex]
  · refine ⟨f, ?_⟩
    have hex : Assumption.execIdealFloat L g t (.float {
        op := .mul, ty := FTy.mk .f32 2, dsts := [some d], srcs := [.reg a, .reg b] }) =
        some (.error f) := by
      simp only [Assumption.execIdealFloat, hra, hrb, hp, hf, Assumption.bindRead]
    rw [hA _ hop _ hex]

/-- **A pack and a packed multiplication**: two local steps when the words are accepted, and a
dead thread when a pair the multiplication reads faults (`PairFault`: an element without a value).
A word that is wider than the store truncates and a NaN or an infinity element is no such case, so
`pairOk` false alone does not say the thread is dead (`pairOk_false_iff`). -/
theorem pack_mul (hA : Assumption.IdealFor A .mulF32x2) (hN : NoPack A) {t : TState}
    {d d' a b c : Nat}
    {va vb vc : Value}
    (hc1 : K.code[t.pc]? = some ⟨none, .move ⟨.pack, .int .b 64, [some d], [.reg a, .reg b]⟩⟩)
    (hc2 : K.code[t.pc + 1]? = some ⟨none, (.float {
      op := .mul, ty := FTy.mk .f32 2, dsts := [some d'], srcs := [.reg d, .reg c] })⟩)
    (hf : t.fault = none)
    (ha : t.regs a = some va) (hb : t.regs b = some vb) (hcv : t.regs c = some vc) (hdc : d ≠ c)
    (hS : Assumption.NoSegments A := by hooks_off) :
    (pairOk va vb vc = true → run K A L g 2 t = some (PTX.next (setReg (PTX.next
      (setReg t d (joinValue va vb))) d' (pairMul va vb vc)))) ∧
    (PairFault (joinValue va vb) vc → Machine.Dead (K := K) (A := A) (L := L) (g := g) t) := by
  constructor
  · intro hok
    simp only [pairOk, Bool.and_eq_true, beq_iff_eq] at hok
    obtain ⟨⟨⟨⟨⟨h4a, h4b⟩, hx0⟩, hx1⟩, hy0⟩, hy1⟩ := hok
    obtain ⟨x0, hx0⟩ := ok_of_toBool hx0
    obtain ⟨x1, hx1⟩ := ok_of_toBool hx1
    obtain ⟨y0, hy0⟩ := ok_of_toBool hy0
    obtain ⟨y1, hy1⟩ := ok_of_toBool hy1
    have o1 : out K A L g t = .tau (PTX.next (setReg t d (joinValue va vb))) := by
      simp only [out, hf, hc1, guardHolds, pure, Except.pure, Op.isLocal, Op.varyingSregs,
        Opnd.varying?, List.filterMap, List.isEmpty_nil, ↓reduceIte,
        exec_pack (A := A) (L := L) (g := g) hN ha hb hS.segFreePc, h4a, h4b,
        and_self]
    set t1 := PTX.next (setReg t d (joinValue va vb))
    have r1 : t1.regs d = some (joinValue va vb) := by simp [t1, PTX.next, setReg]
    have r2 : t1.regs c = some vc := by
      simp [t1, PTX.next, setReg, Function.update_of_ne hdc.symm, hcv]
    have o2 : out K A L g t1 = .tau (PTX.next (setReg t1 d' (pairMul va vb vc))) := by
      have hc2' : K.code[t1.pc]? = some ⟨none, (.float {
        op := .mul, ty := FTy.mk .f32 2, dsts := [some d'], srcs := [.reg d, .reg c] })⟩ := hc2
      simp only [out, show t1.fault = none from hf, hc2', guardHolds, pure, Except.pure,
        Op.isLocal, ↓reduceIte, exec_fmul2 hA.at r1 r2 hx0 hx1 hy0 hy1, hx0, hx1, hy0, hy1,
        pairMul, rd32, Except.toOption, Option.getD_some]
    simp only [run, tauStep, o1, Option.bind_some, o2]
  · intro hbad
    by_cases h4 : va.bytes = 4 ∧ vb.bytes = 4
    swap
    · exact Machine.dead_of_ub (f := .typeMismatch) (by
        simp only [out, hf, hc1, guardHolds, pure, Except.pure, Op.isLocal, Op.varyingSregs,
        Opnd.varying?, List.filterMap, List.isEmpty_nil, ↓reduceIte,
          exec_pack (A := A) (L := L) (g := g) hN ha hb hS.segFreePc, h4])
    have o1 : out K A L g t = .tau (PTX.next (setReg t d (joinValue va vb))) := by
      simp only [out, hf, hc1, guardHolds, pure, Except.pure, Op.isLocal, Op.varyingSregs,
        Opnd.varying?, List.filterMap, List.isEmpty_nil, ↓reduceIte,
        exec_pack (A := A) (L := L) (g := g) hN ha hb hS.segFreePc, h4,
        and_self]
    refine Machine.dead_of_tau o1 ?_
    set t1 := PTX.next (setReg t d (joinValue va vb))
    have r1 : t1.regs d = some (joinValue va vb) := by simp [t1, PTX.next, setReg]
    have r2 : t1.regs c = some vc := by
      simp [t1, PTX.next, setReg, Function.update_of_ne hdc.symm, hcv]
    have hc2' : K.code[t1.pc]? = some ⟨none, (.float {
      op := .mul, ty := FTy.mk .f32 2, dsts := [some d'], srcs := [.reg d, .reg c] })⟩ := hc2
    obtain ⟨f, hfl⟩ := exec_fmul2_error (d := d') hA.at r1 r2 hbad
    refine Machine.dead_of_ub (f := f) ?_
    simp only [out, show t1.fault = none from hf, hc2', guardHolds, pure, Except.pure,
      Op.isLocal, ↓reduceIte]
    rw [hfl]

end
end PTX.Flow
