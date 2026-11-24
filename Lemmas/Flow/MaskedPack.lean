-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Fragment
public import Lemmas.Flow.Widen
public import Lemmas.Flow.FloatOutcome

@[expose] public section

/-! # Packed payloads with one masked pattern

A proof tool for loads of two packed elements of a format `fmt` whose elements are payloads of
`fmt` or one masked bit pattern `m` (a bias tensor in `bf16` with `0xFF80`, its negative infinity,
for masked positions). The return kind is `RetKind.packedWith fmt (maskedElem fmt m)`: it accepts
a pair of two such elements, or a word of twice the format's width whose two halves are (two
masked halves that the load merged into one word). A machine that follows every accepted value
(rule M1) records each element as an `Option ℝ` (`maskedReal`: the payload, or `none` for the
mask), and the two steps that read the word evaluate on every accepted value:

* the unpack `mov.b32 {lo, hi}, w` (`unpack_masked`, `exec_unpack_masked`): it writes the two
  elements back as values (`maskedValue`), low half first;
* the widening `cvt.f32.bf16 d, h` of one half: on the mask the Core rule (THREAD-CVT) widens
  `bf16` negative infinity to `f32` negative infinity (`coreWidenBf_negInf`,
  `exec_widenBf_negInf` when no assumption selects the instruction there); a kernel assumption
  that rereads finite payloads (`readFinite`) declines on the mask (`readFinite_negInf`) and reads
  a payload as itself (`readFinite_float`). -/

namespace PTX.Flow
open PTX PTX.Proof

noncomputable section

/-- An element that is a payload of `fmt` or the masked pattern `m` of the format's width. -/
def maskedElem (fmt : FloatFmt) (m : Nat) : Value → Bool
  | .float f _ => decide (f = fmt)
  | .bits w x => w == 8 * fmt.bytes && x == BitVec.ofNat 64 m
  | _ => false

/-- The payload of an element, `none` for anything else (the mask). -/
def maskedReal : Value → Option ℝ
  | .float _ x => some x
  | _ => none

/-- The value of an element recorded as a payload or the mask. -/
def maskedValue (fmt : FloatFmt) (m : Nat) : Option ℝ → Value
  | some x => .float fmt x
  | none => .bits (8 * fmt.bytes) (BitVec.ofNat 64 m)

/-- **An accepted element is its recorded value.** -/
theorem maskedElem_eq {fmt : FloatFmt} {m : Nat} {v : Value} (h : maskedElem fmt m v = true) :
    v = maskedValue fmt m (maskedReal v) := by
  cases v with
  | float f x =>
    simp only [maskedElem, decide_eq_true_eq] at h
    subst h; rfl
  | bits w x =>
    simp only [maskedElem, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | _ => simp [maskedElem] at h

/-- An accepted element has the format's width. -/
theorem maskedElem_bytes {fmt : FloatFmt} {m : Nat} {v : Value} (h : maskedElem fmt m v = true) :
    v.bytes = fmt.bytes := by
  cases v with
  | float f x =>
    simp only [maskedElem, decide_eq_true_eq] at h
    subst h; rfl
  | bits w x =>
    simp only [maskedElem, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, -⟩ := h
    simp only [Value.bytes]
    omega
  | _ => simp [maskedElem] at h

/-- **An accepted packed word unpacks into two accepted elements**, and has twice the format's
width. -/
theorem unpack_masked {fmt : FloatFmt} {m : Nat} {v : Value}
    (h : packedWithVal fmt (maskedElem fmt m) v = true) :
    v.bytes = 2 * fmt.bytes ∧ maskedElem fmt m (splitValue (16 * fmt.bytes) v).1 = true ∧
      maskedElem fmt m (splitValue (16 * fmt.bytes) v).2 = true := by
  cases v with
  | pair a b =>
    simp only [packedWithVal, Bool.and_eq_true] at h
    obtain ⟨ha, hb⟩ := h
    refine ⟨?_, by simpa [splitValue] using ha, by simpa [splitValue] using hb⟩
    simp only [Value.bytes, maskedElem_bytes ha, maskedElem_bytes hb]
    omega
  | bits w x =>
    simp only [packedWithVal, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨rfl, h1⟩, h2⟩ := h
    refine ⟨?_, h1, h2⟩
    simp only [Value.bytes]
    omega
  | _ => simp [packedWithVal] at h

/-- The two recorded elements of an accepted packed word, low half first. -/
def maskedPair (fmt : FloatFmt) (v : Value) : Option ℝ × Option ℝ :=
  (maskedReal (splitValue (16 * fmt.bytes) v).1, maskedReal (splitValue (16 * fmt.bytes) v).2)

variable {A : List Assumption} {L : Launch} {g : Nat}

/-- **The unpack of an accepted `bf16` word** writes its two recorded elements, low half first. -/
theorem exec_unpack_masked (hN : NoUnpack A) {t : TState} {lo hi src m : Nat} {v : Value}
    (h : t.regs src = some v) (hv : packedWithVal .bf16 (maskedElem .bf16 m) v = true)
    (hS : Assumption.SegFreePc A t.pc := by seg_free) :
    execLocalA A L g t (.move ⟨.unpack, .int .b 32, [some lo, some hi], [.reg src]⟩) =
      .ok (PTX.next (setReg (setReg t lo (maskedValue .bf16 m (maskedPair .bf16 v).1)) hi
        (maskedValue .bf16 m (maskedPair .bf16 v).2))) := by
  obtain ⟨h4, h1, h2⟩ := unpack_masked hv
  have e1 := maskedElem_eq h1
  have e2 := maskedElem_eq h2
  have b1 := maskedElem_bytes h1
  have b2 := maskedElem_bytes h2
  simp only [show 16 * FloatFmt.bf16.bytes = 32 from rfl] at e1 e2 b1 b2
  rw [exec_unpack hN h hS]
  simp only [show FloatFmt.bf16.bytes = 2 from rfl] at h4 b1 b2
  simp only [h4, b1, b2, and_self, ↓reduceIte, maskedPair,
    show 16 * FloatFmt.bf16.bytes = 32 from rfl, ← e1, ← e2]

/-! ### Widening one half -/

/-- `cvt.f32.bf16 d, a`. -/
abbrev widenBfC (d : Nat) (a : Opnd) : CvtInstr :=
  { dst := .float .f32, src := .float .bf16, d := d, srcs := [a] }

/-- The value the Core conversion rule (THREAD-CVT) writes for `cvt.f32.bf16` of a register that
holds `h`: the value read as a `bf16` datum, widened. -/
def coreWidenBf (h : Value) : Exec Value :=
  classify .bf16 h >>= fun x =>
    widenElem (widenBfC 0 (.reg 0)) .f32 FloatFmt.f32.layout false x >>= fun y =>
      pure (y.toValue .f32)

/-- **The Core rule of `cvt.f32.bf16`** writes `coreWidenBf` of the register's value. -/
theorem execLocal_widenBf_core {t : TState} {d r : Nat} {v : Value} (h : t.regs r = some v) :
    execLocal L g t (.cvt (widenBfC d (.reg r))) =
      (coreWidenBf v).map fun w => PTX.next (setReg t d w) := by
  have hw : widenElem (widenBfC d (.reg r)) = widenElem (widenBfC 0 (.reg 0)) := rfl
  have hr : (Op.cvt (widenBfC d (.reg r))).rule = some .threadCvt := by
    simp [Op.rule, CvtInstr.rule, CvtInstr.exact, CvtInstr.widens]
  simp only [execLocal, hr]
  simp [execCvt, readCvtFloat, readReg, h, FType.fmt?, hw, coreWidenBf, bind, Except.bind,
    Except.map, pure, Except.pure]
  cases classify .bf16 v with
  | error e => rfl
  | ok x =>
    dsimp only
    cases widenElem (widenBfC 0 (.reg 0)) .f32 FloatFmt.f32.layout false x <;> rfl

/-- The `bf16` mask classifies as negative infinity. -/
theorem classify_negInf_bf16 :
    classify .bf16 (.bits 16 (BitVec.ofNat 64 0xFF80)) = .ok (.inf true) :=
  classify_bits (fmt := .bf16) (n := 0xFF80) (by decide) (by decide)

/-- **The Core rule widens `bf16` negative infinity to `f32` negative infinity.** -/
theorem coreWidenBf_negInf :
    coreWidenBf (.bits 16 (BitVec.ofNat 64 0xFF80)) =
      .ok (.bits 32 (BitVec.ofNat 64 0xFF800000)) := by
  have hc := classify_negInf_bf16
  unfold coreWidenBf
  rw [hc]
  rfl

/-- **The widening of the `bf16` mask** when no assumption selects the instruction at the state:
`f32` negative infinity. -/
theorem exec_widenBf_negInf {t : TState} {d r : Nat}
    (h : t.regs r = some (.bits 16 (BitVec.ofNat 64 0xFF80)))
    (hN : ∀ a ∈ A, a.localRule L g t (.cvt (widenBfC d (.reg r))) = none)
    (hS : Assumption.SegFreePc A t.pc := by seg_free) :
    execLocalA A L g t (.cvt (widenBfC d (.reg r))) =
      .ok (PTX.next (setReg t d (.bits 32 (BitVec.ofNat 64 0xFF800000)))) := by
  rw [hS.exec, execLocalRule_of_none hN, execLocal_widenBf_core h, coreWidenBf_negInf]
  all_goals rfl

/-- **A finite-operand reading declines on the `bf16` mask** (it is negative infinity). -/
theorem readFinite_negInf {t : TState} {r : Nat}
    (h : t.regs r = some (.bits 16 (BitVec.ofNat 64 0xFF80))) :
    Assumption.readFinite t .bf16 (.reg r) = none := by
  have hc := classify_negInf_bf16
  simp only [Assumption.readFinite, readERealOpnd_reg h, Assumption.readEReal, hc,
    Assumption.readEReal.ofDatum, ↓reduceIte, Assumption.bindRead, pure, Except.pure]
  simp

/-- **A finite-operand reading reads a payload as itself.** -/
theorem readFinite_float {t : TState} {r : Nat} {fmt : FloatFmt} {x : ℝ}
    (h : t.regs r = some (.float fmt x)) :
    Assumption.readFinite t fmt (.reg r) = some (.ok x) := by
  simp [Assumption.readFinite, readERealOpnd_reg h, Assumption.readEReal, Assumption.bindRead,
    pure, Except.pure]

/-- The value of a widened recorded element: the payload in `f32`, or `f32` negative infinity. -/
def maskedWiden : Option ℝ → Value
  | some x => .float .f32 x
  | none => .bits 32 (BitVec.ofNat 64 0xFF800000)

end

end PTX.Flow
