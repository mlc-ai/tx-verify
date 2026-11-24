-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Machine
public import Lemmas.Assumption.Facts

@[expose] public section

/-! # Values that read as floats

A proof tool. A value that reads as an operand of a floating format has that format's width
(`valFloat_bytes`). A `setp` of a register against a finite `0f` constant, read as exact real
comparison at the state, is a local step to the comparison of the register's reading when it
reads as a float, and otherwise kills the thread (`fsetp_imm`). -/

namespace PTX.Flow
open PTX

theorem bitsAsFloat_bytes {fmt : FloatFmt} {v : Value} {x : ℝ} (h : bitsAsFloat fmt v = .ok x) :
    v.bytes = fmt.bytes := by
  by_cases hv : ∃ f, v = .nan f
  · obtain ⟨f, rfl⟩ := hv
    by_cases hf : f = fmt <;>
      simp [bitsAsFloat, classify, hf, FVal.finite, bind, Except.bind, pure, Except.pure] at h
  · push Not at hv
    rw [bitsAsFloat_eq hv] at h
    split at h
    · split_ifs at h with hb
      exact hb
    · cases h

/-- A finite number of a datum, as the extended real the ideal rule reads. -/
theorem readEReal.ofDatum_finite {f : FVal} {x : ℝ} (h : f.finite = .ok x) :
    Assumption.readEReal.ofDatum (.ok f) = some (.ok (x : EReal)) := by
  cases f with
  | zero neg =>
    cases h
    simp [Assumption.readEReal.ofDatum, pure, Except.pure]
  | fin q =>
    cases h
    simp [Assumption.readEReal.ofDatum, pure, Except.pure]
  | inf neg => cases h
  | nan n => cases h

/-- A datum that reads as the number `x` is that number as an extended real, where it is finite. -/
theorem readEReal_of_classify {fmt : FloatFmt} {v : Value} {x : ℝ}
    (h : (classify fmt v).bind FVal.finite = .ok x) :
    Assumption.readEReal.ofDatum (classify fmt v) = some (.ok (x : EReal)) := by
  cases hc : classify fmt v with
  | error e => rw [hc] at h; cases h
  | ok f =>
    rw [hc] at h
    simp only [Except.bind] at h
    exact readEReal.ofDatum_finite h

/-- **A value that reads as a number of format `fmt` is that number as an extended real**: the
ideal rule reads it where the Core rule does, and a NaN or infinity operand is neither. -/
theorem readEReal_of_valFloat {fmt : FloatFmt} {v : Value} {x : ℝ}
    (h : valFloat fmt v = .ok x) : Assumption.readEReal fmt v = some (.ok (x : EReal)) := by
  cases v with
  | float f y =>
    by_cases hf : f = fmt
    · subst hf
      simp [valFloat, pure, Except.pure] at h
      subst h
      simp [Assumption.readEReal, pure, Except.pure]
    · simp only [valFloat, hf, ↓reduceIte, bitsAsFloat, Assumption.readEReal] at h ⊢
      exact readEReal_of_classify h
  | nan f =>
    by_cases hf : f = fmt <;>
      simp [valFloat, bitsAsFloat, classify, hf, FVal.finite, bind, Except.bind, pure,
        Except.pure] at h
  | _ =>
    simp only [valFloat, bitsAsFloat] at h
    exact readEReal_of_classify h

/-- The ideal rule reads a register operand as the value the register holds. -/
theorem readERealOpnd_reg {t : TState} {fmt : FloatFmt} {r : Nat} {v : Value}
    (h : t.regs r = some v) :
    Assumption.readERealOpnd t fmt (.reg r) = Assumption.readEReal fmt v := by
  simp [Assumption.readERealOpnd, readReg, h, pure, Except.pure]

/-- A value that reads as a `fmt` operand has `fmt`'s width. -/
theorem valFloat_bytes {fmt : FloatFmt} {v : Value} {x : ℝ} (h : valFloat fmt v = .ok x) :
    v.bytes = fmt.bytes := by
  cases v with
  | float f y =>
    simp only [valFloat] at h
    split_ifs at h with hf
    · subst hf; rfl
    · exact bitsAsFloat_bytes h
  | _ => exact bitsAsFloat_bytes h

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- **A comparison with a finite constant**: when the register reads as `x`, a local step
writes the comparison of `x` with the constant's reading `y`; when the ideal rule rejects the
register's value the thread is dead. An operand that is a NaN or an infinity makes the ideal rule
decline and leaves the Core comparison, which does not fault, so the fault facts are about the
operands the ideal rule rejects. -/
theorem fsetp_imm {t : TState} {fc : FCmp} {cmp : Cmp} {ftz : Bool} {d a b : Nat} {v : Value}
    {y : ℝ}
    (hc : K.code[t.pc]? = some ⟨none, .float
      { op := .setp fc none, ty := FTy.mk .f32 1, ftz := ftz, dsts := [some d],
        srcs := [.reg a, .f32imm b] }⟩)
    (hfcm : fc = .ord cmp ∨ fc = .unord cmp)
    (hinf : Assumption.isInfConst (.f32imm b) = false)
    (hI : Assumption.IdealAt A (.setp .f32) L g t) (hf : t.fault = none)
    (ha : t.regs a = some v) (hy : valFloat .f32 (.bits 32 (BitVec.ofNat 64 b)) = .ok y) :
    (∀ x, valFloat .f32 v = .ok x → out K A L g t =
      .tau (PTX.next (setReg t d (.pred (Assumption.erealCompare cmp (x : EReal) (y : EReal))))))
    ∧ (∀ f, Assumption.readEReal .f32 v = some (.error f) →
      Machine.Dead (K := K) (A := A) (L := L) (g := g) t) := by
  have hinf' : Assumption.isInfConst (.reg a) = false := rfl
  have hop : Assumption.FloatForm.ofOp (.float
      { op := .setp fc none, ty := FTy.mk .f32 1, ftz := ftz, dsts := [some d],
        srcs := [.reg a, .f32imm b] }) = some (.setp .f32) := by
    rcases hfcm with rfl | rfl <;>
      simp [Assumption.FloatForm.ofOp, hinf, hinf']
  constructor
  · intro x hx
    have hxr : Assumption.readEReal .f32 v = some (.ok (x : EReal)) := readEReal_of_valFloat hx
    have hyr : Assumption.readEReal .f32 (.bits 32 (BitVec.ofNat 64 b)) =
        some (.ok (y : EReal)) := readEReal_of_valFloat hy
    have hbr : Assumption.readERealOpnd t .f32 (.reg a) = some (.ok (x : EReal)) := by
      rw [readERealOpnd_reg ha]; exact hxr
    have hbi : Assumption.readERealOpnd t .f32 (.f32imm b) = some (.ok (y : EReal)) := by
      simpa [Assumption.readERealOpnd] using hyr
    have hex : Assumption.execIdealFloat L g t (.float
        { op := .setp fc none, ty := FTy.mk .f32 1, ftz := ftz, dsts := [some d],
          srcs := [.reg a, .f32imm b] }) =
        some (.ok (PTX.next (setReg t d
          (.pred (Assumption.erealCompare cmp (x : EReal) (y : EReal)))))) := by
      rcases hfcm with rfl | rfl <;>
        simp only [Assumption.execIdealFloat, hbr, hbi, Assumption.bindRead, pure, Except.pure]
    have hstep := hI _ hop _ hex
    simp only [out, hf, hc, guardHolds, pure, Except.pure, Op.isLocal, ↓reduceIte, hstep]
  · intro f hx
    have hxr : Assumption.readERealOpnd t .f32 (.reg a) = some (.error f) := by
      rw [readERealOpnd_reg ha]; exact hx
    have hex : Assumption.execIdealFloat L g t (.float
        { op := .setp fc none, ty := FTy.mk .f32 1, ftz := ftz, dsts := [some d],
          srcs := [.reg a, .f32imm b] }) = some (.error f) := by
      rcases hfcm with rfl | rfl <;>
        simp only [Assumption.execIdealFloat, hxr, Assumption.bindRead]
    exact Machine.dead_of_ub (f := f) (by
      simp only [out, hf, hc, guardHolds, pure, Except.pure, Op.isLocal, ↓reduceIte,
        hI _ hop _ hex])

end PTX.Flow
