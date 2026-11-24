-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.SmBits

@[expose] public section

/-! # The three floating instructions of the softmax region's setup

`seg_fp` evaluates integer and move instructions by computation; it cannot evaluate a floating
instruction whose operand is a symbolic number (`softmax_scale`, a kernel parameter). The setup
has three:

* pc 600, `div.full.f32 %r344, %r343, %r64`: `1 / softmax_scale`, read as the exact quotient by
  `Assumptions.divFullExact`;
* pc 601, `mul.f32 %r37, %r64, 0f3FB8AA3B`: `scale_log2`, read as the exact product by
  `Assumptions.idealArith` (an immediate operand);
* pc 807, `neg.f32 %r38, %r37`: `-scale_log2`, read as the exact negation by
  `Assumptions.negExact`.

Each is one local step; this file gives its execution lemma and the one-instruction segment from
the table's facts at the instruction to the table's facts at the next. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX PTX.Proof PTX.Flow PTX.Assumption

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat}

/-- `1.0` read as an `f32` number. -/
theorem valFloat_one : valFloat .f32 (b32 1065353216) = .ok (1 : ℝ) := by
  have h : f32Value 1065353216 = some (1 : ℚ) := by decide +kernel
  have := valFloat_b32 (b := 1065353216) (by norm_num) h
  simpa using this

/-- `0f3FB8AA3B` read as an `f32` number. -/
theorem valFloat_log2e : valFloat .f32 (.bits 32 (BitVec.ofNat 64 1069066811)) = .ok log2eF32 := by
  have h : f32Value 1069066811 = some (12102203 / 8388608 : ℚ) := by decide +kernel
  have := valFloat_b32 (b := 1069066811) (by norm_num) h
  show valFloat .f32 (b32 1069066811) = _
  rw [this, log2eF32]
  norm_num

/-! ### The assumptions at these pcs -/

/-- No assumption of the kernel takes a segment at a program counter outside the software `exp2`
instances. -/
theorem segFree {pc : Nat} (h : Assumptions.emuSites.contains pc = false) :
    Assumption.SegFreePc asms pc := Loader.asms_segFreePc h

/-- No assumption of the kernel has a local rule for a branch. -/
theorem localRule_bra {t : TState} {target : Nat} {uni : Bool} :
    ∀ a ∈ asms, a.localRule L g t (.bra target uni) = none := Loader.asms_localRule_bra

/-- Evaluate the assumptions of a single-instruction reading: no segment at this pc, then the
local rules in order. -/
theorem idealAt_mul {t : TState} (h : t.pc = 601) :
    Assumption.IdealAt asms (.mul .f32) L g t := by
  show Assumption.IdealAt (Assumption.idealReal _ _ _ :: _) _ L g t
  exact Assumption.idealAt_head (by decide)
    (Assumption.SegFreePc.tail (segFree (by rw [h]; decide +kernel)))

/-! ### `mul.f32` by an immediate -/

/-- `mul.f32 d, a, imm` of a register that reads as a number and an immediate that reads as one. -/
theorem exec_fmulImm {t : TState} {d a b : Nat} {va : Value} {x y : ℝ}
    (hI : IdealAt asms (.mul .f32) L g t) (ha : t.regs a = some va)
    (hx : valFloat .f32 va = .ok x) (hy : valFloat .f32 (.bits 32 (BitVec.ofNat 64 b)) = .ok y) :
    execLocalA asms L g t (.float {
        op := .mul, ty := FTy.mk .f32 1, dsts := [some d], srcs := [.reg a, .f32imm b] }) =
      .ok (PTX.next (setReg t d (.float .f32 (x * y)))) := by
  have hbr : readERealOpnd t .f32 (.reg a) = some (.ok (x : EReal)) := by
    rw [readERealOpnd_reg ha]; exact readEReal_of_valFloat hx
  have hbi : readERealOpnd t .f32 (.f32imm b) = some (.ok (y : EReal)) := by
    simpa [readERealOpnd] using readEReal_of_valFloat hy
  have hmul : mulEReal (x : EReal) (y : EReal) = some ((x * y : ℝ) : EReal) := by
    rw [Assumption.mulEReal, ite_eq_right (by simp)]
    push_cast
    ring
  have hval : erealValue .f32 ((x * y : ℝ) : EReal) = .float .f32 (x * y) := by
    unfold erealValue
    rw [ite_eq_right (EReal.coe_ne_top (x * y)), ite_eq_right (EReal.coe_ne_bot (x * y))]
    rfl
  have hop : FloatForm.ofOp (.float {
      op := .mul, ty := FTy.mk .f32 1, dsts := [some d], srcs := [.reg a, .f32imm b] }) =
      some (.mul .f32) := by
    simp [FloatForm.ofOp]
  have hex : execIdealFloat L g t (.float {
      op := .mul, ty := FTy.mk .f32 1, dsts := [some d], srcs := [.reg a, .f32imm b] }) =
      some (.ok (PTX.next (setReg t d (erealValue .f32 ((x * y : ℝ) : EReal))))) := by
    simp only [execIdealFloat, hbr, hbi, bindRead, hmul, pure, Except.pure, Option.map_some]
  rw [hI _ hop _ hex, hval]

/-! ### `div.full.f32` and `neg.f32` -/

/-- `div.full.f32 d, a, b` at pc 600 of operands that read as numbers, the divisor nonzero. -/
theorem exec_divFull {t : TState} {d a b : Nat} {va vb : Value} {x y : ℝ}
    (hpc : t.pc = 600) (ha : t.regs a = some va) (hb : t.regs b = some vb)
    (hx : valFloat .f32 va = .ok x) (hy : valFloat .f32 vb = .ok y) (hy0 : y ≠ 0) :
    execLocalA asms L g t (.float {
        op := .div, mode := .full, ty := FTy.mk .f32 1, dsts := [some d],
        srcs := [.reg a, .reg b] }) =
      .ok (PTX.next (setReg t d (.float .f32 (x / y)))) := by
  have hbr : readFinite t .f32 (.reg a) = some (.ok x) := by
    simp only [readFinite, readERealOpnd_reg ha, readEReal_of_valFloat hx, bindRead]
    simp [pure, Except.pure]
  have hbi : readFinite t .f32 (.reg b) = some (.ok y) := by
    simp only [readFinite, readERealOpnd_reg hb, readEReal_of_valFloat hy, bindRead]
    simp [pure, Except.pure]
  have h1 : Assumptions.idealArith.localRule L g t (.float {
        op := .div, mode := .full, ty := FTy.mk .f32 1, dsts := [some d],
        srcs := [.reg a, .reg b] }) = none :=
    Assumption.idealReal_localRule_none fun f h => by simp [Assumption.FloatForm.ofOp] at h
  have h2 : Assumptions.approx.localRule L g t (.float {
        op := .div, mode := .full, ty := FTy.mk .f32 1, dsts := [some d],
        srcs := [.reg a, .reg b] }) = none :=
    Assumption.approxExact_localRule_none fun f h => by simp [Assumption.ApproxForm.ofOp] at h
  have h4 : Assumptions.lg2Exact.localRule L g t (.float {
        op := .div, mode := .full, ty := FTy.mk .f32 1, dsts := [some d],
        srcs := [.reg a, .reg b] }) = none := by
    simp [Assumptions.lg2Exact, Assumptions.lg2Sites, hpc]
  have h5 : Assumptions.divFullExact.localRule L g t (.float {
        op := .div, mode := .full, ty := FTy.mk .f32 1, dsts := [some d],
        srcs := [.reg a, .reg b] }) = some (.ok (PTX.next (setReg t d (.float .f32 (x / y))))) := by
    simp [Assumptions.divFullExact, Assumptions.divFullSites, hpc, hbr, hbi, bindRead, hy0, pure,
      Except.pure]
  rw [(segFree (pc := t.pc) (by rw [hpc]; decide +kernel)).exec rfl]
  simp only [execLocalRule, asms, Assumptions.all, List.findSome?, h1, h2, h4, h5]
  rfl
/-- `neg.f32 d, a` at pc 807 of an operand that reads as a number. -/
theorem exec_neg {t : TState} {d a : Nat} {va : Value} {x : ℝ}
    (hpc : t.pc = 807) (ha : t.regs a = some va) (hx : valFloat .f32 va = .ok x) :
    execLocalA asms L g t (.float {
        op := .neg, ty := FTy.mk .f32 1, dsts := [some d], srcs := [.reg a] }) =
      .ok (PTX.next (setReg t d (.float .f32 (-x)))) := by
  have hbr : readERealOpnd t .f32 (.reg a) = some (.ok (x : EReal)) := by
    rw [readERealOpnd_reg ha]; exact readEReal_of_valFloat hx
  have hval : erealValue .f32 (-((x : ℝ) : EReal)) = .float .f32 (-x) := by
    rw [← EReal.coe_neg]
    unfold erealValue
    rw [ite_eq_right (EReal.coe_ne_top (-x)), ite_eq_right (EReal.coe_ne_bot (-x))]
    rfl
  have h1 : Assumptions.idealArith.localRule L g t (.float {
        op := .neg, ty := FTy.mk .f32 1, dsts := [some d], srcs := [.reg a] }) = none :=
    Assumption.idealReal_localRule_none fun f h => by
      simp [Assumption.FloatForm.ofOp] at h; subst h; simp
  have h2 : Assumptions.approx.localRule L g t (.float {
        op := .neg, ty := FTy.mk .f32 1, dsts := [some d], srcs := [.reg a] }) = none :=
    Assumption.approxExact_localRule_none fun f h => by simp [Assumption.ApproxForm.ofOp] at h
  have h4 : Assumptions.lg2Exact.localRule L g t (.float {
        op := .neg, ty := FTy.mk .f32 1, dsts := [some d], srcs := [.reg a] }) = none := by
    simp [Assumptions.lg2Exact, Assumptions.lg2Sites, hpc]
  have h5 : Assumptions.divFullExact.localRule L g t (.float {
        op := .neg, ty := FTy.mk .f32 1, dsts := [some d], srcs := [.reg a] }) = none := by
    simp [Assumptions.divFullExact, Assumptions.divFullSites, hpc]
  have h6 : Assumptions.negExact.localRule L g t (.float {
        op := .neg, ty := FTy.mk .f32 1, dsts := [some d], srcs := [.reg a] }) =
      some (.ok (PTX.next (setReg t d (.float .f32 (-x))))) := by
    simp [Assumptions.negExact, Assumptions.negSites, hpc, hbr, bindRead, hval, pure, Except.pure]
  rw [(segFree (pc := t.pc) (by rw [hpc]; decide +kernel)).exec rfl]
  simp only [execLocalRule, asms, Assumptions.all, List.findSome?, h1, h2, h4, h5, h6]
  rfl
/-! ### One instruction that writes one register, between the table's facts -/

/-- **One local instruction that writes one register**: from the table's facts at `pc` to the
table's facts at `pc + 1`, when the register's table value is the one the instruction computes
and every register live afterwards is that register or live before. -/
theorem seg_one {pc r : Nat} {op : Op} {v : Value} {d : D}
    (hc : kernel.code[pc]? = some ⟨none, op⟩) (hl : op.isLocal = true)
    (hex : ∀ t, At t pc (factsAt L g pc d) →
      execLocalA asms L g t op = .ok (PTX.next (setReg t r v)))
    (hv : valueOf L g d r = v) (hlive : ∀ r' ∈ Flow.live (pc + 1), r' = r ∨ r' ∈ Flow.live pc) :
    Seg kernel asms L g 1 pc (factsAt L g pc d) (pc + 1) (factsAt L g (pc + 1) d) := by
  intro t h
  refine ⟨_, run_local hc hl h (hex t h), congrArg (· + 1) h.1, h.2.1, h.2.2.1, h.2.2.2.1, ?_⟩
  refine Flow.holds_of_pointwise fun r' hr' => ?_
  by_cases hr : r' = r
  · subst hr
    simp [PTX.next, setReg, hv]
  · rcases hlive r' hr' with h' | h'
    · exact absurd h' hr
    · have := holds_mem h.2.2.2.2 (Flow.mem_factsFrom (val := valueOf L g d) h')
      simpa [PTX.next, setReg, Function.update_of_ne hr] using this

/-- **`div.full.f32` at pc 600**: `%r344 = 1 / softmax_scale`. -/
theorem seg_600 (d : D) (hok : d.e.Ok) :
    Seg kernel asms L g 1 600 (factsAt L g 600 d) 601 (factsAt L g 601 d) := by
  refine seg_one (r := 805) (v := .float .f32 (1 / d.e.sc)) Flow.code_600 rfl ?_ ?_ ?_
  · intro t h
    have h805 := holds_mem h.2.2.2.2 (Flow.mem_factsFrom (val := valueOf L g d)
      (show 804 ∈ Flow.live 600 by decide +kernel))
    have h526 := holds_mem h.2.2.2.2 (Flow.mem_factsFrom (val := valueOf L g d)
      (show 525 ∈ Flow.live 600 by decide +kernel))
    have e805 : valueOf L g d 804 = b32 1065353216 := by sm_vals
    have e526 : valueOf L g d 525 = b32 d.e.scb := by sm_vals
    rw [e805] at h805
    rw [e526] at h526
    exact exec_divFull h.1 h805 h526 valFloat_one hok.scale hok.scalePos.ne'
  · sm_vals
  · decide +kernel

/-- **`mul.f32` at pc 601**: `%r37 = softmax_scale * log2e`. -/
theorem seg_601 (d : D) (hok : d.e.Ok) :
    Seg kernel asms L g 1 601 (factsAt L g 601 d) 602 (factsAt L g 602 d) := by
  refine seg_one (r := 498) (v := .float .f32 (d.e.sc * log2eF32)) Flow.code_601 rfl ?_ ?_ ?_
  · intro t h
    have h526 := holds_mem h.2.2.2.2 (Flow.mem_factsFrom (val := valueOf L g d)
      (show 525 ∈ Flow.live 601 by decide +kernel))
    have e526 : valueOf L g d 525 = b32 d.e.scb := by sm_vals
    rw [e526] at h526
    exact exec_fmulImm (idealAt_mul h.1) h526 hok.scale valFloat_log2e
  · sm_vals
  · decide +kernel

/-- **`neg.f32` at pc 807**: `%r38 = -scale_log2`. -/
theorem seg_807 (d : D) :
    Seg kernel asms L g 1 807 (factsAt L g 807 d) 808 (factsAt L g 808 d) := by
  refine seg_one (r := 499) (v := .float .f32 (-(d.e.sc * log2eF32))) Flow.code_807 rfl ?_ ?_ ?_
  · intro t h
    have h499 := holds_mem h.2.2.2.2 (Flow.mem_factsFrom (val := valueOf L g d)
      (show 498 ∈ Flow.live 807 by decide +kernel))
    have e499 : valueOf L g d 498 = .float .f32 (d.e.sc * log2eF32) := by sm_vals
    rw [e499] at h499
    exact exec_neg h.1 h499 (by simp [valFloat, pure, Except.pure])
  · sm_vals
  · decide +kernel

/-! ### Moves of the zero half-word -/

/-- An operation that is neither a floating instruction nor a conversion takes the Core rule: no
assumption of the kernel has a local rule for it. -/
theorem asms_none {t : TState} {op : Op} (hf : ∀ f, op ≠ .float f) (hc : ∀ c, op ≠ .cvt c) :
    ∀ a ∈ asms, a.localRule L g t op = none := by
  have h1 : Assumption.FloatForm.ofOp op = none := by
    cases op <;> first | rfl | exact absurd rfl (hf _) | exact absurd rfl (hc _)
  have h2 : Assumption.ApproxForm.ofOp op = none := by
    cases op <;> first | rfl | exact absurd rfl (hf _)
  intro a ha
  simp only [asms, Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  rotate_right
  · rfl
  · exact Assumption.idealReal_localRule_none fun f h => by rw [h1] at h; cases h
  · exact Assumption.approxExact_localRule_none fun f h => by rw [h2] at h; cases h
  · rfl
  all_goals first | rfl | simp only [Assumptions.lg2Exact, Assumptions.divFullExact,
    Assumptions.negExact, Assumptions.bf16Exact]
  all_goals cases op <;> first | exact absurd rfl (hf _) | exact absurd rfl (hc _) | simp

/-- `mov.u16 d, a` of a register that holds the zero half-word. -/
theorem exec_mov16 {t : TState} {d a : Nat} (hS : Assumption.SegFreePc asms t.pc)
    (ha : t.regs a = some z16) :
    execLocalA asms L g t (.move ⟨.scalar, .int .u 16, [some d], [.reg a]⟩) =
      .ok (PTX.next (setReg t d z16)) := by
  rw [hS.exec rfl, execLocalRule_of_none (asms_none (by simp) (by simp))]
  simp [execLocal, Op.rule, MoveInstr.rule, execMove, DType.width, readValue, readReg, ha, z16,
    Value.bytes, bind, Except.bind, pure, Except.pure]

end
end PTX.Kernels.InklingRelDecode.Proof.Sm
