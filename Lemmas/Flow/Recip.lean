-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.FloatRead
public import Lemmas.Flow.Cvt
public import Lemmas.Flow.Run
public import Lemmas.Flow.Scalars
public import Core.Assumption.ApproxExact

@[expose] public section

/-! # The reciprocal of a sum that may be zero

A proof tool, for `setp.ne.f32 p, a, 0f00000000; selp.f32 s, a, 0f3F800000, p;
rcp.approx.f32 r, s` (the reciprocal of `a`, or of `1` when `a` is zero): when `a` reads as
`x`, with the comparison read as exact real comparison and `rcp.approx` as the exact `1 / x`
(ASM-APPROX), three local steps write `r` with `1 / x'`, `x' = x` or `1` if `x = 0`
(`recip_run`). The constants `0f3F800000` and `0f00000000` read as `1` and `0`. -/

namespace PTX.Flow
open PTX PTX.Proof

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

theorem f32Value_one : f32Value 1065353216 = some 1 := by
  simp [f32Value, FloatFmt.decode, FloatFmt.layout, Layout.decode, Layout.fieldVal,
    Layout.magnitude, Layout.bias, Layout.width, FVal.num]
  norm_num

/-- `0f3F800000` reads as `1`. -/
theorem valFloat_one : valFloat .f32 (.bits 32 (BitVec.ofNat 64 1065353216)) = .ok 1 := by
  have := valFloat_b32 (b := 1065353216) (by norm_num) f32Value_one
  simpa [b32] using this

/-- `0f00000000` reads as `0`. -/
theorem valFloat_zero : valFloat .f32 (.bits 32 (BitVec.ofNat 64 0)) = .ok 0 := valFloat_z0

/-- No assumption of `A` names the selection of `selp` against a `0f` constant. -/
def NoSelp (A : List Assumption) : Prop := ∀ (d a p : Nat) (L : Launch) (g : Nat) (t : TState),
  ∀ x ∈ A, x.localRule L g t (.int ⟨.selp, .float .f32, false, [some d],
    [.reg a, .f32imm 1065353216, .reg p]⟩) = none

/-- The comparison of a real with `0` in the extended reals. -/
theorem erealCompare_ne_coe_zero (x : ℝ) :
    Assumption.erealCompare .ne (x : EReal) ((0 : ℝ) : EReal) = decide (x ≠ 0) := by
  simp [Assumption.erealCompare]

/-- The state after the three steps. -/
def recipState (t : TState) (p s r : Nat) (v : Value) (x : ℝ) : TState :=
  PTX.next (setReg (PTX.next (setReg (PTX.next (setReg t p (.pred (decide (x ≠ 0)))))
    s (if x ≠ 0 then v else .bits 32 (BitVec.ofNat 64 1065353216))))
    r (fl (1 / (if x = 0 then 1 else x))))

/-- **The reciprocal of a value that may be zero**: three local steps. -/
theorem recip_run {t : TState} {ftz ftz' : Bool} {p a s r : Nat} {v : Value} {x : ℝ}
    (h1 : K.code[t.pc]? = some ⟨none, .float
      { op := .setp (.ord .ne) none, ty := FTy.mk .f32 1, ftz := ftz, dsts := [some p],
        srcs := [.reg a, .f32imm 0] }⟩)
    (h2 : K.code[t.pc + 1]? =
      some ⟨none, .int ⟨.selp, .float .f32, false, [some s], [.reg a, .f32imm 1065353216, .reg p]⟩⟩)
    (h3 : K.code[t.pc + 2]? = some ⟨none, .float
      { op := .rcp, ty := FTy.mk .f32 1, mode := .approx, ftz := ftz', dsts := [some r],
        srcs := [.reg s] }⟩)
    (hpa : p ≠ a)
    (hf : t.fault = none) (ha : t.regs a = some v) (hx : valFloat .f32 v = .ok x)
    (hI : Assumption.IdealAt A (.setp .f32) L g t)
    (hN : NoSelp A)
    (hS : Assumption.SegFreePc A (t.pc + 1))
    (hR : ∀ t' : TState, t'.pc = t.pc + 2 → ∀ e,
      Assumption.execApproxExact t' (.float
        { op := .rcp, ty := FTy.mk .f32 1, mode := .approx, ftz := ftz', dsts := [some r],
          srcs := [.reg s] }) = some e →
      execLocalA A L g t' (.float
        { op := .rcp, ty := FTy.mk .f32 1, mode := .approx, ftz := ftz', dsts := [some r],
          srcs := [.reg s] }) = e) :
    run K A L g 3 t = some (recipState t p s r v x) := by
  have o1 : out K A L g t = .tau (PTX.next (setReg t p (.pred (decide (x ≠ 0))))) := by
    have h := (fsetp_imm h1 (Or.inl rfl) rfl hI hf ha valFloat_zero).1 x hx
    rw [h, erealCompare_ne_coe_zero]
  set t1 := PTX.next (setReg t p (.pred (decide (x ≠ 0))))
  have o1' : out K A L g t = .tau t1 := o1
  have hb : v.bytes = 4 := valFloat_bytes hx
  have hp1 : t1.regs p = some (.pred (decide (x ≠ 0))) := by simp [t1, PTX.next, setReg]
  have ha1 : t1.regs a = some v := by
    simp [t1, PTX.next, setReg, Function.update_of_ne hpa.symm, ha]
  set v2 : Value := if x ≠ 0 then v else .bits 32 (BitVec.ofNat 64 1065353216)
  set t2 := PTX.next (setReg t1 s v2)
  have o2 : out K A L g t1 = .tau t2 := by
    have hc2 : K.code[t1.pc]? = some ⟨none, .int ⟨.selp, .float .f32, false, [some s],
        [.reg a, .f32imm 1065353216, .reg p]⟩⟩ := h2
    have hex : execLocalA A L g t1 (.int ⟨.selp, .float .f32, false, [some s],
        [.reg a, .f32imm 1065353216, .reg p]⟩) = .ok t2 := by
      rw [(hS.at rfl).exec, execLocalRule_of_none (hN s a p L g t1)]
      by_cases hx0 : x = 0
      · simp [execLocal_selp (i := ⟨.selp, .float .f32, false, [some s],
          [.reg a, .f32imm 1065353216, .reg p]⟩) rfl, execMove, DType.width, readReg, hp1, hx0,
          readValue, readBits, v2, t2, bind, Except.bind, pure, Except.pure, Value.bytes]
      · simp [execLocal_selp (i := ⟨.selp, .float .f32, false, [some s],
          [.reg a, .f32imm 1065353216, .reg p]⟩) rfl, execMove, DType.width, readReg, hp1, hx0,
          readValue, ha1, hb, v2, t2, bind, Except.bind, pure, Except.pure]
    simp only [out, show t1.fault = none from hf, hc2, guardHolds, pure, Except.pure,
      Op.isLocal, Op.varyingSregs, Opnd.varying?, List.filterMap, List.isEmpty_nil, ↓reduceIte, hex]
  have hs2 : t2.regs s = some v2 := by simp [t2, PTX.next, setReg]
  have hx2 : valFloat .f32 v2 = .ok (if x = 0 then 1 else x) := by
    by_cases hx0 : x = 0
    · simp [v2, hx0, valFloat_one]
    · simp [v2, hx0, hx]
  have o3 : out K A L g t2 = .tau (recipState t p s r v x) := by
    have hc3 : K.code[t2.pc]? = some ⟨none, .float
      { op := .rcp, ty := FTy.mk .f32 1, mode := .approx, ftz := ftz', dsts := [some r],
        srcs := [.reg s] }⟩ := h3
    have hne : (if x = 0 then (1 : ℝ) else x) ≠ 0 := by split_ifs with h <;> simp [h]
    have hr : Assumption.readERealOpnd t2 .f32 (.reg s) =
        some (.ok (((if x = 0 then 1 else x : ℝ)) : EReal)) := by
      rw [readERealOpnd_reg hs2]; exact readEReal_of_valFloat hx2
    have hex : Assumption.execApproxExact t2 (.float
        { op := .rcp, ty := FTy.mk .f32 1, mode := .approx, ftz := ftz', dsts := [some r],
          srcs := [.reg s] }) =
        some (.ok (PTX.next (setReg t2 r (fl (1 / (if x = 0 then 1 else x)))))) := by
      simp [Assumption.execApproxExact, Assumption.readFinite, hr, Assumption.bindRead, hne,
        fl, pure, Except.pure]
    simp only [out, show t2.fault = none from hf, hc3, guardHolds, pure, Except.pure,
      Op.isLocal, ↓reduceIte, hR t2 rfl _ hex]
    rfl
  simp only [run, tauStep, o1', o2, o3, Option.bind_some]

/-- The comparison's operand makes the ideal rule reject it: the thread is dead. -/
theorem recip_dead {t : TState} {ftz : Bool} {p a : Nat} {v : Value} {f : Fault}
    (h1 : K.code[t.pc]? = some ⟨none, .float
      { op := .setp (.ord .ne) none, ty := FTy.mk .f32 1, ftz := ftz, dsts := [some p],
        srcs := [.reg a, .f32imm 0] }⟩)
    (hf : t.fault = none) (ha : t.regs a = some v)
    (hx : Assumption.readEReal .f32 v = some (.error f))
    (hI : Assumption.IdealAt A (.setp .f32) L g t) :
    Machine.Dead (K := K) (A := A) (L := L) (g := g) t :=
  (fsetp_imm h1 (Or.inl rfl) rfl hI hf ha valFloat_zero).2 f hx

end
end PTX.Flow
