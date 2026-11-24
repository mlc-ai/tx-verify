-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.ProANext

@[expose] public section

/-! # The two signed divisions of the prologue

`div.s32 %r25, %r176, %r71` (pc 59, `num_iters` before the clamp) and
`div.s32 %r218, %r217, %r71` (pc 182, `num_pre` before the clamp). The evaluator has a rule for
a quotient rounded toward zero of a non-negative dividend by a positive divisor, which `ArgsOk`
(`0 < num_splits < 2 ^ 31`) and `WordsOk` (the two numerators are non-negative signed words)
provide. -/

namespace PTX.Kernels.InklingRelDecode.Proof.ProA
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- A number below `2 ^ 31` is its own signed 32-bit reading. -/
theorem intOf_s32_ofNat {n : Nat} (h : n < 2 ^ 31) :
    intOf IType.s 32 (truncBits 32 (BitVec.ofNat 64 n)) = n := by
  simp only [intOf, ↓reduceIte, toSigned, truncBits, BitVec.toNat_ofNat]
  have h1 : n % 2 ^ 64 % 2 ^ 32 = n := by
    rw [Nat.mod_mod_of_dvd _ (by decide : 2 ^ 32 ∣ 2 ^ 64)]
    exact Nat.mod_eq_of_lt (by omega)
  simp only [h1]
  have h3 : n < 2147483648 := by omega
  simp [h3]

theorem seg_59_60 (L : Launch) (g : Nat) (dt : Dat) (ha : ArgsOk L g dt.pro)
    (hw : WordsOk L g dt) :
    Seg kernel asms L g 1 59 (factsAt L g 59 dt) 60 (factsAt L g 60 dt) :=
  seg_divS32 Flow.code_59 (by asms_free) (by table_decide) (by table_decide)
    (x := v_r176 L g dt) (y := v_r71 L g dt) rfl rfl hw.2.1
    (by
      have := intOf_s32_ofNat (n := dt.pro.w71) ha.splitsRange
      show 0 < intOf IType.s 32 (truncBits 32 (BitVec.ofNat 64 dt.pro.w71))
      rw [this]; exact_mod_cast ha.splitsPos)
    rfl (by table_decide)

theorem seg_182_183 (L : Launch) (g : Nat) (dt : Dat) (ha : ArgsOk L g dt.pro)
    (hw : WordsOk L g dt) :
    Seg kernel asms L g 1 182 (factsAt L g 182 dt) 183 (factsAt L g 183 dt) :=
  seg_divS32 Flow.code_182 (by asms_free) (by table_decide) (by table_decide)
    (x := v_r217 L g dt) (y := v_r71 L g dt) rfl rfl hw.2.2
    (by
      have := intOf_s32_ofNat (n := dt.pro.w71) ha.splitsRange
      show 0 < intOf IType.s 32 (truncBits 32 (BitVec.ofNat 64 dt.pro.w71))
      rw [this]; exact_mod_cast ha.splitsPos)
    rfl (by table_decide)

/-! ### The divisions with a rule, and without -/

theorem intDiv_of_divOk {x y : BitVec 64} (h : divOk x y = true) :
    intDiv IType.s 32 (truncBits 32 x) (truncBits 32 y) =
      .ok ((intOf IType.s 32 (truncBits 32 x)).tdiv (intOf IType.s 32 (truncBits 32 y))) := by
  unfold divOk at h
  split at h
  · rename_i q hq
    rw [hq]
    unfold intDiv at hq
    simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at hq
    split_ifs at hq
    cases hq
    rfl
  · cases h

theorem divOk_of_nonneg {x y : BitVec 64} (hnn : 0 ≤ intOf IType.s 32 (truncBits 32 x))
    (hpos : 0 < intOf IType.s 32 (truncBits 32 y)) : divOk x y = true := by
  simp [divOk, intDiv_s32 hnn hpos]

/-- `div.s32 d, a, b` of two registers: one step when the division has a rule (`divOk`), and
without a rule the thread dies there. -/
theorem segD_divS32 {L : Launch} {g pc d a b : Nat} {dt : Dat} {x y : BitVec 64}
    (hc : kernel.code[pc]? = some ⟨none, .int ⟨.div, .int .s 32, false, [some d],
      [.reg a, .reg b]⟩⟩)
    (hsf : Assumption.SegFreePc asms pc) (hxa : a ∈ Flow.live pc) (hxb : b ∈ Flow.live pc)
    (ha : valueOf L g dt a = .bits 32 x) (hb : valueOf L g dt b = .bits 32 y)
    (hv : valueOf L g dt d = .bits 32 (intBits 32
      ((intOf IType.s 32 (truncBits 32 x)).tdiv (intOf IType.s 32 (truncBits 32 y)))))
    (hl : ∀ r ∈ Flow.live (pc + 1), r = d ∨ r ∈ Flow.live pc) :
    SegD kernel asms L g 1 pc (factsAt L g pc dt) (pc + 1) (factsAt L g (pc + 1) dt)
      (divOk x y = true) := by
  intro t h
  have hra : t.regs a = some (.bits 32 x) := ha ▸ holds_mem h.2.2.2.2 (mem_factsFrom hxa)
  have hrb : t.regs b = some (.bits 32 y) := hb ▸ holds_mem h.2.2.2.2 (mem_factsFrom hxb)
  have hs := Assumption.SegFreePc.of_eq h.1 hsf
  have hrule : (IntInstr.mk .div (.int .s 32) false [some d] [.reg a, .reg b]).rule =
      some .threadInt := by rfl
  have hln : (DType.int IType.s 32).intLanes? = some (IType.s, 32, 1) := by rfl
  refine ⟨fun hok => ?_, fun hno => ?_⟩
  · have hexec : execLocalA asms L g t
        (.int ⟨.div, .int .s 32, false, [some d], [.reg a, .reg b]⟩) =
        .ok (PTX.next (setReg t d (.bits 32 (intBits 32
          ((intOf IType.s 32 (truncBits 32 x)).tdiv (intOf IType.s 32 (truncBits 32 y))))))) := by
      simp only [hs.exec, execLocalRule_of_none (asms_localRule_int (t := t)),
        execLocal_int hrule, execInt]
      simp [intResult, readBits, readReg, hra, hrb, hln, intDiv_of_divOk hok, DType.width, bind,
        Except.bind, pure, Except.pure]
    exact ⟨_, run_local hc rfl h hexec, at_set_live h hv hl⟩
  · have hno' : divOk x y = false := by simpa using hno
    unfold divOk at hno'
    split at hno'
    · cases hno'
    · rename_i f hf
      refine dead_of_error (f := f) (by rw [h.1]; exact hc) rfl h.2.2.2.1 ?_
      simp only [hs.exec, execLocalRule_of_none (asms_localRule_int (t := t)),
        execLocal_int hrule, execInt]
      simp [intResult, readBits, readReg, hra, hrb, hln, hf, DType.width, bind,
        Except.bind, pure, Except.pure]

/-- The division of pc 59 (`num_iters` before the clamp), with a rule or killing the thread. -/
theorem segD_59_60 (L : Launch) (g : Nat) (dt : Dat) :
    SegD kernel asms L g 1 59 (factsAt L g 59 dt) 60 (factsAt L g 60 dt)
      (div59 L g dt = true) :=
  segD_divS32 Flow.code_59 (by asms_free) (by table_decide) (by table_decide)
    (x := v_r176 L g dt) (y := v_r71 L g dt) rfl rfl rfl (by table_decide)

/-- The division of pc 182 (`num_pre` before the clamp), with a rule or killing the thread. -/
theorem segD_182_183 (L : Launch) (g : Nat) (dt : Dat) :
    SegD kernel asms L g 1 182 (factsAt L g 182 dt) 183 (factsAt L g 183 dt)
      (div182 L g dt = true) :=
  segD_divS32 Flow.code_182 (by asms_free) (by table_decide) (by table_decide)
    (x := v_r217 L g dt) (y := v_r71 L g dt) rfl rfl rfl (by table_decide)

/-- The words of a request with `WordsOk` give both divisions a rule. -/
theorem divs_of_wordsOk {L : Launch} {g : Nat} {dt : Dat} (ha : ArgsOk L g dt.pro)
    (hw : WordsOk L g dt) : div59 L g dt = true ∧ div182 L g dt = true := by
  have hpos : 0 < intOf IType.s 32 (truncBits 32 (v_r71 L g dt)) := by
    have := intOf_s32_ofNat (n := dt.pro.w71) ha.splitsRange
    show 0 < intOf IType.s 32 (truncBits 32 (BitVec.ofNat 64 dt.pro.w71))
    rw [this]; exact_mod_cast ha.splitsPos
  exact ⟨divOk_of_nonneg hw.2.1 hpos, divOk_of_nonneg hw.2.2 hpos⟩

end
end PTX.Kernels.InklingRelDecode.Proof.ProA
