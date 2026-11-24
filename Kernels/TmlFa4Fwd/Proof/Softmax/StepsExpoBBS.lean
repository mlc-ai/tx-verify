-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsExpoBBK
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsExpoBA
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsExpoBBE1
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Tactics.KernelRfl
import Kernels.TmlFa4Fwd.Gen.StepSoftmax

@[expose] public section

/-! # The bias round's exponents: the software path as one segment

The nine runs and eight software `exp2` instances composed (`expoBB_seg`): from the start facts of
run 0 (values `W`, of the kinds `bK0`) at pc 5977 to the end facts of run 8 at pc 6299. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Kernels.TmlFa4Fwd

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The kinds after an instance: its outputs are numbers, the other registers keep theirs. -/
theorem next_has {F : List (Nat × Value)} {m : SegMatch CuteSlot} {K : Nat → Kd}
    {y0r y1r : Nat} {a b : ℝ} (hK : ∀ r, (K r).Has (lookupD F r))
    (h0 : m.regOf CuteSlot.y0 = y0r) (h1 : m.regOf CuteSlot.y1 = y1r) (hne : y0r ≠ y1r) {r : Nat}
    (hr : r = y0r ∨ r = y1r ∨ (segKeys m CuteSlot.y0 CuteSlot.y1).contains r = false) :
    (if r == y0r || r == y1r then Kd.s .fl else K r).Has
      (valueEx (lookupD F) (segValsY m CuteSlot.y0 CuteSlot.y1 a b ++ []) r) := by
  rcases hr with rfl | rfl | hc
  · simp only [beq_self_eq_true, Bool.true_or, ↓reduceIte]
    show SK.fl.Has _
    simp only [valueEx, segValsY, List.cons_append, List.lookup, h0, beq_self_eq_true,
      Option.getD_some]
    exact has_float_fl _
  · simp only [beq_self_eq_true, Bool.or_true, ↓reduceIte]
    show SK.fl.Has _
    have hb : (r == y0r) = false := by simpa using hne.symm
    simp only [valueEx, segValsY, List.cons_append, List.lookup, h0, h1, hb, beq_self_eq_true,
      Option.getD_some]
    exact has_float_fl _
  · have hk : r ∉ segKeys m CuteSlot.y0 CuteSlot.y1 := by simpa using hc
    have hr0 : r ≠ y0r := by rintro rfl; exact hk (by simp [segKeys, h0])
    have hr1 : r ≠ y1r := by rintro rfl; exact hk (by simp [segKeys, h1])
    have hb : (r == y0r || r == y1r) = false := by simp [hr0, hr1]
    rw [hb]
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hn : (segValsY m CuteSlot.y0 CuteSlot.y1 a b ++ []).lookup r = none := by
      rw [List.append_nil, List.lookup_eq_none_iff]
      intro q hq
      simp only [bne_iff_ne, ne_eq]
      intro e
      apply hk
      rw [← segValsY_keys (y₀ := a) (y₁ := b)]
      exact List.mem_map.mpr ⟨q, hq, by simpa using e.symm⟩
    simp only [valueEx, hn, Option.getD_none]
    exact hK r

/-- A lane input of a kind at most `ni` is `ni`. -/
theorem ni_of_kind {k : Kd} {v : Value} (h : k.Has v)
    (hk : (match k with | .s s => s.le .ni | _ => false) = true) : SK.ni.Has v := by
  cases k with
  | s s => exact SK.mono hk h
  | _ => simp at hk

variable {L : Launch} {g : Nat}

/-- The kinds at each run's start. -/
theorem bK1_ok : (bK1).all (fun q => q.1 == 4668 || q.1 == 4671 ||
    !(segKeys mB6059 CuteSlot.y0 CuteSlot.y1).contains q.1) = true := by decide +kernel

theorem k0_1 (W : Nat → Value)
    (hK : ∀ r, (kOf bB0_3 r).Has (lookupD (Gen.expoBB0_facts3 (vB0 W)) r)) :
    ∀ r, (kOf bK1 r).Has (lookupD (Gen.expoBB1_facts0 (vB1 W)) r) := by
  rw [expoBB1_facts0_eq]
  refine kstart (by unfold bK1; kernel_rfl) fun q hq => ?_
  rw [mem_kList hq]
  have hc := List.all_eq_true.mp bK1_ok q hq
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
  have hr := mB6059_regs
  simp only [Prod.mk.injEq] at hr
  exact next_has hK hr.1 hr.2.1 (by decide) (by rcases hc with (h | h) | h <;> simp_all)

theorem bK2_ok : (bK2).all (fun q => q.1 == 4674 || q.1 == 4677 ||
    !(segKeys mB6091 CuteSlot.y0 CuteSlot.y1).contains q.1) = true := by decide +kernel

theorem k0_2 (W : Nat → Value)
    (hK : ∀ r, (kOf bB1_1 r).Has (lookupD (Gen.expoBB1_facts1 (vB1 W)) r)) :
    ∀ r, (kOf bK2 r).Has (lookupD (Gen.expoBB2_facts0 (vB2 W)) r) := by
  rw [expoBB2_facts0_eq]
  refine kstart (by unfold bK2; kernel_rfl) fun q hq => ?_
  rw [mem_kList hq]
  have hc := List.all_eq_true.mp bK2_ok q hq
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
  have hr := mB6091_regs
  simp only [Prod.mk.injEq] at hr
  exact next_has hK hr.1 hr.2.1 (by decide) (by rcases hc with (h | h) | h <;> simp_all)

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
