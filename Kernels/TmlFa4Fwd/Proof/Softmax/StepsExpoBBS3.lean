-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsExpoBBK2
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsExpoBA
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsExpoBBE1
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsExpoBBE2
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsExpoBBS
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Tactics.KernelRfl
import Kernels.TmlFa4Fwd.Gen.StepSoftmax

@[expose] public section

/-! # The bias round's exponents: the software path's start kinds, part 3

The nine runs and eight software `exp2` instances composed (`expoBB_seg`): from the start facts of
run 0 (values `W`, of the kinds `bK0`) at pc 5977 to the end facts of run 8 at pc 6299. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Kernels.TmlFa4Fwd

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

variable {L : Launch} {g : Nat}

theorem bK5_ok : (bK5).all (fun q => q.1 == 4692 || q.1 == 4695 ||
    !(segKeys mB6193 CuteSlot.y0 CuteSlot.y1).contains q.1) = true := by decide +kernel

theorem k0_5 (W : Nat → Value)
    (hK : ∀ r, (kOf bB4_1 r).Has (lookupD (Gen.expoBB4_facts1 (vB4 W)) r)) :
    ∀ r, (kOf bK5 r).Has (lookupD (Gen.expoBB5_facts0 (vB5 W)) r) := by
  rw [expoBB5_facts0_eq]
  refine kstart (by unfold bK5; kernel_rfl) fun q hq => ?_
  rw [mem_kList hq]
  have hc := List.all_eq_true.mp bK5_ok q hq
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
  have hr := mB6193_regs
  simp only [Prod.mk.injEq] at hr
  exact next_has hK hr.1 hr.2.1 (by decide) (by rcases hc with (h | h) | h <;> simp_all)

theorem bK6_ok : (bK6).all (fun q => q.1 == 4698 || q.1 == 4701 ||
    !(segKeys mB6215 CuteSlot.y0 CuteSlot.y1).contains q.1) = true := by decide +kernel

theorem k0_6 (W : Nat → Value)
    (hK : ∀ r, (kOf bB5_1 r).Has (lookupD (Gen.expoBB5_facts1 (vB5 W)) r)) :
    ∀ r, (kOf bK6 r).Has (lookupD (Gen.expoBB6_facts0 (vB6 W)) r) := by
  rw [expoBB6_facts0_eq]
  refine kstart (by unfold bK6; kernel_rfl) fun q hq => ?_
  rw [mem_kList hq]
  have hc := List.all_eq_true.mp bK6_ok q hq
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
  have hr := mB6215_regs
  simp only [Prod.mk.injEq] at hr
  exact next_has hK hr.1 hr.2.1 (by decide) (by rcases hc with (h | h) | h <;> simp_all)

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
