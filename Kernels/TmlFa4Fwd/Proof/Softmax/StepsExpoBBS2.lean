-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsExpoBBK
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsExpoBA
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsExpoBBE1
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsExpoBBS
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Tactics.KernelRfl
import Kernels.TmlFa4Fwd.Gen.StepSoftmax

@[expose] public section

/-! # The bias round's exponents: the software path's start kinds, part 2

The nine runs and eight software `exp2` instances composed (`expoBB_seg`): from the start facts of
run 0 (values `W`, of the kinds `bK0`) at pc 5977 to the end facts of run 8 at pc 6299. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Kernels.TmlFa4Fwd

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

variable {L : Launch} {g : Nat}

theorem bK3_ok : (bK3).all (fun q => q.1 == 4680 || q.1 == 4683 ||
    !(segKeys mB6131 CuteSlot.y0 CuteSlot.y1).contains q.1) = true := by decide +kernel

theorem k0_3 (W : Nat → Value)
    (hK : ∀ r, (kOf bB2_1 r).Has (lookupD (Gen.expoBB2_facts1 (vB2 W)) r)) :
    ∀ r, (kOf bK3 r).Has (lookupD (Gen.expoBB3_facts0 (vB3 W)) r) := by
  rw [expoBB3_facts0_eq]
  refine kstart (by unfold bK3; kernel_rfl) fun q hq => ?_
  rw [mem_kList hq]
  have hc := List.all_eq_true.mp bK3_ok q hq
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
  have hr := mB6131_regs
  simp only [Prod.mk.injEq] at hr
  exact next_has hK hr.1 hr.2.1 (by decide) (by rcases hc with (h | h) | h <;> simp_all)

theorem bK4_ok : (bK4).all (fun q => q.1 == 4686 || q.1 == 4689 ||
    !(segKeys mB6153 CuteSlot.y0 CuteSlot.y1).contains q.1) = true := by decide +kernel

theorem k0_4 (W : Nat → Value)
    (hK : ∀ r, (kOf bB3_1 r).Has (lookupD (Gen.expoBB3_facts1 (vB3 W)) r)) :
    ∀ r, (kOf bK4 r).Has (lookupD (Gen.expoBB4_facts0 (vB4 W)) r) := by
  rw [expoBB4_facts0_eq]
  refine kstart (by unfold bK4; kernel_rfl) fun q hq => ?_
  rw [mem_kList hq]
  have hc := List.all_eq_true.mp bK4_ok q hq
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
  have hr := mB6153_regs
  simp only [Prod.mk.injEq] at hr
  exact next_has hK hr.1 hr.2.1 (by decide) (by rcases hc with (h | h) | h <;> simp_all)

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
