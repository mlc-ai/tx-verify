-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsExpoBBK2
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsExpoBA
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsExpoBBE2
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsExpoBBS
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Tactics.KernelRfl
import Kernels.TmlFa4Fwd.Gen.StepSoftmax

@[expose] public section

/-! # The bias round's exponents: the software path's start kinds, part 4

The nine runs and eight software `exp2` instances composed (`expoBB_seg`): from the start facts of
run 0 (values `W`, of the kinds `bK0`) at pc 5977 to the end facts of run 8 at pc 6299. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Kernels.TmlFa4Fwd

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

variable {L : Launch} {g : Nat}

theorem bK7_ok : (bK7).all (fun q => q.1 == 4704 || q.1 == 4707 ||
    !(segKeys mB6255 CuteSlot.y0 CuteSlot.y1).contains q.1) = true := by decide +kernel

theorem k0_7 (W : Nat → Value)
    (hK : ∀ r, (kOf bB6_1 r).Has (lookupD (Gen.expoBB6_facts1 (vB6 W)) r)) :
    ∀ r, (kOf bK7 r).Has (lookupD (Gen.expoBB7_facts0 (vB7 W)) r) := by
  rw [expoBB7_facts0_eq]
  refine kstart (by unfold bK7; kernel_rfl) fun q hq => ?_
  rw [mem_kList hq]
  have hc := List.all_eq_true.mp bK7_ok q hq
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
  have hr := mB6255_regs
  simp only [Prod.mk.injEq] at hr
  exact next_has hK hr.1 hr.2.1 (by decide) (by rcases hc with (h | h) | h <;> simp_all)

theorem bK8_ok : (bK8).all (fun q => q.1 == 4710 || q.1 == 7252 ||
    !(segKeys mB6277 CuteSlot.y0 CuteSlot.y1).contains q.1) = true := by decide +kernel

theorem k0_8 (W : Nat → Value)
    (hK : ∀ r, (kOf bB7_1 r).Has (lookupD (Gen.expoBB7_facts1 (vB7 W)) r)) :
    ∀ r, (kOf bK8 r).Has (lookupD (Gen.expoBB8_facts0 (vB8 W)) r) := by
  rw [expoBB8_facts0_eq]
  refine kstart (by unfold bK8; kernel_rfl) fun q hq => ?_
  rw [mem_kList hq]
  have hc := List.all_eq_true.mp bK8_ok q hq
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
  have hr := mB6277_regs
  simp only [Prod.mk.injEq] at hr
  exact next_has hK hr.1 hr.2.1 (by decide) (by rcases hc with (h | h) | h <;> simp_all)

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
