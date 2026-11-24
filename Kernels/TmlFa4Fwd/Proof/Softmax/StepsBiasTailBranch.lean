-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsBiasTail
import Kernels.TmlFa4Fwd.Flow.Code
import Std.Tactic.BVDecide.Normalize.Prop
import Kernels.TmlFa4Fwd.Proof.Softmax.Base
import Kernels.TmlFa4Fwd.Gen.StepSoftmax
import Tactics.KernelRfl

@[expose] public section

/-! # The six bias loop instructions before its branch -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (i32 addi xor32 scmpi)
open PTX.Kernels.TmlFa4Fwd.Proof.Mma (neg32)

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}


theorem pwB_branch (hp : Pre p L m) (v : V) (b : Bool) (r x : ℝ) :
    ∃ n, Seg kernel Assumptions.all L g n 6647
      ((7257, .float .f32 x) :: pwBH p L g v (mxVal (biasTailV v b r x))) 6653
      (pwBBranch p L g v b r x) := by
  have hparams := params hp
  cases b <;> unfold pwBBranch pwBH ctlBE biasTailV <;> seg_sym using (soft_seg)

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
