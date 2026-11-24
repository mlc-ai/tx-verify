-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsBiasTail
import Kernels.TmlFa4Fwd.Flow.Code
import Std.Tactic.BVDecide.Normalize.Prop
import Kernels.TmlFa4Fwd.Proof.Softmax.Base
import Kernels.TmlFa4Fwd.Gen.StepSoftmax
import Tactics.KernelRfl

@[expose] public section

/-! # A bias round's loop tail after the row sum -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (i32 addi xor32 scmpi)
open PTX.Kernels.TmlFa4Fwd.Proof.Mma (neg32)

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- When there is no plain round, the bias loop exits into the final stores. -/
theorem pwB_fin (hp : Pre p L m) (v : V) (b : Bool) (r x : ℝ)
    (hc : scmpi .lt .s (r431 p L g v) 1 = true) :
    ∃ n, Seg kernel Assumptions.all L g n 6654 (pwBBranch p L g v b r x) 7614
      (factsD p L g (D.mk' (.fin 0) (biasTailV v b r x))) := by
  have hparams := params hp
  simp only [r431] at hc
  cases b <;> unfold pwBBranch pwBH ctlBE biasTailV <;> seg_sym using (soft_seg)

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
