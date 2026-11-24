-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsPwEBiasMasked

@[expose] public section

/-! # The first round's bias successor with a finite maximum

The segment carries the finite maximum into the biased round. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof2.Epilogue (i32 sub32 addi scmpi add32 shrs shru sel scmp andi)
open PTX.Kernels.TmlFa4Fwd.Proof2.Mma (neg32)

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 1200000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem pwBiR (hp : Pre p L m) (v : V) (x : ℝ) (r : ℝ)
    (_h1 : ¬ scmpi .lt .s (sub32 (r169 p L g v) (r299 p L g v)) 1 = true) :
    ∃ n, Seg kernel Assumptions.all L g n 5022 ((630, .pred false) ::
      pwMid p L g v (.float .f32 r) x) 5109
      (factsD p L g (D.mk' (.ws .bias) { v with
          ppar := i32 1, spar := i32 1, mf := true, mr := r, rs := x,
          nb := sub32 (r299 p L g v) (r166 p L g v), bt := addi (r169 p L g v) (-1),
          bpar := i32 1 })) := by
  have hparams := params hp
  unfold pwMid
  seg_sym using (soft_seg)

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
