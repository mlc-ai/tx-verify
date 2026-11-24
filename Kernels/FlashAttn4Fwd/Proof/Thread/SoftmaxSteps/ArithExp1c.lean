-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSteps.ArithExp1Facts

@[expose] public section

/-! # A loop tile's exponentials: part c -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem exp1C_seg {L : Launch} {g : Nat} (d : D) :
    ChainSeg L g (chainStop (chainStop 2941 exp1A) exp1B)
      (chainV (chainV (valueOf L g d) exp1A) exp1B) exp1C :=
  ⟨pieceSeg_run (by decide +kernel) (by decide +kernel) (by kernel_rfl)
      (by decide +kernel) (by decide +kernel) (by decide +kernel),
    pieceSeg_sw Flow.code_3316 rfl (by decide) swMatch_3316 rfl
      (.inr ⟨by decide +kernel, by kernel_rfl⟩) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel),
    pieceSeg_sw Flow.code_3337 rfl (by decide) swMatch_3337 rfl
      (.inr ⟨by decide +kernel, by kernel_rfl⟩) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel),
    pieceSeg_run (by decide +kernel) (by decide +kernel) (by kernel_rfl)
      (by decide +kernel) (by decide +kernel) (by decide +kernel),
    pieceSeg_sw Flow.code_3364 rfl (by decide) swMatch_3364 rfl
      (.inr ⟨by decide +kernel, by kernel_rfl⟩) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel),
    pieceSeg_sw Flow.code_3385 rfl (by decide) swMatch_3385 rfl
      (.inr ⟨by decide +kernel, by kernel_rfl⟩) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel),
    pieceSeg_run (by decide +kernel) (by decide +kernel) (by kernel_rfl)
      (by decide +kernel) (by decide +kernel) (by decide +kernel),
    pieceSeg_sw Flow.code_3412 rfl (by decide) swMatch_3412 rfl
      (.inr ⟨by decide +kernel, by kernel_rfl⟩) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel),
    pieceSeg_sw Flow.code_3433 rfl (by decide) swMatch_3433 rfl
      (.inr ⟨by decide +kernel, by kernel_rfl⟩) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel), trivial⟩

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
