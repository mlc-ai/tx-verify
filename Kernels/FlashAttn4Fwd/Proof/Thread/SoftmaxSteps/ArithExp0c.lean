-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSteps.ArithExp0Facts

@[expose] public section

/-! # The first tile's exponentials: part c -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem exp0C_seg {L : Launch} {g : Nat} (d : D) :
    ChainSeg L g (chainStop (chainStop 1863 exp0A) exp0B)
      (chainV (chainV (valueOf L g d) exp0A) exp0B) exp0C :=
  ⟨pieceSeg_run (by decide +kernel) (by decide +kernel) (by kernel_rfl)
      (by decide +kernel) (by decide +kernel) (by decide +kernel),
    pieceSeg_sw Flow.code_2301 rfl (by decide) swMatch_2301 rfl
      (.inr ⟨by decide +kernel, by kernel_rfl⟩) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel),
    pieceSeg_sw Flow.code_2322 rfl (by decide) swMatch_2322 rfl
      (.inr ⟨by decide +kernel, by kernel_rfl⟩) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel),
    pieceSeg_run (by decide +kernel) (by decide +kernel) (by kernel_rfl)
      (by decide +kernel) (by decide +kernel) (by decide +kernel),
    pieceSeg_sw Flow.code_2349 rfl (by decide) swMatch_2349 rfl
      (.inr ⟨by decide +kernel, by kernel_rfl⟩) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel),
    pieceSeg_sw Flow.code_2370 rfl (by decide) swMatch_2370 rfl
      (.inr ⟨by decide +kernel, by kernel_rfl⟩) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel),
    pieceSeg_run (by decide +kernel) (by decide +kernel) (by kernel_rfl)
      (by decide +kernel) (by decide +kernel) (by decide +kernel),
    pieceSeg_sw Flow.code_2397 rfl (by decide) swMatch_2397 rfl
      (.inr ⟨by decide +kernel, by kernel_rfl⟩) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel),
    pieceSeg_sw Flow.code_2418 rfl (by decide) swMatch_2418 rfl
      (.inr ⟨by decide +kernel, by kernel_rfl⟩) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel), trivial⟩

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
