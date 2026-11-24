-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSteps.ArithExp1Facts

@[expose] public section

/-! # A loop tile's exponentials: part b -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem exp1B_seg {L : Launch} {g : Nat} (d : D) :
    ChainSeg L g (chainStop 2941 exp1A)
      (chainV (valueOf L g d) exp1A) exp1B :=
  ⟨pieceSeg_sw Flow.code_3136 rfl (by decide) swMatch_3136 rfl
      (.inl rfl) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel),
    pieceSeg_sw Flow.code_3167 rfl (by decide) swMatch_3167 rfl
      (.inr ⟨by decide +kernel, by kernel_rfl⟩) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel),
    pieceSeg_run (by decide +kernel) (by decide +kernel) (by kernel_rfl)
      (by decide +kernel) (by decide +kernel) (by decide +kernel),
    pieceSeg_sw Flow.code_3194 rfl (by decide) swMatch_3194 rfl
      (.inr ⟨by decide +kernel, by kernel_rfl⟩) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel),
    pieceSeg_sw Flow.code_3215 rfl (by decide) swMatch_3215 rfl
      (.inr ⟨by decide +kernel, by kernel_rfl⟩) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel),
    pieceSeg_run (by decide +kernel) (by decide +kernel) (by kernel_rfl)
      (by decide +kernel) (by decide +kernel) (by decide +kernel),
    pieceSeg_sw Flow.code_3242 rfl (by decide) swMatch_3242 rfl
      (.inr ⟨by decide +kernel, by kernel_rfl⟩) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel),
    pieceSeg_sw Flow.code_3263 rfl (by decide) swMatch_3263 rfl
      (.inr ⟨by decide +kernel, by kernel_rfl⟩) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel), trivial⟩

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
