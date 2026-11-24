-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSteps.ArithExp0Facts

@[expose] public section

/-! # The first tile's exponentials: part b -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem exp0B_seg {L : Launch} {g : Nat} (d : D) :
    ChainSeg L g (chainStop 1863 exp0A)
      (chainV (valueOf L g d) exp0A) exp0B :=
  ⟨pieceSeg_sw Flow.code_2121 rfl (by decide) swMatch_2121 rfl
      (.inl rfl) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel),
    pieceSeg_sw Flow.code_2152 rfl (by decide) swMatch_2152 rfl
      (.inr ⟨by decide +kernel, by kernel_rfl⟩) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel),
    pieceSeg_run (by decide +kernel) (by decide +kernel) (by kernel_rfl)
      (by decide +kernel) (by decide +kernel) (by decide +kernel),
    pieceSeg_sw Flow.code_2179 rfl (by decide) swMatch_2179 rfl
      (.inr ⟨by decide +kernel, by kernel_rfl⟩) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel),
    pieceSeg_sw Flow.code_2200 rfl (by decide) swMatch_2200 rfl
      (.inr ⟨by decide +kernel, by kernel_rfl⟩) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel),
    pieceSeg_run (by decide +kernel) (by decide +kernel) (by kernel_rfl)
      (by decide +kernel) (by decide +kernel) (by decide +kernel),
    pieceSeg_sw Flow.code_2227 rfl (by decide) swMatch_2227 rfl
      (.inr ⟨by decide +kernel, by kernel_rfl⟩) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel),
    pieceSeg_sw Flow.code_2248 rfl (by decide) swMatch_2248 rfl
      (.inr ⟨by decide +kernel, by kernel_rfl⟩) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel), trivial⟩

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
