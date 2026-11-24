-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSteps.ArithExp0Facts

@[expose] public section

/-! # The first tile's exponentials: part d -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem exp0D_seg {L : Launch} {g : Nat} (d : D) :
    ChainSeg L g (chainStop (chainStop (chainStop 1863 exp0A) exp0B) exp0C)
      (chainV (chainV (chainV (valueOf L g d) exp0A) exp0B) exp0C) exp0D :=
  ⟨pieceSeg_run (by decide +kernel) (by decide +kernel) (by kernel_rfl)
      (by decide +kernel) (by decide +kernel) (by decide +kernel), trivial⟩

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
