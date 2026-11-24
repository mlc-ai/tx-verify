-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSteps.ArithExp1Facts

@[expose] public section

/-! # A loop tile's exponentials: part d -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem exp1D_seg {L : Launch} {g : Nat} (d : D) :
    ChainSeg L g (chainStop (chainStop (chainStop 2941 exp1A) exp1B) exp1C)
      (chainV (chainV (chainV (valueOf L g d) exp1A) exp1B) exp1C) exp1D :=
  ⟨pieceSeg_run (by decide +kernel) (by decide +kernel) (by kernel_rfl)
      (by decide +kernel) (by decide +kernel) (by decide +kernel), trivial⟩

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
