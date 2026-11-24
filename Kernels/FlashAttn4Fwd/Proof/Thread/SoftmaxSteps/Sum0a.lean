-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxBase

@[expose] public section

/-! # The first tile's row sum, part 1

The branch out of the successful second statistics poll, to the row sum. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- From the successful poll to the row sum. -/
theorem sum0_a {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} (hpre : Pre P L mem0)
    (i tt : Nat) (s : Nat → Value) (m l : Value) :
    Seg kernel asms L g 1 2575 ((5568, .pred true) :: factsAt L g 2574 ⟨.statsW 1, i, tt, s, m, l⟩)
      2577 (factsAt L g 2577 ⟨.statsW 1, i, tt, s, m, l⟩) := by
  intro t h
  sm_seg h hpre

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
