-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSteps.SumTail

@[expose] public section

/-! # A loop tile's row sum, part 2

The branch out of the successful statistics poll ending a loop trip, and after the row sum the
statistics parity, the trip counter, the tile parity and the loop test. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- From the successful poll to the row sum. -/
theorem sum1_a (hpre : Pre P L mem0) (i tt : Nat) (s : Nat → Value) (m l : Value) :
    Seg kernel asms L g 1 3588 ((5666, .pred true) :: factsAt L g 3587 ⟨.statsW 2, i, tt, s, m, l⟩)
      3590 (factsAt L g 3590 ⟨.statsW 2, i, tt, s, m, l⟩) := by
  intro t h
  sm_segs h hpre

/-- After the row sum: the parities, the trip counter and the loop test (`s'` the branch's
successor); the reference maximum is still the old one, the new one in `%r177`. -/
theorem sum1_c (hpre : Pre P L mem0) (i tt : Nat) (s : Nat → Value) (m l m2 l2 : Value)
    (htr : tt + 1 < trips L) (s' : Site) (hs' : s' = .lSt ∨ s' = .sW true) :
    Seg kernel asms L g 4 3723 (factsAt L g 3723 ⟨.statsW 2, i, tt, s, m, l2⟩) 3727
      (factsX L g 3727 ⟨s', i, tt + 1, s, m2, l2⟩ [(286, .pred (decide (tt + 2 < trips L))),
          (3932, m), (512, mNV L ⟨.statsW 2, i, tt, s, m, l⟩)]) := by
  intro t h
  have hn := trips_lt hpre
  rcases hs' with rfl | rfl <;>
    sm_segs h hpre [xor_par, tileIdx_statsW2, tileIdx_sW, tileIdx_lSt]

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
