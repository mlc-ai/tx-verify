-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Loader.Machine
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Proof.Loader.StepsArrSteady
import Kernels.TmlFa4Fwd.Proof.Loader.StepsArrWarm
import Kernels.TmlFa4Fwd.Proof.Loader.StepsCommit

@[expose] public section

/-! # The packets' commits and arrivals

The commit of each packet's copies and the arrival on its slot's full barrier, in the three
periods; an arrival ends the half of a block (the next half, a TMA group, the next round, the
end of the warm rounds, or the scheduler's second pass). The first block's V arrival (the
transition into the later blocks) is `StepsArrPrime.lean`. The commits are `StepsCommit.lean`,
the other arrivals `StepsArrWarm.lean` and `StepsArrSteady.lean`, which check in parallel. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g w : Nat} {ent : Nat → Value}

theorem stepAt_pk_end (hp : Pre p L m) (_hg : g < L.threads) (hw : w = 14 ∨ w = 15) (d : D)
    (hk : d.k = 0)
    (hs : (∃ per b, d.site = .commit per b) ∨
      ∃ per b, d.site = .arrive per b ∧ ¬ (per = .prime ∧ b = true)) :
    (code p L g w ent).StepAt d := by
  rcases hs with h | ⟨per, b, h, hpb⟩
  · exact stepAt_commit hp _hg hw d hk h
  · cases per
    · exact stepAt_arr_warm hp _hg hw d hk ⟨_, b, h, hpb, by decide⟩
    · exact stepAt_arr_warm hp _hg hw d hk ⟨_, b, h, hpb, by decide⟩
    · exact stepAt_arr_steady hp _hg hw d hk ⟨b, h⟩

end
end PTX.Kernels.TmlFa4Fwd.Proof.Loader
