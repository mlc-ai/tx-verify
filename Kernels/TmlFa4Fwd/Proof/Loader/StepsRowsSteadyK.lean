-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Loader.Machine
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Proof.Loader.StepsRowsSteadyKC
import Kernels.TmlFa4Fwd.Proof.Loader.StepsRowsSteadyKS

@[expose] public section

/-! # The rows of a steady block's K packet

Per row the two shuffles of its address and its two asynchronous copies, from the two halves
(`StepsRowsSteadyKS.lean`, `StepsRowsSteadyKC.lean`), which check in parallel. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g w : Nat} {ent : Nat → Value}

theorem stepAt_rows_steadyK (hp : Pre p L m) (_hg : g < L.threads) (hw : w = 14 ∨ w = 15)
    (d : D) (hk : d.k = 0)
    (hs : (∃ i, d.site = .xl .steady false i) ∨ (∃ i, d.site = .xh .steady false i) ∨
      ∃ i c, d.site = .cp .steady false i c) :
    (code p L g w ent).StepAt d := by
  rcases hs with h | h | h
  · exact stepAt_rows_steadyK_shfl hp _hg hw d hk (.inl h)
  · exact stepAt_rows_steadyK_shfl hp _hg hw d hk (.inr h)
  · exact stepAt_rows_steadyK_cp hp _hg hw d hk h

end
end PTX.Kernels.TmlFa4Fwd.Proof.Loader
