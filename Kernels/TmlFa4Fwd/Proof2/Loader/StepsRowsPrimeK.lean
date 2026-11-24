-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Loader.StepsRowsPrimeKS
public import Kernels.TmlFa4Fwd.Proof2.Loader.StepsRowsPrimeKC

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Loader
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g w : Nat} {ent : Nat → Value}

theorem stepAt_rows_primeK (hp : Pre p L m) (_hg : g < L.threads) (hw : w = 14 ∨ w = 15)
    (d : D) (hk : d.k = 0)
    (hs : (∃ i, d.site = .xl .prime false i) ∨ (∃ i, d.site = .xh .prime false i) ∨
      ∃ i c, d.site = .cp .prime false i c) :
    (code p L g w ent).StepAt d := by
  rcases hs with h | h | h
  · exact stepAt_rows_primeK_shfl hp _hg hw d hk (.inl h)
  · exact stepAt_rows_primeK_shfl hp _hg hw d hk (.inr h)
  · exact stepAt_rows_primeK_cp hp _hg hw d hk h

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Loader
