-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Loader.Machine
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Proof.Loader.StepsRowsPrimeKH
import Kernels.TmlFa4Fwd.Proof.Loader.StepsRowsPrimeKL

@[expose] public section

/-! # The shuffles of the first block's K packet

Per row the two shuffles of its address, from `StepsRowsPrimeKL.lean` and `StepsRowsPrimeKH.lean`
(the copies are `StepsRowsPrimeKC.lean`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g w : Nat} {ent : Nat → Value}

theorem stepAt_rows_primeK_shfl (hp : Pre p L m) (_hg : g < L.threads) (hw : w = 14 ∨ w = 15)
    (d : D) (hk : d.k = 0)
    (hs : (∃ i, d.site = .xl .prime false i) ∨ ∃ i, d.site = .xh .prime false i) :
    (code p L g w ent).StepAt d := by
  rcases hs with h | h
  · exact stepAt_rows_primeK_xl hp _hg hw d hk h
  · exact stepAt_rows_primeK_xh hp _hg hw d hk h

end
end PTX.Kernels.TmlFa4Fwd.Proof.Loader
