-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Loader.Base

@[expose] public section

/-! # The pointer loops' row loads

Both rounds of the pointer loop of each half of a block, in the three periods. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Loader
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g w : Nat} {ent : Nat → Value}

theorem stepAt_ptR (hp : Pre p L m) (_hg : g < L.threads) (hw : w = 14 ∨ w = 15) (d : D)
    (hk : d.k = 0) (hs : ∃ per b it, d.site = .ptR per b it) :
    (code p L g w ent).StepAt d := by
  have hparams := Epilogue.params hp
  obtain ⟨_h13, _h12, _h7, _h8⟩ := warp_facts hw
  obtain ⟨s, v, k⟩ := d
  cases hk
  obtain ⟨per, b, it, rfl⟩ := hs
  load_sites per b it

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Loader
