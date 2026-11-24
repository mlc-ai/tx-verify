-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Loader.Base

@[expose] public section

/-! # The rows of a steady block's V packet

Per row the two shuffles of its address and its two asynchronous copies. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Loader
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g w : Nat} {ent : Nat → Value}

theorem stepAt_rows_steadyV (hp : Pre p L m) (_hg : g < L.threads) (hw : w = 14 ∨ w = 15)
    (d : D) (hk : d.k = 0)
    (hs : (∃ i, d.site = .xl .steady true i) ∨ (∃ i, d.site = .xh .steady true i) ∨
      ∃ i c, d.site = .cp .steady true i c) :
    (code p L g w ent).StepAt d := by
  have hparams := Epilogue.params hp
  obtain ⟨_h13, _h12, _h7, _h8⟩ := warp_facts hw
  obtain ⟨s, v, k⟩ := d
  cases hk
  rcases hs with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, c, rfl⟩
  · load_sites i
  · load_sites i
  · load_sites i c

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Loader
