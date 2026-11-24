-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Loader.Base

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Loader
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g w : Nat} {ent : Nat → Value}

theorem stepAt_scan_loop2 (hp : Pre p L m) (_hg : g < L.threads) (hw : w = 14 ∨ w = 15) (d : D)
    (hk : d.k = 0)
    (hs : d.site = .word .loop2 ∨ d.site = .down .loop2 ∨
      (∃ j, d.site = .up .loop2 j) ∨ d.site = .total .loop2) :
    (code p L g w ent).StepAt d := by
  have hparams := Epilogue.params hp
  obtain ⟨_h13, _h12, _h7, _h8⟩ := warp_facts hw
  obtain ⟨s, v, k⟩ := d
  cases hk
  rcases hs with rfl | rfl | ⟨j, rfl⟩ | rfl
  · load_step
  · load_step
  · load_sites j
  · load_step

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Loader
