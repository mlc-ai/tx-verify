-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Mma.Base

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Mma
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat} {ent : Nat → Value}

theorem stepAt_scan_loop (hp : Pre p L m) (_hg : g < L.threads) (d : D)
    (hs : d.site = .word .loop ∨ d.site = .down .loop ∨ (∃ j, d.site = .up .loop j) ∨
      d.site = .total .loop) :
    (code p L g ent).StepAt d := by
  have hparams := Epilogue.params hp
  obtain ⟨s, v⟩ := d
  mma_sites s

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Mma
