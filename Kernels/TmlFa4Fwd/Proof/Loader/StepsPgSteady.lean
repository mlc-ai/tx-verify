-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Loader.Machine
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Proof.Epilogue.Base
import Kernels.TmlFa4Fwd.Proof.Loader.Base
import Std.Tactic.BVDecide.Normalize.Prop
import Kernels.TmlFa4Fwd.Gen.StepEarly

@[expose] public section

/-! # The page-table loop of a steady block

Both rounds' page loads, page stores and row stores. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g w : Nat} {ent : Nat → Value}

theorem stepAt_pg_steady (hp : Pre p L m) (_hg : g < L.threads) (hw : w = 14 ∨ w = 15) (d : D)
    (hk : d.k = 0)
    (hs : (∃ it, d.site = .pgLd .steady it) ∨ (∃ it, d.site = .pgSt .steady it) ∨
      ∃ it, d.site = .rwSt .steady it) :
    (code p L g w ent).StepAt d := by
  have hparams := Epilogue.params hp
  obtain ⟨_h13, _h12, _h7, _h8⟩ := warp_facts hw
  obtain ⟨s, v, k⟩ := d
  cases hk
  rcases hs with ⟨it, rfl⟩ | ⟨it, rfl⟩ | ⟨it, rfl⟩
  · load_sites it
  · load_sites it
  · load_sites it

end
end PTX.Kernels.TmlFa4Fwd.Proof.Loader
