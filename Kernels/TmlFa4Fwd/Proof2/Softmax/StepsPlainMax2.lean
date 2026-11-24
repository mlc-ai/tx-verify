-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsPlainMax

@[expose] public section

/-! # A plain round's maximum after its fourth score load: the finite case

The walks of `StepsPlainMax.lean` when the maximum before the round is a real, and the step of
the implicit wait for both kinds. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
set_option seg_sym.decideHeartbeats 40000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- The implicit wait of a plain round's fourth score load when the maximum before the round is
the real `mr`. -/
theorem stepAt_sldw3T (hp : Pre p L m) (sc ukw nb bt bpar spar ppar pl sv bk br mr rs) :
    (codeD p L g).StepAt ⟨.sldw 3,
      ⟨sc, ukw, nb, bt, bpar, spar, ppar, pl, sv, bk, br, true, mr, rs⟩, 1, []⟩ := by
  have hparams := params hp
  obtain ⟨hw, hs⟩ := scl_word hp
  have hm := mulEReal_coe_bot_pos hs
  soft_sldw3 p L g (⟨sc, ukw, nb, bt, bpar, spar, ppar, pl, sv, bk, br, true, mr, rs⟩ : V)
    (.float .f32 mr)

/-- **The implicit wait of a plain round's fourth score load**: the packs, the round's maximum
and the rescaling factor, to the statistics store. -/
theorem stepAt_sldw3 (hp : Pre p L m) (v : V) :
    (codeD p L g).StepAt ⟨.sldw 3, v, 1, []⟩ := by
  obtain ⟨sc, ukw, nb, bt, bpar, spar, ppar, pl, sv, bk, br, mf, mr, rs⟩ := v
  cases mf
  · exact stepAt_sldw3F hp _ _ _ _ _ _ _ _ _ _ _ _ _
  · exact stepAt_sldw3T hp _ _ _ _ _ _ _ _ _ _ _ _ _

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
