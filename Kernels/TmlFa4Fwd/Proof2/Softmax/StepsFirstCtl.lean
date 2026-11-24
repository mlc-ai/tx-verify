-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Softmax.Base
public import Kernels.TmlFa4Fwd.Gen.StepSoftmax

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem stepAt_first_ctl (hp : Pre p L m) (_hg : g < L.threads) (d : D)
    (hk : d.k = 0) (ha : d.acc = [])
    (hs : d.site = .wq ∨ d.site = .ws .first ∨ d.site = .wb false ∨ d.site = .fence false) :
    (codeD p L g).StepAt d := by
  have hparams := params hp
  obtain ⟨s, v, k, acc⟩ := d
  cases hk; cases ha
  soft_sites s

/-- The control sites of the first round's P part, on the control machine (`StepsP1.lean` lifts
them to the data machine). -/
theorem stepAt_first_pctl (hp : Pre p L m) (_hg : g < L.threads) (d : D)
    (hk : d.k = 0) (ha : d.acc = [])
    (hs : d.site = .pst .first 2 ∨ d.site = .pwst .first 0 ∨ d.site = .pst .first 3 ∨
      d.site = .pwst .first 1 ∨ d.site = .pws .first ∨ d.site = .pel .first ∨
      d.site = .parr2 .first) :
    (code p L g).StepAt d := by
  have hparams := params hp
  obtain ⟨s, v, k, acc⟩ := d
  cases hk; cases ha
  soft_sites s except [.pst _ _ => (by soft_tst)]

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
