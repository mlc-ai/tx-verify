-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Softmax.Base

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem stepAt_plain_ctl (hp : Pre p L m) (_hg : g < L.threads) (d : D)
    (hk : d.k = 0) (ha : d.acc = [])
    (hs : d.site = .ws .plain ∨ d.site = .stat true) :
    (codeD p L g).StepAt d := by
  have hparams := params hp
  obtain ⟨s, ⟨sc, ukw, nb, bt, bpar, spar, ppar, pl, sv, bk, br, mf, mr, rs⟩, k, acc⟩ := d
  cases hk; cases ha
  -- the plain round's table states its values per kind of the maximum before the round
  cases mf
  · soft_sites s
  · soft_sites s

/-- The control sites of a plain round's P part, on the control machine (`StepsPlainP.lean` lifts
them to the data machine). -/
theorem stepAt_plain_pctl (hp : Pre p L m) (_hg : g < L.threads) (d : D)
    (hk : d.k = 0) (ha : d.acc = [])
    (hs : d.site = .pst .plain 2 ∨ d.site = .pwst .plain 0 ∨ d.site = .pst .plain 3 ∨
      d.site = .pwst .plain 1 ∨ d.site = .pws .plain ∨ d.site = .pel .plain ∨
      d.site = .parr2 .plain) :
    (code p L g).StepAt d := by
  have hparams := params hp
  obtain ⟨s, v, k, acc⟩ := d
  cases hk; cases ha
  soft_sites s except [.pst _ _ => (by soft_tst)]

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
