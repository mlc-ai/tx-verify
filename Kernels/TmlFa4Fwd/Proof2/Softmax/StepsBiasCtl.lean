-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsBiasCtlPoll
public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsBiasCtlStore

@[expose] public section

/-! # The softmax warps' control sites of one round

The biased rounds' control sites (`stepAt_bias_ctl`), in two files: the polls
(`StepsBiasCtlPoll.lean`) and the P part's control sites (`StepsBiasCtlStore.lean`).
-/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem stepAt_bias_ctl (hp : Pre p L m) (_hg : g < L.threads) (d : D)
    (hk : d.k = 0) (ha : d.acc = [])
    (hs : d.site = .ws .bias
      ∨ d.site = .wb true
      ∨ d.site = .fence true
      ∨ d.site = .stat false
      ∨ d.site = .pst .bias 2
      ∨ d.site = .pwst .bias 0
      ∨ d.site = .pst .bias 3
      ∨ d.site = .pwst .bias 1
      ∨ d.site = .pws .bias
      ∨ d.site = .pel .bias
      ∨ d.site = .parr2 .bias) :
    (codeD p L g).StepAt d := by
  rcases hs with h | h | h | h | h | h | h | h | h | h | h
  · exact stepAt_bias_ctl_poll hp _hg d hk ha (by simp [h])
  · exact stepAt_bias_ctl_poll hp _hg d hk ha (by simp [h])
  · exact stepAt_bias_ctl_poll hp _hg d hk ha (by simp [h])
  · exact stepAt_bias_ctl_poll hp _hg d hk ha (by simp [h])
  · exact stepAt_bias_ctl_store hp _hg d hk ha (by simp [h])
  · exact stepAt_bias_ctl_store hp _hg d hk ha (by simp [h])
  · exact stepAt_bias_ctl_store hp _hg d hk ha (by simp [h])
  · exact stepAt_bias_ctl_store hp _hg d hk ha (by simp [h])
  · exact stepAt_bias_ctl_store hp _hg d hk ha (by simp [h])
  · exact stepAt_bias_ctl_store hp _hg d hk ha (by simp [h])
  · exact stepAt_bias_ctl_store hp _hg d hk ha (by simp [h])

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
