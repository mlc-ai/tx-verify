-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsScanFirstWord
public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsScanFirstDown
public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsScanFirstUp0
public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsScanFirstUp1
public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsScanFirstUp2
public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsScanFirstUp3
public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsScanFirstUp4
public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsScanFirstTotal

@[expose] public section

/-! # The softmax warps' scan: the first's sites

`stepAt_scan_first`: the step obligations of the `first` scan's eight sites (`word`, `down`, the
five `up` steps and `total`), each proved in its own file (`StepsScanFirstWord.lean` and
friends) so that they check in parallel, and this theorem dispatching over the state's site. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem stepAt_scan_first (hp : Pre p L m) (_hg : g < L.threads) (d : D)
    (hk : d.k = 0) (ha : d.acc = [])
    (hs : d.site = .word .first ∨ d.site = .down .first ∨ (∃ j, d.site = .up .first j) ∨
      d.site = .total .first) :
    (codeD p L g).StepAt d := by
  rcases hs with h | h | ⟨j, h⟩ | h
  · exact stepAt_scan_first_word hp _hg d hk ha h
  · exact stepAt_scan_first_down hp _hg d hk ha h
  · fin_cases j
    · exact stepAt_scan_first_up0 hp _hg d hk ha h
    · exact stepAt_scan_first_up1 hp _hg d hk ha h
    · exact stepAt_scan_first_up2 hp _hg d hk ha h
    · exact stepAt_scan_first_up3 hp _hg d hk ha h
    · exact stepAt_scan_first_up4 hp _hg d hk ha h
  · exact stepAt_scan_first_total hp _hg d hk ha h

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
