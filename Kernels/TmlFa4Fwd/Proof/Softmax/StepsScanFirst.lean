-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Data
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsScanFirstDown
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsScanFirstTotal
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsScanFirstUp0
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsScanFirstUp1
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsScanFirstUp2
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsScanFirstUp3
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsScanFirstUp4
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsScanFirstWord

@[expose] public section

/-! # The softmax warps' scan: the first's sites

`stepAt_scan_first`: the step obligations of the `first` scan's eight sites (`word`, `down`, the
five `up` steps and `total`), each proved in its own file (`StepsScanFirstWord.lean` and
friends) so that they check in parallel, and this theorem dispatching over the state's site. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
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
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
