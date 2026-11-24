-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Data
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsScanSecondDown
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsScanSecondTotal
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsScanSecondUp0
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsScanSecondUp1
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsScanSecondUp2
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsScanSecondUp3
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsScanSecondUp4
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsScanSecondWord

@[expose] public section

/-! # The softmax warps' scan: the second's sites

`stepAt_scan_second`: the step obligations of the `second` scan's eight sites (`word`, `down`, the
five `up` steps and `total`), each proved in its own file (`StepsScanSecondWord.lean` and
friends) so that they check in parallel, and this theorem dispatching over the state's site. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem stepAt_scan_second (hp : Pre p L m) (_hg : g < L.threads) (d : D)
    (hk : d.k = 0) (ha : d.acc = [])
    (hs : d.site = .word .second ∨ d.site = .down .second ∨ (∃ j, d.site = .up .second j) ∨
      d.site = .total .second) :
    (codeD p L g).StepAt d := by
  rcases hs with h | h | ⟨j, h⟩ | h
  · exact stepAt_scan_second_word hp _hg d hk ha h
  · exact stepAt_scan_second_down hp _hg d hk ha h
  · fin_cases j
    · exact stepAt_scan_second_up0 hp _hg d hk ha h
    · exact stepAt_scan_second_up1 hp _hg d hk ha h
    · exact stepAt_scan_second_up2 hp _hg d hk ha h
    · exact stepAt_scan_second_up3 hp _hg d hk ha h
    · exact stepAt_scan_second_up4 hp _hg d hk ha h
  · exact stepAt_scan_second_total hp _hg d hk ha h

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
