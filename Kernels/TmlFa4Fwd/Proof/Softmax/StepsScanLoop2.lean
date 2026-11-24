-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Data
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsScanLoop2Down
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsScanLoop2Total
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsScanLoop2Up0
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsScanLoop2Up1
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsScanLoop2Up2
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsScanLoop2Up3
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsScanLoop2Up4
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsScanLoop2Word

@[expose] public section

/-! # The softmax warps' scan: the second pass loop's sites

`stepAt_scan_loop2`: the step obligations of the `loop2` scan's eight sites (`word`, `down`, the
five `up` steps and `total`), each proved in its own file (`StepsScanLoop2Word.lean` and
friends) so that they check in parallel, and this theorem dispatching over the state's site. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem stepAt_scan_loop2 (hp : Pre p L m) (_hg : g < L.threads) (d : D)
    (hk : d.k = 0) (ha : d.acc = [])
    (hs : d.site = .word .loop2 ∨ d.site = .down .loop2 ∨ (∃ j, d.site = .up .loop2 j) ∨
      d.site = .total .loop2) :
    (codeD p L g).StepAt d := by
  rcases hs with h | h | ⟨j, h⟩ | h
  · exact stepAt_scan_loop2_word hp _hg d hk ha h
  · exact stepAt_scan_loop2_down hp _hg d hk ha h
  · fin_cases j
    · exact stepAt_scan_loop2_up0 hp _hg d hk ha h
    · exact stepAt_scan_loop2_up1 hp _hg d hk ha h
    · exact stepAt_scan_loop2_up2 hp _hg d hk ha h
    · exact stepAt_scan_loop2_up3 hp _hg d hk ha h
    · exact stepAt_scan_loop2_up4 hp _hg d hk ha h
  · exact stepAt_scan_loop2_total hp _hg d hk ha h

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
